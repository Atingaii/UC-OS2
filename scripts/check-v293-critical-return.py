#!/usr/bin/env python3
"""Saved-token/actual-return gate. Does NOT close the external port call."""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
SOURCE = 'certiucos/v293/proofs/V293CriticalReturn.v'
PROBE = 'audit/probes/V293CriticalReturnProbe.v'
ROOTS = ['V293_reserved_entry_preserves_saved', 'V293_excrit_restores_saved',
         'V293_missing_port_has_no_step', 'V293_error_return_execution',
         'V293_error_after_port_return', 'V293_error_return_locals_witness',
         'V293_reserved_saved_witness', 'V293_saved_byte_alias_counterexample']


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def changed_header(source, root, old, new):
    start = source.index('Theorem ' + root + ' :')
    end = source.index('Proof.', start)
    header = source[start:end]
    assert header.count(old) == 1
    return source[:start] + header.replace(old, new) + source[end:]


def controls(source):
    return [
        ('ForceEnabled', changed_header(source, ROOTS[1],
         '((ge,le,M),ir,(saved,si,ci)) /\\', '((ge,le,M),ir,(true,si,ci)) /\\'), ROOTS[1]),
        ('SavedAlias', changed_header(source, ROOTS[0],
         'bs <> bc ->', 'True ->'), ROOTS[0]),
        ('WrongReturn', changed_header(source, ROOTS[3],
         'sskip (Some (Vint32 (Int.repr error)))',
         'sskip (Some (Vint32 (Int.repr (error+1))))'), ROOTS[3]),
        ('NoDistinctLocals', changed_header(source, ROOTS[3],
         'NoDup (map fst (getaddr le)) ->', 'True ->'), ROOTS[3]),
    ]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path)
    args = parser.parse_args()
    out = args.output_dir or ROOT/'audit/logs/stage26-critical-token-return'/time.strftime('run-%Y%m%d-%H%M%S')
    out.mkdir(parents=True, exist_ok=False)
    inputs = {str(p.relative_to(ROOT)): sha(p) for d in ['framework', 'tactics', 'certiucos/v293']
              for p in sorted((ROOT/d).rglob('*.v'))}
    for name in [PROBE, '_CoqProject', 'scripts/check-v293-critical-return.py']:
        inputs[name] = sha(ROOT/name)
    source = (ROOT/SOURCE).read_text()
    assert 'Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn' not in source
    cases = controls(source)  # Freeze BEFORE running either positive or negative.
    report = {'inputs': inputs, 'checks': {}, 'scope': 'raw reserved entry to sfexec; actual return AFTER port; no call-to-primitive/GOOD_OS credit',
              'controls_import_candidate_module': False, 'controls_dependency': 'unchanged original 165 active sources'}
    protocol = [{'label': label, 'target': root, 'source_sha256': hashlib.sha256(s.encode()).hexdigest(),
                 'downstream_credit': False} for label, s, root in cases]
    (out/'control-protocol.json').write_text(json.dumps(protocol, indent=2)+'\n')
    coq = os.environ.get('COQBIN', '')
    def run(label, command):
        start = time.monotonic()
        with (out/(label+'.log')).open('w') as log:
            result = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT, timeout=600)
        row = {'exit_code': result.returncode, 'elapsed_seconds': time.monotonic()-start, 'log': label+'.log'}
        report['checks'][label] = row
        (out/'result.partial.json').write_text(json.dumps(report, indent=2)+'\n')
        return row
    temp = Path(tempfile.mkdtemp(prefix='v293-critical-return-'))
    try:
        assert run('production-coqc', [coq+'coqc', '-q', '-R', str(ROOT), 'CertiOS', SOURCE])['exit_code'] == 0
        assert run('probe-coqc', [coq+'coqc', '-q', '-R', str(ROOT), 'CertiOS', PROBE])['exit_code'] == 0
        for label, module in [('production', 'certiucos.v293.proofs.V293CriticalReturn'),
                              ('probe', 'audit.probes.V293CriticalReturnProbe')]:
            assert run(label+'-coqchk', [coq+'coqchk', '-silent', '-R', str(ROOT), 'CertiOS', 'CertiOS.'+module])['exit_code'] == 0
        flags = ['-q', '-R', str(ROOT), 'CertiOS', '-Q', str(temp), 'CriticalReturnControls']
        (temp/'Positive.v').write_text(source+'\n'+''.join('Print Assumptions '+r+'.\n' for r in ROOTS))
        assert run('isolated-positive', [coq+'coqc', *flags, str(temp/'Positive.v')])['exit_code'] == 0
        spec = importlib.util.spec_from_file_location('assumptions', ROOT/'scripts/check-v293-task-prio-rekey.py')
        checker = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(checker)
        report['probe_assumptions'] = checker.checked_assumptions((out/'probe-coqc.log').read_text(), 9)
        report['positive_assumptions'] = checker.checked_assumptions((out/'isolated-positive.log').read_text(), len(ROOTS))
        for label, s, root in cases:
            p = temp/(label+'.v')
            p.write_text(s)
            proof_line = s[:s.index('Proof.', s.index('Theorem '+root+' :'))].count('\n')+1
            row = run('negative-'+label, [coq+'coqc', *flags, str(p)])
            match = re.search(r'line (\d+)', (out/row['log']).read_text())
            assert row['exit_code'] == 1 and match and int(match[1]) > proof_line, row
            row.update(target=root, target_proof_line=proof_line, error_line=int(match[1]), downstream_credit=False)
        report['passed'] = True
    finally:
        manifest = [{'path': str(p), 'size': p.stat().st_size, 'sha256': sha(p)}
                    for p in sorted(temp.rglob('*')) if p.is_file()]
        (out/'temporary-cleanup.json').write_text(json.dumps(manifest, indent=2)+'\n')
        for row in manifest:
            p = Path(row['path'])
            assert p.stat().st_size == row['size'] and sha(p) == row['sha256']
        shutil.rmtree(temp)
        report['temporary_tree_removed'] = not temp.exists()
        report['inputs_unchanged'] = all(sha(ROOT/p) == h for p,h in inputs.items())
        (out/'result.json').write_text(json.dumps(report, indent=2)+'\n')
    assert report['inputs_unchanged']
    print(json.dumps({'passed': report['passed'], 'output_dir': str(out)}, indent=2))


if __name__ == '__main__':
    main()
