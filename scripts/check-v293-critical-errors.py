#!/usr/bin/env python3
"""Actual elaborated NULL/reserved returns; no raw-port or whole-API credit."""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
SOURCE = 'certiucos/v293/proofs/V293CriticalReturn.v'
PROBE = 'audit/probes/V293CriticalErrorsProbe.v'
LOOKUP = 'V293_resolve_lookup_resources'
ERROR = 'V293_lookup_error_critical_return'
WITNESS = 'V293_lookup_error_critical_witness'
ROOTS = [LOOKUP, ERROR, WITNESS]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def module(name):
    spec = importlib.util.spec_from_file_location(name, ROOT/'scripts'/name)
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


def projections(source):
    base = module('check-v293-critical-elaboration.py')
    definitions = source[:source.index('Theorem V293_critical_prefix_normalization :')]
    closure = source[source.index('(* Standard reflexive/transitive closure'):
                     source.index('(* Same program for both initial IE states;')]
    additions = source[source.index('Require Import CertiOS.framework.proof.rulesoundlib.') :]
    focused = definitions + closure + additions
    return base.through_qed(focused, LOOKUP), base.through_qed(focused, ERROR)


def controls(source):
    base = module('check-v293-critical-elaboration.py')
    lookup, error = projections(source)
    # Isolate the target statement; preserve the entire Proof suffix literally.
    def header_change(s, target, old, new):
        start = s.index('Theorem '+target+' :')
        proof = s.index('Proof.', start)
        return s[:start]+base.replace_once(s[start:proof], old, new)+s[proof:]
    skip_self = header_change(lookup, LOOKUP,
                             '(sseq (V293_task_prio_self_read oldprio current)', '(sseq (sskip None)')
    skip_lookup = header_change(lookup, LOOKUP,
                               '(sseq (V293_task_prio_lookup table oldprio ptcb) suffix)',
                               '(sseq (sskip None) suffix)')
    wrong = header_change(error, ERROR,
                          '(Int.repr (if absent then 41 else 67))',
                          '(Int.repr (if absent then 67 else 41))')
    exit_sti = base.replace_once(error,
                                'sseq (sprim excrit) (srete (econst32 (Int.repr error)))',
                                'sseq (sprim sti) (srete (econst32 (Int.repr error)))')
    cases = [('SkipSelf', skip_self, LOOKUP, lookup), ('SkipLookup', skip_lookup, LOOKUP, lookup),
             ('WrongReturn', wrong, ERROR, error), ('ExitSti', exit_sti, ERROR, error)]
    for label, changed, target, original in cases:
        i = original.index('Proof.', original.index('Theorem '+target+' :'))
        j = changed.index('Proof.', changed.index('Theorem '+target+' :'))
        assert original[i:] == changed[j:]
        assert original[:i] != changed[:j]
        assert 'Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn' not in changed
    return cases


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path, required=True)
    args = parser.parse_args()
    out = args.output_dir.resolve()
    out.mkdir(parents=True, exist_ok=False)
    base = module('check-v293-critical-elaboration.py')
    checker = module('check-v293-task-prio-rekey.py')
    inputs = {str(p.relative_to(ROOT)): sha(p) for d in ['framework', 'tactics', 'certiucos/v293']
              for p in sorted((ROOT/d).rglob('*.v'))}
    for p in [PROBE, '_CoqProject', 'scripts/check-v293-critical-errors.py',
              'scripts/check-v293-critical-elaboration.py', 'scripts/check-v293-task-prio-rekey.py',
              'csrc/config/v29301-profile.json', 'csrc/analysis-port/os_cpu.h',
              'csrc/analysis-port/app_cfg.h', 'csrc/repairs/FROZEN_SOURCE.json', 'audit/c-regressions.json']:
        inputs[p] = sha(ROOT/p)
    source = (ROOT/SOURCE).read_text()
    lookup, error = projections(source)
    positive = [('PositiveFull', source, ROOTS), ('PositiveLookup', lookup, [LOOKUP]),
                ('PositiveError', error, [ERROR])]
    cases = controls(source)
    tree = Path(tempfile.mkdtemp(prefix='v293-critical-errors-'))
    protocol = []
    for label, s, roots in positive:
        full = s+'\n'+''.join('Print Assumptions '+r+'.\n' for r in roots)
        (tree/(label+'.v')).write_text(full)
        (out/(label+'.v.snapshot.txt')).write_text(full)
    for label, s, target, original in cases:
        (tree/(label+'.v')).write_text(s)
        (out/(label+'.v.snapshot.txt')).write_text(s)
        line = s[:s.index('Proof.', s.index('Theorem '+target+' :'))].count('\n')+1
        protocol.append({'label': label, 'target': target, 'target_proof_line': line,
                         'sha256': hashlib.sha256(s.encode()).hexdigest(),
                         'proof_suffix_unchanged': True, 'downstream_credit': False})
    (out/'control-protocol.json').write_text(json.dumps(protocol, indent=2)+'\n')
    report = {'inputs': inputs, 'checks': {}, 'controls_import_candidate_module': False,
              'scope': 'same elaborated AST, actual 41/67 return/free; NOT raw port, init reachability, whole API, Hoare or GOOD_OS',
              'dependency_products': 'existing original 165 sources; no clean-build credit'}
    coq = os.environ.get('COQBIN', '')
    def run(label, command):
        start = time.monotonic()
        with (out/(label+'.log')).open('w') as log:
            result = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT, timeout=600)
        row = {'exit_code': result.returncode, 'elapsed_seconds': time.monotonic()-start, 'log': label+'.log'}
        report['checks'][label] = row
        (out/'result.partial.json').write_text(json.dumps(report, indent=2)+'\n')
        return row
    try:
        report['configured_C'] = base.configured_shape(out)
        assert run('production-coqc', [coq+'coqc', '-q', '-R', str(ROOT), 'CertiOS', SOURCE])['exit_code'] == 0
        assert run('probe-coqc', [coq+'coqc', '-q', '-R', str(ROOT), 'CertiOS', PROBE])['exit_code'] == 0
        for label, mod in [('production', 'certiucos.v293.proofs.V293CriticalReturn'),
                           ('probe', 'audit.probes.V293CriticalErrorsProbe')]:
            assert run(label+'-coqchk', [coq+'coqchk', '-silent', '-R', str(ROOT), 'CertiOS', 'CertiOS.'+mod])['exit_code'] == 0
        report['probe_assumptions'] = checker.checked_assumptions((out/'probe-coqc.log').read_text(), 3)
        report['positive_assumptions'] = {}
        flags = ['-q', '-R', str(ROOT), 'CertiOS', '-Q', str(tree), 'CriticalErrorControls']
        for label, s, roots in positive:
            assert run(label, [coq+'coqc', *flags, str(tree/(label+'.v'))])['exit_code'] == 0
            report['positive_assumptions'][label] = checker.checked_assumptions((out/(label+'.log')).read_text(), len(roots))
        for entry in protocol:
            label = entry['label']
            assert sha(tree/(label+'.v')) == entry['sha256']
            row = run('negative-'+label, [coq+'coqc', *flags, str(tree/(label+'.v'))])
            match = re.search(r'line (\d+)', (out/row['log']).read_text())
            assert row['exit_code'] == 1 and match and int(match[1]) > entry['target_proof_line'], row
            row.update(entry, error_line=int(match[1]))
        report['passed'] = True
    finally:
        base.cleanup(tree, out/'temporary-cleanup.json')
        report['temporary_tree_removed'] = not tree.exists()
        report['inputs_unchanged'] = all(sha(ROOT/p) == h for p,h in inputs.items())
        (out/'result.json').write_text(json.dumps(report, indent=2)+'\n')
    assert report['inputs_unchanged']
    print(json.dumps({'passed': report['passed'], 'output_dir': str(out)}, indent=2))


if __name__ == '__main__':
    main()
