#!/usr/bin/env python3
"""Check the finite success prefix/update/excrit trace, not scheduler/API completion."""
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
PROBE = 'audit/probes/V293CriticalSuccessProbe.v'
ENTRY = 'V293_primitive_entry_success'
SEGMENT = 'V293_success_segment_execution'
NULL = 'V293_critical_null_update_execution'
EVENT = 'V293_critical_event_update_execution'
ROOTS = [ENTRY, SEGMENT, NULL, EVENT, 'V293_critical_null_update_witness', 'V293_critical_event_update_witness']


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def module(name):
    spec = importlib.util.spec_from_file_location(name, ROOT/'scripts'/name)
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


def projection(source, target):
    definitions = source[:source.index('Theorem V293_critical_prefix_normalization :')]
    closure = source[source.index('(* Standard reflexive/transitive closure'):
                     source.index('(* Same program for both initial IE states;')]
    additions = source[source.index('(* Successful path: original-memory resources, actual stores, actual excrit. *)'):]
    focused = definitions+closure+additions
    start = focused.index(target+' :')
    return focused[:focused.index('\nQed.', start)+6]+'\n'


def controls(source):
    base = module('check-v293-critical-elaboration.py')
    result = []

    def edit(label, target, transform):
        original = projection(source, target)
        i = original.index('Proof.', original.index(('Lemma ' if target == SEGMENT else 'Theorem ')+target+' :'))
        changed = transform(original[:i])+original[i:]
        assert changed[changed.index('Proof.', changed.index(target+' :')):] == original[i:]
        assert changed != original
        result.append((label, changed, target, original))

    def definition(text, start, end, old, new):
        i, j = text.index(start), text.index(end, text.index(start))
        return text[:i]+base.replace_once(text[i:j], old, new)+text[j:]

    for label, stmt in [('SkipSelf', 'V293_task_prio_self_read oldprio current'),
                        ('SkipLookup', 'V293_task_prio_lookup table oldprio ptcb')]:
        edit(label, ENTRY, lambda text, stmt=stmt: definition(
            text, 'Definition V293_primitive_entry ', 'Definition V293_raw_critical_prefix ',
            '('+stmt+')', '(sskip None)'))
    edit('EnterCli', SEGMENT, lambda text: definition(
        text, 'Definition V293_primitive_critical_prefix ', '(* Standard reflexive/transitive closure',
        '(sprim encrit)', '(sprim cli)'))

    def exit_sti(text):
        # ONE semantic factor: the tail primitive. Update its continuation
        # occurrences too, so the old proof reaches the actual final step,
        # rather than failing on an unrelated pending-continuation mismatch.
        i = text.index('Definition V293_primitive_success_update ')
        head, tail = text[:i], text[i:]
        assert tail.count('(sprim excrit)') == 5
        return head+tail.replace('(sprim excrit)', '(sprim sti)')
    edit('ExitSti', SEGMENT, exit_sti)
    edit('WrongIE', SEGMENT, lambda text: base.replace_once(
        text, '((ge,le,Mh),ir,(enabled,si,ci)).', '((ge,le,Mh),ir,(negb enabled,si,ci)).'))

    def header_change(text, target, old, new):
        i = text.index('Theorem '+target+' :')
        return text[:i]+base.replace_once(text[i:], old, new)
    edit('WrongTCB', NULL, lambda text: header_change(
        text, NULL, 'V293_tcb_updated_loads Mh bt base new', 'V293_tcb_updated_loads Mh bt base old'))
    edit('WrongEvent', EVENT, lambda text: header_change(
        text, EVENT, 'let er := V293_ready_rekey_rows elo ehi old new in', 'let er := (elo,ehi) in'))
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path, required=True)
    out = parser.parse_args().output_dir.resolve()
    out.mkdir(parents=True, exist_ok=False)
    base = module('check-v293-critical-elaboration.py')
    checker = module('check-v293-task-prio-rekey.py')
    source = (ROOT/SOURCE).read_text()
    inputs = {str(p.relative_to(ROOT)): sha(p) for d in ['framework', 'tactics', 'certiucos/v293']
              for p in sorted((ROOT/d).rglob('*.v'))}
    for path in [PROBE, '_CoqProject', 'scripts/check-v293-critical-success.py',
                 'scripts/check-v293-critical-elaboration.py', 'scripts/check-v293-task-prio-rekey.py',
                 'csrc/repairs/FROZEN_SOURCE.json', 'audit/coverage.json']:
        inputs[path] = sha(ROOT/path)
    cases = controls(source)
    tree = Path(tempfile.mkdtemp(prefix='v293-critical-success-'))
    positives = [('PositiveFull', source, ROOTS)]
    positives += [('Positive'+label, projection(source, root), [root])
                  for label,root in [('Entry',ENTRY), ('Segment',SEGMENT), ('Null',NULL), ('Event',EVENT)]]
    protocol = []
    for label, s, roots in positives:
        assert 'Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn' not in s
        s += '\n'+''.join('Print Assumptions '+r+'.\n' for r in roots)
        (tree/(label+'.v')).write_text(s)
        (out/(label+'.v.snapshot.txt')).write_text(s)
    for label, s, target, original in cases:
        (tree/(label+'.v')).write_text(s)
        (out/(label+'.v.snapshot.txt')).write_text(s)
        protocol.append({'label': label, 'target': target,
                         'target_proof_line': s[:s.index('Proof.', s.index(target+' :'))].count('\n')+1,
                         'sha256': sha(tree/(label+'.v')), 'proof_suffix_unchanged': True,
                         'downstream_credit': False})
    (out/'control-protocol.json').write_text(json.dumps(protocol, indent=2)+'\n')
    report = {'inputs': inputs, 'checks': {}, 'passed': False,
              'scope': 'finite success prefix/update/excrit; NOT raw-port execution, scheduler, success return, concurrency, initialization, whole API or GOOD_OS',
              'dependencies': 'existing products, no clean-build credit'}
    coq = os.environ.get('COQBIN', '')

    def run(label, command):
        start = time.monotonic()
        with (out/(label+'.log')).open('w') as log:
            result = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT, timeout=600)
        row = {'exit_code': result.returncode, 'seconds': time.monotonic()-start, 'log': label+'.log'}
        report['checks'][label] = row
        (out/'result.partial.json').write_text(json.dumps(report, indent=2)+'\n')
        return row
    try:
        for label, path in [('production', SOURCE), ('probe', PROBE)]:
            assert run(label+'-coqc', [coq+'coqc', '-q', '-R', str(ROOT), 'CertiOS', path])['exit_code'] == 0
        report['probe_assumptions'] = checker.checked_assumptions((out/'probe-coqc.log').read_text(), 6)
        for label, mod in [('production', 'certiucos.v293.proofs.V293CriticalReturn'),
                           ('probe', 'audit.probes.V293CriticalSuccessProbe')]:
            assert run(label+'-coqchk', [coq+'coqchk', '-silent', '-R', str(ROOT), 'CertiOS', 'CertiOS.'+mod])['exit_code'] == 0
        flags = ['-q', '-R', str(ROOT), 'CertiOS', '-Q', str(tree), 'CriticalSuccessControls']
        report['positive_assumptions'] = {}
        for label, s, roots in positives:
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
    print(json.dumps({'passed': report['passed'], 'checks': len(report['checks']), 'output_dir': str(out)}, indent=2))


if __name__ == '__main__':
    main()
