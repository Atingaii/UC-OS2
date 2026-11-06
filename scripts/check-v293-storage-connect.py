#!/usr/bin/env python3
"""Local typed guards and relational conditional call/count/switch checks; never full-function evidence."""
from __future__ import annotations
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
SOURCE = 'certiucos/v293/proofs/V293OSSchedStorageConnect.v'
WITNESS = 'certiucos/v293/proofs/V293OSSchedStorageConnectWitness.v'
PROBE = 'audit/probes/V293StorageConnectProbe.v'
SCOPE = 'LOCAL_TYPED_GUARDED_AND_READY_CONDITIONAL_EXPLICIT_CURRENT_NOT_FULL_OS_SCHED_PORT_OR_GOOD_OS'
ROOT_COUNT = 25
_spec = importlib.util.spec_from_file_location('connect_prefix_checks', ROOT / 'scripts/check-v293-storage-prefix.py')
PREFIX = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(PREFIX)
replace_once = PREFIX.replace_once
check_rejection = PREFIX.check_rejection


def checked_assumptions(output):
    if output.count('Axioms:') != ROOT_COUNT:
        raise ValueError('missing actual root assumption output')
    return PREFIX.TRUST.check_assumptions(output, PREFIX.TRUST.FRAMEWORK_ALLOWED)


def mutations(source):
    decl = 'Lemma V293_storage_connected_increment_under :'
    start = source.index(decl)
    end = source.index('Proof.', start)
    header = replace_once(source[start:end], '(V293_OSSched_increment counter)', '(sskip None)')
    projection = replace_once(source,
        '''  { intros st H. apply V293_storage_observation_flags in H.
    unfold V293_storage_open. sep auto. }''',
        '''  { intros st H.
    assert (HO : st |= SWINV (V293_storage_inv cells target tp) //\\\\
      (((CurTid tid ** V293_shared_fields tid tasks events now) **
        (GV target @ (Tptr tp) |-> (Vptr next))) ** Atrue)).
    { split; [exact (proj1 H) | ]. destruct H as [_ H]. sep auto. }
    clear H. apply V293_storage_observation_flags in HO.
    unfold V293_storage_open. sep auto. }''')
    return_start = source.index('Lemma V293_storage_connected_return :')
    return_end = source.index('Qed.', return_start)
    missing_return = (source[:return_start] + replace_once(source[return_start:return_end],
        'apply V293_prefix_physical_return; assumption', 'intros st H; exact H') + source[return_end:])
    begin = source.index('Definition V293_priority_closed :=')
    priority_end = source.index('Lemma V293_priority_kept_erase :', begin)
    forgotten = replace_once(source[begin:priority_end],
        'lo hi entries extra V293_priority_kept tid',
        'lo hi entries extra (V293_storage extra) tid')
    forgotten_priority = source[:begin] + forgotten + source[priority_end:]
    conditional_start = source.index('Definition V293_conditional_closed :=')
    conditional_end = source.index('Let middle :=', conditional_start)
    lost_conditional = (source[:conditional_start] + replace_once(source[conditional_start:conditional_end],
        'lo hi entries extra V293_conditional_kept tid',
        'lo hi entries extra (V293_storage extra) tid') + source[conditional_end:])
    branch_start = source.index('Theorem V293_conditional_change :')
    branch_end = source.index('Proof.', branch_start)
    skipped_conditional = (source[:branch_start] + replace_once(source[branch_start:branch_end],
        '(V293_OSSched_change high current counter (sprim (switch target)))',
        '(sifthen (V293_OSSched_different high current) (sseq (sskip None) (sprim (switch target))))') + source[branch_end:])
    no_self_schedule = replace_once(source,
        "eapply (absinfer_sched' _ (fun _ => True) _ _ _ _); try exact Hfree.",
        "apply absinfer_eq'.")
    guard_start = source.index('Theorem V293_OSSched_storage_guarded :')
    guard_end = source.index('Proof.', guard_start)
    def guard_program(expression):
        return (source[:guard_start] + replace_once(source[guard_start:guard_end],
            '(V293_OSSched_guards interrupt lock', expression) + source[guard_end:])
    entry_start = source.index('Definition V293_storage_guarded_entry')
    entry_end = source.index('Definition V293_storage_guarded_resumed', entry_start)
    lost_guard = (source[:entry_start] + replace_once(source[entry_start:entry_end],
        r"""stack critical guardbindings old hv //\\
  ((V293_guard_cell interrupt bi ni ** V293_guard_cell lock bl nl) ** Atrue).""",
        'stack critical guardbindings old hv.') + source[entry_end:])
    ready_start = source.index('Theorem V293_ready_OSSched_prefix_increment_switch :')
    ready_end = source.index('Proof.', ready_start)
    ready_header = source[ready_start:ready_end]
    def ready_program(before):
        return (source[:ready_start] + replace_once(ready_header, before, '(sskip None)') + source[ready_end:])
    ready_return_start = source.index('Lemma V293_ready_connected_return :')
    ready_return_end = source.index('Qed.', ready_return_start)
    typed_return = (source[:ready_return_start] + replace_once(source[ready_return_start:ready_return_end],
        'apply V293_ready_prefix_return; eassumption',
        'apply V293_retained_prefix_return_snapshot; eassumption') + source[ready_return_end:])
    ready_branch_start = source.index('Theorem V293_ready_conditional_change :')
    ready_branch_end = source.index('Proof.', ready_branch_start)
    def ready_branch_program(then_program):
        return (source[:ready_branch_start] + replace_once(source[ready_branch_start:ready_branch_end],
            '(V293_OSSched_change high current counter (sprim (switch target)))',
            '(sifthen (V293_OSSched_different high current) ' + then_program + ')') + source[ready_branch_end:])
    ready_open_start = source.index('Definition V293_ready_conditional_open :=')
    ready_open_end = source.index('Let tail next c :=', ready_open_start)
    lost_ready_current = (source[:ready_open_start] + replace_once(source[ready_open_start:ready_open_end],
        'lo hi entries kept tid', 'lo hi entries (V293_storage extra) tid') + source[ready_open_end:])
    ready_equal_start = source.index('Theorem V293_ready_conditional_equal_finish :')
    ready_equal_end = source.index('Proof.', ready_equal_start)
    lost_current_task = (source[:ready_equal_start] + replace_once(source[ready_equal_start:ready_equal_end],
        'V293_current_task tasks tid nc ->', 'True ->') + source[ready_equal_end:])
    return {
        'ready_conditional_increment_omitted_only':
            (ready_branch_program('(sseq (sskip None) (sprim (switch target)))'),
             'Theorem V293_ready_conditional_change :'),
        'ready_conditional_switch_omitted_only':
            (ready_branch_program('(sseq (V293_OSSched_increment counter) (sskip None))'),
             'Theorem V293_ready_conditional_change :'),
        'ready_conditional_current_byte_forgotten_only':
            (lost_ready_current, 'Theorem V293_ready_conditional_comparison :'),
        'ready_conditional_current_task_omitted_only':
            (lost_current_task, 'Theorem V293_ready_conditional_equal_finish :'),
        'ready_increment_omitted_only': (ready_program('(V293_OSSched_increment counter)'),
            'Theorem V293_ready_OSSched_prefix_increment_switch :'),
        'ready_switch_omitted_only': (ready_program('(sprim (switch target))'),
            'Theorem V293_ready_OSSched_prefix_increment_switch :'),
        'ready_relation_erased_on_return_only': (typed_return, 'Lemma V293_ready_connected_return :'),
        'outer_guard_omitted_only': (guard_program('(sifthen (V293_OSSched_zero lock)'),
                                    'Theorem V293_OSSched_storage_guarded :'),
        'inner_guard_omitted_only': (guard_program('(sifthen (V293_OSSched_zero interrupt)'),
                                    'Theorem V293_OSSched_storage_guarded :'),
        'guard_exactness_forgotten_only': (lost_guard, 'Theorem V293_OSSched_storage_guarded :'),
        'conditional_increment_omitted_only': (skipped_conditional, 'Theorem V293_conditional_change :'),
        'conditional_exactness_forgotten_only': (lost_conditional, 'Theorem V293_conditional_comparison :'),
        'equal_sched_not_consumed_only': (no_self_schedule, 'Lemma V293_self_schedule_consume :'),
        'increment_omitted_only': (source[:start] + header + source[end:], decl),
        'physical_projection_forgotten_only': (projection, 'Lemma V293_storage_connected_prefix_open :'),
        'arrays_not_returned_only': (missing_return, 'Lemma V293_storage_connected_return :'),
        'exact_priority_forgotten_only': (forgotten_priority, 'Theorem V293_storage_priority_comparison :'),
    }


def witness_mutation(source):
    start = source.index('Definition V293_priority_fixture_memory')
    end = source.index('Theorem V293_storage_priority_entry_witness', start)
    changed = source[:start] + replace_once(source[start:end],
        '(encode_val Tint8 (V293_byteval (V293_current_mode_priority different)))',
        '(encode_val Tint8 (V293_byteval 0))') + source[end:]
    return changed, 'Theorem V293_storage_priority_entry_witness :'


def conditional_witness_mutation(source):
    start = source.index('Definition V293_conditional_priority_memory')
    end = source.index('Theorem V293_storage_conditional_entry_witness', start)
    changed = source[:start] + replace_once(source[start:end],
        '(encode_val Tint8 (V293_byteval (V293_current_mode_priority different)))',
        '(encode_val Tint8 (V293_byteval 0))') + source[end:]
    return changed, 'Theorem V293_storage_conditional_entry_witness :'


def guarded_witness_mutation(source, guard):
    names = {'interrupt': 'ni', 'lock': 'nl'}
    value = names[guard]
    start = source.index(f'Definition V293_guarded_{guard}_memory')
    end = source.index('.', start) + 1
    changed = (source[:start] + replace_once(source[start:end],
        f'(encode_val Tint8 (V293_byteval {value}))',
        '(encode_val Tint8 (V293_byteval 0))') + source[end:])
    return changed, 'Theorem V293_storage_guarded_entry_witness :'


def cleanup_work(work, out):
    rows = [{'path': str(p), 'size': p.stat().st_size,
             'sha256': hashlib.sha256(p.read_bytes()).hexdigest()}
            for p in sorted(work.rglob('*')) if p.is_file()]
    (out / 'temporary-cleanup-manifest.json').write_text(json.dumps(rows, indent=2) + '\n')
    for row in rows:
        p = Path(row['path'])
        if p.stat().st_size != row['size'] or hashlib.sha256(p.read_bytes()).hexdigest() != row['sha256']:
            raise ValueError('temporary cleanup identity changed')
    shutil.rmtree(work)
    return {'files': len(rows), 'bytes': sum(r['size'] for r in rows)}


def main():
    coqbin = os.environ.get('COQBIN', '')
    out = ROOT / 'audit/logs/stage26-connect' / time.strftime('run-%Y%m%d-%H%M%S')
    out.mkdir(parents=True, exist_ok=False)
    paths = sorted({p.relative_to(ROOT).as_posix()
                    for tree in ['framework', 'tactics', 'certiucos/v293']
                    for p in (ROOT / tree).rglob('*.v')} |
                   {PROBE, 'scripts/check-v293-storage-connect.py', 'scripts/check-v293-storage-prefix.py',
                    'scripts/check-memory-trust.py', 'tests/test_storage_connect_local.py', 'Makefile', '_CoqProject',
                    'audit/logs/stage26-connect/PROTOCOL.txt', 'audit/logs/stage26-retained/PROTOCOL.txt',
                    'tests/test_storage_prefix_local.py', 'audit/logs/stage26-conditional/PROTOCOL.txt',
                    'audit/logs/stage26-guards/PROTOCOL.txt', 'audit/logs/stage26-guards/PROTOCOL-ADDENDUM.txt',
                    'audit/logs/stage26-ready-switch/PROTOCOL.txt',
                    'audit/logs/stage26-ready-conditional/PROTOCOL.txt'})
    identity = {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in paths}
    report = {'scope': SCOPE, 'formal_function_evidence_updated': False, 'prebuilt_dependency_closure': True,
              'input_sha256': identity, 'checks': {}, 'negative_controls': {}}

    def run(label, args):
        result = subprocess.run(args, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, timeout=1800)
        (out / (label + '.log')).write_text(result.stdout)
        report['checks'][label] = {'exit_code': result.returncode,
                                  'log': str((out / (label + '.log')).relative_to(ROOT))}
        return result.returncode, result.stdout

    def passed(label, args):
        code, output = run(label, args)
        if code:
            raise ValueError(f'{label} failed; inspect {out}')
        return output

    version = passed('version', [coqbin + 'coqc', '--version'])
    if not re.search(r'version 8\.18\.0(?: |$)', version, re.MULTILINE):
        raise ValueError('Coq 8.18.0 required')
    for label, path in [('prefix', PREFIX.SOURCE), ('prefix-witness', PREFIX.WITNESS),
                        ('source', SOURCE), ('witness', WITNESS)]:
        passed(label, [coqbin + 'coqc', '-q', '-R', '.', 'CertiOS', path])
    output = passed('interface-assumptions', [coqbin + 'coqc', '-q', '-R', '.', 'CertiOS', PROBE])
    report['actual_assumptions_union'] = sorted(checked_assumptions(output))
    passed('coqchk', [coqbin + 'coqchk', '-silent', '-R', '.', 'CertiOS',
                     'CertiOS.certiucos.v293.proofs.V293OSSchedStorageConnect',
                     'CertiOS.certiucos.v293.proofs.V293OSSchedStorageConnectWitness'])
    source, witness = (ROOT / SOURCE).read_text(), (ROOT / WITNESS).read_text()
    work = Path(tempfile.mkdtemp(prefix='v293-connected-storage-'))
    try:
        cases = {'positive_same_environment': (source, None, SOURCE)}
        cases.update({label: (candidate, declaration, SOURCE)
                      for label, (candidate, declaration) in mutations(source).items()})
        candidate, declaration = witness_mutation(witness)
        cases['physical_priority_mismatch_only'] = (candidate, declaration, WITNESS)
        candidate, declaration = conditional_witness_mutation(witness)
        cases['combined_physical_priority_mismatch_only'] = (candidate, declaration, WITNESS)
        for guard in ['interrupt', 'lock']:
            candidate, declaration = guarded_witness_mutation(witness, guard)
            cases[f'physical_{guard}_mismatch_only'] = (candidate, declaration, WITNESS)
        for label, (candidate, declaration, relative) in cases.items():
            case = work / label
            case.mkdir()
            path = case / Path(relative).name
            path.write_text(candidate)
            if relative == WITNESS:
                source_path = case / Path(SOURCE).name
                source_path.write_text(source)
                passed(label + '-same-environment-source', [coqbin + 'coqc', '-q', '-R', '.',
                    'CertiOS', '-R', str(case), 'CertiOS.certiucos.v293.proofs', str(source_path)])
            args = [coqbin + 'coqc', '-q', '-R', '.', 'CertiOS', '-R', str(case),
                    'CertiOS.certiucos.v293.proofs', str(path)]
            if declaration is None:
                passed(label, args)
                witness_path = case / Path(WITNESS).name
                witness_path.write_text(witness)
                passed(label + '-witness', [coqbin + 'coqc', '-q', '-R', '.', 'CertiOS',
                    '-R', str(case), 'CertiOS.certiucos.v293.proofs', str(witness_path)])
                actual = passed(label + '-interface', [coqbin + 'coqc', '-q', '-R', '.', 'CertiOS',
                    '-R', str(case), 'CertiOS.certiucos.v293.proofs', PROBE])
                checked_assumptions(actual)
            else:
                code, output = run(label, args)
                report['negative_controls'][label] = check_rejection(code, output, candidate, declaration, path)
    finally:
        report['temporary_cleanup'] = cleanup_work(work, out)
        (out / 'result.json').write_text(json.dumps(report, indent=2) + '\n')
    if identity != {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in paths}:
        raise ValueError('local gate inputs changed during checking')
    report['input_identity_rechecked'] = True
    report['passed'] = True
    (out / 'result.json').write_text(json.dumps(report, indent=2) + '\n')
    print('LOCAL CONNECT: PASS (not the full function gate)')
    print(out.relative_to(ROOT) / 'result.json')


if __name__ == '__main__':
    main()
