#!/usr/bin/env python3
"""Local closed-prefix/entry checks; NOT the full check-functions evidence."""
from __future__ import annotations
import importlib.util
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
SOURCE = 'certiucos/v293/proofs/V293OSSchedStoragePrefix.v'
WITNESS = 'certiucos/v293/proofs/V293OSSchedStoragePrefixWitness.v'
PROBE = 'audit/probes/V293StoragePrefixProbe.v'
SCOPE = 'LOCAL_CLOSED_PHYSICAL_PREFIX_NOT_FULL_OS_SCHED_OR_GOOD_OS'
ROOT_COUNT = 17
_spec = importlib.util.spec_from_file_location('prefix_trust', ROOT / 'scripts/check-memory-trust.py')
TRUST = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(TRUST)


def checked_assumptions(output):
    if output.count('Axioms:') != ROOT_COUNT:
        raise ValueError('missing actual root assumption output')
    return TRUST.check_assumptions(output, TRUST.FRAMEWORK_ALLOWED)


def replace_once(text, before, after):
    if text.count(before) != 1:
        raise ValueError('mutation anchor must occur exactly once')
    return text.replace(before, after, 1)


def mutations(source):
    start = source.index('Lemma V293_array_reunite :')
    end = source.index('Proof.', start)
    head = source[start:end]
    half = replace_once(head,
        'V293_array false b offset step tau vs ** V293_array false b offset step tau vs ==>',
        'V293_array false b offset step tau vs ==>')
    root_start = source.index('Theorem V293_OSSched_storage_prefix :')
    root_end = source.index('Proof.', root_start)
    skip_head = replace_once(source[root_start:root_end],
        '    (V293_OSSched_unlocked_prefix sched_id table high target)\n',
        '    (sseq (scall sched_id nil) (sskip None))\n')
    skip = source[:root_start] + skip_head + source[root_end:]
    unborrowed = replace_once(source,
        '[apply V293_inputs_borrow | intros st H;',
        '[intros st H; exact H | intros st H;')
    return {
        'reserve_half_omitted_only':
            (source[:start] + half + source[end:], 'Lemma V293_array_reunite :'),
        'target_assignment_omitted_only': (skip, 'Theorem V293_OSSched_storage_prefix :'),
        'inputs_not_borrowed_only': (unborrowed, 'Lemma V293_retained_storage_prefix_lend_value :'),
    }


def witness_mutation(source):
    mismatch = replace_once(source,
        'merge (V293_encoded_memory 6%positive 0 true (encode_val (Tptr Tvoid) (Vptr V293_idle_tid)))',
        'merge (V293_encoded_memory 6%positive 0 true (encode_val (Tptr Tvoid) (Vptr V293_current_next)))')
    return mismatch, 'Lemma V293_storage_prefix_shared_witness :'


def ready_mutations(source):
    start = source.index('Definition V293_ready_resources ')
    end = source.index('Definition V293_ready_core ', start)
    resource = source[start:end]
    bitmap = replace_once(resource, 'V293_bitmap_tasks lo hi tasks', 'True')
    # Preserve the dimension used by typed erasure; neutralize only the link
    # to the actual shared task map, not the subsequent snapshot obligation.
    table = replace_once(resource, 'V293_priority_table entries tasks',
                         'V293_priority_table entries TcbMod.emp')
    root = 'Theorem V293_ready_enter_critical :'
    rs = source.index(root)
    re_ = source.index('Proof.', rs)
    skip = replace_once(source[rs:re_], '(sprim encrit)', '(sskip None)')
    store_root = 'Lemma V293_ready_store :'
    ss = source.index(store_root)
    se = source.index('Proof.', ss)
    no_update = replace_once(source[ss:se], 'set O curtid (oscurt t)', 'O')
    return {
        'ready_bitmap_relation_neutralized_only':
            (source[:start] + bitmap + source[end:], 'Theorem V293_ready_core_snapshot :'),
        'ready_table_task_relation_neutralized_only':
            (source[:start] + table + source[end:], 'Theorem V293_ready_core_snapshot :'),
        'critical_entry_primitive_omitted_only':
            (source[:rs] + skip + source[re_:], root),
        'ready_abstract_current_update_omitted_only':
            (source[:ss] + no_update + source[se:], store_root),
    }


def roundtrip_mutations(source):
    declaration = 'Theorem V293_ready_OSSched_critical_prefix :'
    start = source.index(declaration)
    end = source.index('Proof.', start)
    head = source[start:end]
    factors = {
        'roundtrip_entry_omitted_only': ('(sprim encrit)', '(sskip None)'),
        'roundtrip_call_assignment_omitted_only':
            ('(V293_OSSched_unlocked_prefix sched_id table high target)', '(sskip None)'),
        'roundtrip_exit_omitted_only': ('(sprim excrit)', '(sskip None)'),
    }
    return {name: (source[:start] + replace_once(head, before, after) + source[end:], declaration)
            for name, (before, after) in factors.items()}


def check_rejection(code, output, candidate, declaration, expected_file):
    match = re.search(r'File "([^"\n]+)", line (\d+), characters', output)
    start = candidate.index(declaration)
    lo = candidate[:start].count('\n') + 1
    hi = candidate[:candidate.index('Qed.', start)].count('\n') + 1
    if (code != 1 or 'Error:' not in output or not match
            or Path(match[1]).resolve() != expected_file.resolve()
            or not lo <= int(match[2]) <= hi):
        raise ValueError('not the designated rejection; no downstream credit')
    return {'declaration': declaration, 'line': int(match[2]), 'range': [lo, hi],
            'downstream_credit': False}


def main():
    coqbin = os.environ.get('COQBIN', '')
    out = ROOT / 'audit/logs/stage26-entry' / time.strftime('run-%Y%m%d-%H%M%S')
    out.mkdir(parents=True, exist_ok=False)
    paths = sorted({p.relative_to(ROOT).as_posix()
                    for tree in ['framework', 'tactics', 'certiucos/v293']
                    for p in (ROOT / tree).rglob('*.v')} |
                   {SOURCE, WITNESS, PROBE, 'scripts/check-v293-storage-prefix.py',
                    'scripts/check-memory-trust.py', 'Makefile', '_CoqProject'})
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
    passed('source', [coqbin + 'coqc', '-q', '-R', '.', 'CertiOS', SOURCE])
    passed('witness', [coqbin + 'coqc', '-q', '-R', '.', 'CertiOS', WITNESS])
    output = passed('interface-assumptions', [coqbin + 'coqc', '-q', '-R', '.', 'CertiOS', PROBE])
    assumptions = checked_assumptions(output)
    report['actual_assumptions_union'] = sorted(assumptions)
    passed('coqchk', [coqbin + 'coqchk', '-silent', '-R', '.', 'CertiOS',
                     'CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefix',
                     'CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefixWitness'])
    source = (ROOT / SOURCE).read_text()
    witness = (ROOT / WITNESS).read_text()
    # Context cleanup confirms every temporary file's identity before removal.
    # Generated .vo files and the positive/negative copies are not deliverables.
    work = Path(tempfile.mkdtemp(prefix='v293-closed-prefix-'))
    try:
        cases = {'positive_same_environment': (source, None, SOURCE)}
        cases.update({label: (candidate, declaration, SOURCE)
                      for label, (candidate, declaration) in mutations(source).items()})
        cases.update({label: (candidate, declaration, SOURCE)
                      for label, (candidate, declaration) in ready_mutations(source).items()})
        cases.update({label: (candidate, declaration, SOURCE)
                      for label, (candidate, declaration) in roundtrip_mutations(source).items()})
        candidate, declaration = witness_mutation(witness)
        cases['physical_current_mismatch_only'] = (candidate, declaration, WITNESS)
        for label, (candidate, declaration, relative) in cases.items():
            case = work / label
            case.mkdir()
            path = case / Path(relative).name
            path.write_text(candidate)
            args = [coqbin + 'coqc', '-q', '-R', '.', 'CertiOS', '-R', str(case),
                    'CertiOS.certiucos.v293.proofs', str(path)]
            if declaration is None:
                passed(label, args)
                witness_path = case / Path(WITNESS).name
                witness_path.write_text(witness)
                passed(label + '-witness', [coqbin + 'coqc', '-q', '-R', '.', 'CertiOS',
                    '-R', str(case), 'CertiOS.certiucos.v293.proofs', str(witness_path)])
                passed(label + '-interface', [coqbin + 'coqc', '-q', '-R', '.', 'CertiOS',
                    '-R', str(case), 'CertiOS.certiucos.v293.proofs', PROBE])
            else:
                code, output = run(label, args)
                report['negative_controls'][label] = check_rejection(code, output, candidate, declaration, path)
    finally:
        cleanup = [{'path': str(p), 'size': p.stat().st_size,
                    'sha256': hashlib.sha256(p.read_bytes()).hexdigest()}
                   for p in sorted(work.rglob('*')) if p.is_file()]
        (out / 'temporary-cleanup-manifest.json').write_text(json.dumps(cleanup, indent=2) + '\n')
        for row in cleanup:
            p = Path(row['path'])
            if (p.stat().st_size != row['size'] or
                    hashlib.sha256(p.read_bytes()).hexdigest() != row['sha256']):
                raise ValueError('temporary cleanup identity changed')
        shutil.rmtree(work)
    if identity != {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in paths}:
        raise ValueError('local gate inputs changed during checking')
    report['temporary_cleanup'] = {'files': len(cleanup), 'bytes': sum(p['size'] for p in cleanup)}
    (out / 'result.json').write_text(json.dumps(report, indent=2) + '\n')
    print('LOCAL PREFIX: PASS (not the full function gate)')
    print(out.relative_to(ROOT) / 'result.json')


if __name__ == '__main__':
    main()
