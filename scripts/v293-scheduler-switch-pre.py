#!/usr/bin/env python3
"""Actual tail establishes spatial SWPRE_NDEAD; switch/GoodI remain open."""
from pathlib import Path
import re
import shutil

CORE = 'certiucos/v293/proofs/V293OSSchedSwitchPre.v'
WITNESS = 'certiucos/v293/proofs/V293OSSchedSwitchPreWitness.v'
FILES = [CORE, WITNESS]
ROOTS = ['V293_current_halves_write', 'V293_OSSched_tail_switch_pre', 'V293_OSSched_guarded_switch_pre_prefix', 'V293_OSSched_switch_precondition_witness']
SCOPE = 'SAME_PREFIX_FULL_CURRENT_WRITE_AND_SWPRE_NDEAD_NOT_SWINVT_SWITCH_OR_GOOD_OS'
CONTROLS = {
    'current_second_half_removed_only': 'REJECTED_AT_V293_current_halves_write',
    'current_membership_removed_only': 'REJECTED_AT_V293_OSSched_tail_switch_pre',
    'fixture_current_read_only': 'CORE_COMPILES_REJECTED_AT_V293_switch_current_sat',
    'switch_pre_false_premise_added_only': 'MUTANT_AND_WITNESS_COMPILE_REJECTED_AT_checked_guarded_switch_pre',
}

# Fixed expected types and independent assertions from the prior probes.
PROBE = r'''
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitchPre.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitchPreWitness.
Definition checked_current_halves_write : forall tid,
  CurTid tid ** CurTid tid ==> EX tp : type, GV OSTCBCur @ (Tptr tp) |-> (Vptr tid) :=
  V293_current_halves_write.
Definition checked_tail_switch_pre : forall
    unmap group rows high bt bg br bh lo hi li tid aop
    table target tp bp bo entries tasks current counter bcur bcounter nc frame c I stack critical,
  checked_current_task tasks tid nc ->
  checked_tail unmap group rows high bt bg br bh lo hi li tid aop
    table target tp bp bo entries tasks current counter bcur bcounter nc
      (checked_critical I stack critical ** (CurTid tid ** frame)) c ==>
  SWPRE_NDEAD checked_scheduler target tid :=
  V293_OSSched_tail_switch_pre.
Definition checked_guarded_switch_pre : forall Spec sd li I r ri tid aop frame
    sched_id unmap group rows high bt bg br bh lo hi table target tp bp bo entries tasks old
    interrupt lock bi bl ni nl current counter bcur bcounter nc c stack critical suffix q (Hli : GoodLInvAsrt li),
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  checked_bitmap_tasks lo hi tasks -> checked_priority_table entries tasks -> GoodFrm frame ->
  ni < 256 -> nl < 256 -> checked_current_task tasks tid nc ->
  Spec sched_id = Some
    (V293_critical_fpre unmap group rows high bt bg br bh li I Hli,
     V293_critical_fpost unmap group rows high bt bg br bh li I Hli, (Tvoid, nil)) ->
  let gf := checked_guard_cell interrupt bi ni ** (checked_guard_cell lock bl nl ** (CurTid tid ** frame)) in
  let k := checked_critical I stack critical in
  let pre := (checked_pre unmap group rows high bt bg br bh lo hi li tid aop ** k) **
    (checked_prefix_frame table high target tp bp bo entries tasks
      (checked_guard_cell current bcur nc ** gf) **
      (checked_prefix_output tp bo old ** checked_counter_cell counter bcounter c)) in
  let mid := checked_tail unmap group rows high bt bg br bh lo hi li tid aop
    table target tp bp bo entries tasks current counter bcur bcounter nc (k ** gf) in
  let current_link := checked_linked_tail unmap group rows high bt bg br bh lo hi li tid aop
    table target tp bp bo entries tasks current counter bcur bcounter nc (k ** gf) in
  let linked := fun n => current_link n //\\ SWPRE_NDEAD checked_scheduler target tid in
  (ni = 0 -> nl = 0 -> V293_ready_select lo hi (V293_ready_group lo hi) <> nc ->
    InfRules Spec sd li I r ri (linked (Int.add c Int.one)) suffix q tid) ->
  InfRules Spec sd li I r ri pre
    (sifthen (ebinop oeq (ecast (evar interrupt) Tint32) (econst32 (Int.repr 0)))
      (sifthen (ebinop oeq (ecast (evar lock) Tint32) (econst32 (Int.repr 0)))
        (sseq (sseq (scall sched_id nil) (sassign (evar target) (earrayelem (evar table) (evar high))))
          (sifthen (eunop oppsite (ebinop oeq (ecast (evar high) Tint32) (ecast (evar current) Tint32)))
            (sseq (sassign (evar counter) (ebinop oplus (evar counter) (econst32 Int.one))) suffix)))))
    (if Nat.eqb ni 0 && Nat.eqb nl 0 then
      (if Nat.eqb (V293_ready_select lo hi (V293_ready_group lo hi)) nc then mid c else q) else pre) tid :=
  V293_OSSched_guarded_switch_pre_prefix.
Definition checked_switch_pre_witness : forall different ni nl c,
  ni < 256 -> nl < 256 -> exists s,
  checked_bitmap_tasks 0 16 (V293_current_mode_tasks different) /\
  checked_priority_table (V293_current_mode_entries different) (V293_current_mode_tasks different) /\
  checked_current_task (V293_current_mode_tasks different) V293_idle_tid (V293_current_mode_priority different) /\
  (V293_ready_select 0 16 (V293_ready_group 0 16) <> V293_current_mode_priority different <-> different = true) /\
  s |= (checked_pre 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive
    0 16 V293_witness_li V293_idle_tid (spec_done None) **
      checked_critical V293_critical_fixture_inv nil nil) **
    (checked_prefix_frame 106%Z 103%Z 107%Z Tvoid 8%positive 10%positive
      (V293_current_mode_entries different) (V293_current_mode_tasks different)
      (checked_guard_cell 110%Z 13%positive (V293_current_mode_priority different) **
        (checked_guard_cell 108%Z 11%positive ni ** (checked_guard_cell 109%Z 12%positive nl ** (CurTid V293_idle_tid ** Aemp)))) **
      (checked_prefix_output Tvoid 10%positive Vnull ** checked_counter_cell 111%Z 14%positive c)) :=
  V293_OSSched_switch_precondition_witness.
'''

def mutations(source, witness, replace):
    half = replace(source, 'CurTid tid ** CurTid tid ==>', 'CurTid tid ==>')
    member = replace(source, '\n  V293_current_task tasks tid nc ->', '\n  True ->')
    readonly = replace(witness,
        'Definition V293_switch_current_memory := V293_encoded_memory 6%positive 0 true',
        'Definition V293_switch_current_memory := V293_encoded_memory 6%positive 0 false')
    start = source.index('Theorem V293_OSSched_guarded_switch_pre_prefix')
    false = source[:start] + replace(source[start:],
        '(Hli : GoodLInvAsrt li),\n  lo < 256 ->', '(Hli : GoodLInvAsrt li),\n  False -> lo < 256 ->')
    start = false.index('Theorem V293_OSSched_guarded_switch_pre_prefix')
    false = false[:start] + replace(false[start:],
        '    Hli Hlo Hhi Hr Hb', '    Hli Hfalse Hlo Hhi Hr Hb')
    return {
        'current_second_half_removed_only': (half, witness, CORE, 'Theorem V293_current_halves_write'),
        'current_membership_removed_only': (member, witness, CORE, 'Theorem V293_OSSched_tail_switch_pre'),
        'fixture_current_read_only': (source, readonly, WITNESS, 'Lemma V293_switch_current_sat'),
        'switch_pre_false_premise_added_only': (false, witness, None, 'Definition checked_guarded_switch_pre'),
    }

def check(root, work, build, coqbin, run, loader, location):
    caller = loader(root, 'v293-scheduler-caller.py')
    probe = (loader(root, 'v293-scheduler-source.py').PROBE +
             loader(root, 'v293-scheduler-internal.py').PRELUDE + caller.PROBE +
             loader(root, 'v293-scheduler-prefix.py').PROBE +
             loader(root, 'v293-scheduler-guards.py').PROBE +
             loader(root, 'v293-scheduler-change.py').PROBE +
             loader(root, 'v293-scheduler-current.py').PROBE +
             loader(root, 'v293-scheduler-critical.py').PROBE + PROBE)
    checks = {}
    def record(label, command, cwd):
        if label in checks:
            raise ValueError('duplicate switch_pre command identity: ' + label)
        row = run('switch_pre:' + label, command, cwd); checks[label] = row
        return row

    def compile_tree(label, core, witness, assumptions=False):
        dest = work / ('switch_pre_' + label)
        shutil.copytree(build / 'certiucos', dest / 'certiucos')
        (dest / 'checks').mkdir()
        flags = ['-R', str(build / 'framework'), 'CertiOS.framework',
                 '-R', str(build / 'tactics'), 'CertiOS.tactics',
                 '-R', str(dest / 'certiucos'), 'CertiOS.certiucos',
                 '-R', str(dest / 'checks'), 'SwitchPreCheck']
        for rel, contents in zip(FILES, [core, witness]):
            path = dest / rel
            for suffix in ['.vo', '.vos', '.vok', '.glob']:
                path.with_suffix(suffix).unlink(missing_ok=True)
            path.write_text(contents)
            row = record(label + ':' + Path(rel).stem, [coqbin + 'coqc', '-q', *flags, str(path)], dest)
            if row['exit_code']:
                return row, flags, dest
        path = dest / 'checks/Contract.v'
        path.write_text(probe + ('\n' + '\n'.join('Print Assumptions ' + r + '.' for r in ROOTS) if assumptions else ''))
        return record(label + ':contract', [coqbin + 'coqc', '-q', *flags, str(path)], dest), flags, dest

    source = (root / CORE).read_text(); witness = (root / WITNESS).read_text()
    variants = mutations(source, witness, caller.replace_once)
    row, flags, dest = compile_tree('positive', source, witness, assumptions=True)
    if row['exit_code']:
        raise ValueError('switch_pre proof/probe failed: ' + str(row))
    trust = loader(root, 'check-memory-trust.py'); assumptions = set()
    for part in row['stdout'].split('Axioms:')[1:]:
        assumptions |= set(trust.check_assumptions(part.split('Closed under the global context')[0], trust.FRAMEWORK_ALLOWED))
    if row['stdout'].count('Axioms:') + row['stdout'].count('Closed under the global context') != len(ROOTS):
        raise ValueError('missing switch_pre root assumption output')
    row = record('coqchk', [coqbin + 'coqchk', '-silent', *flags,
        *['CertiOS.' + Path(f).with_suffix('').as_posix().replace('/', '.') for f in FILES],
        'SwitchPreCheck.Contract'], dest)
    if row['exit_code']:
        raise ValueError('switch_pre coqchk failed: ' + str(row))
    for label, (core, wit, failed_rel, declaration) in variants.items():
        row, _, _ = compile_tree(label, core, wit)
        failed_source = probe if failed_rel is None else (core if failed_rel == CORE else wit)
        start = failed_source.index(declaration)
        lo = failed_source[:start].count('\n') + 1
        end = (failed_source.index(' :=\n', start) + len(' :=\n  V293_OSSched_guarded_switch_pre_prefix.')
               if failed_rel is None else failed_source.index('Qed.', start) + len('Qed.'))
        hi = failed_source[:end].count('\n') + 1
        match = re.search(r'line (\d+), characters', row['stderr'])
        expected_file = '/checks/Contract.v' if failed_rel is None else '/' + failed_rel
        if (row['exit_code'] != 1 or not match or not lo <= int(match[1]) <= hi
                or expected_file not in row['stderr']):
            raise ValueError('switch_pre control missed designated obligation: ' + label + ': ' + str(row))
        for rel in (FILES if failed_rel is None else FILES[:FILES.index(failed_rel)]):
            if checks[label + ':' + Path(rel).stem]['exit_code'] != 0:
                raise ValueError('switch_pre control prerequisite failed')
    return {'scope': SCOPE, 'coverage_credit': False, 'roots': ROOTS, 'source_location': location,
            'root_assumptions': sorted(assumptions), 'negative_controls': CONTROLS}


def validate(root, checkpoint, checks, loader):
    import json
    inventory = json.loads((root / 'audit/repaired-source-inventory.json').read_text())
    expected = {'scope': SCOPE, 'coverage_credit': False, 'roots': ROOTS,
        'source_location': next(f for f in inventory['functions'] if f['name'] == 'OS_Sched'),
        'root_assumptions': checkpoint['root_assumptions'], 'negative_controls': CONTROLS}
    if checkpoint != expected:
        raise ValueError('switch_pre checkpoint scope/roots/source/controls differ')
    if not set(checkpoint['root_assumptions']) <= loader(root, 'check-memory-trust.py').FRAMEWORK_ALLOWED:
        raise ValueError('unexpected switch_pre root assumptions')
    for key in ['positive:' + Path(f).stem for f in FILES] + ['positive:contract', 'coqchk']:
        if checks['switch_pre:' + key]['exit_code'] != 0:
            raise ValueError('switch_pre checkpoint positive check failed')
    for label in CONTROLS:
        fail = (Path(CORE).stem if label in {'current_second_half_removed_only', 'current_membership_removed_only'}
                else Path(WITNESS).stem if label == 'fixture_current_read_only' else 'contract')
        prerequisites = FILES if fail == 'contract' else FILES[:FILES.index(WITNESS)] if fail == Path(WITNESS).stem else []
        for rel in prerequisites:
            if checks['switch_pre:' + label + ':' + Path(rel).stem]['exit_code'] != 0:
                raise ValueError('switch_pre control prerequisite missing')
        if checks['switch_pre:' + label + ':' + fail]['exit_code'] != 1:
            raise ValueError('switch_pre designated control missing')
