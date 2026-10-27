#!/usr/bin/env python3
"""Current TCB and writable target linkage; SWPRE/SWINV remain OPEN."""
from pathlib import Path
import re
import shutil

CORE = 'certiucos/v293/proofs/V293OSSchedCurrent.v'
WITNESS = 'certiucos/v293/proofs/V293OSSchedCurrentWitness.v'
FILES = [CORE, WITNESS]
ROOTS = ['V293_OSSched_current_target', 'V293_OSSched_current_tail_entails',
         'V293_OSSched_guarded_current_prefix', 'V293_OSSched_current_precondition_witness']
SCOPE = 'SAME_GUARDED_PREFIX_CURRENT_MEMBERSHIP_DISTINCT_SPATIAL_TARGET_NOT_SWPRE_OR_GOOD_OS'
CONTROLS = {
    'target_equality_inverted_only': 'REJECTED_AT_V293_OSSched_current_target',
    'target_output_read_permission_only': 'REJECTED_AT_V293_target_global_spatial',
    'target_abstract_table_removed_only': 'REJECTED_AT_V293_OSSched_current_tail_entails',
    'blocked_current_forced_ready_only': 'CORE_COMPILES_REJECTED_AT_V293_current_relations',
    'current_prefix_false_premise_added_only': 'MUTANT_AND_WITNESS_COMPILE_REJECTED_AT_checked_guarded_current',
}

# Expected interfaces below are independent of candidate assertion definitions.
PROBE = r'''
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrentWitness.
Definition checked_current_task (tasks : TcbMod.map) (t : Modules.addrval) nc :=
  nc < 13 /\ exists st m, get tasks t = Some (Int.repr (Z.of_nat nc), st, m).
Definition checked_switch_target (tasks : TcbMod.map) tid target : asrt :=
  EX next : Modules.tid, [|indom tasks tid /\ next <> tid|] **
    (AHprio checked_scheduler next ** ((EX p : type, GV target @ (Tptr p) |-> (Vptr next)) ** Atrue)).
Definition checked_current_target : forall lo hi entries tasks current nc next,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  checked_bitmap_tasks lo hi tasks -> checked_priority_table entries tasks ->
  checked_current_task tasks current nc -> checked_highest tasks next ->
  (next = current <-> V293_ready_select lo hi (V293_ready_group lo hi) = nc) :=
  V293_OSSched_current_target.
Section CheckedCurrent.
Variables unmap group rows high : var.
Variables bt bg br bh : block.
Variables lo hi : nat.
Variable li : LocalInv.
Variable tid : Modules.tid.
Variable aop : spec_code.
Variables table target : var.
Variable tp : type.
Variables bp bo : block.
Variable entries : list val.
Variable tasks : TcbMod.map.
Variables current counter : var.
Variables bcur bcounter : block.
Variable nc : nat.
Variable frame : asrt.
Let tail := checked_tail unmap group rows high bt bg br bh lo hi li tid aop
  table target tp bp bo entries tasks current counter bcur bcounter nc frame.
Definition checked_current_tail_entails : forall c,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  checked_bitmap_tasks lo hi tasks -> checked_priority_table entries tasks ->
  checked_current_task tasks tid nc -> V293_ready_select lo hi (V293_ready_group lo hi) <> nc ->
  tail c ==> (tail c //\\ checked_switch_target tasks tid target) :=
  V293_OSSched_current_tail_entails unmap group rows high bt bg br bh lo hi li tid aop
    table target tp bp bo entries tasks current counter bcur bcounter nc frame.
End CheckedCurrent.

Definition checked_guarded_current : forall Spec sd li I r ri tid aop frame
    sched_id unmap group rows high bt bg br bh lo hi table target tp bp bo entries tasks old
    interrupt lock bi bl ni nl current counter bcur bcounter nc c suffix q (Hli : GoodLInvAsrt li),
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  checked_bitmap_tasks lo hi tasks -> checked_priority_table entries tasks -> GoodFrm frame ->
  ni < 256 -> nl < 256 -> checked_current_task tasks tid nc ->
  Spec sched_id = Some
    (V293_sched_fpre unmap group rows high bt bg br bh li Hli,
     V293_sched_fpost unmap group rows high bt bg br bh li Hli, (Tvoid, nil)) ->
  let gf := checked_guard_cell interrupt bi ni ** (checked_guard_cell lock bl nl ** frame) in
  let pre := checked_pre unmap group rows high bt bg br bh lo hi li tid aop **
    (checked_prefix_frame table high target tp bp bo entries tasks
      (checked_guard_cell current bcur nc ** gf) **
      (checked_prefix_output tp bo old ** checked_counter_cell counter bcounter c)) in
  let mid := checked_tail unmap group rows high bt bg br bh lo hi li tid aop
    table target tp bp bo entries tasks current counter bcur bcounter nc gf in
  (ni = 0 -> nl = 0 -> V293_ready_select lo hi (V293_ready_group lo hi) <> nc ->
    InfRules Spec sd li I r ri
      (mid (Int.add c Int.one) //\\ checked_switch_target tasks tid target) suffix q tid) ->
  InfRules Spec sd li I r ri pre
    (sifthen (ebinop oeq (ecast (evar interrupt) Tint32) (econst32 (Int.repr 0)))
      (sifthen (ebinop oeq (ecast (evar lock) Tint32) (econst32 (Int.repr 0)))
        (sseq (sseq (scall sched_id nil) (sassign (evar target) (earrayelem (evar table) (evar high))))
          (sifthen (eunop oppsite (ebinop oeq (ecast (evar high) Tint32) (ecast (evar current) Tint32)))
            (sseq (sassign (evar counter) (ebinop oplus (evar counter) (econst32 Int.one))) suffix)))))
    (if Nat.eqb ni 0 && Nat.eqb nl 0 then
      (if Nat.eqb (V293_ready_select lo hi (V293_ready_group lo hi)) nc then mid c else q) else pre) tid :=
  V293_OSSched_guarded_current_prefix.

(* Fix BOTH concrete maps independently, including the blocked current case. *)
Definition checked_mode_tasks (different : bool) : TcbMod.map := if different then
  set (sig V293_idle_tid (Int.repr 4, wait os_stat_time Int.one, Vnull))
    (15%positive, Int.zero) (Int.repr 12, rdy, Vnull)
  else sig V293_idle_tid (Int.repr 12, rdy, Vnull).
Definition checked_mode_entries (different : bool) : list val := if different then
  repeat Vnull 4 ++ cons (Vptr V293_idle_tid) (repeat Vnull 7 ++ cons (Vptr (15%positive, Int.zero)) nil)
  else repeat Vnull 12 ++ cons (Vptr V293_idle_tid) nil.
Definition checked_current_witness : forall different ni nl c,
  ni < 256 -> nl < 256 -> exists s,
  checked_bitmap_tasks 0 16 (checked_mode_tasks different) /\
  checked_priority_table (checked_mode_entries different) (checked_mode_tasks different) /\
  checked_current_task (checked_mode_tasks different) V293_idle_tid (if different then 4 else 12) /\
  (V293_ready_select 0 16 (V293_ready_group 0 16) <> (if different then 4 else 12) <-> different = true) /\
  s |= checked_pre 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive
    0 16 V293_witness_li V293_idle_tid (spec_done None) **
    (checked_prefix_frame 106%Z 103%Z 107%Z Tvoid 8%positive 10%positive
      (checked_mode_entries different) (checked_mode_tasks different)
      (checked_guard_cell 110%Z 13%positive (if different then 4 else 12) **
        (checked_guard_cell 108%Z 11%positive ni ** (checked_guard_cell 109%Z 12%positive nl ** Aemp))) **
      (checked_prefix_output Tvoid 10%positive Vnull ** checked_counter_cell 111%Z 14%positive c)) :=
  V293_OSSched_current_precondition_witness.
'''


def mutations(source, witness, replace):
    def only(name, old, new):
        start = source.index(name)
        end = source.index('Qed.', start) + len('Qed.')
        return source[:start] + replace(source[start:end], old, new) + source[end:]
    wrong_equal = only('Theorem V293_OSSched_current_target',
        '(next = current <->', '(next <> current <->')
    permission = only('Lemma V293_target_global_spatial',
        'V293_prefix_output tp bo (Vptr next) ==>','Amapsto (bo, 0%Z) (Tptr tp) false (Vptr next) ==>')
    no_table = only('Theorem V293_OSSched_current_tail_entails',
        's |= Aabsdata abstcblsid (abstcblist tasks) **', 's |= Aemp **')
    forced_ready = replace(witness,
        'get V293_current_tasks V293_idle_tid =\n    Some (Int.repr 4, wait os_stat_time Int.one, Vnull)',
        'get V293_current_tasks V293_idle_tid =\n    Some (Int.repr 4, rdy, Vnull)')
    false_pre = only('Theorem V293_OSSched_guarded_current_prefix',
        '  lo < 256 -> hi < 256 ->', '  False -> lo < 256 -> hi < 256 ->')
    start = false_pre.index('Theorem V293_OSSched_guarded_current_prefix')
    false_pre = false_pre[:start] + replace(false_pre[start:],
        '    Hli Hlo Hhi Hr Hb', '    Hli Hfalse Hlo Hhi Hr Hb')
    return {
        'target_equality_inverted_only': (wrong_equal, witness, CORE, 'Theorem V293_OSSched_current_target'),
        'target_output_read_permission_only': (permission, witness, CORE, 'Lemma V293_target_global_spatial'),
        'target_abstract_table_removed_only': (no_table, witness, CORE, 'Theorem V293_OSSched_current_tail_entails'),
        'blocked_current_forced_ready_only': (source, forced_ready, WITNESS, 'Lemma V293_current_relations'),
        'current_prefix_false_premise_added_only': (false_pre, witness, None, 'Definition checked_guarded_current :'),
    }


def check(root, work, build, coqbin, run, loader, location):
    caller = loader(root, 'v293-scheduler-caller.py')
    probe = (loader(root, 'v293-scheduler-source.py').PROBE +
             loader(root, 'v293-scheduler-internal.py').PRELUDE + caller.PROBE +
             loader(root, 'v293-scheduler-prefix.py').PROBE +
             loader(root, 'v293-scheduler-guards.py').PROBE +
             loader(root, 'v293-scheduler-change.py').PROBE + PROBE)
    checks = {}
    def record(label, command, cwd):
        if label in checks:
            raise ValueError('duplicate current command identity: ' + label)
        row = run('current:' + label, command, cwd); checks[label] = row
        return row

    def compile_tree(label, core, witness, assumptions=False):
        dest = work / ('current_' + label)
        shutil.copytree(build / 'certiucos', dest / 'certiucos')
        (dest / 'checks').mkdir()
        flags = ['-R', str(build / 'framework'), 'CertiOS.framework',
                 '-R', str(build / 'tactics'), 'CertiOS.tactics',
                 '-R', str(dest / 'certiucos'), 'CertiOS.certiucos',
                 '-R', str(dest / 'checks'), 'CurrentCheck']
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
    row, flags, dest = compile_tree('positive', source, witness, assumptions=True)
    if row['exit_code']:
        raise ValueError('current proof/probe failed: ' + str(row))
    trust = loader(root, 'check-memory-trust.py'); assumptions = set()
    for part in row['stdout'].split('Axioms:')[1:]:
        assumptions |= set(trust.check_assumptions(part.split('Closed under the global context')[0], trust.FRAMEWORK_ALLOWED))
    if row['stdout'].count('Axioms:') + row['stdout'].count('Closed under the global context') != len(ROOTS):
        raise ValueError('missing current root assumption output')
    row = record('coqchk', [coqbin + 'coqchk', '-silent', *flags,
        *['CertiOS.' + Path(f).with_suffix('').as_posix().replace('/', '.') for f in FILES],
        'CurrentCheck.Contract'], dest)
    if row['exit_code']:
        raise ValueError('current coqchk failed: ' + str(row))
    for label, (core, wit, failed_rel, declaration) in mutations(source, witness, caller.replace_once).items():
        row, _, _ = compile_tree(label, core, wit)
        failed_source = probe if failed_rel is None else (core if failed_rel == CORE else wit)
        start = failed_source.index(declaration)
        lo = failed_source[:start].count('\n') + 1
        end = (failed_source.index('\n(* Fix BOTH', start) if failed_rel is None
               else failed_source.index('Qed.', start))
        hi = failed_source[:end].count('\n') + 1
        match = re.search(r'line (\d+), characters', row['stderr'])
        expected_file = '/checks/Contract.v' if failed_rel is None else '/' + failed_rel
        if (row['exit_code'] != 1 or not match or not lo <= int(match[1]) <= hi
                or expected_file not in row['stderr']):
            raise ValueError('current control missed designated obligation: ' + label + ': ' + str(row))
        for rel in (FILES if failed_rel is None else FILES[:FILES.index(failed_rel)]):
            if checks[label + ':' + Path(rel).stem]['exit_code'] != 0:
                raise ValueError('current control prerequisite failed')
    return {'scope': SCOPE, 'coverage_credit': False, 'roots': ROOTS, 'source_location': location,
            'root_assumptions': sorted(assumptions), 'negative_controls': CONTROLS}


def validate(root, checkpoint, checks, loader):
    import json
    inventory = json.loads((root / 'audit/repaired-source-inventory.json').read_text())
    expected = {'scope': SCOPE, 'coverage_credit': False, 'roots': ROOTS,
        'source_location': next(f for f in inventory['functions'] if f['name'] == 'OS_Sched'),
        'root_assumptions': checkpoint['root_assumptions'], 'negative_controls': CONTROLS}
    if checkpoint != expected:
        raise ValueError('current checkpoint scope/roots/source/controls differ')
    if not set(checkpoint['root_assumptions']) <= loader(root, 'check-memory-trust.py').FRAMEWORK_ALLOWED:
        raise ValueError('unexpected current root assumptions')
    for key in ['positive:' + Path(f).stem for f in FILES] + ['positive:contract', 'coqchk']:
        if checks['current:' + key]['exit_code'] != 0:
            raise ValueError('current checkpoint positive check failed')
    for label in CONTROLS:
        fail = ('contract' if label == 'current_prefix_false_premise_added_only' else
                Path(WITNESS if label == 'blocked_current_forced_ready_only' else CORE).stem)
        for rel in (FILES if fail == 'contract' else FILES[:FILES.index(WITNESS)] if fail == Path(WITNESS).stem else []):
            if checks['current:' + label + ':' + Path(rel).stem]['exit_code'] != 0:
                raise ValueError('current control prerequisite missing')
        if checks['current:' + label + ':' + fail]['exit_code'] != 1:
            raise ValueError('current designated control missing')
