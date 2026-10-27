#!/usr/bin/env python3
"""Finish the enabled self branch without pretending disabled guards schedule.

Expected contracts below are literal. The unchanged stage23 literal probe is
reused for its independent resource definitions, never candidate type output.
"""
from pathlib import Path
import re
import shutil

CORE = 'certiucos/v293/proofs/V293OSSchedDispatchFinish.v'
WITNESS = 'certiucos/v293/proofs/V293OSSchedDispatchFinishWitness.v'
FILES = [CORE, WITNESS]
ROOTS = ['V293_dispatch_self_sched', 'V293_dispatch_equal_finish',
         'V293_dispatch_change_finish', 'V293_dispatch_prefix_finish',
         'V293_OSSched_guarded_dispatch_finish', 'V293_locked_dispatch_deferred_witness']
SCOPE = 'ENABLED_NORMALIZED_DISPATCH_CONSUMES_SCHED_DISABLED_DEFERS_NOT_FULL_OS_SCHED_OR_GOOD_OS'
OBLIGATIONS = {
    'equal_pending_post_only': (CORE, 'Theorem V293_dispatch_equal_finish :'),
    'counter_condition_inverted_only': (CORE, 'Theorem V293_dispatch_change_finish :'),
    'guard_false_premise_only': (None, 'Definition checked_V293_OSSched_guarded_dispatch_finish :'),
    'guard_entry_action_only': (CORE, 'Theorem V293_OSSched_guarded_dispatch_finish :'),
}
CONTROLS = {
    'equal_pending_post_only': 'REJECTED_AT_V293_dispatch_equal_finish_NOT_DOWNSTREAM_CREDIT',
    'counter_condition_inverted_only': 'REJECTED_AT_V293_dispatch_change_finish_NOT_DOWNSTREAM_CREDIT',
    'guard_false_premise_only': 'CORE_AND_WITNESS_COMPILE_REJECTED_AT_checked_V293_OSSched_guarded_dispatch_finish',
    'guard_entry_action_only': 'REJECTED_AT_V293_OSSched_guarded_dispatch_finish_NOT_DOWNSTREAM_CREDIT',
}

PROBE = r'''
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedDispatchFinish.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedDispatchFinishWitness.
Section CheckedDispatchFinish.
Variables unmap group rows high : var.
Variables bt bg br bh : block.
Variables lo hi : nat.
Variable tid : Modules.tid.
Variable aop : spec_code.
Variables table target : var.
Variable tp : type.
Variables bp bo : block.
Variable entries : list val.
Variable tasks : TcbMod.map.
Variable events : EcbMod.map.
Variable now : int32.
Variables current counter : var.
Variables bcur bcounter : block.
Variable nc : nat.
Variable frame : asrt.
Variable stack : list hid.
Variable critical : list bool.
Let tail c := checked_dispatch_tail unmap group rows high bt bg br bh lo hi tid aop
  table target tp bp bo entries tasks events now current counter bcur bcounter nc frame stack critical c.
Let locals c := checked_dispatch_locals unmap group rows high bt bg br bh lo hi
  table target tp bp bo entries current counter bcur bcounter nc frame c.
Let resumed op c := checked_switch_resume target tp tid op stack critical (locals c).
Definition checked_self_resources c :=
  ((checked_lent_flags ** ((CurTid tid ** checked_lent_fields tid tasks events now) **
    (GV target @ (Tptr tp) |-> (Vptr tid)))) ** CurTid tid) **
  ((Ais stack ** Acs critical) ** locals c).
Definition checked_V293_dispatch_self_sched : forall c s,
  V293_highest_ready tasks tid -> s |= checked_self_resources c ->
  sched_self V293_scheduler (getabst s).
Proof. intros; eapply V293_dispatch_self_sched; eassumption. Qed.

Definition checked_V293_dispatch_equal_finish : forall c,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
  V293_current_task tasks tid nc -> GoodFrm frame ->
  V293_ready_select lo hi (V293_ready_group lo hi) = nc ->
  absinferfull V293_scheduler V293_shared_li (tail c) (resumed aop c) tid.
Proof. intros; eapply V293_dispatch_equal_finish; eassumption. Qed.

Definition checked_completed_counter c :=
  if Nat.eqb (V293_ready_select lo hi (V293_ready_group lo hi)) nc then c else Int.add c Int.one.
Definition checked_V293_dispatch_change_finish : forall Spec r ri c,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
  V293_current_task tasks tid nc -> GoodFrm frame ->
  InfRules Spec V293_scheduler V293_shared_li (V293_dispatch_inv target tp) r ri
    (tail c) (V293_OSSched_change high current counter (sprim (switch target)))
    (resumed aop (checked_completed_counter c)) tid.
Proof. intros; eapply V293_dispatch_change_finish; eassumption. Qed.

Definition checked_V293_dispatch_prefix_finish : forall Spec r ri sched_id c,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
  V293_current_task tasks tid nc -> GoodFrm frame ->
  Spec sched_id = Some
    (V293_critical_fpre unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     V293_critical_fpost unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good, (Tvoid, nil)) ->
  InfRules Spec V293_scheduler V293_shared_li (V293_dispatch_inv target tp) r ri
    (checked_lent_pre unmap group rows high bt bg br bh lo hi V293_shared_li tid (sched;;aop)
      table target tp bp bo entries tasks events now
      (V293_guard_cell current bcur nc ** (V293_counter_cell counter bcounter c ** frame)) stack critical)
    (sseq (V293_OSSched_unlocked_prefix sched_id table high target)
      (V293_OSSched_change high current counter (sprim (switch target))))
    (resumed aop (checked_completed_counter c)) tid.
Proof. intros; eapply V293_dispatch_prefix_finish; eassumption. Qed.
End CheckedDispatchFinish.

Definition checked_V293_OSSched_guarded_dispatch_finish : forall Spec r ri tid aop frame
    sched_id unmap group rows high bt bg br bh lo hi table target tp bp bo entries tasks events now
    stack critical interrupt lock bi bl ni nl current counter bcur bcounter nc c,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
  V293_current_task tasks tid nc -> GoodFrm frame -> ni < 256 -> nl < 256 ->
  Spec sched_id = Some
    (V293_critical_fpre unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     V293_critical_fpost unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good, (Tvoid, nil)) ->
  let gf := V293_guard_cell interrupt bi ni ** (V293_guard_cell lock bl nl ** frame) in
  let pre := checked_lent_pre unmap group rows high bt bg br bh lo hi V293_shared_li tid (sched;;aop)
    table target tp bp bo entries tasks events now
    (V293_guard_cell current bcur nc ** (V293_counter_cell counter bcounter c ** gf)) stack critical in
  let post := checked_switch_resume target tp tid aop stack critical
    (checked_dispatch_locals unmap group rows high bt bg br bh lo hi table target tp bp bo entries
      current counter bcur bcounter nc gf
      (if Nat.eqb (V293_ready_select lo hi (V293_ready_group lo hi)) nc then c else Int.add c Int.one)) in
  InfRules Spec V293_scheduler V293_shared_li (V293_dispatch_inv target tp) r ri pre
    (V293_OSSched_guards interrupt lock
      (sseq (V293_OSSched_unlocked_prefix sched_id table high target)
        (V293_OSSched_change high current counter (sprim (switch target)))))
    (if Nat.eqb ni 0 && Nat.eqb nl 0 then post else pre) tid.
Proof. intros; eapply V293_OSSched_guarded_dispatch_finish; eassumption. Qed.

Definition checked_V293_locked_dispatch_deferred_witness : forall c events now aop, exists s,
  s |= checked_lent_pre 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive
    0 16 V293_shared_li V293_idle_tid (sched;;aop)
    106%Z 107%Z Tvoid 8%positive 10%positive
    (V293_current_mode_entries true) (V293_current_mode_tasks true) events now
    (V293_guard_cell 110%Z 13%positive (V293_current_mode_priority true) **
      (V293_counter_cell 111%Z 14%positive c **
        (V293_guard_cell 108%Z 11%positive 0 ** (V293_guard_cell 109%Z 12%positive 1 ** Aemp)))) nil nil /\
  ~ sched_self V293_scheduler (getabst s).
Proof. intros; eapply V293_locked_dispatch_deferred_witness; eassumption. Qed.
'''


def mutations(core, witness, replace):
    equal = replace(core, '(tail c) (resumed aop c) tid.', '(tail c) (resumed (sched;;aop) c) tid.')
    counter = replace(core,
        'if Nat.eqb (V293_ready_select lo hi (V293_ready_group lo hi)) nc then c else Int.add c Int.one.',
        'if negb (Nat.eqb (V293_ready_select lo hi (V293_ready_group lo hi)) nc) then c else Int.add c Int.one.')
    start = core.index('Theorem V293_OSSched_guarded_dispatch_finish :')
    prefix, guard = core[:start], core[start:]
    false = prefix + replace(replace(guard, '  lo < 256 ->', '  False -> lo < 256 ->'),
        'nc c Hlo Hhi', 'nc c Hfalse Hlo Hhi')
    action = prefix + replace(guard, 'V293_shared_li tid (sched;;aop)', 'V293_shared_li tid aop')
    return {label: (source, witness, *OBLIGATIONS[label]) for label, source in {
        'equal_pending_post_only': equal, 'counter_condition_inverted_only': counter,
        'guard_false_premise_only': false, 'guard_entry_action_only': action}.items()}


def contract(loader, root):
    return loader(root, 'v293-scheduler-dispatch-tail.py').PROBE + PROBE


def check_rejection(row, source, rel, declaration, label):
    start = source.index(declaration)
    lo = source[:start].count('\n') + 1
    hi = source[:source.index('Qed.', start) + len('Qed.')].count('\n') + 1
    match = re.search(r'File "([^"\n]+)", line (\d+), characters', row['stderr'])
    expected = '/checks/Contract.v' if rel is None else '/' + rel
    if (row['exit_code'] != 1 or not match or not lo <= int(match[2]) <= hi
            or not ('/' + match[1]).endswith(expected) or '\nError:' not in row['stderr']):
        raise ValueError('dispatch-finish control missed designated obligation: ' + label + ': ' + str(row))


def check(root, work, build, coqbin, run, loader, location):
    probe = contract(loader, root)
    checks = {}

    def record(label, command, cwd):
        if label in checks:
            raise ValueError('duplicate dispatch-finish command identity: ' + label)
        row = run('dispatch_finish:' + label, command, cwd)
        checks[label] = row
        return row

    def compile_tree(label, core, witness, assumptions=False):
        dest = work / ('dispatch_finish_' + label)
        shutil.copytree(build / 'certiucos', dest / 'certiucos')
        (dest / 'checks').mkdir()
        flags = ['-R', str(build / 'framework'), 'CertiOS.framework',
                 '-R', str(build / 'tactics'), 'CertiOS.tactics',
                 '-R', str(dest / 'certiucos'), 'CertiOS.certiucos',
                 '-R', str(dest / 'checks'), 'DispatchFinishCheck']
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

    core = (root / CORE).read_text()
    witness = (root / WITNESS).read_text()
    variants = mutations(core, witness, loader(root, 'v293-scheduler-caller.py').replace_once)
    row, flags, dest = compile_tree('positive', core, witness, assumptions=True)
    if row['exit_code']:
        raise ValueError('dispatch-finish proof/probe failed: ' + str(row))
    trust = loader(root, 'check-memory-trust.py')
    assumptions = set()
    for part in row['stdout'].split('Axioms:')[1:]:
        assumptions |= set(trust.check_assumptions(part.split('Closed under the global context')[0], trust.FRAMEWORK_ALLOWED))
    if row['stdout'].count('Axioms:') + row['stdout'].count('Closed under the global context') != len(ROOTS):
        raise ValueError('missing dispatch-finish root assumption output')
    row = record('coqchk', [coqbin + 'coqchk', '-silent', *flags,
        *['CertiOS.' + Path(f).with_suffix('').as_posix().replace('/', '.') for f in FILES],
        'DispatchFinishCheck.Contract'], dest)
    if row['exit_code']:
        raise ValueError('dispatch-finish coqchk failed: ' + str(row))
    for label, (source, wit, rel, declaration) in variants.items():
        row, _, _ = compile_tree(label, source, wit)
        check_rejection(row, probe if rel is None else source if rel == CORE else wit, rel, declaration, label)
        for previous in (FILES if rel is None else FILES[:FILES.index(rel)]):
            if checks[label + ':' + Path(previous).stem]['exit_code'] != 0:
                raise ValueError('dispatch-finish control prerequisite failed')
    return {'scope': SCOPE, 'coverage_credit': False, 'roots': ROOTS, 'source_location': location,
            'root_assumptions': sorted(assumptions), 'negative_controls': CONTROLS}


def validate(root, checkpoint, checks, loader):
    import json
    inventory = json.loads((root / 'audit/repaired-source-inventory.json').read_text())
    expected = {'scope': SCOPE, 'coverage_credit': False, 'roots': ROOTS,
        'source_location': next(f for f in inventory['functions'] if f['name'] == 'OS_Sched'),
        'root_assumptions': checkpoint['root_assumptions'], 'negative_controls': CONTROLS}
    if checkpoint != expected:
        raise ValueError('dispatch-finish checkpoint scope/roots/source/controls differ')
    if not set(checkpoint['root_assumptions']) <= loader(root, 'check-memory-trust.py').FRAMEWORK_ALLOWED:
        raise ValueError('unexpected dispatch-finish root assumptions')
    for key in ['positive:' + Path(f).stem for f in FILES] + ['positive:contract', 'coqchk']:
        if checks['dispatch_finish:' + key]['exit_code'] != 0:
            raise ValueError('dispatch-finish checkpoint positive check failed')
    probe = contract(loader, root)
    variants = mutations((root / CORE).read_text(), (root / WITNESS).read_text(),
                         loader(root, 'v293-scheduler-caller.py').replace_once)
    for label, (source, wit, rel, declaration) in variants.items():
        prerequisites = FILES if rel is None else FILES[:FILES.index(rel)]
        for previous in prerequisites:
            if checks['dispatch_finish:' + label + ':' + Path(previous).stem]['exit_code'] != 0:
                raise ValueError('dispatch-finish control prerequisite missing')
        fail = 'contract' if rel is None else Path(rel).stem
        row = checks['dispatch_finish:' + label + ':' + fail]
        if row['exit_code'] != 1:
            raise ValueError('dispatch-finish designated control missing')
        check_rejection(row, probe if rel is None else source if rel == CORE else wit, rel, declaration, label)
