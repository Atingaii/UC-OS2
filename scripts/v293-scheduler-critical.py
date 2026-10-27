#!/usr/bin/env python3
"""Actual SWINV and dynamic stacks inside the internal contract, not GoodFrm."""
from pathlib import Path
import re
import shutil

CORE = 'certiucos/v293/proofs/V293OSSchedCritical.v'
WITNESS = 'certiucos/v293/proofs/V293OSSchedCriticalWitness.v'
FILES = [CORE, WITNESS]
ROOTS = ['V293_OSSchedNew_critical_contract', 'V293_OSSchedNew_critical_WFFunEnv', 'V293_critical_args_roundtrip', 'V293_OSSchedNew_critical_call', 'V293_OSSched_critical_prefix', 'V293_OSSched_guarded_critical_prefix', 'V293_OSSched_critical_precondition_witness']
SCOPE = 'SAME_SOURCE_PREFIX_PRESERVES_SWINV_AND_DYNAMIC_STACKS_NOT_SWITCH_OR_GOOD_OS'
CONTROLS = {
    'payload_return_dropped_only': 'REJECTED_AT_V293_sched_return_resource_payload',
    'critical_call_snapshot_reset_only': 'REJECTED_AT_V293_critical_args_roundtrip',
    'critical_stack_ignored_only': 'MUTANT_AND_WITNESS_COMPILE_REJECTED_AT_checked_critical_pre_selector',
    'critical_prefix_false_premise_added_only': 'MUTANT_AND_WITNESS_COMPILE_REJECTED_AT_checked_guarded_critical',
    'critical_prefix_illegal_frame_premise_added_only': 'MUTANT_AND_WITNESS_COMPILE_REJECTED_AT_checked_guarded_critical',
}

# Static expected assertions, selectors and exact interfaces; no type reflection.
PROBE = r'''
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCritical.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCriticalWitness.
Definition checked_critical (I : Inv) (stack : is) (critical : cs) : asrt :=
  SWINV I ** (Ais stack ** Acs critical).
Definition checked_linked_tail unmap group rows high bt bg br bh lo hi li tid aop
    table target tp bp bo entries tasks current counter bcur bcounter nc frame c :=
  checked_tail unmap group rows high bt bg br bh lo hi li tid aop
    table target tp bp bo entries tasks current counter bcur bcounter nc frame c //\\
    checked_switch_target tasks tid target.
Definition checked_mode_priority (different : bool) := if different then 4 else 12.
Definition checked_critical_args (lg : list logicvar) : option (nat * nat * spec_code * is * cs) :=
  match lg with
  | cons (logic_lv (cons (Vint32 low) (cons (Vint32 upper) nil)))
      (cons (logic_code aop) (cons (logic_is stack) (cons (logic_cs critical) nil))) =>
      Some (Z.to_nat (Int.unsigned low), Z.to_nat (Int.unsigned upper), aop, stack, critical)
  | _ => None
  end.
Lemma checked_critical_pre_selector : forall unmap group rows high bt bg br bh li I
    (Hli : GoodLInvAsrt li) vl lg tid,
  getasrt (V293_critical_fpre unmap group rows high bt bg br bh li I Hli vl lg tid) =
  match checked_critical_args lg with
  | Some (lo, hi, aop, stack, critical) =>
      checked_pre unmap group rows high bt bg br bh lo hi li tid aop **
          checked_critical I stack critical
  | _ => Afalse
  end.
Proof. intros. reflexivity. Qed.
Lemma checked_critical_post_selector : forall unmap group rows high bt bg br bh li I
    (Hli : GoodLInvAsrt li) vl result lg tid,
  getasrt (V293_critical_fpost unmap group rows high bt bg br bh li I Hli vl result lg tid) =
  match checked_critical_args lg with
  | Some (lo, hi, aop, stack, critical) =>
      checked_post unmap group rows high bt bg br bh lo hi li tid aop result **
          checked_critical I stack critical
  | _ => Afalse
  end.
Proof. intros. reflexivity. Qed.

Definition checked_critical_contract : forall P f Spec sd li I
    unmap group rows high y bt bg br bh (Hli : GoodLInvAsrt li) lg tid vl pre post,
  unmap <> y -> group <> y -> rows <> y -> high <> y ->
  P f = Some (V293_OSSchedNew_function unmap group rows high y) ->
  Some pre = BuildPreI P f vl lg (V293_critical_fpre unmap group rows high bt bg br bh li I Hli) tid ->
  Some post = BuildRetI P f vl lg (V293_critical_fpost unmap group rows high bt bg br bh li I Hli) tid ->
  InfRules Spec sd li I post Afalse pre (V293_OSSchedNew_body unmap group rows high y) Afalse tid :=
  V293_OSSchedNew_critical_contract.

Definition checked_critical_WFFunEnv : forall sched_id unmap group rows high y bt bg br bh li I Hli sd,
  unmap <> y -> group <> y -> rows <> y -> high <> y ->
  WFFunEnv (fun f => if Z.eq_dec f sched_id then Some (Tvoid, dnil, dcons y Tint8 dnil,
      V293_OSSchedNew_body unmap group rows high y) else None)
    (fun f => if Z.eq_dec f sched_id then Some
      (V293_critical_fpre unmap group rows high bt bg br bh li I Hli,
       V293_critical_fpost unmap group rows high bt bg br bh li I Hli, (Tvoid, nil)) else None) sd li I :=
  V293_OSSchedNew_critical_WFFunEnv.

Definition checked_critical_roundtrip : forall lo hi aop stack critical,
  lo < 256 -> hi < 256 ->
  V293_critical_args (V293_critical_call_lg lo hi aop stack critical) = Some (lo,hi,aop,stack,critical) :=
  V293_critical_args_roundtrip.

Definition checked_critical_call : forall Spec sd li I r ri tid aop frame
    sched_id unmap group rows high bt bg br bh lo hi stack critical (Hli : GoodLInvAsrt li),
  lo < 256 -> hi < 256 -> GoodFrm frame ->
  Spec sched_id = Some
    (V293_critical_fpre unmap group rows high bt bg br bh li I Hli,
     V293_critical_fpost unmap group rows high bt bg br bh li I Hli, (Tvoid, nil)) ->
  InfRules Spec sd li I r ri
    ((checked_pre unmap group rows high bt bg br bh lo hi li tid aop **
       checked_critical I stack critical) ** frame)
    (scall sched_id nil)
    (EX result : option val,
      (checked_post unmap group rows high bt bg br bh lo hi li tid aop result **
        checked_critical I stack critical) ** frame) tid :=
  V293_OSSchedNew_critical_call.

Definition checked_critical_prefix : forall Spec sd li I r ri tid aop frame
    sched_id unmap group rows high bt bg br bh lo hi table target tp bp bo entries tasks old
    stack critical (Hli : GoodLInvAsrt li),
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  checked_bitmap_tasks lo hi tasks -> checked_priority_table entries tasks -> GoodFrm frame ->
  Spec sched_id = Some
    (V293_critical_fpre unmap group rows high bt bg br bh li I Hli,
     V293_critical_fpost unmap group rows high bt bg br bh li I Hli, (Tvoid, nil)) ->
  InfRules Spec sd li I r ri
    ((checked_pre unmap group rows high bt bg br bh lo hi li tid aop **
      checked_critical I stack critical) **
      (checked_prefix_frame table high target tp bp bo entries tasks frame ** checked_prefix_output tp bo old))
    (V293_OSSched_unlocked_prefix sched_id table high target)
    (EX t : Modules.tid, [|checked_highest tasks t|] **
      (checked_post unmap group rows high bt bg br bh lo hi li tid aop None **
        (checked_prefix_frame table high target tp bp bo entries tasks
          (checked_critical I stack critical ** frame) ** checked_prefix_output tp bo (Vptr t)))) tid :=
  V293_OSSched_critical_prefix.

Definition checked_guarded_critical : forall Spec sd li I r ri tid aop frame
    sched_id unmap group rows high bt bg br bh lo hi table target tp bp bo entries tasks old
    interrupt lock bi bl ni nl current counter bcur bcounter nc c stack critical suffix q (Hli : GoodLInvAsrt li),
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  checked_bitmap_tasks lo hi tasks -> checked_priority_table entries tasks -> GoodFrm frame ->
  ni < 256 -> nl < 256 -> checked_current_task tasks tid nc ->
  Spec sched_id = Some
    (V293_critical_fpre unmap group rows high bt bg br bh li I Hli,
     V293_critical_fpost unmap group rows high bt bg br bh li I Hli, (Tvoid, nil)) ->
  let gf := checked_guard_cell interrupt bi ni ** (checked_guard_cell lock bl nl ** frame) in
  let k := checked_critical I stack critical in
  let pre := (checked_pre unmap group rows high bt bg br bh lo hi li tid aop ** k) **
    (checked_prefix_frame table high target tp bp bo entries tasks
      (checked_guard_cell current bcur nc ** gf) **
      (checked_prefix_output tp bo old ** checked_counter_cell counter bcounter c)) in
  let mid := checked_tail unmap group rows high bt bg br bh lo hi li tid aop
    table target tp bp bo entries tasks current counter bcur bcounter nc (k ** gf) in
  let linked := checked_linked_tail unmap group rows high bt bg br bh lo hi li tid aop
    table target tp bp bo entries tasks current counter bcur bcounter nc (k ** gf) in
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
  V293_OSSched_guarded_critical_prefix.

Lemma checked_critical_fixture_empty : forall k,
  getinv (V293_critical_fixture_inv k) = Aemp.
Proof. intros. reflexivity. Qed.

Definition checked_critical_witness : forall different ni nl c,
  ni < 256 -> nl < 256 -> exists s,
  checked_bitmap_tasks 0 16 (checked_mode_tasks different) /\
  checked_priority_table (checked_mode_entries different) (checked_mode_tasks different) /\
  checked_current_task (checked_mode_tasks different) V293_idle_tid (checked_mode_priority different) /\
  (V293_ready_select 0 16 (V293_ready_group 0 16) <> checked_mode_priority different <-> different = true) /\
  s |= (checked_pre 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive
    0 16 V293_witness_li V293_idle_tid (spec_done None) **
      checked_critical V293_critical_fixture_inv nil nil) **
    (checked_prefix_frame 106%Z 103%Z 107%Z Tvoid 8%positive 10%positive
      (checked_mode_entries different) (checked_mode_tasks different)
      (checked_guard_cell 110%Z 13%positive (checked_mode_priority different) **
        (checked_guard_cell 108%Z 11%positive ni ** (checked_guard_cell 109%Z 12%positive nl ** Aemp))) **
      (checked_prefix_output Tvoid 10%positive Vnull ** checked_counter_cell 111%Z 14%positive c)) :=
  V293_OSSched_critical_precondition_witness.
'''


def mutations(source, witness, replace):
    def only(name, old, new):
        start = source.index(name)
        end = source.index('Qed.', start) + len('Qed.')
        return source[:start] + replace(source[start:end], old, new) + source[end:]
    dropped = only('Lemma V293_sched_return_resource_payload',
        'tid hv ** payload)) **', 'tid hv ** Aemp)) **')
    # Snapshot mutation is confined to the encoder, not the decoder or statement.
    start = source.index('Definition V293_critical_call_lg')
    end = source.index('Lemma V293_critical_args_roundtrip', start)
    reset = source[:start] + replace(source[start:end], '(logic_cs critical)', '(logic_cs nil)') + source[end:]
    ignored = replace(source, 'SWINV I ** (Ais stack ** Acs critical).', 'SWINV I ** (Ais stack ** Acs nil).')
    def extra_premise(premise, binder):
        result = only('Theorem V293_OSSched_guarded_critical_prefix',
            '  lo < 256 -> hi < 256 ->', '  ' + premise + ' -> lo < 256 -> hi < 256 ->')
        start = result.index('Theorem V293_OSSched_guarded_critical_prefix')
        return result[:start] + replace(result[start:],
            '    Hli Hlo Hhi Hr Hb', '    Hli ' + binder + ' Hlo Hhi Hr Hb')
    return {
        'payload_return_dropped_only': (dropped, witness, CORE, 'Lemma V293_sched_return_resource_payload'),
        'critical_call_snapshot_reset_only': (reset, witness, CORE, 'Lemma V293_critical_args_roundtrip'),
        'critical_stack_ignored_only': (ignored, witness, None, 'Lemma checked_critical_pre_selector'),
        'critical_prefix_false_premise_added_only': (extra_premise('False', 'Hfalse'), witness, None, 'Definition checked_guarded_critical'),
        'critical_prefix_illegal_frame_premise_added_only': (
            extra_premise('GoodFrm (V293_sched_critical I stack critical)', 'Hillegal'), witness, None, 'Definition checked_guarded_critical'),
    }

def check(root, work, build, coqbin, run, loader, location):
    caller = loader(root, 'v293-scheduler-caller.py')
    probe = (loader(root, 'v293-scheduler-source.py').PROBE +
             loader(root, 'v293-scheduler-internal.py').PRELUDE + caller.PROBE +
             loader(root, 'v293-scheduler-prefix.py').PROBE +
             loader(root, 'v293-scheduler-guards.py').PROBE +
             loader(root, 'v293-scheduler-change.py').PROBE +
             loader(root, 'v293-scheduler-current.py').PROBE + PROBE)
    checks = {}
    def record(label, command, cwd):
        if label in checks:
            raise ValueError('duplicate critical command identity: ' + label)
        row = run('critical:' + label, command, cwd); checks[label] = row
        return row

    def compile_tree(label, core, witness, assumptions=False):
        dest = work / ('critical_' + label)
        shutil.copytree(build / 'certiucos', dest / 'certiucos')
        (dest / 'checks').mkdir()
        flags = ['-R', str(build / 'framework'), 'CertiOS.framework',
                 '-R', str(build / 'tactics'), 'CertiOS.tactics',
                 '-R', str(dest / 'certiucos'), 'CertiOS.certiucos',
                 '-R', str(dest / 'checks'), 'CriticalCheck']
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
        raise ValueError('critical proof/probe failed: ' + str(row))
    trust = loader(root, 'check-memory-trust.py'); assumptions = set()
    for part in row['stdout'].split('Axioms:')[1:]:
        assumptions |= set(trust.check_assumptions(part.split('Closed under the global context')[0], trust.FRAMEWORK_ALLOWED))
    if row['stdout'].count('Axioms:') + row['stdout'].count('Closed under the global context') != len(ROOTS):
        raise ValueError('missing critical root assumption output')
    row = record('coqchk', [coqbin + 'coqchk', '-silent', *flags,
        *['CertiOS.' + Path(f).with_suffix('').as_posix().replace('/', '.') for f in FILES],
        'CriticalCheck.Contract'], dest)
    if row['exit_code']:
        raise ValueError('critical coqchk failed: ' + str(row))
    for label, (core, wit, failed_rel, declaration) in mutations(source, witness, caller.replace_once).items():
        row, _, _ = compile_tree(label, core, wit)
        failed_source = probe if failed_rel is None else (core if failed_rel == CORE else wit)
        start = failed_source.index(declaration)
        lo = failed_source[:start].count('\n') + 1
        end = (failed_source.index('\nProof.', start) + len('\nProof. intros. reflexivity. Qed.')
               if declaration.startswith('Lemma checked_critical_pre_selector')
               else failed_source.index(' :=\n', start) + len(' :=\n  V293_OSSched_guarded_critical_prefix.')
               if failed_rel is None else failed_source.index('Qed.', start))
        hi = failed_source[:end].count('\n') + 1
        match = re.search(r'line (\d+), characters', row['stderr'])
        expected_file = '/checks/Contract.v' if failed_rel is None else '/' + failed_rel
        if (row['exit_code'] != 1 or not match or not lo <= int(match[1]) <= hi
                or expected_file not in row['stderr']):
            raise ValueError('critical control missed designated obligation: ' + label + ': ' + str(row))
        for rel in (FILES if failed_rel is None else FILES[:FILES.index(failed_rel)]):
            if checks[label + ':' + Path(rel).stem]['exit_code'] != 0:
                raise ValueError('critical control prerequisite failed')
    return {'scope': SCOPE, 'coverage_credit': False, 'roots': ROOTS, 'source_location': location,
            'root_assumptions': sorted(assumptions), 'negative_controls': CONTROLS}


def validate(root, checkpoint, checks, loader):
    import json
    inventory = json.loads((root / 'audit/repaired-source-inventory.json').read_text())
    expected = {'scope': SCOPE, 'coverage_credit': False, 'roots': ROOTS,
        'source_location': next(f for f in inventory['functions'] if f['name'] == 'OS_Sched'),
        'root_assumptions': checkpoint['root_assumptions'], 'negative_controls': CONTROLS}
    if checkpoint != expected:
        raise ValueError('critical checkpoint scope/roots/source/controls differ')
    if not set(checkpoint['root_assumptions']) <= loader(root, 'check-memory-trust.py').FRAMEWORK_ALLOWED:
        raise ValueError('unexpected critical root assumptions')
    for key in ['positive:' + Path(f).stem for f in FILES] + ['positive:contract', 'coqchk']:
        if checks['critical:' + key]['exit_code'] != 0:
            raise ValueError('critical checkpoint positive check failed')
    for label in CONTROLS:
        fail = Path(CORE).stem if label in {'payload_return_dropped_only', 'critical_call_snapshot_reset_only'} else 'contract'
        for rel in (FILES if fail == 'contract' else []):
            if checks['critical:' + label + ':' + Path(rel).stem]['exit_code'] != 0:
                raise ValueError('critical control prerequisite missing')
        if checks['critical:' + label + ':' + fail]['exit_code'] != 1:
            raise ValueError('critical designated control missing')
