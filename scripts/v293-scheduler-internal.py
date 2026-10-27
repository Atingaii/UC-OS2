#!/usr/bin/env python3
"""Internal builder/WFFunEnv checkpoint; no whole-kernel coverage credit."""
from pathlib import Path
import re

CORE = 'certiucos/v293/proofs/V293OSSchedNewInternal.v'
WITNESS = 'certiucos/v293/proofs/V293OSSchedNewInternalWitness.v'
FILES = [CORE, WITNESS]
SCOPE = 'PARAMETRIC_INTERNAL_WFFUNENV_AND_SATISFIABLE_BUILDERS_NOT_FULL_KERNEL'
ROOTS = ['V293_OSSchedNew_internal_contract', 'V293_OSSchedNew_WFFunEnv',
         'V293_OSSchedNew_internal_builders', 'V293_OSSchedNew_internal_precondition_witness']
CONTROLS = {
    'local_domain_removed_only': 'REJECTED_AT_V293_sched_entry_context',
    'internal_program_entry_removed_only': 'REJECTED_AT_V293_OSSchedNew_internal_domains',
    'return_value_changed_only': 'REJECTED_AT_V293_sched_return_post',
    'contract_false_premise_added_only': 'ISOLATED_MUTANT_COMPILES_REJECTED_AT_checked_internal_contract',
    'pre_assertion_false_only': 'ISOLATED_SELECTOR_MUTANT_COMPILES_REJECTED_AT_checked_pre_selector',
}

# Exact expected resources/selectors are independent of exported definitions.
# checked_bytes and checked_body_hoare come from the retained body probe.
PRELUDE = r'''
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Definition checked_globals unmap group rows high bt bg br bh : asrt :=
  Agvarenv unmap (Tarray Tint8 256) (bt, 0%Z) //\\
  Agvarenv group Tint8 (bg, 0%Z) //\\
  Agvarenv rows (Tarray Tint8 2) (br, 0%Z) //\\
  Agvarenv high Tint8 (bh, 0%Z).
Definition checked_internal_resource unmap group rows high bt bg br bh lo hi li tid hv :=
  ((checked_globals unmap group rows high bt bg br bh **
    (checked_bytes bt 0 V293_ready_table ** checked_bytes br 0 (cons lo (cons hi nil)) **
      Amapsto (bg, 0%Z) Tint8 false (V293_byteval (V293_ready_group lo hi)))) **
    (CurLINV li tid ** Aie false)) ** PV (bh, Int.zero) @ Tint8 |-> hv.
Definition checked_pre unmap group rows high bt bg br bh lo hi li tid aop :=
  EX hv : val, (<||aop||> ** checked_internal_resource unmap group rows high bt bg br bh lo hi li tid hv) **
    [|lo < 256 /\ hi < 256 /\ (exists p, V293_bitmap_ready lo hi p)|].
Definition checked_post unmap group rows high bt bg br bh lo hi li tid aop (result : option val) :=
  [|result = None /\ V293_bitmap_ready lo hi (V293_ready_select lo hi (V293_ready_group lo hi)) /\
    (forall p, V293_bitmap_ready lo hi p -> V293_ready_select lo hi (V293_ready_group lo hi) <= p)|] **
  (<||aop||> ** checked_internal_resource unmap group rows high bt bg br bh lo hi li tid
    (V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi)))).
Lemma checked_pre_selector : forall unmap group rows high bt bg br bh li (Hli : GoodLInvAsrt li) vl lg tid,
  getasrt (V293_sched_fpre unmap group rows high bt bg br bh li Hli vl lg tid) =
  match lg with
  | cons (logic_lv (cons (Vint32 low) (cons (Vint32 upper) nil))) (cons (logic_code aop) nil) =>
      checked_pre unmap group rows high bt bg br bh
        (Z.to_nat (Int.unsigned low)) (Z.to_nat (Int.unsigned upper)) li tid aop
  | _ => Afalse
  end.
Proof. intros. reflexivity. Qed.
Lemma checked_post_selector : forall unmap group rows high bt bg br bh li (Hli : GoodLInvAsrt li) vl result lg tid,
  getasrt (V293_sched_fpost unmap group rows high bt bg br bh li Hli vl result lg tid) =
  match lg with
  | cons (logic_lv (cons (Vint32 low) (cons (Vint32 upper) nil))) (cons (logic_code aop) nil) =>
      checked_post unmap group rows high bt bg br bh
        (Z.to_nat (Int.unsigned low)) (Z.to_nat (Int.unsigned upper)) li tid aop result
  | _ => Afalse
  end.
Proof. intros. reflexivity. Qed.
Definition checked_internal_contract : forall P f Spec sd li I unmap group rows high y bt bg br bh
    (Hli : GoodLInvAsrt li) lg tid vl pre post,
  unmap <> y -> group <> y -> rows <> y -> high <> y ->
  P f = Some (Tvoid, dnil, dcons y Tint8 dnil, V293_OSSchedNew_body unmap group rows high y) ->
  Some pre = BuildPreI P f vl lg (V293_sched_fpre unmap group rows high bt bg br bh li Hli) tid ->
  Some post = BuildRetI P f vl lg (V293_sched_fpost unmap group rows high bt bg br bh li Hli) tid ->
  InfRules Spec sd li I post Afalse pre (V293_OSSchedNew_body unmap group rows high y) Afalse tid
  := V293_OSSchedNew_internal_contract.
'''
COMPONENT = r'''
Definition checked_WFFunEnv : forall sched_id unmap group rows high y bt bg br bh li Hli sd I,
  unmap <> y -> group <> y -> rows <> y -> high <> y ->
  WFFunEnv
    (fun f => if Z.eq_dec f sched_id then
      Some (Tvoid, dnil, dcons y Tint8 dnil, V293_OSSchedNew_body unmap group rows high y) else None)
    (fun f => if Z.eq_dec f sched_id then Some
      (V293_sched_fpre unmap group rows high bt bg br bh li Hli,
       V293_sched_fpost unmap group rows high bt bg br bh li Hli, (Tvoid, nil)) else None) sd li I
  := V293_OSSchedNew_WFFunEnv.
Definition checked_internal_builders : forall sched_id unmap group rows high y bt bg br bh li Hli lg tid,
  exists pre post,
    Some pre = BuildPreI (V293_OSSchedNew_internal_unit sched_id unmap group rows high y) sched_id nil lg
      (V293_sched_fpre unmap group rows high bt bg br bh li Hli) tid /\
    Some post = BuildRetI (V293_OSSchedNew_internal_unit sched_id unmap group rows high y) sched_id nil lg
      (V293_sched_fpost unmap group rows high bt bg br bh li Hli) tid
  := V293_OSSchedNew_internal_builders.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternalWitness.
Definition checked_lg : list logicvar :=
  cons (logic_lv (cons (Vint32 (Int.repr 0)) (cons (Vint32 (Int.repr 16)) nil)))
    (cons (logic_code (spec_done None)) nil).
Definition checked_internal_witness : exists pre post s,
  Some pre = BuildPreI (V293_OSSchedNew_internal_unit 200%Z 100%Z 101%Z 102%Z 103%Z 104%Z)
    200%Z nil checked_lg
    (V293_sched_fpre 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive
      V293_witness_li V293_witness_li_good) (7%positive, Int.zero) /\
  Some post = BuildRetI (V293_OSSchedNew_internal_unit 200%Z 100%Z 101%Z 102%Z 103%Z 104%Z)
    200%Z nil checked_lg
    (V293_sched_fpost 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive
      V293_witness_li V293_witness_li_good) (7%positive, Int.zero) /\
  s |= pre := V293_OSSchedNew_internal_precondition_witness.
'''


def replace_once(source, old, new):
    if source.count(old) != 1:
        raise ValueError('internal mutation anchor is not unique')
    return source.replace(old, new, 1)


def check(root, work, build, coqbin, run, loader):
    scheduler = loader(root, 'v293-scheduler-source.py')
    checks = {}
    def record(label, command, cwd):
        row = run('internal:' + label, command, cwd)
        checks[label] = row
        return row

    def compile_tree(label, core=None, partial=False, probe=None):
        dest = work / ('internal_' + label)
        flags = ['-R', str(build / 'framework'), 'CertiOS.framework',
                 '-R', str(build / 'tactics'), 'CertiOS.tactics',
                 '-R', str(dest / 'certiucos'), 'CertiOS.certiucos',
                 '-R', str(dest / 'checks'), 'InternalCheck']
        (dest / 'checks').mkdir(parents=True)
        for rel in scheduler.FILES + ([CORE] if partial else FILES):
            path = dest / rel
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(core if rel == CORE and core is not None else (root / rel).read_text())
            row = record(label + ':' + Path(rel).stem, [coqbin + 'coqc', '-q', *flags, str(path)], dest)
            if row['exit_code']:
                return row, flags, dest
        if probe is not None:
            path = dest / 'checks/Contract.v'; path.write_text(probe)
            row = record(label + ':contract', [coqbin + 'coqc', '-q', *flags, str(path)], dest)
        return row, flags, dest

    def failed_at(row, source, declaration):
        match = re.search(r'line (\d+), characters', row['stderr'])
        start = source.index(declaration)
        lo = source[:start].count('\n') + 1
        end = source.find('Qed.', start)
        if declaration.startswith('Definition '):
            end = source.find('\nDefinition ', start + len(declaration))
        hi = source[:end].count('\n') + 1 if end >= 0 else source.count('\n') + 1
        if row['exit_code'] != 1 or not match or not lo <= int(match[1]) <= hi:
            raise ValueError('internal control missed designated obligation: ' + str(row))

    partial_probe = scheduler.PROBE + PRELUDE
    full_probe = partial_probe + COMPONENT
    row, flags, dest = compile_tree('positive', probe=full_probe + '\n' +
        '\n'.join('Print Assumptions ' + name + '.' for name in ROOTS))
    if row['exit_code']:
        raise ValueError('internal proof/probe failed: ' + str(row))
    trust = loader(root, 'check-memory-trust.py')
    assumptions = set()
    for part in row['stdout'].split('Axioms:')[1:]:
        assumptions |= set(trust.check_assumptions(part.split('Closed under the global context')[0], trust.FRAMEWORK_ALLOWED))
    if row['stdout'].count('Axioms:') + row['stdout'].count('Closed under the global context') != len(ROOTS):
        raise ValueError('missing internal root assumption output')
    row = record('coqchk', [coqbin + 'coqchk', '-silent', *flags,
        'CertiOS.certiucos.v293.proofs.V293OSSchedNewInternalWitness', 'InternalCheck.Contract'], dest)
    if row['exit_code']:
        raise ValueError('internal coqchk failed: ' + str(row))

    source = (root / CORE).read_text()
    mutations = {
        'local_domain_removed_only': (replace_once(source,
            'Definition V293_sched_local_domain y := A_dom_lenv (cons (y, Tint8) nil).',
            'Definition V293_sched_local_domain (y : var) := Aemp.'), 'Lemma V293_sched_entry_context'),
        'internal_program_entry_removed_only': (replace_once(source,
            'Some (V293_OSSchedNew_function unmap group rows high y) else None.',
            'None else None.'), 'Lemma V293_OSSchedNew_internal_domains'),
        'return_value_changed_only': (replace_once(source,
            '  [|result = None /\\ V293_bitmap_ready',
            '  [|result = Some (Vint32 Int.zero) /\\ V293_bitmap_ready'), 'Lemma V293_sched_return_post'),
    }
    for label, (changed, declaration) in mutations.items():
        row, _, _ = compile_tree(label, core=changed)
        failed_at(row, changed, declaration)
        if any(checks[label + ':' + Path(rel).stem]['exit_code'] != 0 for rel in scheduler.FILES):
            raise ValueError('internal negative control prerequisites failed')

    # Both baseline and mutant isolate the same exported root before downstream
    # theorems. Only the mutant gains False; no downstream early rejection is
    # counted as the independent interface test.
    prefix = source[:source.index('Definition V293_OSSchedNew_internal_unit')]
    row, _, _ = compile_tree('contract_isolation_baseline', core=prefix, partial=True, probe=partial_probe)
    if row['exit_code']:
        raise ValueError('isolated baseline must compile')
    start = prefix.index('Theorem V293_OSSchedNew_internal_contract')
    mutant = prefix[:start] + replace_once(prefix[start:],
        '  unmap <> y -> group <> y -> rows <> y -> high <> y ->',
        '  False -> unmap <> y -> group <> y -> rows <> y -> high <> y ->')
    mutant = replace_once(mutant, '    Hu Hg Hr Hh Hcode Hpre Hpost.',
                          '    Hfalse Hu Hg Hr Hh Hcode Hpre Hpost.')
    label = 'contract_false_premise_added_only'
    row, _, _ = compile_tree(label, core=mutant, partial=True, probe=partial_probe)
    if checks[label + ':' + Path(CORE).stem]['exit_code']:
        raise ValueError('isolated vacuous mutant must compile first')
    failed_at(row, partial_probe, 'Definition checked_internal_contract')
    # Isolate just the constructor boundary for the all-False fpre control.
    # Compile the same prefix and selector-only probe on the baseline first.
    selector_prefix = source[:source.index('Lemma V293_single_local_not_shadow')]
    selector_probe = scheduler.PROBE + PRELUDE[:PRELUDE.index('Definition checked_internal_contract')]
    row, _, _ = compile_tree('selector_isolation_baseline', core=selector_prefix, partial=True, probe=selector_probe)
    if row['exit_code']:
        raise ValueError('isolated selector baseline must compile')
    start = selector_prefix.index('Definition V293_sched_fpre')
    body = selector_prefix.index('Proof.', start)
    end = selector_prefix.index('Defined.', body) + len('Defined.')
    mutant = selector_prefix[:body] + 'Proof. intros vl lg tid. exact (@mkfunasrt Afalse I). Defined.' + selector_prefix[end:]
    label = 'pre_assertion_false_only'
    row, _, _ = compile_tree(label, core=mutant, partial=True, probe=selector_probe)
    if checks[label + ':' + Path(CORE).stem]['exit_code']:
        raise ValueError('vacuous selector mutant must compile first')
    failed_at(row, selector_probe, 'Lemma checked_pre_selector')
    return {'scope': SCOPE, 'coverage_credit': False, 'roots': ROOTS,
            'root_assumptions': sorted(assumptions), 'negative_controls': CONTROLS}


def validate(root, checkpoint, checks, loader):
    if checkpoint != {'scope': SCOPE, 'coverage_credit': False, 'roots': ROOTS,
                      'root_assumptions': checkpoint['root_assumptions'], 'negative_controls': CONTROLS}:
        raise ValueError('internal checkpoint scope/roots/controls differ')
    if not set(checkpoint['root_assumptions']) <= loader(root, 'check-memory-trust.py').FRAMEWORK_ALLOWED:
        raise ValueError('unexpected internal root assumptions')
    scheduler = loader(root, 'v293-scheduler-source.py')
    for rel in scheduler.FILES + FILES:
        if checks['internal:positive:' + Path(rel).stem]['exit_code'] != 0:
            raise ValueError('internal positive compilation failed')
    for name in ['positive:contract', 'coqchk', 'contract_isolation_baseline:contract', 'selector_isolation_baseline:contract']:
        if checks['internal:' + name]['exit_code'] != 0:
            raise ValueError('internal positive/isolation check failed')
    for label in CONTROLS:
        for rel in scheduler.FILES:
            if checks['internal:' + label + ':' + Path(rel).stem]['exit_code'] != 0:
                raise ValueError('internal control prerequisite failed')
        expected = 0 if label in {'contract_false_premise_added_only', 'pre_assertion_false_only'} else 1
        if checks['internal:' + label + ':' + Path(CORE).stem]['exit_code'] != expected:
            raise ValueError('internal designated core control missing')
    for label in ['contract_false_premise_added_only', 'pre_assertion_false_only']:
        if checks['internal:' + label + ':contract']['exit_code'] != 1:
            raise ValueError('internal vacuous contract/selector probe control missing')
