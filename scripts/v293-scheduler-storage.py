#!/usr/bin/env python3
"""Shared physical storage at the real increment/switch tail, not full OS_Sched.

Literal contracts bind the footprint and actions; no candidate type printing is
used to manufacture the expected interface. The extra-cell fixture is empty.
"""
from pathlib import Path
import re
import shutil

STATE = 'certiucos/v293/proofs/V293DispatchStorage.v'
CORE = 'certiucos/v293/proofs/V293OSSchedStorageTail.v'
WITNESS = 'certiucos/v293/proofs/V293OSSchedStorageWitness.v'
FILES = [STATE, CORE, WITNESS]
ROOTS = ['V293_storage_switch_open', 'V293_storage_invariant_good',
         'V293_storage_tail_return', 'V293_storage_tail_increment',
         'V293_storage_increment_switch', 'V293_storage_increment_entry_witness']
SCOPE = 'SHARED_TYPED_STORAGE_INCREMENT_AND_NORMAL_SWITCH_TAIL_NOT_FULL_OS_SCHED_OR_GOOD_OS'
OBLIGATIONS = {
    'storage_omitted_only': (CORE, 'Lemma V293_storage_return :'),
    'increment_omitted_only': (CORE, 'Theorem V293_storage_tail_increment :'),
    'frozen_counter_post_only': (CORE, 'Theorem V293_storage_increment_switch :'),
    'extra_false_only': (None, 'Definition checked_V293_storage_increment_switch :'),
}
CONTROLS = {name: ('ALL_THREE_SOURCES_COMPILE_FIXED_INTERFACE_REJECTS_EXTRA_PREMISE'
    if name == 'extra_false_only' else 'REJECTED_AT_' + decl.split()[1] + '_NOT_DOWNSTREAM_CREDIT')
    for name, (_, decl) in OBLIGATIONS.items()}

PROBE = r'''
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStorageTail.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStorageWitness.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitch.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitchWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrentWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import Coq.Lists.List.
Local Open Scope nat_scope.
Fixpoint checked_storage (cells : list (addr * type)) : asrt :=
  match cells with
  | nil => Aemp
  | (a, tau) :: rest =>
      (EX v : val, [|rule_type_val_match tau v = true|] ** Amapsto a tau true v) ** checked_storage rest
  end.
Definition checked_fields (t : tid) (ts : TcbMod.map) (es : EcbMod.map) (n : int32) :=
  Aabsdata curtid (oscurt t) ** (Aabsdata abstcblsid (abstcblist ts) **
    (Aabsdata absecblsid (absecblist es) ** Aabsdata ostmid (ostm n))).
Definition checked_flags := (isrclr ** Aie false) ** (EX k : hid, ATopis k).
Definition checked_target target tp := EX v : val,
  [|rule_type_val_match (Tptr tp) v = true|] ** (GV target @ (Tptr tp) |-> v).
Definition checked_shared_core := EX t : tid, EX ts : TcbMod.map, EX es : EcbMod.map, EX n : int32,
  CurTid t ** checked_fields t ts es n.
Definition checked_V293_storage_switch_open : forall cells target tp,
  SWINV (V293_storage_inv cells target tp) ==>
  checked_flags ** (checked_shared_core ** (checked_target target tp ** checked_storage cells)).
Proof.
  intros cells target tp s Hs. apply V293_storage_switch_open in Hs.
  assert (E : V293_storage cells = checked_storage cells).
  { clear Hs. induction cells as [ | [a tau] rest IH]; simpl; [reflexivity | rewrite IH; reflexivity]. }
  unfold V293_storage_core in Hs. rewrite E in Hs. exact Hs.
Qed.
Definition checked_V293_storage_invariant_good : forall cells target tp,
  GoodI (V293_storage_inv cells target tp) V293_scheduler V293_shared_li :=
  V293_storage_invariant_good.
Section FixedTail.
Variables target counter : var.
Variable tp : type.
Variable bcounter : block.
Variable rest : list (addr * type).
Variable tid : Modules.tid.
Variable tasks : TcbMod.map.
Variable events : EcbMod.map.
Variable now : int32.
Variable next : Modules.tid.
Variable aop : spec_code.
Variable stack : list hid.
Variable critical : list bool.
Variable px : asrt.
Let cells := ((bcounter, 0%Z), Tint32) :: rest.
Let open_core := checked_flags ** ((CurTid tid ** checked_fields tid tasks events now) **
  (GV target @ (Tptr tp) |-> (Vptr next))).
Let payload c := <||sched;;aop||> ** ((open_core ** CurTid tid) **
  ((Ais stack ** Acs critical) **
    (PV (bcounter, Int.zero) @ Tint32 |-> (Vint32 c) ** checked_storage rest))).
Let binding := Agvarenv counter Tint32 (bcounter, 0%Z) //\\ A_notin_lenv counter.
Let tail c := payload c ** (binding ** px).
Let resumed := <||aop||> ** SWINVt (V293_storage_inv cells target tp) tid ** Ais stack ** Acs critical **
  (binding ** px).
Lemma checked_storage_equal : V293_storage rest = checked_storage rest.
Proof. induction rest as [ | [a tau] rs IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.
Definition checked_V293_storage_tail_return : forall c,
  payload c ==>
  <||sched;;aop||> ** SWINVt (V293_storage_inv cells target tp) tid ** Ais stack ** Acs critical.
Proof. unfold payload. rewrite <- checked_storage_equal. apply V293_storage_tail_return. Qed.
Definition checked_V293_storage_tail_increment : forall Spec r ri c,
  (px ==> LINV V293_shared_li tid nil ** Atrue) ->
  InfRules Spec V293_scheduler V293_shared_li (V293_storage_inv cells target tp) r ri
    (tail c) (V293_OSSched_increment counter) (tail (Int.add c Int.one)) tid.
Proof. unfold tail, payload. rewrite <- checked_storage_equal. apply V293_storage_tail_increment. Qed.
Definition checked_V293_storage_increment_switch : forall Spec r ri c,
  indom tasks tid -> V293_highest_ready tasks next -> GoodFrm px ->
  (px ==> LINV V293_shared_li tid nil ** Atrue) ->
  InfRules Spec V293_scheduler V293_shared_li (V293_storage_inv cells target tp) r ri
    (tail c) (sseq (V293_OSSched_increment counter) (sprim (switch target))) resumed tid.
Proof. unfold tail, payload. rewrite <- checked_storage_equal. apply V293_storage_increment_switch. Qed.
End FixedTail.
Definition checked_V293_storage_increment_entry_witness : forall different c events now aop,
  exists s,
    indom (V293_current_mode_tasks different) V293_idle_tid /\
    V293_highest_ready (V293_current_mode_tasks different) (V293_switch_target different) /\
    s |=
      (<||sched;;aop||> **
        (((checked_flags ** ((CurTid V293_idle_tid **
          checked_fields V293_idle_tid (V293_current_mode_tasks different) events now) **
          (GV 107%Z @ (Tptr Tvoid) |-> (Vptr (V293_switch_target different))))) ** CurTid V293_idle_tid) **
        ((Ais nil ** Acs nil) ** (PV (3%positive, Int.zero) @ Tint32 |-> (Vint32 c) ** Aemp)))) **
        ((Agvarenv 111%Z Tint32 (3%positive, 0%Z) //\\ A_notin_lenv 111%Z) ** Aemp) :=
  V293_storage_increment_entry_witness.
'''


def mutations(state, core, witness, replace):
    start = core.index('Lemma V293_storage_return :')
    end = core.index('Qed.', start) + 4
    omitted = core[:start] + replace(core[start:end], 'V293_storage_inv cells target tp',
                                    'V293_storage_inv nil target tp') + core[end:]
    start = core.index('Theorem V293_storage_tail_increment :')
    end = core.index('Qed.', start) + 4
    increment = core[:start] + replace(core[start:end], '(V293_OSSched_increment counter)', '(sskip None)') + core[end:]
    start = core.index('Theorem V293_storage_increment_switch :')
    pre, main = core[:start], core[start:]
    frozen = pre + replace(main, '    V293_storage_resumed tid.',
        '    (V293_storage_resumed ** PV (bcounter, Int.zero) @ Tint32 |-> (Vint32 (Int.add c Int.one))) tid.')
    false = pre + replace(replace(main, '  indom tasks tid ->', '  False -> indom tasks tid ->'),
                          'intros Spec r ri c Hmem', 'intros Spec r ri c Hfalse Hmem')
    return {name: (state, source, witness, *OBLIGATIONS[name]) for name, source in {
        'storage_omitted_only': omitted, 'increment_omitted_only': increment,
        'frozen_counter_post_only': frozen, 'extra_false_only': false}.items()}


def check_rejection(row, source, rel, declaration, label):
    start = source.index(declaration)
    lo = source[:start].count('\n') + 1
    hi = source[:source.index('Qed.', start) + 4].count('\n') + 1
    match = re.search(r'File "([^"\n]+)", line (\d+), characters', row['stderr'])
    expected = '/checks/Contract.v' if rel is None else '/' + rel
    if (row['exit_code'] != 1 or not match or not lo <= int(match[2]) <= hi
            or not ('/' + match[1]).endswith(expected) or '\nError:' not in row['stderr']):
        raise ValueError('storage control missed designated obligation: ' + label + ': ' + str(row))



def checked_assumptions(stdout, trust):
    assumptions = set()
    for part in stdout.split('Axioms:')[1:]:
        assumptions |= set(trust.check_assumptions(part.split('Closed under the global context')[0], trust.FRAMEWORK_ALLOWED))
    if stdout.count('Axioms:') + stdout.count('Closed under the global context') != len(ROOTS):
        raise ValueError('missing scheduler-storage root assumption output')
    return sorted(assumptions)


def check(root, work, build, coqbin, run, loader, location):
    probe = PROBE
    checks = {}

    def record(label, command, cwd):
        if label in checks:
            raise ValueError('duplicate scheduler-storage command identity: ' + label)
        row = run('scheduler_storage:' + label, command, cwd)
        checks[label] = row
        return row

    def compile_tree(label, state, core, witness, assumptions=False):
        dest = work / ('scheduler_storage_' + label)
        shutil.copytree(build / 'certiucos', dest / 'certiucos')
        (dest / 'checks').mkdir()
        flags = ['-R', str(build / 'framework'), 'CertiOS.framework',
                 '-R', str(build / 'tactics'), 'CertiOS.tactics',
                 '-R', str(dest / 'certiucos'), 'CertiOS.certiucos',
                 '-R', str(dest / 'checks'), 'SchedulerStorageCheck']
        for rel, contents in zip(FILES, [state, core, witness]):
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

    state = (root / STATE).read_text()
    core = (root / CORE).read_text()
    witness = (root / WITNESS).read_text()
    variants = mutations(state, core, witness, loader(root, 'v293-scheduler-caller.py').replace_once)
    row, flags, dest = compile_tree('positive', state, core, witness, assumptions=True)
    if row['exit_code']:
        raise ValueError('scheduler-storage proof/probe failed: ' + str(row))
    trust = loader(root, 'check-memory-trust.py')
    assumptions = checked_assumptions(row['stdout'], trust)
    row = record('coqchk', [coqbin + 'coqchk', '-silent', *flags,
        *['CertiOS.' + Path(f).with_suffix('').as_posix().replace('/', '.') for f in FILES],
        'SchedulerStorageCheck.Contract'], dest)
    if row['exit_code']:
        raise ValueError('scheduler-storage coqchk failed: ' + str(row))
    for label, (st, source, wit, rel, declaration) in variants.items():
        row, _, _ = compile_tree(label, st, source, wit)
        check_rejection(row, probe if rel is None else source if rel == CORE else st if rel == STATE else wit, rel, declaration, label)
        for previous in (FILES if rel is None else FILES[:FILES.index(rel)]):
            if checks[label + ':' + Path(previous).stem]['exit_code'] != 0:
                raise ValueError('scheduler-storage control prerequisite failed')
    return {'scope': SCOPE, 'coverage_credit': False, 'roots': ROOTS, 'source_location': location,
            'root_assumptions': sorted(assumptions), 'negative_controls': CONTROLS}


def validate(root, checkpoint, checks, loader):
    import json
    inventory = json.loads((root / 'audit/repaired-source-inventory.json').read_text())
    expected = {'scope': SCOPE, 'coverage_credit': False, 'roots': ROOTS,
        'source_location': next(f for f in inventory['functions'] if f['name'] == 'OS_Sched'),
        'root_assumptions': checkpoint['root_assumptions'], 'negative_controls': CONTROLS}
    if checkpoint != expected:
        raise ValueError('scheduler-storage checkpoint scope/roots/source/controls differ')
    if not set(checkpoint['root_assumptions']) <= loader(root, 'check-memory-trust.py').FRAMEWORK_ALLOWED:
        raise ValueError('unexpected scheduler-storage root assumptions')
    actual = checked_assumptions(checks['scheduler_storage:positive:contract']['stdout'],
                                 loader(root, 'check-memory-trust.py'))
    if checkpoint['root_assumptions'] != actual:
        raise ValueError('scheduler-storage assumption metadata differs from root output')
    for key in ['positive:' + Path(f).stem for f in FILES] + ['positive:contract', 'coqchk']:
        if checks['scheduler_storage:' + key]['exit_code'] != 0:
            raise ValueError('scheduler-storage checkpoint positive check failed')
    probe = PROBE
    variants = mutations((root / STATE).read_text(), (root / CORE).read_text(), (root / WITNESS).read_text(),
                         loader(root, 'v293-scheduler-caller.py').replace_once)
    for label, (st, source, wit, rel, declaration) in variants.items():
        prerequisites = FILES if rel is None else FILES[:FILES.index(rel)]
        for previous in prerequisites:
            if checks['scheduler_storage:' + label + ':' + Path(previous).stem]['exit_code'] != 0:
                raise ValueError('scheduler-storage control prerequisite missing')
        fail = 'contract' if rel is None else Path(rel).stem
        row = checks['scheduler_storage:' + label + ':' + fail]
        if row['exit_code'] != 1:
            raise ValueError('scheduler-storage designated control missing')
        check_rejection(row, probe if rel is None else source if rel == CORE else st if rel == STATE else wit, rel, declaration, label)
