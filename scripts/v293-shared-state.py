#!/usr/bin/env python3
"""Nonempty shared pointer/abstract-state core; not physical-kernel invariants."""
from pathlib import Path
import re
import shutil

CORE = 'certiucos/v293/proofs/V293SharedState.v'
WITNESS = 'certiucos/v293/proofs/V293SharedStateWitness.v'
FILES = [CORE, WITNESS]
ROOTS = ['V293_shared_switch_open', 'V293_shared_switch_close',
         'V293_shared_store', 'V293_shared_good', 'V293_shared_store_witness', 'V293_shared_switch_cases_witness']
SCOPE = 'NONEMPTY_SHARED_CORE_GOODI_NOT_PHYSICAL_KERNEL_INVARIANT_OR_SWITCH_OR_GOOD_OS'
OBLIGATIONS = {
    'time_slot_removed_only': (CORE, 'Lemma V293_shared_fields_get'),
    'abstract_current_update_omitted_only': (CORE, 'Lemma V293_shared_store :'),
    'fixture_current_read_only': (WITNESS, 'Lemma V293_shared_fixture_pointer'),
    'goodi_false_premise_added_only': (None, 'Definition checked_shared_good :'),
}
CONTROLS = {
    'time_slot_removed_only': 'REJECTED_AT_V293_shared_fields_get_NOT_DOWNSTREAM_CREDIT',
    'abstract_current_update_omitted_only': 'REJECTED_AT_V293_shared_store',
    'fixture_current_read_only': 'CORE_COMPILES_REJECTED_AT_V293_shared_fixture_pointer',
    'goodi_false_premise_added_only': 'MUTANT_AND_WITNESS_COMPILE_REJECTED_AT_checked_shared_good',
}

# Fixed expected fields, ownership and root types; not generated from candidates.
PROBE = r'''
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293SharedStateWitness.
Require Import Coq.Lists.List.
Definition checked_shared_fields current tasks events now :=
  Aabsdata curtid (oscurt current) **
  (Aabsdata abstcblsid (abstcblist tasks) **
    (Aabsdata absecblsid (absecblist events) ** Aabsdata ostmid (ostm now))).
Definition checked_shared_core := EX current : tid, EX tasks : TcbMod.map,
  EX events : EcbMod.map, EX now : int32,
  CurTid current ** checked_shared_fields current tasks events now.
Definition checked_shared_shape : V293_shared_core = checked_shared_core := eq_refl.
Definition checked_shared_inv_shape : forall k,
  getinv (V293_shared_inv k) = match k with O => checked_shared_core | S _ => Aemp end :=
  fun k => match k with O => eq_refl | S _ => eq_refl end.
Definition checked_shared_li_shape : V293_shared_li = (fun _ _ => Aemp) := eq_refl.
Definition checked_shared_flags := (isrclr ** Aie false) ** (EX k : hid, ATopis k).
Definition checked_shared_open : SWINV V293_shared_inv ==> checked_shared_flags ** checked_shared_core :=
  V293_shared_switch_open.
Definition checked_shared_close : checked_shared_flags ** checked_shared_core ==> SWINV V293_shared_inv :=
  V293_shared_switch_close.
Definition checked_shared_store : forall ct t ge le M M' ir aux O op b tp,
  (ge, le, M, ir, aux, O, op) |= SWINVt V293_shared_inv ct ->
  get ge OSTCBCur = Some (b, Tptr tp) ->
  store (Tptr tp) M (b, 0%Z) (Vptr t) = Some M' ->
  (ge, le, M', ir, aux, set O curtid (oscurt t), op) |= SWINVt V293_shared_inv t :=
  V293_shared_store.
Definition checked_shared_good : GoodI V293_shared_inv V293_scheduler (fun _ _ => Aemp) :=
  V293_shared_good.
Definition checked_shared_witness : forall ct t ts es n,
  exists ge M M' O,
  get ge OSTCBCur = Some (1%positive, Tptr Tvoid) /\
  (ge, emp, M, (fun _ => false), (false, nil, nil), O, spec_done None) |= SWINVt V293_shared_inv ct /\
  store (Tptr Tvoid) M (1%positive, 0%Z) (Vptr t) = Some M' /\
  (ge, emp, M', (fun _ => false), (false, nil, nil), set O curtid (oscurt t), spec_done None) |= SWINVt V293_shared_inv t /\
  get O abstcblsid = Some (abstcblist ts) /\
  get O absecblsid = Some (absecblist es) /\ get O ostmid = Some (ostm n) :=
  V293_shared_store_witness.
Definition checked_shared_case_tasks (live : bool) : TcbMod.map := if live then
  set (sig (7%positive, Int.zero) (Int.repr 4, wait os_stat_time Int.one, Vnull))
    (15%positive, Int.zero) (Int.repr 12, rdy, Vnull)
  else sig (15%positive, Int.zero) (Int.repr 12, rdy, Vnull).
Definition checked_shared_cases : forall live,
  exists ge M M' O,
  get ge OSTCBCur = Some (1%positive, Tptr Tvoid) /\
  (ge, emp, M, (fun _ => false), (false, nil, nil), O, spec_done None) |= SWINVt V293_shared_inv (7%positive, Int.zero) /\
  (ge, emp, M, (fun _ => false), (false, nil, nil), O, spec_done None) |= AHprio V293_scheduler (15%positive, Int.zero) ** Atrue /\
  get O abstcblsid = Some (abstcblist (checked_shared_case_tasks live)) /\
  get (checked_shared_case_tasks live) (7%positive, Int.zero) =
    (if live then Some (Int.repr 4, wait os_stat_time Int.one, Vnull) else None) /\
  store (Tptr Tvoid) M (1%positive, 0%Z) (Vptr (15%positive, Int.zero)) = Some M' /\
  (ge, emp, M', (fun _ => false), (false, nil, nil), set O curtid (oscurt (15%positive, Int.zero)), spec_done None) |=
    SWINVt V293_shared_inv (15%positive, Int.zero) := V293_shared_switch_cases_witness.

'''

def mutations(source, witness, replace):
    time = replace(source, '(Aabsdata absecblsid (absecblist events) ** Aabsdata ostmid (ostm now))',
                   '(Aabsdata absecblsid (absecblist events) ** Aemp)')
    start = source.index('Lemma V293_shared_store :')
    end = source.index('Proof.', start)
    update = source[:start] + replace(source[start:end],
        'aux, set O curtid (oscurt t), op)', 'aux, O, op)') + source[end:]
    readonly = replace(witness, 'Definition V293_shared_fixture_mem t := V293_encoded_memory 1%positive 0 true',
                       'Definition V293_shared_fixture_mem t := V293_encoded_memory 1%positive 0 false')
    false = replace(source, 'Theorem V293_shared_good : GoodI', 'Theorem V293_shared_good : False -> GoodI')
    start = false.index('Theorem V293_shared_good :')
    false = false[:start] + replace(false[start:], 'Proof.\n  split.', 'Proof.\n  intro Hfalse. split.')
    texts = {'time_slot_removed_only': (time, witness),
             'abstract_current_update_omitted_only': (update, witness),
             'fixture_current_read_only': (source, readonly),
             'goodi_false_premise_added_only': (false, witness)}
    return {label: (*pair, *OBLIGATIONS[label]) for label, pair in texts.items()}

def check_rejection(row, source, failed_rel, declaration, label):
    start = source.index(declaration)
    lo = source[:start].count('\n') + 1
    end = (source.index('.', source.index(':=', start)) + 1
           if failed_rel is None else source.index('Qed.', start) + len('Qed.'))
    hi = source[:end].count('\n') + 1
    match = re.search(r'File "([^"\n]+)", line (\d+), characters', row['stderr'])
    expected_file = '/checks/Contract.v' if failed_rel is None else '/' + failed_rel
    if (row['exit_code'] != 1 or not match or not lo <= int(match[2]) <= hi
            or not ('/' + match[1]).endswith(expected_file) or '\nError:' not in row['stderr']):
        raise ValueError('shared control missed designated obligation: ' + label + ': ' + str(row))


def check(root, work, build, coqbin, run, loader, location):
    caller = loader(root, 'v293-scheduler-caller.py')
    probe = PROBE
    checks = {}
    def record(label, command, cwd):
        if label in checks:
            raise ValueError('duplicate shared command identity: ' + label)
        row = run('shared:' + label, command, cwd); checks[label] = row
        return row

    def compile_tree(label, core, witness, assumptions=False):
        dest = work / ('shared_' + label)
        shutil.copytree(build / 'certiucos', dest / 'certiucos')
        (dest / 'checks').mkdir()
        flags = ['-R', str(build / 'framework'), 'CertiOS.framework',
                 '-R', str(build / 'tactics'), 'CertiOS.tactics',
                 '-R', str(dest / 'certiucos'), 'CertiOS.certiucos',
                 '-R', str(dest / 'checks'), 'SharedCheck']
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
        raise ValueError('shared proof/probe failed: ' + str(row))
    trust = loader(root, 'check-memory-trust.py'); assumptions = set()
    for part in row['stdout'].split('Axioms:')[1:]:
        assumptions |= set(trust.check_assumptions(part.split('Closed under the global context')[0], trust.FRAMEWORK_ALLOWED))
    if row['stdout'].count('Axioms:') + row['stdout'].count('Closed under the global context') != len(ROOTS):
        raise ValueError('missing shared root assumption output')
    row = record('coqchk', [coqbin + 'coqchk', '-silent', *flags,
        *['CertiOS.' + Path(f).with_suffix('').as_posix().replace('/', '.') for f in FILES],
        'SharedCheck.Contract'], dest)
    if row['exit_code']:
        raise ValueError('shared coqchk failed: ' + str(row))
    for label, (core, wit, failed_rel, declaration) in variants.items():
        row, _, _ = compile_tree(label, core, wit)
        failed_source = probe if failed_rel is None else (core if failed_rel == CORE else wit)
        check_rejection(row, failed_source, failed_rel, declaration, label)
        for rel in (FILES if failed_rel is None else FILES[:FILES.index(failed_rel)]):
            if checks[label + ':' + Path(rel).stem]['exit_code'] != 0:
                raise ValueError('shared control prerequisite failed')
    return {'scope': SCOPE, 'coverage_credit': False, 'roots': ROOTS, 'source_location': location,
            'root_assumptions': sorted(assumptions), 'negative_controls': CONTROLS}


def validate(root, checkpoint, checks, loader):
    import json
    inventory = json.loads((root / 'audit/repaired-source-inventory.json').read_text())
    expected = {'scope': SCOPE, 'coverage_credit': False, 'roots': ROOTS,
        'source_location': next(f for f in inventory['functions'] if f['name'] == 'OS_Sched'),
        'root_assumptions': checkpoint['root_assumptions'], 'negative_controls': CONTROLS}
    if checkpoint != expected:
        raise ValueError('shared checkpoint scope/roots/source/controls differ')
    if not set(checkpoint['root_assumptions']) <= loader(root, 'check-memory-trust.py').FRAMEWORK_ALLOWED:
        raise ValueError('unexpected shared root assumptions')
    for key in ['positive:' + Path(f).stem for f in FILES] + ['positive:contract', 'coqchk']:
        if checks['shared:' + key]['exit_code'] != 0:
            raise ValueError('shared checkpoint positive check failed')
    for label, (failed_rel, _) in OBLIGATIONS.items():
        fail = 'contract' if failed_rel is None else Path(failed_rel).stem
        prerequisites = FILES if failed_rel is None else FILES[:FILES.index(failed_rel)]
        for rel in prerequisites:
            if checks['shared:' + label + ':' + Path(rel).stem]['exit_code'] != 0:
                raise ValueError('shared control prerequisite missing')
        if checks['shared:' + label + ':' + fail]['exit_code'] != 1:
            raise ValueError('shared designated control missing')
    variants = mutations((root / CORE).read_text(), (root / WITNESS).read_text(),
                         loader(root, 'v293-scheduler-caller.py').replace_once)
    for label, (core, witness, failed_rel, declaration) in variants.items():
        fail = 'contract' if failed_rel is None else Path(failed_rel).stem
        text = PROBE if failed_rel is None else core if failed_rel == CORE else witness
        check_rejection(checks['shared:' + label + ':' + fail], text, failed_rel, declaration, label)
