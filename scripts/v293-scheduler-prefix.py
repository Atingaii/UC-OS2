#!/usr/bin/env python3
"""Check actual call/assignment composition, not the OS_Sched wrapper."""
from pathlib import Path
import re
import shutil

CORE = 'certiucos/v293/proofs/V293OSSchedPrefix.v'
WITNESS = 'certiucos/v293/proofs/V293OSSchedPrefixWitness.v'
FILES = [CORE, WITNESS]
ROOTS = ['V293_OSSched_target_assign', 'V293_OSSched_unlocked_prefix_hoare',
         'V293_OSSched_prefix_precondition_witness']
SCOPE = 'SOURCE_BOUND_TWO_STATEMENT_HOARE_NOT_OS_SCHED_OR_GOOD_OS'
CONTROLS = {
    'selected_load_changed_only': 'REJECTED_AT_V293_prefix_selected_load',
    'output_write_permission_removed_only': 'REJECTED_AT_V293_OSSched_target_assign',
    'statement_order_reversed_only': 'REJECTED_AT_V293_OSSched_unlocked_prefix_hoare',
    'prefix_false_premise_added_only': 'MUTANT_AND_WITNESS_COMPILE_REJECTED_AT_checked_prefix',
}

# Fixed expected types. These are not read or synthesized from the theorem
# under test. Earlier checked_pre/post and pointer/task relations are also
# independently specified by the retained probes.
PROBE = r'''
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefixWitness.
Definition checked_prefix_bindings table high target tp bp bo : asrt :=
  Agvarenv table (Tarray (Tptr tp) 13) (bp, 0%Z) //\\
  Agvarenv target (Tptr tp) (bo, 0%Z) //\\
  A_notin_lenv table //\\ A_notin_lenv high //\\ A_notin_lenv target.
Definition checked_prefix_frame table high target tp bp bo entries tasks frame :=
  (checked_prefix_bindings table high target tp bp bo **
    (checked_pointers tp bp 0 entries ** Aabsdata abstcblsid (abstcblist tasks))) ** frame.
Definition checked_prefix_output tp bo v := Amapsto (bo, 0%Z) (Tptr tp) true v.

Definition checked_assignment : forall Spec sd li I r ri tid aop frame
    unmap group rows high bt bg br bh lo hi table target tp bp bo entries tasks old t,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  checked_bitmap_tasks lo hi tasks -> checked_priority_table entries tasks ->
  nth (V293_ready_select lo hi (V293_ready_group lo hi)) entries Vnull = Vptr t ->
  InfRules Spec sd li I r ri
    (checked_post unmap group rows high bt bg br bh lo hi li tid aop None **
      (checked_prefix_frame table high target tp bp bo entries tasks frame ** checked_prefix_output tp bo old))
    (sassign (evar target) (earrayelem (evar table) (evar high)))
    (checked_post unmap group rows high bt bg br bh lo hi li tid aop None **
      (checked_prefix_frame table high target tp bp bo entries tasks frame ** checked_prefix_output tp bo (Vptr t))) tid
  := V293_OSSched_target_assign.

Definition checked_prefix : forall Spec sd li I r ri tid aop frame
    sched_id unmap group rows high bt bg br bh lo hi table target tp bp bo entries tasks old
    (Hli : GoodLInvAsrt li),
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  checked_bitmap_tasks lo hi tasks -> checked_priority_table entries tasks -> GoodFrm frame ->
  Spec sched_id = Some
    (V293_sched_fpre unmap group rows high bt bg br bh li Hli,
     V293_sched_fpost unmap group rows high bt bg br bh li Hli, (Tvoid, nil)) ->
  InfRules Spec sd li I r ri
    (checked_pre unmap group rows high bt bg br bh lo hi li tid aop **
      (checked_prefix_frame table high target tp bp bo entries tasks frame ** checked_prefix_output tp bo old))
    (sseq (scall sched_id nil) (sassign (evar target) (earrayelem (evar table) (evar high))))
    (EX t : Modules.tid, [|checked_highest tasks t|] **
      (checked_post unmap group rows high bt bg br bh lo hi li tid aop None **
        (checked_prefix_frame table high target tp bp bo entries tasks frame ** checked_prefix_output tp bo (Vptr t)))) tid
  := V293_OSSched_unlocked_prefix_hoare.

Definition checked_prefix_witness : exists s,
  checked_bitmap_tasks 0 16 V293_idle_tasks /\ checked_priority_table V293_idle_entries V293_idle_tasks /\
  s |= checked_pre 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive
    0 16 V293_witness_li V293_idle_tid (spec_done None) **
    (checked_prefix_frame 106%Z 103%Z 107%Z Tvoid 8%positive 10%positive V293_idle_entries V293_idle_tasks Aemp **
      checked_prefix_output Tvoid 10%positive Vnull) := V293_OSSched_prefix_precondition_witness.
'''


def mutations(source, replace):
    load = 'Some (V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi))).'
    # The precondition, memory ownership, old modules and proofs stay fixed.
    changed_load = replace(source, load,
        'Some (V293_byteval (S (V293_ready_select lo hi (V293_ready_group lo hi)))).')
    readonly = replace(source,
        'Definition V293_prefix_output tp bo v := Amapsto (bo, 0%Z) (Tptr tp) true v.',
        'Definition V293_prefix_output tp bo v := Amapsto (bo, 0%Z) (Tptr tp) false v.')
    reversed_order = replace(source, '(V293_OSSched_unlocked_prefix sched_id table high target)\n',
        '(sseq (V293_OSSched_target_update table high target) (scall sched_id nil))\n')
    start = source.index('Theorem V293_OSSched_unlocked_prefix_hoare')
    before, theorem = source[:start], source[start:]
    theorem = replace(theorem, '  lo < 256 -> hi < 256 ->', '  False -> lo < 256 -> hi < 256 ->')
    theorem = replace(theorem, 'old Hli Hlo Hhi Hr Hb Htable Hframe Hspec.',
                      'old Hli Hfalse Hlo Hhi Hr Hb Htable Hframe Hspec.')
    return {
        'selected_load_changed_only': (changed_load, 'Lemma V293_prefix_selected_load'),
        'output_write_permission_removed_only': (readonly, 'Theorem V293_OSSched_target_assign'),
        'statement_order_reversed_only': (reversed_order, 'Theorem V293_OSSched_unlocked_prefix_hoare'),
        'prefix_false_premise_added_only': (before + theorem, 'Definition checked_prefix :'),
    }


def check(root, work, build, coqbin, run, loader, location):
    caller = loader(root, 'v293-scheduler-caller.py')
    probe = (loader(root, 'v293-scheduler-source.py').PROBE +
             loader(root, 'v293-scheduler-internal.py').PRELUDE + caller.PROBE + PROBE)
    checks = {}
    def record(label, command, cwd):
        row = run('prefix:' + label, command, cwd); checks[label] = row
        return row

    def compile_tree(label, replacement=None, assumptions=False):
        dest = work / ('prefix_' + label)
        # Dependencies only from this run's empty-directory full build.
        shutil.copytree(build / 'certiucos', dest / 'certiucos')
        (dest / 'checks').mkdir()
        flags = ['-R', str(build / 'framework'), 'CertiOS.framework',
                 '-R', str(build / 'tactics'), 'CertiOS.tactics',
                 '-R', str(dest / 'certiucos'), 'CertiOS.certiucos',
                 '-R', str(dest / 'checks'), 'PrefixCheck']
        for rel in FILES:
            path = dest / rel
            for suffix in ['.vo', '.vos', '.vok', '.glob']:
                path.with_suffix(suffix).unlink(missing_ok=True)
            path.write_text(replacement if rel == CORE and replacement is not None else (root / rel).read_text())
            row = record(label + ':' + Path(rel).stem, [coqbin + 'coqc', '-q', *flags, str(path)], dest)
            if row['exit_code']:
                return row, flags, dest
        path = dest / 'checks/Contract.v'
        path.write_text(probe + ('\n' + '\n'.join('Print Assumptions ' + r + '.' for r in ROOTS) if assumptions else ''))
        row = record(label + ':contract', [coqbin + 'coqc', '-q', *flags, str(path)], dest)
        return row, flags, dest

    row, flags, dest = compile_tree('positive', assumptions=True)
    if row['exit_code']:
        raise ValueError('prefix proof/probe failed: ' + str(row))
    trust = loader(root, 'check-memory-trust.py'); assumptions = set()
    for part in row['stdout'].split('Axioms:')[1:]:
        assumptions |= set(trust.check_assumptions(part.split('Closed under the global context')[0], trust.FRAMEWORK_ALLOWED))
    if row['stdout'].count('Axioms:') + row['stdout'].count('Closed under the global context') != len(ROOTS):
        raise ValueError('missing prefix root assumption output')
    row = record('coqchk', [coqbin + 'coqchk', '-silent', *flags,
        *['CertiOS.' + Path(f).with_suffix('').as_posix().replace('/', '.') for f in FILES],
        'PrefixCheck.Contract'], dest)
    if row['exit_code']:
        raise ValueError('prefix coqchk failed: ' + str(row))
    for label, (mutant, declaration) in mutations((root / CORE).read_text(), caller.replace_once).items():
        row, _, _ = compile_tree(label, mutant)
        is_probe = declaration.startswith('Definition ')
        failed_source = probe if is_probe else mutant
        start = failed_source.index(declaration)
        lo = failed_source[:start].count('\n') + 1
        end = failed_source.index('\nDefinition ', start + len(declaration)) if is_probe else failed_source.index('Qed.', start)
        hi = failed_source[:end].count('\n') + 1
        match = re.search(r'line (\d+), characters', row['stderr'])
        expected_file = '/checks/Contract.v' if is_probe else '/' + CORE
        if (row['exit_code'] != 1 or not match or not lo <= int(match[1]) <= hi
                or expected_file not in row['stderr']):
            raise ValueError('prefix control missed designated obligation: ' + label + ': ' + str(row))
        if is_probe and any(checks[label + ':' + Path(f).stem]['exit_code'] != 0 for f in FILES):
            raise ValueError('prefix vacuity control prerequisite failed')
    return {'scope': SCOPE, 'coverage_credit': False, 'roots': ROOTS, 'source_location': location,
            'root_assumptions': sorted(assumptions), 'negative_controls': CONTROLS}


def validate(root, checkpoint, checks, loader):
    import json
    inventory = json.loads((root / 'audit/repaired-source-inventory.json').read_text())
    expected = {'scope': SCOPE, 'coverage_credit': False, 'roots': ROOTS,
        'source_location': next(f for f in inventory['functions'] if f['name'] == 'OS_Sched'),
        'root_assumptions': checkpoint['root_assumptions'], 'negative_controls': CONTROLS}
    if checkpoint != expected:
        raise ValueError('prefix checkpoint scope/roots/source/controls differ')
    if not set(checkpoint['root_assumptions']) <= loader(root, 'check-memory-trust.py').FRAMEWORK_ALLOWED:
        raise ValueError('unexpected prefix root assumptions')
    for key in ['positive:' + Path(f).stem for f in FILES] + ['positive:contract', 'coqchk']:
        if checks['prefix:' + key]['exit_code'] != 0:
            raise ValueError('prefix checkpoint positive check failed')
    for label in CONTROLS:
        is_probe = label == 'prefix_false_premise_added_only'
        if is_probe and any(checks['prefix:' + label + ':' + Path(f).stem]['exit_code'] != 0 for f in FILES):
            raise ValueError('prefix control prerequisite missing')
        key = label + (':contract' if is_probe else ':' + Path(CORE).stem)
        if checks['prefix:' + key]['exit_code'] != 1:
            raise ValueError('prefix designated control missing')
