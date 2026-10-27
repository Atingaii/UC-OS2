#!/usr/bin/env python3
"""Two concrete byte guards and an OPEN continuation, not whole OS_Sched."""
from pathlib import Path
import re
import shutil

CODE = 'certiucos/v293/code/V293OSSchedGuards.v'
CORE = 'certiucos/v293/proofs/V293OSSchedGuards.v'
WITNESS = 'certiucos/v293/proofs/V293OSSchedGuardsWitness.v'
FILES = [CODE, CORE, WITNESS]
ROOTS = ['V293_OSSched_interrupt_skip', 'V293_OSSched_guards_rule',
         'V293_OSSched_guarded_prefix_continuation', 'V293_OSSched_guarded_precondition_witness']
SCOPE = 'SOURCE_BOUND_TWO_GUARDS_WITH_OPEN_SUFFIX_NOT_OS_SCHED_OR_GOOD_OS'
CONTROLS = {
    'guard_result_inverted_only': 'REJECTED_AT_V293_guard_eval',
    'lock_guard_replaced_with_interrupt_only': 'REJECTED_AT_V293_OSSched_guards_rule',
    'enabled_post_ignores_lock_only': 'REJECTED_AT_V293_OSSched_guards_rule',
    'continuation_false_premise_added_only': 'MUTANT_AND_WITNESS_COMPILE_REJECTED_AT_checked_guarded_prefix',
}

EMISSION = '(* The two configured guards of OS_Sched. The continuation is explicit:\n   it still contains the priority comparison, counter and switch obligations.\n   Critical-section entry/exit are not included here. *)\nRequire Import CertiOS.framework.model.memory CertiOS.framework.model.language.\n\nDefinition V293_OSSched_zero (x : var) : expr :=\n  ebinop oeq (ecast (evar x) Tint32) (econst32 (Int.repr 0)).\n\nDefinition V293_OSSched_guards (interrupt lock : var) (body : stmts) : stmts :=\n  sifthen (V293_OSSched_zero interrupt)\n    (sifthen (V293_OSSched_zero lock) body).\n'

PROBE = r'''
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedGuardsWitness.
Definition checked_guard_cell x b n : asrt :=
  (Agvarenv x Tint8 (b, 0%Z) //\\ A_notin_lenv x) **
    Amapsto (b, 0%Z) Tint8 false (V293_byteval n).
Definition checked_interrupt_skip : forall Spec sd li I r ri tid x lock b n rest body,
  n < 256 -> n <> 0 ->
  InfRules Spec sd li I r ri (checked_guard_cell x b n ** rest)
    (sifthen (ebinop oeq (ecast (evar x) Tint32) (econst32 (Int.repr 0)))
      (sifthen (ebinop oeq (ecast (evar lock) Tint32) (econst32 (Int.repr 0))) body))
    (checked_guard_cell x b n ** rest) tid := V293_OSSched_interrupt_skip.
Definition checked_guards : forall Spec sd li I r ri tid p q x lock bi bl ni nl ri_mem rl_mem body,
  ni < 256 -> nl < 256 ->
  (p ==> checked_guard_cell x bi ni ** ri_mem) ->
  (p ==> checked_guard_cell lock bl nl ** rl_mem) ->
  (ni = 0 -> nl = 0 -> InfRules Spec sd li I r ri p body q tid) ->
  InfRules Spec sd li I r ri p
    (sifthen (ebinop oeq (ecast (evar x) Tint32) (econst32 (Int.repr 0)))
      (sifthen (ebinop oeq (ecast (evar lock) Tint32) (econst32 (Int.repr 0))) body))
    (if Nat.eqb ni 0 && Nat.eqb nl 0 then q else p) tid := V293_OSSched_guards_rule.
Definition checked_guarded_prefix : forall Spec sd li I r ri tid aop frame
    sched_id unmap group rows high bt bg br bh lo hi table target tp bp bo entries tasks old
    interrupt lock bi bl ni nl suffix q (Hli : GoodLInvAsrt li),
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  checked_bitmap_tasks lo hi tasks -> checked_priority_table entries tasks -> GoodFrm frame ->
  ni < 256 -> nl < 256 ->
  Spec sched_id = Some
    (V293_sched_fpre unmap group rows high bt bg br bh li Hli,
     V293_sched_fpost unmap group rows high bt bg br bh li Hli, (Tvoid, nil)) ->
  let guardframe := checked_guard_cell interrupt bi ni ** (checked_guard_cell lock bl nl ** frame) in
  let pre := checked_pre unmap group rows high bt bg br bh lo hi li tid aop **
    (checked_prefix_frame table high target tp bp bo entries tasks guardframe ** checked_prefix_output tp bo old) in
  let mid := EX t : Modules.tid, [|checked_highest tasks t|] **
    (checked_post unmap group rows high bt bg br bh lo hi li tid aop None **
      (checked_prefix_frame table high target tp bp bo entries tasks guardframe ** checked_prefix_output tp bo (Vptr t))) in
  (ni = 0 -> nl = 0 -> InfRules Spec sd li I r ri mid suffix q tid) ->
  InfRules Spec sd li I r ri pre
    (sifthen (ebinop oeq (ecast (evar interrupt) Tint32) (econst32 (Int.repr 0)))
      (sifthen (ebinop oeq (ecast (evar lock) Tint32) (econst32 (Int.repr 0)))
        (sseq (sseq (scall sched_id nil) (sassign (evar target) (earrayelem (evar table) (evar high)))) suffix)))
    (if Nat.eqb ni 0 && Nat.eqb nl 0 then q else pre) tid := V293_OSSched_guarded_prefix_continuation.

Definition checked_guarded_witness : forall ni nl,
  ni < 256 -> nl < 256 -> exists s,
  checked_bitmap_tasks 0 16 V293_idle_tasks /\ checked_priority_table V293_idle_entries V293_idle_tasks /\
  s |= checked_pre 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive
    0 16 V293_witness_li V293_idle_tid (spec_done None) **
    (checked_prefix_frame 106%Z 103%Z 107%Z Tvoid 8%positive 10%positive V293_idle_entries V293_idle_tasks
      (checked_guard_cell 108%Z 11%positive ni ** (checked_guard_cell 109%Z 12%positive nl ** Aemp)) **
      checked_prefix_output Tvoid 10%positive Vnull) := V293_OSSched_guarded_precondition_witness.
'''

def mutations(source, replace):
    inverted = replace(source,
        'Some (Vint32 (if Nat.eqb n 0 then Int.one else Int.zero)) /\\',
        'Some (Vint32 (if Nat.eqb n 0 then Int.zero else Int.one)) /\\')
    start = source.index('Theorem V293_OSSched_guards_rule')
    end = source.index('Qed.', start) + len('Qed.')
    before, theorem, after = source[:start], source[start:end], source[end:]
    wrong_lock = replace(theorem, '(V293_OSSched_guards x lock body)', '(V293_OSSched_guards x x body)')
    wrong_post = replace(theorem, 'if Nat.eqb ni 0 && Nat.eqb nl 0 then q else p', 'if Nat.eqb ni 0 then q else p')
    start = source.index('Theorem V293_OSSched_guarded_prefix_continuation')
    prefix, continuation = source[:start], source[start:]
    continuation = replace(continuation, '  lo < 256 -> hi < 256 ->', '  False -> lo < 256 -> hi < 256 ->')
    continuation = replace(continuation, '    Hlo Hhi Hr Hb Htable Hframe Hni Hnl Hspec',
                           '    Hfalse Hlo Hhi Hr Hb Htable Hframe Hni Hnl Hspec')
    return {
        'guard_result_inverted_only': (inverted, 'Lemma V293_guard_eval'),
        'lock_guard_replaced_with_interrupt_only': (before + wrong_lock + after, 'Theorem V293_OSSched_guards_rule'),
        'enabled_post_ignores_lock_only': (before + wrong_post + after, 'Theorem V293_OSSched_guards_rule'),
        'continuation_false_premise_added_only': (prefix + continuation, 'Definition checked_guarded_prefix :'),
    }

def unit_label(rel):
    # The code and proof intentionally have the same basename. Keep their
    # command identities distinct so a success cannot overwrite a failure.
    return ('code:' if rel == CODE else '') + Path(rel).stem


def check(root, work, build, coqbin, run, loader, location):
    if (root / CODE).read_text() != EMISSION:
        raise ValueError('guard Coq emission differs from checked configured guard AST')
    caller = loader(root, 'v293-scheduler-caller.py')
    probe = (loader(root, 'v293-scheduler-source.py').PROBE +
             loader(root, 'v293-scheduler-internal.py').PRELUDE + caller.PROBE +
             loader(root, 'v293-scheduler-prefix.py').PROBE + PROBE)
    checks = {}
    def record(label, command, cwd):
        if label in checks:
            raise ValueError('duplicate guard command identity: ' + label)
        row = run('guards:' + label, command, cwd); checks[label] = row
        return row

    def compile_tree(label, replacement=None, assumptions=False):
        dest = work / ('guards_' + label)
        # Dependencies only from this run's empty-directory full build.
        shutil.copytree(build / 'certiucos', dest / 'certiucos')
        (dest / 'checks').mkdir()
        flags = ['-R', str(build / 'framework'), 'CertiOS.framework',
                 '-R', str(build / 'tactics'), 'CertiOS.tactics',
                 '-R', str(dest / 'certiucos'), 'CertiOS.certiucos',
                 '-R', str(dest / 'checks'), 'GuardsCheck']
        for rel in FILES:
            path = dest / rel
            for suffix in ['.vo', '.vos', '.vok', '.glob']:
                path.with_suffix(suffix).unlink(missing_ok=True)
            path.write_text(replacement if rel == CORE and replacement is not None else (root / rel).read_text())
            row = record(label + ':' + unit_label(rel), [coqbin + 'coqc', '-q', *flags, str(path)], dest)
            if row['exit_code']:
                return row, flags, dest
        path = dest / 'checks/Contract.v'
        path.write_text(probe + ('\n' + '\n'.join('Print Assumptions ' + r + '.' for r in ROOTS) if assumptions else ''))
        row = record(label + ':contract', [coqbin + 'coqc', '-q', *flags, str(path)], dest)
        return row, flags, dest

    row, flags, dest = compile_tree('positive', assumptions=True)
    if row['exit_code']:
        raise ValueError('guards proof/probe failed: ' + str(row))
    trust = loader(root, 'check-memory-trust.py'); assumptions = set()
    for part in row['stdout'].split('Axioms:')[1:]:
        assumptions |= set(trust.check_assumptions(part.split('Closed under the global context')[0], trust.FRAMEWORK_ALLOWED))
    if row['stdout'].count('Axioms:') + row['stdout'].count('Closed under the global context') != len(ROOTS):
        raise ValueError('missing guards root assumption output')
    row = record('coqchk', [coqbin + 'coqchk', '-silent', *flags,
        *['CertiOS.' + Path(f).with_suffix('').as_posix().replace('/', '.') for f in FILES],
        'GuardsCheck.Contract'], dest)
    if row['exit_code']:
        raise ValueError('guards coqchk failed: ' + str(row))
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
            raise ValueError('guards control missed designated obligation: ' + label + ': ' + str(row))
        if checks[label + ':' + unit_label(CODE)]['exit_code'] != 0:
            raise ValueError('guards control code prerequisite failed')
        if is_probe and any(checks[label + ':' + unit_label(f)]['exit_code'] != 0 for f in FILES):
            raise ValueError('guards vacuity control prerequisite failed')
    return {'scope': SCOPE, 'coverage_credit': False, 'roots': ROOTS, 'source_location': location,
            'root_assumptions': sorted(assumptions), 'negative_controls': CONTROLS}


def validate(root, checkpoint, checks, loader):
    import json
    inventory = json.loads((root / 'audit/repaired-source-inventory.json').read_text())
    expected = {'scope': SCOPE, 'coverage_credit': False, 'roots': ROOTS,
        'source_location': next(f for f in inventory['functions'] if f['name'] == 'OS_Sched'),
        'root_assumptions': checkpoint['root_assumptions'], 'negative_controls': CONTROLS}
    if checkpoint != expected:
        raise ValueError('guards checkpoint scope/roots/source/controls differ')
    if not set(checkpoint['root_assumptions']) <= loader(root, 'check-memory-trust.py').FRAMEWORK_ALLOWED:
        raise ValueError('unexpected guards root assumptions')
    for key in ['positive:' + unit_label(f) for f in FILES] + ['positive:contract', 'coqchk']:
        if checks['guards:' + key]['exit_code'] != 0:
            raise ValueError('guards checkpoint positive check failed')
    for label in CONTROLS:
        if checks['guards:' + label + ':' + unit_label(CODE)]['exit_code'] != 0:
            raise ValueError('guards control code prerequisite missing')
        is_probe = label == 'continuation_false_premise_added_only'
        if is_probe and any(checks['guards:' + label + ':' + unit_label(f)]['exit_code'] != 0 for f in FILES):
            raise ValueError('guards control prerequisite missing')
        key = label + (':contract' if is_probe else ':' + Path(CORE).stem)
        if checks['guards:' + key]['exit_code'] != 1:
            raise ValueError('guards designated control missing')
