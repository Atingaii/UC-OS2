#!/usr/bin/env python3
"""Check the repaired representation, negative controls and framework root closure."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
ROOTS = ['blocks_below_monotone', 'blocks_below_empty', 'blocks_below_fresh',
         'bounded_memory_has_fresh_block', 'blocks_below_set', 'blocks_below_set_grow',
         'blocks_below_del', 'blocks_below_allocb', 'blocks_below_allocb_grow',
         'blocks_below_storebytes', 'blocks_below_freeb']
REPRESENTATION_ROOTS = ['erase_empty', 'erase_get', 'erase_set', 'erase_del',
    'erase_merge', 'erase_minus', 'erase_sig', 'erase_join', 'erase_allocb',
    'erase_freeb', 'erase_storebytes', 'memory_inhabited', 'memory_is_bounded',
    'allocation_can_continue', 'saturated_raw_not_bounded', 'saturated_raw_not_representable',
    'concrete_allocation', 'concrete_write', 'concrete_release', 'readonly_write_rejected']
FRAMEWORK_ROOTS = ['memory.memory_has_fresh_block', 'memory.memory_not_full',
    'memory_prop.fresh_exist', 'rulesoundlib.fresh_exist',
    'rulesoundlib.cstep_safe_mono', 'cstepLib.cstep_safe_mono',
    'rulesoundlib.env_domain_eq_imply_alloc_exist', "rulesoundlib.alloc_star_exist'",
    'rulesoundlib.alloc_star_exist', 'step_prop.tstep_alloc_nabt',
    'soundness.RuleSound', 'toptheorem.verified_os\'', 'toptheorem.Soundness']
ALLOWED = {'FunctionalExtensionality.functional_extensionality_dep', 'Classical_Prop.classic'}
# The inspected framework roots also use the standard equality-transport axiom.
# Legacy map axioms are derived instead of added as allowlist exceptions.
FRAMEWORK_ALLOWED = ALLOWED | {'Eqdep.Eq_rect_eq.eq_rect_eq'}
HISTORY = 'audit/memory-trust.json'
HISTORY_SHA256 = '45ba9ca37bc7d3226c2227e3433e4a689712dcd348535effa8c751aea2fad819'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def assumptions(output):
    # Keep unknown Unicode/universe-annotated names too: never silently drop
    # a dependency merely because its spelling is outside an ASCII pattern.
    return set(re.findall(r"^([^\s:]+)\s*(?::|$)", output, re.MULTILINE)) - {'Axioms'}


def check_assumptions(output, allowed):
    actual = assumptions(output)
    if actual - allowed or 'MemoryNotFull' in output:
        raise ValueError(f'unexpected root assumptions: {sorted(actual - allowed)}')
    return sorted(actual)


def inspect(bounds_only=False):
    coqbin = os.environ.get('COQBIN', '')
    executable = lambda name: coqbin + name
    version = subprocess.run([executable('coqc'), '--version'], capture_output=True, text=True, check=True).stdout
    if not re.search(r'^The Coq Proof Assistant, version 8\.18\.0(?: |$)', version, re.MULTILINE):
        raise ValueError('memory trust checks require Coq 8.18.0')
    if sha(ROOT / HISTORY) != HISTORY_SHA256:
        raise ValueError('historical failing evidence changed; do not rewrite it')
    inputs = [p for tree in ['framework', 'tactics', 'certiucos/v293']
              for p in sorted((ROOT / tree).rglob('*.v'))]
    inputs += [ROOT / p for p in ['scripts/check-memory-trust.py', 'Makefile', '_CoqProject', HISTORY]]
    report = {'schema_version': 2, 'scope': 'FRAMEWORK_MEMORY_REPAIR_NOT_KERNEL_PROOF',
        'coq_version': version.strip(), 'checks': {}, 'historical_failure_sha256': HISTORY_SHA256,
        'input_sha256': {str(p.relative_to(ROOT)): sha(p) for p in inputs},
        'kernel_GOOD_OS_proved': False}

    def run(label, command, cwd, timeout=900):
        result = subprocess.run(command, cwd=cwd, capture_output=True, text=True, timeout=timeout)
        row = {'exit_code': result.returncode, 'stdout': result.stdout, 'stderr': result.stderr}
        report['checks'][label] = row
        return row

    def require_pass(row, label):
        if row['exit_code'] != 0:
            raise ValueError(f'{label} failed: {row["stdout"]}{row["stderr"]}')

    def require_rejected(row, label, fragment):
        if row['exit_code'] != 1 or fragment not in row['stderr']:
            raise ValueError(f'{label} did not fail at the preselected type error: {row}')

    # Direct invocation also builds sources, rather than trusting stale .vo files.
    require_pass(run('active_build', ['make', 'build', f'COQBIN={coqbin}', 'JOBS=2'], ROOT, 1800), 'active build')
    with tempfile.TemporaryDirectory(prefix='ucos-memory-repair-') as directory:
        work = Path(directory)
        flags = ['-q', '-R', str(ROOT), 'CertiOS', '-R', str(work), 'MemoryRepair']

        def compile(name, body):
            path = work / (name + '.v'); path.write_text(body)
            return run(name, [executable('coqc'), *flags, str(path)], work)

        prefix = 'Require Import memory memory_bound memory_representation.\n'
        bounded = compile('BoundedAssumptions', prefix + '\n'.join(f'Print Assumptions {r}.' for r in ROOTS))
        require_pass(bounded, 'bounded roots')
        report['bounded_root_assumptions'] = check_assumptions(bounded['stdout'], ALLOWED)
        report['bounded_roots_checked'] = ROOTS
        representation = compile('RepresentationAssumptions', prefix + '\n'.join(
            f'Print Assumptions {r}.' for r in REPRESENTATION_ROOTS))
        require_pass(representation, 'representation refinement roots')
        report['representation_root_assumptions'] = check_assumptions(representation['stdout'], ALLOWED)
        report['representation_roots_checked'] = REPRESENTATION_ROOTS

        # Prospective single-factor faults in the independent legacy oracle.
        # Each must reach its own named refinement proof, not fail earlier.
        source = (ROOT / 'framework/proof/memory_representation.v').read_text()
        faults = [
            # The dead branch keeps v's original inferred type. The mutant
            # still returns None; it must fail at erase_set, not elaboration.
            ('FaultSet', 'then Some v else m x',
             'then (if true then None else Some v) else m x', 'erase_set'),
            ('FaultMergePermission', 'then Some (true,x) else Some v1',
             'then Some (false,x) else Some v1', 'erase_merge'),
            ('FaultReleasePermission', 'Some (true,_), Some m\' => Some (remove m\' (b,i))',
             'Some (false,_), Some m\' => Some (remove m\' (b,i))', 'erase_freeb')]
        for name, old, new, theorem in faults:
            if source.count(old) != 1:
                raise ValueError(f'{name}: mutation target changed')
            mutated = source.replace(old, new)
            row = compile(name, mutated)
            match = re.search(r'line (\d+), characters', row['stderr'])
            start = mutated.index('Theorem ' + theorem + ' :')
            finish = mutated.index('Qed.', start)
            lo, hi = mutated.count('\n', 0, start) + 1, mutated.count('\n', 0, finish) + 1
            if row['exit_code'] != 1 or not match or not lo <= int(match[1]) <= hi:
                raise ValueError(f'{name} did not reach the designated {theorem} rejection: {row}')

        # Actual constructor rejects the old saturated function with a True proof.
        invalid = compile('InvalidTypedMemory', prefix + '''Definition invalid_memory : mem :=
  @HalfPermMap.mkMap occupied_everywhere_raw I.
''')
        require_rejected(invalid, 'saturated constructor', 'raw_bounded')
        # One-factor control: only neutralize the constructor's bound predicate;
        # candidate, data, record shape and proof term remain literally identical.
        control = prefix + '''Module ConstructorControl.
Definition invariant (m : RawMemory.t) : Prop := HalfPermMap.raw_bounded m.
Record t := make { data : RawMemory.t; bounded : invariant data }.
Definition candidate : t := @make occupied_everywhere_raw I.
End ConstructorControl.
'''
        require_rejected(compile('BoundEnforced', control), 'bound-enforced control', 'invariant')
        neutral = control.replace(':= HalfPermMap.raw_bounded m.', ':= True.')
        require_pass(compile('BoundNeutralized', neutral), 'bound-neutralized control')
        # Independent exact known logical path; not imported by any active root.
        baseline = '''Require Import ZArith.
Definition raw := (positive * Z)%type -> option bool.
Definition full (m : raw) := forall b, exists i, m (b,i) = Some true.
Definition saturated : raw := fun _ => Some true.
Lemma saturated_full : full saturated.
Proof. intro b; exists 0%Z; reflexivity. Qed.
Axiom global_not_full : forall m, ~ full m.
Theorem contradiction : False.
Proof. exact (global_not_full saturated saturated_full). Qed.
Print Assumptions contradiction.
'''
        if not bounds_only:
            require_pass(compile('HistoricalLogicalPath', baseline), 'historical logical path')
            removed = baseline.replace('Axiom global_not_full : forall m, ~ full m.\n', '')
            require_rejected(compile('HistoricalPathWithoutAxiom', removed), 'historical axiom removal',
                             'global_not_full was not found')
            import_roots = 'Require Import memory_prop rulesoundlib cstepLib step_prop soundness toptheorem.\n'
            roots = compile('FrameworkAssumptions', import_roots + '\n'.join(
                f'Print Assumptions {r}.' for r in FRAMEWORK_ROOTS))
            require_pass(roots, 'framework root closure')
            report['framework_root_assumptions'] = check_assumptions(roots['stdout'], FRAMEWORK_ALLOWED)
            report['framework_roots_checked'] = FRAMEWORK_ROOTS
        modules = ['MemoryRepair.BoundedAssumptions', 'MemoryRepair.RepresentationAssumptions',
                   'MemoryRepair.BoundNeutralized']
        if not bounds_only:
            modules.append('MemoryRepair.FrameworkAssumptions')
        require_pass(run('coqchk', [executable('coqchk'), '-silent', *flags[1:], *modules], work), 'kernel closure check')
    if any(sha(ROOT / name) != digest for name, digest in report['input_sha256'].items()):
        raise ValueError('inputs changed during checking')
    report['bounded_roots_exclude_MemoryNotFull'] = True
    report['framework_status'] = 'NOT_ASSESSED_BOUNDS_ONLY' if bounds_only else 'PASS_MEMORY_REPAIR_WITH_RECORDED_ASSUMPTIONS'
    report['memory_repair_applied_to_framework_roots'] = not bounds_only
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--bounds-only', action='store_true', help='do not assess the full framework root closure')
    parser.add_argument('--report', type=Path, help='write fresh evidence only; never overwrite')
    args = parser.parse_args()
    try:
        report = inspect(args.bounds_only)
        if args.report:
            with args.report.open('x') as stream:
                json.dump(report, stream, ensure_ascii=False, indent=2); stream.write('\n')
        print('BOUNDED MEMORY INTERFACES: PASS (11 roots)')
        print('REPRESENTATION REFINEMENT: PASS (20 roots; 3 targeted faults; constructor control)')
        print('FRAMEWORK TRUST:', report['framework_status'])
        print('Recorded root assumptions:', ', '.join(report.get('framework_root_assumptions', report['representation_root_assumptions'])))
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        parser.exit(2, f'MEMORY TRUST CHECK ERROR: {error}\n')


if __name__ == '__main__':
    main()
