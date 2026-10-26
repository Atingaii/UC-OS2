#!/usr/bin/env python3
"""Check bounded allocation lemmas; reject the existing inconsistent global axiom."""
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
AXIOM = 'Axiom MemoryNotFull : forall m, ~FullMemory m.'
ALLOWED = {'FunctionalExtensionality.functional_extensionality_dep', 'Classical_Prop.classic'}
WITNESS = '''Definition occupied_everywhere : mem := fun _ => Some (true, Undef).
Lemma occupied_everywhere_full : FullMemory occupied_everywhere.
Proof.
  unfold FullMemory; intro b; exists 0%Z.
  unfold indom; exists (true, Undef); reflexivity.
Qed.
Print Assumptions occupied_everywhere_full.
'''
CONTRADICTION = '''Theorem memory_inconsistent : False.
Proof. exact (@MemoryNotFull occupied_everywhere occupied_everywhere_full). Qed.
Print Assumptions memory_inconsistent.
'''


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def assumptions(output):
    # coqc output of Print Assumptions: qualified names begin in column zero.
    return set(re.findall(r'^([A-Za-z_][\w.]*)\s*(?::|$)', output, re.MULTILINE)) - {'Axioms'}


def inspect(bounds_only=False):
    coqbin = os.environ.get('COQBIN', '')
    executable = lambda name: coqbin + name
    version = subprocess.run([executable('coqc'), '--version'], capture_output=True, text=True, check=True).stdout
    if not re.search(r'^The Coq Proof Assistant, version 8\.18\.0(?: |$)', version, re.MULTILINE):
        raise ValueError('memory trust checks require Coq 8.18.0')
    report = {'schema_version': 1, 'scope': 'MEMORY_TRUST_DIAGNOSTIC_NOT_KERNEL_PROOF',
              'coq_version': version.strip(), 'checks': {},
              'input_sha256': {p: sha(ROOT / p) for p in ['scripts/check-memory-trust.py',
                  'framework/model/memory.v', 'framework/proof/memory_bound.v',
                  'framework/auxlibs/Maps.v']}}
    with tempfile.TemporaryDirectory(prefix='ucos-memory-trust-') as directory:
        work = Path(directory)
        flags = ['-q', '-R', str(ROOT), 'CertiOS', '-R', str(work), 'MemoryTrust']

        def compile(name, text):
            path = work / (name + '.v')
            path.write_text(text)
            result = subprocess.run([executable('coqc'), *flags, str(path)], cwd=work,
                                    capture_output=True, text=True, timeout=180)
            row = {'exit_code': result.returncode, 'stdout': result.stdout, 'stderr': result.stderr}
            report['checks'][name] = row
            return row

        def require_pass(row, label):
            if row['exit_code'] != 0:
                raise ValueError(f'{label} failed: {row["stdout"]}{row["stderr"]}')

        require_pass(compile('BoundedMemory', (ROOT / 'framework/proof/memory_bound.v').read_text()), 'bounded module')
        text = 'From MemoryTrust Require Import BoundedMemory.\nRequire Import memory.\n'
        text += '\n'.join(f'Print Assumptions {name}.' for name in ROOTS) + '\n'
        bounded = compile('BoundedAssumptions', text)
        require_pass(bounded, 'bounded assumptions')
        actual = assumptions(bounded['stdout'])
        if actual - ALLOWED or 'MemoryNotFull' in bounded['stdout']:
            raise ValueError(f'unexpected bounded theorem assumptions: {sorted(actual)}')
        # Direct counterexample to dropping the bound, without the bad axiom.
        control = 'From MemoryTrust Require Import BoundedMemory.\nRequire Import memory.\n' + WITNESS
        control += '''Lemma saturated_has_no_bound : forall upper, ~ blocks_below occupied_everywhere upper.
Proof.
  intros upper Hbound; apply (Pos.lt_irrefl upper).
  apply (Hbound upper 0%Z (true, Undef)); reflexivity.
Qed.
Print Assumptions saturated_has_no_bound.
'''
        counterexample = compile('BoundNecessary', control)
        require_pass(counterexample, 'bound necessity counterexample')
        if assumptions(counterexample['stdout']) - ALLOWED or 'MemoryNotFull' in counterexample['stdout']:
            raise ValueError('bound necessity witness depends on an unexpected axiom')
        result = subprocess.run([executable('coqchk'), '-silent', *flags[1:], 'MemoryTrust.BoundedAssumptions',
                                 'MemoryTrust.BoundNecessary'], cwd=work, capture_output=True, text=True, timeout=180)
        report['checks']['bounded_coqchk'] = {'exit_code': result.returncode, 'stdout': result.stdout, 'stderr': result.stderr}
        require_pass(report['checks']['bounded_coqchk'], 'bounded coqchk')
        report['bounded_roots_checked'] = ROOTS
        report['bounded_root_assumptions'] = sorted(actual)
        report['bounded_roots_exclude_MemoryNotFull'] = True
        if not bounds_only:
            original = (ROOT / 'framework/model/memory.v').read_text()
            if original.count(AXIOM) != 1:
                raise ValueError('global axiom has changed; investigate and update the diagnostic, do not infer safety')
            for name, body in [('BaselineMemory', original), ('WithoutAxiomMemory', original.replace(AXIOM, ''))]:
                require_pass(compile(name, body), name)
                prefix = f'From MemoryTrust Require Import {name}.\n'
                witness = compile(name + 'Witness', prefix + WITNESS)
                require_pass(witness, name + ' witness')
                if assumptions(witness['stdout']) - ALLOWED:
                    raise ValueError('saturated witness unexpectedly depends on the bad axiom')
                contradiction = compile(name + 'Contradiction', prefix + WITNESS + CONTRADICTION)
                if name == 'BaselineMemory':
                    require_pass(contradiction, 'baseline contradiction reproduction')
                    if 'MemoryNotFull' not in contradiction['stdout']:
                        raise ValueError('baseline contradiction has unexpected provenance')
                elif contradiction['exit_code'] != 1 or 'The variable MemoryNotFull was not found' not in contradiction['stderr']:
                    raise ValueError('removal control did not fail at the preselected missing axiom: ' + json.dumps(contradiction))
            report['framework_status'] = 'BLOCKED_GLOBAL_MEMORY_AXIOM_DERIVES_FALSE'
            report['global_framework_repaired'] = False
        else:
            report['framework_status'] = 'NOT_ASSESSED_BOUNDS_ONLY'
            report['global_framework_repaired'] = False
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--bounds-only', action='store_true', help='check bounded interfaces, not whole-framework safety')
    parser.add_argument('--report', type=Path, help='write fresh evidence only; never overwrite')
    args = parser.parse_args()
    try:
        report = inspect(args.bounds_only)
        if args.report:
            with args.report.open('x') as stream:
                json.dump(report, stream, ensure_ascii=False, indent=2)
                stream.write('\n')
        print('BOUNDED MEMORY INTERFACES: PASS (11 roots; no MemoryNotFull dependency)')
        print('Other recorded assumptions:', ', '.join(report['bounded_root_assumptions']) or 'none')
        print('FRAMEWORK TRUST:', report['framework_status'])
        if not args.bounds_only:
            print('The original global axiom derives False; its single-factor removal rejects that proof.')
            raise SystemExit(1)
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        parser.exit(2, f'MEMORY TRUST CHECK ERROR: {error}\n')


if __name__ == '__main__':
    main()
