#!/usr/bin/env python3
"""Finite, source-bound scheduler investigation; no Coq/coverage proof credit."""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import tempfile

ROOT = Path(__file__).resolve().parents[1]
REPORT = 'audit/ready-bitmap-investigation.json'


def inspect():
    spec = importlib.util.spec_from_file_location('functions', ROOT / 'scripts/check-v293-functions.py')
    functions = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(functions)
    with tempfile.TemporaryDirectory(prefix='ucos-ready-investigation-') as directory:
        work = Path(directory)
        inventory, _, _ = functions.source_replay(ROOT, work)
        tool = functions.load(ROOT, 'inventory-v293-source.py')
        ast = json.loads(tool.run(work, ['clang', *tool.CLANG_FLAGS, '-x', 'c', '-fsyntax-only',
                                        '-Xclang', '-ast-dump=json', 'kernel.i']))
        candidates = [c for n in ast['inner'] if n.get('kind') == 'VarDecl'
                      and n.get('name') == 'OSUnMapTbl' for c in n.get('inner', [])
                      if c.get('kind') == 'InitListExpr']
        if len(candidates) != 1:
            raise ValueError('expected exactly one actual lookup-table initializer, not a declaration')
        table = []
        for cast in functions.children(candidates[0], 'InitListExpr', 256):
            literal, = functions.children(cast, 'ImplicitCastExpr', 1)
            functions.children(literal, 'IntegerLiteral', 0)
            if (cast.get('castKind') != 'IntegralCast'
                    or cast['type'].get('desugaredQualType') != 'unsigned char'
                    or literal['type']['qualType'] != 'unsigned int'):
                raise ValueError('unsupported lookup-table initializer conversion')
            value = int(literal['value'])
            if not 0 <= value < 256:
                raise ValueError('lookup-table literal does not fit byte')
            table.append(value)
        expected = [next((b for b in range(8) if x & (1 << b)), 0) for x in range(256)]
        if table != expected:
            raise ValueError('actual table does not implement the expected least-set-bit lookup')
        ready_types = {n['type']['qualType'] for n in ast['inner']
                       if n.get('kind') == 'VarDecl' and n.get('name') == 'OSRdyTbl'}
        if ready_types != {'OS_PRIO[2]'}:
            raise ValueError('unexpected ready-table extent')

        def select(lo, hi, *, decoder=table, shift=3, group=None):
            if group is None:
                group = bool(lo) + 2 * bool(hi)
            y = decoder[group]
            return (y << shift) + decoder[[lo, hi][y]]

        # Single-factor ablation: permit the high three bits of row 1, keeping
        # exact group coherence and a nonempty valid-priority set unchanged.
        count = 0
        for lo in range(256):
            for hi in range(256):
                valid = [p for p in range(13) if [lo, hi][p // 8] & (1 << (p % 8))]
                if not valid:
                    continue
                result = select(lo, hi)
                if result != min(valid) or result != select(lo, hi & 31):
                    raise ValueError('removing range-mask restriction changed the decision')
                count += 1
        # Prospective semantic faults; each retains all other inputs.
        wrong_table = list(table)
        wrong_table[16] = 3
        controls = {
            'lookup_entry_16_changed_only': (select(0, 16, decoder=wrong_table), 12),
            'shift_changed_only': (select(0, 17, shift=2), 8),
            'group_coherence_removed_only': (select(2, 16, group=2), 1),
            'nonempty_removed_only': (select(0, 0), None),
        }
        if any(actual == expected for actual, expected in controls.values()):
            raise ValueError('a designated semantic counterexample was not observed')
        freeze = json.loads((ROOT / 'csrc/repairs/FROZEN_SOURCE.json').read_text())
        paths = set(freeze['input_sha256']) | {
            'scripts/inspect-v293-ready-bitmap.py', 'scripts/check-v293-functions.py',
            'csrc/repairs/FROZEN_SOURCE.json', 'audit/repaired-source-inventory.json'}
        return {'scope': 'FINITE_INVESTIGATION_NOT_COQ_OR_SOURCE_PROOF',
                'source_identity_sha256': inventory['source_identity_sha256'],
                'function': next(f for f in inventory['functions'] if f['name'] == 'OS_SchedNew'),
                'input_sha256': {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in sorted(paths)},
                'lookup_table': table, 'ready_table_type': 'OS_PRIO[2]',
                'range_mask_ablation': {'states': count, 'decision_changes': 0,
                    'unchanged': ['exact two-row group coherence', 'nonempty priorities 0-12']},
                'semantic_controls': {k: {'observed': a, 'required': e} for k, (a, e) in controls.items()},
                'coverage_credit': False, 'kernel_GOOD_OS_proved': False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record', action='store_true')
    args = parser.parse_args()
    report = inspect()
    if args.record:
        with (ROOT / REPORT).open('x') as stream:
            json.dump(report, stream, ensure_ascii=False, indent=2)
            stream.write('\n')
    print('READY BITMAP INVESTIGATION: PASS (finite experiment only)')
    print('range-mask ablation:', report['range_mask_ablation'])
    print('No Coq theorem or function coverage credit claimed.')


if __name__ == '__main__':
    main()
