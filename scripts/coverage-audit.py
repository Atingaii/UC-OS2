#!/usr/bin/env python3
"""Validate locations and dedicated function evidence, never file-count progress."""
from __future__ import annotations

import json
from pathlib import Path
import sys

from importlib.util import module_from_spec, spec_from_file_location

ROOT = Path(__file__).resolve().parents[1]


def audit(root):
    spec = spec_from_file_location('source_freeze', root / 'scripts/freeze-v293-source.py')
    source = module_from_spec(spec)
    spec.loader.exec_module(source)
    import hashlib
    sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
    freeze = json.loads((root / source.FREEZE).read_text())
    inventory = json.loads((root / source.INVENTORY).read_text())
    coverage = json.loads((root / 'audit/coverage.json').read_text())
    lock = json.loads((root / 'csrc/UPSTREAM.lock.json').read_text())
    profile = json.loads((root / 'csrc/config/v29301-profile.json').read_text())
    if freeze['source_layer'] != source.LAYER or inventory['source_layer'] != source.LAYER:
        raise ValueError('coverage requires repaired source, not upstream-only inventory')
    for p in [freeze['program'], inventory, coverage]:
        if (p['target_release'], p['target_commit']) != (lock['release'], lock['commit']):
            raise ValueError('coverage target differs from locked release/commit')
    source_id = source.identity(freeze['program'])
    if any(p['source_identity_sha256'] != source_id for p in [freeze, inventory, coverage]):
        raise ValueError('source identity does not match frozen program')
    if freeze['inventory'] != {'path': str(source.INVENTORY), 'sha256': sha(root / source.INVENTORY)}:
        raise ValueError('repaired inventory hash/path differs from freeze')
    for rel, expected in freeze['input_sha256'].items():
        if sha(root / rel) != expected:
            raise ValueError(f'frozen input identity drift: {rel}')
    output = freeze['program']['source_sha256']
    if set(output) != set(lock['files']):
        raise ValueError('frozen source-file set differs from upstream lock')
    if {p for p in output if output[p] != lock['files'][p]} != {'Source/os_mutex.c', 'Source/os_task.c'}:
        raise ValueError('frozen changes exceed two authorized source files')
    if freeze['program']['os_cfg_sha256'] != profile['expected_effective_os_cfg_sha256']:
        raise ValueError('frozen configuration differs from profile')
    for rel, expected in freeze['program']['analysis_port_sha256'].items():
        if sha(root / 'csrc/analysis-port' / rel) != expected:
            raise ValueError(f'analysis port drift: {rel}')
    if coverage['states'] != source.STATES:
        raise ValueError('coverage state order/set must be the six fixed gates')
    status = coverage['inventory_status']
    if status not in {'REPAIRED_SOURCE_FROZEN_LOCATION_EVIDENCE_ONLY',
                      'REPAIRED_SOURCE_WITH_CHECKED_FUNCTION_EVIDENCE'}:
        raise ValueError('unsupported coverage inventory status')
    expected_rows = source.location_rows(inventory)
    supported = {}
    if status == 'REPAIRED_SOURCE_WITH_CHECKED_FUNCTION_EVIDENCE':
        checker = source.load_tool(root, 'check-v293-functions.py')
        evidence = json.loads((root / checker.REPORT).read_text())
        supported = checker.validate_record(root, evidence)
        for row in expected_rows:
            if row['name'] in supported:
                gates = supported[row['name']]['gates']
                row.update({gate: True for gate in gates})
                row['evidence'] = {'report': checker.REPORT,
                                   'sha256': sha(root / checker.REPORT), 'gates': gates}
    names = [r['name'] for r in expected_rows]
    if len(set(names)) != len(names) or len(names) != inventory['summary']['configured_c_definitions']:
        raise ValueError('repaired inventory definition names/count disagree')
    for f in inventory['functions']:
        rel = Path(f['source']).relative_to(source.SOURCE).as_posix()
        if f['source_file_sha256'] != output[rel]:
            raise ValueError(f"inventory source-file hash mismatch: {f['name']}")
        if not (isinstance(f['first_line'], int) and isinstance(f['last_line'], int)
                and 1 <= f['first_line'] <= f['last_line']):
            raise ValueError(f"invalid source location: {f['name']}")
    actual = coverage['rows']
    seen = set()
    for row in actual:
        name = row.get('name')
        if not name or name in seen:
            raise ValueError(f'missing/duplicate coverage name: {name!r}')
        seen.add(name)
        if any(type(row.get(s)) is not bool for s in source.STATES):
            raise ValueError(f'{name}: stage values must be explicit booleans')
        values = [row[s] for s in source.STATES]
        if any(values[i] and not values[i-1] for i in range(1, len(values))):
            raise ValueError(f'{name}: coverage cannot skip an earlier gate')
        # Later gates need dedicated source/model/theorem linkage checkers first.
        # A path or theorem name alone must not manufacture proof credit.
        allowed = supported.get(name, {}).get('gates', [])
        if any(row[s] and s not in allowed for s in source.STATES[1:]):
            raise ValueError(f'{name}: later-stage evidence checker not implemented; proof credit rejected')
    if actual != expected_rows:
        raise ValueError('coverage must exactly match every frozen function location and body hash')
    return {s: sum(r[s] for r in actual) for s in source.STATES}


def main():
    try:
        counts = audit(ROOT)
        print('COVERAGE AUDIT: PASS')
        print('rows:', counts['located'])
        for stage, count in counts.items():
            print(f'{stage}: {count}')
        print('Scope: recorded evidence identity; use source-freeze-check/check-functions for live replay.')
    except (OSError, ValueError, KeyError, TypeError) as error:
        sys.exit(f'COVERAGE AUDIT: FAIL: {error}')


if __name__ == '__main__':
    main()
