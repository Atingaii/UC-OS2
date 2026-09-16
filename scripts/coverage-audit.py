#!/usr/bin/env python3
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
p=json.loads((ROOT/'audit/coverage.json').read_text())
allowed=p['states']
seen=set()
for i,row in enumerate(p['rows']):
    name=row.get('name')
    if not name or name in seen:
        raise SystemExit(f'coverage row {i}: missing/duplicate name {name!r}')
    seen.add(name)
    values=[bool(row.get(k,False)) for k in allowed]
    # Progress may not skip an earlier gate.
    for j in range(1,len(values)):
        if values[j] and not values[j-1]:
            raise SystemExit(f'{name}: {allowed[j]} set before {allowed[j-1]}')
print('COVERAGE AUDIT: PASS')
print('rows:',len(seen))
for k in allowed:
    print(k+':',sum(bool(r.get(k,False)) for r in p['rows']))
