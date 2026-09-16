#!/usr/bin/env python3
from __future__ import annotations
import re, sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
legacy_tokens=['V'+'252','v'+'252','V2'+'.52','2'+'.52']
forbidden=re.compile(r'\b(Admitted|admit|Axiom|Conjecture|Parameter)\b')
issues=[]
for p in ROOT.rglob('*'):
    if '.git' in p.parts or not p.is_file():
        continue
    rel=p.relative_to(ROOT)
    if any(part in {'checkout','__pycache__'} for part in rel.parts):
        continue
    if p.suffix.lower() in {'.v','.md','.json','.py','.sh','.c','.h'}:
        try: text=p.read_text(errors='replace')
        except Exception: continue
        if any(token in text or token in str(rel) for token in legacy_tokens):
            issues.append(f'legacy-target reference: {rel}')
for p in (ROOT/'certiucos/v293').rglob('*.v'):
    text=p.read_text(errors='replace')
    for i,line in enumerate(text.splitlines(),1):
        code=line.split('(*',1)[0]
        if forbidden.search(code):
            issues.append(f'proof escape in active V293 tree: {p.relative_to(ROOT)}:{i}')
if not (ROOT/'csrc/UPSTREAM.lock.json').is_file():
    issues.append('missing upstream lock')
if issues:
    print('PROJECT AUDIT: FAIL')
    for x in issues: print(' -',x)
    sys.exit(1)
print('PROJECT AUDIT: PASS')
print(' active V293 Coq files:', len(list((ROOT/'certiucos/v293').rglob('*.v'))))
print(' framework/tactic Coq files:', len(list((ROOT/'framework').rglob('*.v'))) + len(list((ROOT/'tactics').rglob('*.v'))))
