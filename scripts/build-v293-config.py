#!/usr/bin/env python3
from __future__ import annotations
import argparse, hashlib, json, re
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
PROFILE = json.loads((ROOT/'csrc/config/v29301-profile.json').read_text())

def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main() -> None:
    ap=argparse.ArgumentParser()
    ap.add_argument('template')
    ap.add_argument('output')
    args=ap.parse_args()
    template=Path(args.template)
    output=Path(args.output)
    text=template.read_text()
    for name,value in PROFILE['overrides'].items():
        pattern=r'(#define\s+'+re.escape(name)+r'\s+)\d+u\b'
        text,count=re.subn(pattern, lambda m: m.group(1)+str(value)+'u', text)
        if count != 1:
            raise SystemExit(f'{name}: expected exactly one template definition, found {count}')
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(text)
    actual=sha(output)
    expected=PROFILE['expected_effective_os_cfg_sha256']
    if actual != expected:
        raise SystemExit(f'effective os_cfg.h hash mismatch: {actual} != {expected}')
    print('CONFIG BUILD: PASS', actual)
if __name__=='__main__': main()
