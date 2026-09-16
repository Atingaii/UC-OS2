#!/usr/bin/env python3
from __future__ import annotations
import argparse, hashlib, json, re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LOCK = json.loads((ROOT / 'csrc/UPSTREAM.lock.json').read_text())
PROFILE = json.loads((ROOT / 'csrc/config/v29301-profile.json').read_text())

def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open('rb') as f:
        for block in iter(lambda: f.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()

def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('checkout', nargs='?', default=str(ROOT / 'csrc/upstream/v2.93.01/checkout'))
    args = ap.parse_args()
    checkout = Path(args.checkout).resolve()
    failures = []
    expected_source = set(LOCK['files'])
    source_dir = checkout / 'Source'
    if source_dir.is_dir():
        actual_source = {str(p.relative_to(checkout)) for p in source_dir.iterdir() if p.is_file() and p.suffix in {'.c','.h'}}
        unexpected = sorted(actual_source - expected_source)
        missing = sorted(expected_source - actual_source)
        if unexpected:
            failures.append('unexpected Source files: ' + ', '.join(unexpected))
        if missing:
            failures.append('missing Source files: ' + ', '.join(missing))
    for rel, expected in LOCK['files'].items():
        p = checkout / rel
        if not p.is_file():
            failures.append(f'missing {rel}')
            continue
        actual = sha256(p)
        if actual != expected:
            failures.append(f'hash {rel}: {actual} != {expected}')
    cfg = checkout / LOCK['config_template']
    if not cfg.is_file():
        failures.append(f"missing {LOCK['config_template']}")
    else:
        actual = sha256(cfg)
        if actual != LOCK['config_template_sha256']:
            failures.append(f'config template hash: {actual}')
    header = checkout / 'Source/ucos_ii.h'
    if header.is_file():
        text = header.read_text(errors='replace')
        if 'Version  : V2.93.01' not in text:
            failures.append('ucos_ii.h version comment is not V2.93.01')
        if not re.search(r'#define\s+OS_VERSION\s+29300u\b', text):
            failures.append('OS_VERSION is not 29300u')
        for marker in ('OSTCBStatPend', 'OS_STAT_PEND_TO', 'OS_STAT_PEND_ABORT'):
            if marker not in text:
                failures.append(f'missing native pend marker {marker}')
    if failures:
        print('UPSTREAM AUDIT: FAIL')
        for item in failures:
            print(' -', item)
        raise SystemExit(1)
    print('UPSTREAM AUDIT: PASS')
    print(' release:', LOCK['release'])
    print(' commit :', LOCK['commit'])
    print(' files  :', len(LOCK['files']))

if __name__ == '__main__':
    main()
