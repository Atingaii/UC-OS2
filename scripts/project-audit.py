#!/usr/bin/env python3
"""Static boundary checks; compilation and assumption checks remain separate gates."""
from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEGACY_TOKENS = ('V' + '252', 'v' + '252', 'V2' + '.52', '2' + '.52')
# Match path literals, not this regular expression's own spelling.
ARCHIVED_PATH = re.compile(
    r'''(?<![\w.-])(?:references(?=[/\\\s'"]|$)|(?:start|work)-prompt\.md)'''
)
FORBIDDEN = re.compile(r'\b(Admitted|admit|Axioms?|Conjectures?|Parameters?)\b')
CODE_SUFFIXES = {'.v', '.c', '.h', '.py', '.sh', '.json', '.mk'}
ACTIVE_DIRS = {'framework', 'tactics', 'certiucos', 'csrc', 'scripts'}
BUILD_FILES = {'Makefile', '_CoqProject', 'coqc-wrapper.sh'}


def coq_code(text: str) -> str:
    """Blank nested comments and strings, preserving offsets and line numbers."""
    result = list(text)
    depth = 0
    in_string = False
    i = 0
    while i < len(text):
        pair = text[i:i + 2]
        width = 1
        if depth:
            if pair == '(*':
                depth += 1
                width = 2
            elif pair == '*)':
                depth -= 1
                width = 2
        elif in_string:
            if pair == '""':
                width = 2
            elif text[i] == '"':
                in_string = False
        elif pair == '(*':
            depth = 1
            width = 2
        elif text[i] == '"':
            in_string = True
        else:
            i += 1
            continue
        for j in range(i, i + width):
            if text[j] != '\n':
                result[j] = ' '
        i += width
    return ''.join(result)


def main() -> int:
    issues = []
    active_coq = sorted((ROOT / 'certiucos/v293').rglob('*.v'))
    if not active_coq:
        issues.append('missing active V293 Coq tree')
    if not (ROOT / 'csrc/UPSTREAM.lock.json').is_file():
        issues.append('missing upstream lock')

    for path in sorted(ROOT.rglob('*')):
        rel = path.relative_to(ROOT)
        if not path.is_file() or any(p in {'.git', 'checkout', '__pycache__'} for p in rel.parts):
            continue
        # Documentation and regression fixtures are not build inputs. Check the
        # configured source trees, scripts, and root build inputs instead.
        in_active_tree = rel.parts[0] in ACTIVE_DIRS
        root_code = len(rel.parts) == 1 and path.suffix in CODE_SUFFIXES
        unarchived_coq = (path.suffix == '.v' and rel.parts[0] != 'tests' and
                          not ARCHIVED_PATH.match(rel.as_posix()))
        if not (rel.as_posix() in BUILD_FILES or
                (in_active_tree and (path.suffix in CODE_SUFFIXES or path.name in BUILD_FILES)) or
                root_code or unarchived_coq):
            continue
        try:
            text = path.read_text(encoding='utf-8')
        except (OSError, UnicodeError) as error:
            issues.append(f'unreadable active input: {rel}: {error}')
            continue
        if any(token in text or token in rel.as_posix() for token in LEGACY_TOKENS):
            issues.append(f'legacy-target reference: {rel}')
        if ARCHIVED_PATH.search(text):
            issues.append(f'archived-input dependency: {rel}')
        if path in active_coq:
            code = coq_code(text)
            for match in FORBIDDEN.finditer(code):
                line = code.count('\n', 0, match.start()) + 1
                issues.append(f'proof escape in active V293 tree: {rel}:{line}')

    if issues:
        print('PROJECT AUDIT: FAIL')
        for issue in issues:
            print(' -', issue)
        return 1
    print('PROJECT AUDIT: PASS')
    print(' active V293 Coq files:', len(active_coq))
    print(' framework/tactic Coq files:', sum(
        len(list((ROOT / directory).rglob('*.v'))) for directory in ('framework', 'tactics')
    ))
    return 0


if __name__ == '__main__':
    sys.exit(main())
