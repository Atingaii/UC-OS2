#!/usr/bin/env bash
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/.." && pwd)
DEST=${1:-"$ROOT/csrc/upstream/v2.93.01/checkout"}
COMMIT=0c4a48e6fbc6e915714e816196619a5481accf0c
REPO=https://github.com/weston-embedded/uC-OS2.git
TMP=$(mktemp -d "${TMPDIR:-/tmp}/certiucos-v29301.XXXXXX")
trap 'rm -rf "$TMP"' EXIT

git init -q "$TMP/repo"
git -C "$TMP/repo" remote add origin "$REPO"
git -C "$TMP/repo" -c protocol.version=2 fetch -q --depth=1 --filter=blob:none origin "$COMMIT"
git -C "$TMP/repo" checkout -q --detach FETCH_HEAD
[ "$(git -C "$TMP/repo" rev-parse HEAD)" = "$COMMIT" ]
rm -rf "$DEST"
mkdir -p "$DEST"
git -C "$TMP/repo" archive HEAD Source Cfg/Template/os_cfg.h | tar -x -C "$DEST"
python3 "$ROOT/scripts/audit-v293-upstream.py" "$DEST"
python3 "$ROOT/scripts/build-v293-config.py" \
  "$DEST/Cfg/Template/os_cfg.h" "$DEST/os_cfg.h"
echo "Pinned V2.93.01 source prepared at $DEST"
