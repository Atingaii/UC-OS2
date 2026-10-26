#!/usr/bin/env bash
# Compile every configured Coq source without existing products or archives.
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/.." && pwd)
COQBIN=${COQBIN:-}
TMP=$(mktemp -d "${TMPDIR:-/tmp}/ucos-clean-build.XXXXXX")
# Only files copied/compiled by this invocation can be under TMP.
trap 'rm -rf "$TMP"' EXIT
cp "$ROOT/Makefile" "$ROOT/_CoqProject" "$ROOT/coqc-wrapper.sh" "$TMP/"
cd "$ROOT"
while IFS= read -r -d '' file; do
  mkdir -p "$TMP/$(dirname "$file")"
  cp "$file" "$TMP/$file"
done < <(find framework tactics certiucos/v293 -type f -name '*.v' -print0)
cd "$TMP"
make build COQBIN="$COQBIN" JOBS="${JOBS:-2}"
echo 'CLEAN COQ BUILD: PASS (framework + tactics + V293 models; not GOOD_OS)'
