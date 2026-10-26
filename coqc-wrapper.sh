#!/usr/bin/env bash
set -euo pipefail

if (( $# < 1 )); then
  echo "usage: $0 /path/to/coqc [coqc arguments ...]" >&2
  exit 64
fi

coq_compiler=$1
shift

# 512 MiB stack by default. A lower hard limit is tolerated and reported by
# Coq itself if it proves insufficient.
stack_kb=${COQ_STACK_KB:-524288}
ulimit -s "$stack_kb" 2>/dev/null || true

# Optional legacy GC setting: o controls space overhead, not the minor heap.
# No performance improvement is claimed; callers may override OCAMLRUNPARAM.
export OCAMLRUNPARAM="${OCAMLRUNPARAM:-o=5}"

exec "$coq_compiler" "$@"
