#!/usr/bin/env bash
# Isolated regression of the six small models; not a source-level kernel proof.
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/.." && pwd)
COQBIN=${COQBIN:-}
"${COQBIN}coqc" --version | head -n 1 | grep -Eq 'version 8\.18\.0( |$)' || {
  echo 'This check requires Coq 8.18.0.' >&2
  exit 1
}
TMP=$(mktemp -d "${TMPDIR:-/tmp}/ucos-v293-models.XXXXXX")
# TMP contains only this invocation's copied models and compilation outputs.
trap 'rm -rf "$TMP"' EXIT
cd "$TMP"
for file in \
  code/V293Config.v \
  model/V293MutexPriorityModel.v \
  model/V293PendModel.v \
  model/V293TaskDeleteModel.v \
  spec/V293SafetySpec.v \
  proofs/V293SafetyProof.v; do
  mkdir -p "$(dirname "certiucos/v293/$file")"
  cp "$ROOT/certiucos/v293/$file" "certiucos/v293/$file"
  echo "CHECK certiucos/v293/$file"
  "${COQBIN}coqc" -q -R . CertiOS "certiucos/v293/$file"
done
cat > assumptions.v <<'COQ'
Require Import CertiOS.certiucos.v293.proofs.V293SafetyProof.
Print Assumptions V293_timeout_suspend_resume_safety_proved.
Print Assumptions V293_nested_mutex_restoration_safety_proved.
Print Assumptions V293_locked_self_delete_safety_proved.
COQ
"${COQBIN}coqtop" -quiet -batch -R . CertiOS -l assumptions.v > assumptions.log 2>&1
cat assumptions.log
if [ "$(grep -c '^Closed under the global context$' assumptions.log)" != 3 ] ||
   grep -q '^Axioms:' assumptions.log; then
  echo 'Unexpected assumptions in small-model roots.' >&2
  exit 1
fi
"${COQBIN}coqchk" -silent -R . CertiOS CertiOS.certiucos.v293.proofs.V293SafetyProof
echo 'V293 SMALL-MODEL CHECK: PASS (not a C-function coverage result)'
