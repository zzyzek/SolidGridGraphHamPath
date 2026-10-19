#!/usr/bin/env bash
# SPDX-License-Identifier: CC0-1.0
#
# Release check, from the repository root: `scripts/check.sh`.
#   1. builds the library, failing on any warning (`lake build --wfail`, which also replays the
#      messages of files already built);
#   2. checks that the main results use only `propext`, `Classical.choice` and `Quot.sound`
#      (`lean/CheckAxioms.lean`), so no `sorry` and no extra axioms;
#   3. runs the cost-model lint on the counted algorithm (`checks/timed_lint.py`).
# Honours LEAN_MEM and LEAN_NUM_THREADS like `lean/build.sh`.
set -euo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"

echo "== build (warnings are errors)"
"$root/lean/build.sh" --wfail

echo "== axioms"
cd "$root/lean"
out="$(lake env lean CheckAxioms.lean)"
echo "$out"
n_ok="$(printf '%s\n' "$out" | grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]" || true)"
n_all="$(grep -c '^#print axioms' CheckAxioms.lean)"
if [ "$n_ok" != "$n_all" ]; then
  echo "axiom check FAILED: $n_ok of $n_all results use only the standard axioms" >&2
  exit 1
fi

echo "== cost-model lint"
python3 "$root/checks/timed_lint.py"

echo "== all checks passed"
