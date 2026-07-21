#!/bin/bash
# Erdős-7 publication gate (ERDOS7_PLAN.md step 8).
#
# Every published theorem must depend on AT MOST the three standard axioms
#   propext, Classical.choice, Quot.sound
# (subsets are fine — several lemmas need less), with zero `sorryAx` and zero
# `_native.*` (native_decide is forbidden: it mints a per-theorem trust axiom).
#
# Usage: scripts/axiom_gate.sh          (from anywhere; exits 0 on PASS, 1 on FAIL)
set -uo pipefail
cd "$(dirname "$0")/.."

out=$(lake env lean Erdos7/AxiomCheck.lean 2>&1)
status=$?
echo "$out"

if [ $status -ne 0 ]; then
  echo "AXIOM GATE: FAIL (AxiomCheck.lean did not compile)"
  exit 1
fi

# Any axiom token outside the allowed three is a violation.
viol=$(echo "$out" | grep "depends on" \
  | sed 's/.*axioms: \[//; s/\]//' | tr ',' '\n' | tr -d ' ' \
  | grep -vE '^(propext|Classical\.choice|Quot\.sound)$' || true)

count=$(echo "$out" | grep -c "depends on")

if [ -n "$viol" ]; then
  echo "AXIOM GATE: FAIL — disallowed axioms:"
  echo "$viol" | sort -u
  exit 1
fi
if echo "$out" | grep -qE "sorryAx|_native"; then
  echo "AXIOM GATE: FAIL — sorryAx or native axiom present"
  exit 1
fi
if [ "$count" -eq 0 ]; then
  echo "AXIOM GATE: FAIL — no '#print axioms' output found"
  exit 1
fi

echo "AXIOM GATE: PASS ($count theorems, axioms ⊆ {propext, Classical.choice, Quot.sound})"
