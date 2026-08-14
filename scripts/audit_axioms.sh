#!/usr/bin/env bash
# Run the #print axioms audit in lean/RequestProject/Main.lean and fail on any
# axiom outside the three Mathlib permits.
set -uo pipefail
cd lean
out=$(lake env lean RequestProject/Main.lean 2>&1) || { echo "FAIL: lean invocation failed"; echo "$out"; exit 1; }
echo "$out"
axioms=$(echo "$out" | grep 'depends on axioms' \
  | sed 's/.*\[\(.*\)\]/\1/' | tr ',' '\n' | sed 's/^[[:space:]]*//;s/[[:space:]]*$//' \
  | grep -v '^$' | sort -u)
if [ -z "$axioms" ]; then
  echo "FAIL: no '#print axioms' output found; the audit did not run"
  exit 1
fi
echo "--- axiom footprint ---"
echo "$axioms"
unexpected=$(echo "$axioms" | grep -vxE 'propext|Classical\.choice|Quot\.sound' || true)
if [ -n "$unexpected" ]; then
  echo "FAIL: unexpected axioms:"
  echo "$unexpected"
  exit 1
fi
echo "OK: axiom footprint is propext, Classical.choice, Quot.sound"
