#!/usr/bin/env bash
# Fail if any Lean source in the development contains an unproved statement.
set -uo pipefail
hits=$(grep -rn --include='*.lean' -E '\b(sorry|admit)\b' lean/RequestProject || true)
if [ -n "$hits" ]; then
  echo "FAIL: unproved statements found"
  echo "$hits"
  exit 1
fi
echo "OK: no sorry/admit in lean/RequestProject"
