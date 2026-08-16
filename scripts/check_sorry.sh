#!/usr/bin/env bash
# Fail if any Lean source contains an unproved statement, ignoring comments.
# Comments are stripped first (line comments and block comments), so doc-comment
# mentions of "sorry" cannot false-positive; the semantic backstop is the axiom
# audit, which would report sorryAx.
set -uo pipefail
fail=0
for f in $(find lean/RequestProject -name '*.lean'); do
  hits=$(python3 - "$f" <<'PYEOF'
import re,sys
src=open(sys.argv[1]).read()
src=re.sub(r'/-.*?-/','',src,flags=re.S)      # block & doc comments
src=re.sub(r'--.*','',src)                    # line comments
for i,line in enumerate(src.split('\n'),1):
    if re.search(r'\b(sorry|admit)\b',line):
        print(f"{i}:{line.strip()}")
PYEOF
)
  if [ -n "$hits" ]; then echo "FAIL: $f"; echo "$hits"; fail=1; fi
done
[ $fail -eq 0 ] && echo "OK: no sorry/admit outside comments in lean/RequestProject"
exit $fail
