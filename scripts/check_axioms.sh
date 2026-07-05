#!/usr/bin/env bash
# Verification gate for the proof index.
#
# Fails if:
#   1. any tracked source contains a literal `sorry` or `admit`, or
#   2. `Audit.lean` reports `sorryAx` for any headline theorem, or
#   3. any headline theorem depends on an axiom outside the allowed kernel set.
#
# Run locally with the Mathlib cache primed:
#   lake exe cache get && lake build && bash scripts/check_axioms.sh
set -euo pipefail

ALLOWED='[propext, Classical.choice, Quot.sound]'
fail() { echo "FAIL: $*" >&2; exit 1; }

# 1. No literal sorry / admit in the hosted proofs.
if grep -rnoE '\b(sorry|admit)\b' ErdosProblems/ ; then
  fail "literal sorry/admit in ErdosProblems/"
fi

# 2/3. Build the audit and inspect the axiom report.
report="$(lake env lean Audit.lean 2>&1)"
echo "$report"

echo "$report" | grep -qiE '(^| )error' && fail "Audit.lean did not compile cleanly"
echo "$report" | grep -q 'sorryAx'        && fail "a headline theorem depends on sorryAx"

# Every reported axiom must be in the allowed kernel set. Some theorems use a
# strict subset, and Lean may wrap long axiom lists across multiple lines.
REPORT="$report" python3 - <<'PY'
import os
import re
import sys

allowed = {"propext", "Classical.choice", "Quot.sound"}
report = os.environ["REPORT"]
matches = re.findall(r"'([^']+)'\s+depends on axioms:\s*\[([^\]]*)\]", report, flags=re.S)
if not matches:
    print("FAIL: no axiom report produced (is Audit.lean wired up?)", file=sys.stderr)
    sys.exit(1)

for theorem, raw_axioms in matches:
    axioms = [part.strip() for part in raw_axioms.replace("\n", " ").split(",") if part.strip()]
    unexpected = sorted(set(axioms) - allowed)
    if unexpected:
        print(f"FAIL: unexpected axioms for {theorem}: {unexpected}", file=sys.stderr)
        sys.exit(1)

print(f"PASS: {len(matches)} audited theorem(s) clean, axioms subset of {sorted(allowed)}")
PY
