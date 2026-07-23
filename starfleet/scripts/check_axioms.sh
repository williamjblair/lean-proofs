#!/usr/bin/env bash
# Axiom audit for one Star Fleet Math project.  Run from inside the project dir
# (the one holding Audit.lean).  Fails if:
#   1. Audit.lean does not elaborate cleanly, or
#   2. the terminal theorem depends on sorryAx (a gap), Lean.ofReduceBool
#      (native_decide), or any axiom outside [propext, Classical.choice,
#      Quot.sound].
set -euo pipefail
fail() { echo "FAIL: $*" >&2; exit 1; }

# `#print axioms` on the terminal theorem is the authoritative gate: it reports
# `sorryAx` iff the theorem's dependency cone contains a `sorry`/`admit`, and
# `Lean.ofReduceBool` iff it uses `native_decide` — both immune to comments and
# to `sorry` sitting in unrelated scaffold files.  A raw source grep is not used
# because it flags the word "sorry" in docstrings.
report="$(lake env lean Audit.lean 2>&1)"
echo "$report"
echo "$report" | grep -qiE '(^| )error' && fail "Audit.lean did not elaborate cleanly"
echo "$report" | grep -q 'sorryAx'        && fail "theorem depends on sorryAx (hidden gap)"

seen=0
while IFS= read -r line; do
  if [[ "$line" == *"depends on axioms:"* ]]; then
    seen=$((seen+1))
    axioms="${line#*depends on axioms: }"
    while [[ "$axioms" != *"]"* ]]; do
      IFS= read -r cont || fail "unterminated axiom report -> $line"
      axioms+="$cont"
    done
    compact="$(printf '%s' "$axioms" | tr -d '[][:space:]')"
    if [ -n "$compact" ]; then
      IFS=',' read -r -a names <<< "$compact"
      for ax in "${names[@]}"; do
        case "$ax" in
          propext|Classical.choice|Quot.sound) ;;
          *) fail "unexpected axiom '$ax'" ;;
        esac
      done
    fi
  fi
done <<< "$report"

[ "$seen" -gt 0 ] || fail "no axiom report produced (did Audit.lean name a real theorem?)"
echo "PASS: audited theorem is sorry-free; axioms subset of [propext, Classical.choice, Quot.sound]"
