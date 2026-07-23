#!/usr/bin/env bash
# Keeps proofs.yaml (the machine-readable index that erdos-fc-sync ingests)
# honest: every theorem advertised in the manifest must actually be audited in
# the manifest-tracked section of Audit.lean, and every theorem in that section
# must be advertised. Conditional research surfaces in Audit.lean are excluded
# from the solved-proof manifest.
set -euo pipefail
fail() { echo "FAIL: $*" >&2; exit 1; }

# Only the proofs hosted in the ErdosProblems library are audited in Audit.lean.
# Externally-pinned sources (e.g. starfleet/, a different toolchain) are audited
# by their own CI (see .github/workflows/starfleet.yml), so exclude them here by
# keying on each entry's `file:` prefix.
manifest_thms="$(awk '
  /^[[:space:]]*-[[:space:]]*problem:/ { file=""; thm="" }
  /^[[:space:]]*file:/    { f=$0; sub(/^[[:space:]]*file:[[:space:]]*/,"",f); file=f }
  /^[[:space:]]*theorem:/ { t=$0; sub(/^[[:space:]]*theorem:[[:space:]]*/,"",t); gsub(/"/,"",t); thm=t
                            if (file ~ /^ErdosProblems\//) print thm }
  ' proofs.yaml | sort -u)"
audited_thms="$(
  awk '
    /^-- Manifest-tracked formal proof targets[.]$/ { in_manifest = 1; next }
    /^-- Conditional research surfaces/ { in_manifest = 0; next }
    in_manifest && /^#print axioms / {
      sub(/^#print axioms /, "")
      print
    }
  ' Audit.lean | sort -u
)"

if [ "$manifest_thms" != "$audited_thms" ]; then
  echo "proofs.yaml theorems:"; echo "$manifest_thms" | sed 's/^/  /'
  echo "Audit.lean theorems:";  echo "$audited_thms"  | sed 's/^/  /'
  fail "proofs.yaml and Audit.lean disagree on the tracked theorem set"
fi
echo "PASS: manifest matches the audit ($(echo "$manifest_thms" | grep -c . ) theorem(s))"
