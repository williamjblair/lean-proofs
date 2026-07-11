# Erdős 686 Three-Bucket Short-CRT LCM Hostile Audit Plan

**Goal:** Independently decide whether the frozen three-bucket checkpoint proves its advertised zero-obstruction exclusion, whether its finite arithmetic is exact, and whether the claimed `abc` restriction is genuinely new in the equation context.

**Architecture:** Freeze the producer artifacts by SHA-256; rebuild and print every public theorem's kernel assumptions; rederive the cyclic zero branch and common-LCM packing; independently reconstruct all Taylor coefficients and scan every owner case; replay the named falsifiers; compare the row-wise `abc` thresholds against already-banked equation-level inequalities; issue a separate scoped verdict without editing producer or integration files.

**Tech stack:** Lean 4.29.1 with mathlib, Python 3 exact integers and `fractions.Fraction`, pytest, POSIX shell.

## Task 1: Freeze and inspect the producer

1. Record hashes for the Lean source, verifier, tests, findings, and producer plan.
2. Enumerate all public theorem declarations and inspect every premise and cancellation.
3. Scan for forbidden proof constructs, unproved private declarations, and hidden imports.

## Task 2: Rebuild the kernel surface

1. Create an audit-only Lean importer.
2. Print the assumptions of all nine public producer theorems and the banked equation-level gap theorem used in the claim comparison.
3. Require every assumption set to be a subset of `[propext, Classical.choice, Quot.sound]`.

## Task 3: Reconstruct the mathematics independently

1. Recompute `C,D,E` by reciprocal elementary sums, without importing producer arithmetic.
2. Re-derive the denominator-cleared cross identity for the two nonzero owners.
3. Re-derive the zero owner's square cancellation, pairwise-coprime packing, and exact `g^4` loss; search for a fixture showing `g^3` is insufficient.
4. Enumerate all 3,105 owner occurrences, all 1,427 positive-zero cases, every row maximum, every denominator boundary, all center/reflected triples, all coarse bounds, and all row-wise `abc` thresholds.

## Task 4: Replay boundaries and audit the claim

1. Exercise small primes shared with `g`, unit components, both `d=1` telescopes, the `d=6790` below-threshold fixture, and the 121-digit CRT pseudo-witness.
2. Compare the new thresholds with the exact equation consequence `abc > 125*g^2*d` derived from the banked `2d<n` estimate.
3. State the residual short-CRT lemma with progression, windows, cyclic divisibilities, all three nonzero obstructions, and the row threshold.
4. Return PASS/FAIL with exact hashes, counts, scope correction, and no closure claim.
