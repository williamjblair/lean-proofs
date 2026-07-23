---
id: F-061
title: Positive answer to Erdős Problem 489
tier: lean
polarity: positive
depends_on: [F-001, F-002, F-007, F-058, F-059, F-060]
supersedes: []
verifier: cd verified_math/F-061_erdos-489-positive-answer && PATH="$HOME/.elan/bin:$PATH" lake update && lake build && ! rg -n '\\b(sorry|admit)\\b' F061 F061.lean
date: 2026-07-12
---

## Statement

For every `A : Set ℕ` whose inclusive counting function on `[1,x]` is
`o(√x)`, if the positive integers divisible by no member of `A` form an
infinite set, then the normalized sum of squared consecutive gaps with left
endpoint below `x` tends to a finite real limit. Formally, the artifact proves
the exact pinned theorem `Erdos489.erdos489_statement`.

## Proof / verification

For infinite `A`, remove the irrelevant values 0 and 1 and enumerate the
remaining forbidden moduli. Thinness gives eventual quadratic enumeration
growth, reciprocal summability, and negligible endpoint counts. The affine
factorial-sieve construction charges every sufficiently long actual gap to
coprime high-rank divisor pairs; global occurrence bounds and the summable
rank-pair kernel give uniform integrability of squared gaps. For each fixed
cutoff, local gap words are approximated in density by finite periodic sieves,
whose Cesàro averages converge. Two uniform-approximation arguments first give
convergence of truncated averages and then of the full gap average. Finite `A`
is handled separately by shifted periodicity and a one-period maximum-gap
bound. Finally, the natural squared gaps are identified exactly with the real
differences in `gapSumSq`.

`F061/Erdos489.lean` contains the exact final statement; the other files in
`F061/` are its complete dependency closure. The listed verifier builds all
files with Lean 4.31.0 and Mathlib revision
`fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`, then rejects any `sorry` or
`admit` token.
