# Verification verdicts

Two independent gates per problem:

- **Proof gate** (CI, `scripts/check_axioms.sh`): the pinned project builds
  against its pinned Mathlib and the terminal theorem's `#print axioms` is a
  subset of `[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no
  `Lean.ofReduceBool` (native_decide).
- **Faithfulness** (manual read): the Lean statement and its definitions encode
  the erdosproblems.com problem, checked term by term.

| # | Claimed answer | Faithful | Proof gate | Notes |
|--:|----------------|:--------:|:----------:|-------|
| 254 | positive | yes | pass | `IsComplete` = every large m is a sum of distinct elements (Finset); both hypotheses (dyadic increment → ∞, phase sums → ∞ for all θ∈(0,1)) map exactly |
| 267 | positive | yes | pass | `Irrational (∑' 1/fib(nₖ))` for any positive strictly-increasing `n` with ratio gap `c>1`; `Nat.fib` matches `F₁=F₂=1` |
| 489 | positive | yes | pass | statement is Formal Conjectures' own `erdos_489` right-hand side, verbatim |
| 521 | negative | yes | pass | disproves a.s. `Rₙ/log n → 2/π`; genuine real roots (`rootSet ℝ` of the ±1 polynomial), `rademacherMeasure` proven `IsProbabilityMeasure`, negation via a positive-measure event.  The a.s. limit is itself open (only the *expected* count `~(2/π)log n` is a theorem), so a negative answer contradicts nothing proven |
| 538 | order Θ(log N/log log N) | yes* | pass | matching upper/lower bounds on `∑_{a∈A} 1/a` over admissible A.  *"best possible upper bound" is rendered as the asymptotic order, not a sharp constant |

Scope of the claim: a faithful statement plus a kernel-accepted `sorry`-free
proof.  The underlying mathematics was not re-derived by hand; kernel validity
rules out a logical gap, and the faithfulness read rules out a mis-stated
theorem, but neither is a substitute for mathematical peer review — especially
for 521 (a negative answer) and 538 (an order claim).

These proofs are Colin Snyder's (Star Fleet Math), not this repo's.
