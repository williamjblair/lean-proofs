---
id: F-013
title: Uniform linear Turán scale and matching linear obstruction
tier: lean
polarity: positive
depends_on: [F-001, F-002]
supersedes: []
verifier: check_answer/check.sh verified_math/F-013_turan-linear-scale
date: 2026-07-12
---

## Statement

For every real `ε > 0`, choose a finite set `Sε` of primes at least five such
that

\[
  \mu_\epsilon:=\sum_{p\in S_\epsilon}\frac1p>\frac{152}{\epsilon},
  \qquad
  Q_\epsilon:=\prod_{p\in S_\epsilon}p^2.
\]

Such a set exists because the sum of the reciprocals of the primes diverges.
Then the **linear** threshold

\[
  Y(\epsilon,n)=n\,(Q_\epsilon+2)
\]

is sufficient in the pinned uniform sense: for every `ε > 0`, all sufficiently
large `n`, every `y ≥ Y(ε,n)`, and every natural translate `x`, at most `ε y`
integers in the open interval `(x,x+y)` have a divisor in `(n,2n)`.

The principal formal theorem is

```lean
theorem turanLinearAnswer_isSufficientScale :
    IsSufficientScale turanLinearAnswer
```

where `turanLinearAnswer ε n = n * (primeSquarePeriod (turanPrimeSet ε) + 2)`.
Thus, for each fixed positive `ε`, the required scale is `O_ε(n)`.

This order is sharp for every fixed `0 < ε < 1`.  Formally,

```lean
theorem sufficientScale_eventually_gt_n
    (Y : ℝ → ℕ → ℕ) (hY : IsSufficientScale Y)
    (ε : ℝ) (hεpos : 0 < ε) (hεone : ε < 1) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → n < Y ε n
```

so every sufficient eventual threshold is `Ω(n)`.

## Proof / verification

For a finite selected-prime set `S`, let `U(m)` count selected primes dividing
`m`, and let `W(m)` count both `p | m` and the extra events `p² | m`.  Both are
periodic modulo `Q=∏_{p∈S}p²`.  Exact first and second moments over one period
give

\[
 \sum_{m<Q}(U(m)-\mu)^2\le Q\mu,
 \qquad \mu=\sum_{p\in S}1/p.
\]

Chebyshev therefore bounds the low-score set `U≤3μ/4` by `16Q/μ` per
period.  The product inequality

\[
 U(d)+U(k)\le W(dk)
\]

and a Markov bound for selected prime squares bound the high set `W≥3μ/2` by
`28Q/μ` per period.  Periodicity transfers both estimates to arbitrary
intervals with one boundary-period loss.

Write a bad integer as `m=d k` with `n<d<2n`.  It belongs to one of three
classes: `d` has low score, `k` has low score, or `m` has high two-level score.
Uniform union bounds for these classes, valid when `Q≤n` and
`y≥n(Q+2)`, are respectively

\[
 64y/\mu,\qquad 32y/\mu,\qquad 56y/\mu.
\]

Hence the total bad count is at most `152y/μ≤εy`, uniformly in the translate.
Mathlib's formal theorem that prime reciprocals are not summable supplies a
finite `Sε` with `μ>152/ε`.  The lower bound uses the F-002 factorial translate:
at length `y=n` it contains exactly `n-1` bad integers, which violates the
target eventually whenever `ε<1`.

Proof artifacts:

- `Research/TuranScores.lean`: score/product inequality, exact moments,
  Chebyshev/Markov estimates, and arbitrary-interval periodic transfer.
- `Research/TuranLocal.lean`: three-class decomposition and the uniform
  `152y/μ` local bound.
- `Research/PrimeSelection.lean`: finite large reciprocal-prime set from
  divergence of `∑p 1/p`.
- `Research/TuranAnswer.lean`: the `IsSufficientScale` theorem and matching
  eventual linear lower obstruction.
- `Research/Basic.lean`, `DenseBlock.lean`, `PeriodicBounds.lean`, and
  `MobiusDiscrepancy.lean`: self-contained definitions and supporting interval
  lemmas.

The verifier rejects `sorry`, `admit`, local axioms, and unsafe declarations,
then runs a standalone Lean/Mathlib build.
