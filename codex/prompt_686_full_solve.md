# Prompt: complete the refutation of Erdős #686

> **2026-07-10 campaign update.**  Global residual concentration plus exact
> second/third local lifts now exclude every odd-tail gap with one or exactly
> two distinct prime divisors, uniformly including bases `2` and `3`.  Any
> surviving Target 1 gap therefore has at least three distinct prime divisors.
> The obstruction argument closes any two-owner grouping under the exact
> all-prime loss `G_k`, and the finite factorization interface is now
> kernel-banked.  Global concentration constructs one certified assignment;
> at target size its nonzero cleaned owner range cannot be covered by two
> indices.  For Target 2, reflection and matching owners now correlate: every
> residual reflection-center power divides the absolute owner offset, with
> reflected alignment as the exact surviving alternative.
> For three cleaned residual buckets, cyclic second/third obstruction formulas
> are kernel-banked and hostile-audited, but a 121-digit CRT non-solution shows
> that the congruences alone do not enforce the verified short window.  The
> exact next three-bucket node is the quantified short-CRT lemma in
> `compute/campaign686/three_bucket_findings.md`; Target 1 itself remains open.

## Current task statement

For naturals k, n, m write B(k, x) = (x+1)(x+2)···(x+k). Erdős
problem #686 asks whether every integer N ≥ 2 is representable as
B(k, m)/B(k, n) with k ≥ 2 and m ≥ n + k. The refutation via N = 4 is
machine-verified (Lean 4, kernel axioms only) down to EXACTLY TWO
statements. Prove both:

TARGET 1 (six odd tails). For each odd k ∈ {5, 7, 9, 11, 13, 15}:
there are no naturals n, d with d ≥ 10^120 and
B(k, n+d) = 4 · B(k, n).

TARGET 2 (large-k double smoothness). For every k ≥ 16 and naturals
n, d with k ≤ d and B(k, n+d) = 4 · B(k, n): NOT every element of
{n+1, ..., n+k} is (d+k)-smooth (i.e., some n+i has a prime factor
≥ d + k).

A complete solution proves both targets, with all constants explicit
and every analytic estimate quantified. Either target alone is a
substantial partial return. Proving Target 1 for even one new k, or
Target 2 for a restricted-but-unbounded regime (e.g. all d ≥ f(k)),
counts as rigorous partial progress and should be reported as such at
the end of budget — but do not return early for it.

## Verified context you may rely upon (all kernel-checked in
williamjblair/lean-proofs, main; statements in FRONTIER.md)

- Any solution has k odd in [5,15] with d ≥ 10^120, or k ≥ 16: all
  other cases are unconditionally closed (even k ≤ 14 fully; odd
  k ≤ 15 for d < 10^120 by Stern–Brocot/Farey-descent certificates;
  k ≤ 4 classically).
- Centered form (odd k): with X = n+d+(k+1)/2, Y = n+(k+1)/2 and
  P_k(T) = T·∏_{j=1}^{(k-1)/2}(T² − j²), the equation is
  P_k(X) = 4·P_k(Y), and it forces |4^{1/k} − X/Y| ≤ C_k/Y² with
  exact rationals C₅ = 61/100, C₇ = 399/500, C₉ = 1031/1000,
  C₁₁ = 13/10, C₁₃ = 3/2, C₁₅ = 1729/1000. Hence X/Y is a
  quasi-convergent of 4^{1/k} (explicit finite classes per CF index).
  Telescope caveat: k = 9, 15 admit d = 1 polynomial identities
  (P₉(8) = 4·P₉(7)); the domain d ≥ k excludes them.
- Prime obstruction (proved, 5 lines): a prime q ≥ d + k dividing any
  element of either block refutes the equation. This is why Target 2
  is phrased as smoothness.
- Window: any solution has n + 1 within a band of exact width k
  around c(k)·d, c(k) = 1/(4^{1/k} − 1); for k ≥ 16,
  c(k) ≈ 0.7213·k + 0.5, so block elements are ≈ 0.72·k·d with
  smoothness bound only d + k — Dickman-heuristically ρ(u)^k-rare,
  u ≈ 1 + log(0.72k)/log(d+k).
- Rows: any solution satisfies n+j | ∏_{i=1..k}(d+i−j) for all
  j ≤ k; for p > k each prime power p^e | n+j must divide a single
  element of a length-k sliding window [d+1−j, d+k−j].

## Falsification record — do not attempt these routes

- Effective irrationality measures below Liouville for 4^{1/k} at odd
  k ∈ {5,...,15} do not exist; the hypergeometric (Padé) method fails
  STRUCTURALLY at these exponents (verified against Bennett's
  criteria; representations like 4^{4/5} = 3·(256/243)^{1/5} miss the
  convergence condition by orders of magnitude). Only k = 6 (2^{1/3},
  measure 2.45) and k = 12 (≤ 4.9) exist, and those k are already
  closed. A proof of Target 1 must find leverage beyond generic
  rational approximation: e.g. exploit that the coincidence
  P_k(X) = 4·P_k(Y) at a convergent forces an exact integer identity
  against the CF remainder — a Thue-inequality-with-structure, not a
  Thue inequality.
- Baker–Feldman closes Target 1 on paper but with bounds ~10^(10^500):
  acceptable ONLY if you can make the constants small enough to meet
  the certificates at 10^120 (nobody has); otherwise it does not
  compose with the verified context.
- For Target 2: pure congruence/counting is dead. Gross log-mass
  counting fails (supply ≈ 2k·log d exceeds demand ≈ k·log(0.72kd)
  always). No congruence obstruction can exist in related settings
  (for (N,k) = (4,5) there are admissible solutions mod every M —
  MalekZ). Smoothness alone is also insufficient as a universal
  statement: smooth blocks of length k near 0.72kd plausibly exist;
  Target 2 may combine smoothness with the ROW structure (which the
  hypothesis grants you for free) — the census shows deep row-prefix
  survivors exist (n = 48502, n = 3177026 clusters) but none satisfy
  the full equation; the fixed-prefix boundary conjecture (rows 1..15
  ⟹ row 16 fails) is FALSE at (k, n, d) = (984, 3177026, 4480).
- Beukers–Shorey–Tijdeman finiteness (fixed k) is Siegel-ineffective:
  citing it proves nothing usable.

## Orchestration

Use the full multiagent budget with a diverse portfolio: p-adic /
valuation attacks, CF-remainder integer identities, unit equations in
ℚ(4^{1/k}), Runge-type expansions beyond the even-k square-root trick
(e.g. k-th root Puiseux with denominator control), double-smoothness
vs row-divisibility interplay for Target 2, Grimm-type matching
arguments with the window constraint, transfer between the two
targets. Maintain an approach registry; audit adversarially against
the falsification record above (especially: any claimed obstruction
must survive the (984, 3177026, 4480) and n = 48502 data points, the
d = 1 telescopes, and the MalekZ congruence family). Do not converge
early. Do not return a reduction of theorem-equivalent strength.
Spend at least 8 hours before considering any return.

Public search may be used for standard mathematical background only —
not to determine the status of Erdős #686 or to find this benchmark.
