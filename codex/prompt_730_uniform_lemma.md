# Prompt: the uniform incomplete-block digit-count lemma (Erdős #730)

## Current task statement

An audited proof skeleton (compute730/audit.md in
williamjblair/lean-proofs) reduces "infinitely many consecutive pairs
(n, n+1) whose central binomial coefficients share prime support" to
ONE missing analytic lemma plus bookkeeping. Prove:

TARGET. For the quadratic-family maps G (the audited p-adic isometries
b_L = ±2·3²·41²·43 / ±2·3²·41·43², explicit in the audit), primes
p ∉ {2, 3, 41, 43}, branch parameters a ≥ 1, and intervals I with
|I| ≥ p^r · polylog(p^r):
  #{k ∈ I : the first 2r base-p digits of G(k) are restricted}
    ≤ 4^{−r} (1 + 1/p)^{2r} |I| (1 + o(1)),
UNIFORMLY in p, branch, a, and congruence class — including INCOMPLETE
blocks — with the o(1) explicit. Then verify the range-split first
moment: summed over all obstruction primes and branches as in the
audit's sieve, the total is < 1 − δ for explicit δ > 0. (The audit
computed that the naive quantification gives ≈ 1.2 > 1: the lemma must
beat the trivial completion bound in the middle range and the sieve
constant in the top range; empirical headroom is ≈ 40%, measured
E[#obstructions] = 0.597 at x ≤ 3000.)

## Verified context (all machine-checked; details and exact formulas
in compute730/audit.md)

- Kummer transition criterion: exact, verified against brute force for
  all n ≤ 2000 and all known pairs. Supports agree iff explicit
  digit-domination conditions hold at every odd prime-power divisor of
  n+1 and 2n+1.
- The family n+1 = PQ, 2n+1 = 3RS with the five linear identities
  (12P−7Q = 41 etc.): all verified symbolically; each obstruction
  prime hits exactly one branch; p = 3 harmless.
- The p-adic permutation lemma: G is a p-adic isometry for
  p ∉ {2,3,41,43}; complete blocks need no Fourier analysis (counts
  exact). Verified on random (branch, p, a).
- Top range p > L^{2/3}: obstructions degenerate to explicit
  congruences (c ≡ 3,4 mod 7; c ≡ 5,9 mod 14); needs only a sieve
  upper bound whose constant enters the budget.
- 1,556 unconditionally certified consecutive pairs exist (smallest
  family member n = 338,381,863,522) — the conclusion is not vacuous.

## Falsification record / known failure point

The phrase "essentially 4^{−r}" is precisely square-root-critical:
the digit condition is mod p^{2r} on blocks of length p^r, where
generic exponential-sum completion is vacuous. Any proof must exploit
the specific structure (quadratic coefficient divisible by p^a ⟹
sparse surviving frequencies after the isometry; the audit sketches
this). Do NOT return an argument whose uniformity in incomplete
intervals or whose union-bound bookkeeping is asserted rather than
computed — that is exactly where the original private argument fails
the public record. The final budget must be a verified numerical
inequality with all constants explicit.

## Orchestration

Portfolio: complete-sum vanishing + sparse-frequency completion;
Weil/Salié bounds for the specific quadratic phases; van der Corput on
the short ranges; elementary large-sieve variants for the top range.
Adversarial audit: instantiate every claimed bound at p = 5, 7, 11
against exact counts (the audit's diagnostics reproduce them). Return
the lemma with explicit constants and the closed budget, or the
strongest proved sub-range with the exact residual gap. At least 4
hours before any return. Public search for standard analytic number
theory only.
