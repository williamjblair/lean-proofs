# Prompt: the uniform incomplete-block digit-count lemma (Erdős #730)

## Current task statement — corrected after exact falsification

An audited proof skeleton (`compute730/audit.md`) reduces “infinitely many
consecutive pairs `(n,n+1)` whose central binomial coefficients share prime
support” to an incomplete-block estimate and a first-moment budget.

**The formerly stated uniform lemma is FALSE.**  Write

```text
H=(p+1)/2,  s=max(2r-a,0),  kappa_p=log_p(p/H).
```

On the admissible Q branch, taking `a=2r` makes
`G(k)=b_Q k+v (mod p^(2r))`.  Translating an interval and pigeonholing the
restricted `r`-digit outputs modulo `b_Q p` produces at least
`(H-1)H^(r-1)/(b_Q p)` exact-valuation hits in a span shorter than `p^r`.
This is exponentially larger than the old claimed main term even after the
interval is extended to `p^r` times any fixed polylogarithm.  More generally,
partitioning modulo `b_Q p^max(s,1)` gives failure whenever

```text
(p/H)^r p^(-s) / poly(r) -> infinity,
```

in particular throughout `s <= (kappa_p-epsilon)r` for fixed
`epsilon>0`.  See `compute730/campaign_uniform/uniformity_counterexample.md`.
This falsifies the analytic lemma, **not Erdős #730**.

**AUDITED REPAIR (Lean intake pending).**  With `C=2`, `eta=1/12`, and `r` chosen maximally from
the actual branch-class length, the whole near-affine band has normalized
first-moment contribution below `1/100` for every `X>=2^57`.  The proof is
in `compute730/campaign_uniform/repair/near_affine_payment_findings.md`; all
finite constants are reproduced with exact integer/rational tests.  Its
Lean/attestation step is not yet complete.  The maximal choice of `r` is
load-bearing.

**CORRECTED LIVE TARGET (OPEN).**  Prove one explicit separated-range
counting and short/top-range lemma with constants `B,delta>0`:

1. For every relevant prime, admissible branch/root, `a,r`, and interval
   `|I|>=p^r(log p^r)^2` in the separated range
   `s >= (kappa_p+eta)r`, prove an explicit incomplete-block estimate

   ```text
   #bad(I) <= (H/p)^(2r)|I|(1+(log p^r)^(-1)) + E_far(p,a,r,I),
   ```

   and prove that the normalized sum of `E_far` in the family sieve is
   bounded by an explicit constant.
2. Combine the far-range main terms and errors with a rigorous short/top
   range bound and verify

   ```text
   far main + far errors + short/top range <= 0.99-delta.
   ```

The displayed inequality is the single remaining campaign gate.  No
far-range estimate or closed budget satisfying it is currently claimed.

The exact Fourier reduction is now audited in
`compute730/campaign_uniform/repair/far/far_range_findings.md`.  If `E` is
the restricted output set with the exact-valuation least digit removed,
`F(h)=sum_(y in E)e(-hy/p^(2r))`, and
`S_I(h)=sum_(k in I)e(hG(k)/p^(2r))`, the separated estimate reduces to

```text
Re sum_(h!=0) F(h)S_I(h)
  <= |I| H^(2r) (1/H + 1/log(p^r)).
```

Sparse Gauss completion is proved with exact constants, but applying the
triangle inequality afterward is exponentially over this allowance for
each fixed `p=5,7,11`.  A proof must preserve signed cross-frequency
cancellation.  The proper long-interval subrange
`|I| >= (H-1)p^(2r)` is already proved but is noncritical.

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

The phrase “essentially `4^(-r)`” is square-root-critical, but the decisive
failure is stronger than a weak completion bound: in the near-affine band
the asserted density is mathematically false on adversarial translated
intervals.  Exact Q-branch scans retaining `p` not dividing `c(k)` give:

```text
p=5,  r=2, a=4:  6 hits > 4.2466 diagnostic RHS;
p=7,  r=3, a=6: 16 hits > 13.9873 diagnostic RHS;
p=11, r=2, a=4: 14 hits > 12.9441 diagnostic RHS.
```

The logarithmic RHS values are diagnostics; pytest clears the rational main
term denominator and uses exact integer assertions.  Sparse-frequency
completion may be pursued only outside the counterexample band.  Do not
return an argument whose interval uniformity or first-moment bookkeeping is
asserted rather than computed.  The final budget must be a verified numerical
inequality with all constants explicit.

## Orchestration

Portfolio: separate payment for the near-affine high-valuation band;
complete-sum vanishing + sparse-frequency completion only in the complementary range;
Weil/Salié bounds for the specific quadratic phases; van der Corput on
the short ranges; elementary large-sieve variants for the top range.
Adversarial audit: instantiate every claimed bound at p = 5, 7, 11
against exact counts (the audit's diagnostics reproduce them). Return
the lemma with explicit constants and the closed budget, or the
strongest proved sub-range with the exact residual gap. At least 4
hours before any return. Public search for standard analytic number
theory only.
