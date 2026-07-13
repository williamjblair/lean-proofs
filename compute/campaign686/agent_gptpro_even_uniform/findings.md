# GPT Pro centered-interval passes: exact findings

## Verdict

The newest pass does not solve the full uniform residual, but its interval-lcm
reframing is valid and yields a substantially stronger theorem than stated.
The evenness hypothesis is unnecessary:

```text
k >= 16,  k <= d,  18*d <= k^2
  -> blockProduct k (n+d) != 4*blockProduct k n
```

This is proved in ordinary-kernel Lean as
`no_four_solution_of_quadratic_strip`, for both row parities.  Its hypothesis
is first nonempty at `(k,d)=(18,18)`.  The exact cross-multiplied certificate
is `quadratic_strip_certificate`.

The earlier pass splits as follows.

- The one-factorial lcm compression (D) was already banked exactly as
  `blockProduct_dvd_factorial_mul_centeredDiffLcm_four`; it is reused.
- The reflected square lift underlying (B) was already banked.  Exact
  reflection geometry gives the sharper new bound `2*q^2 < 5*H`, hence the
  stronger cofactor exclusion `5*a <= 2*q`.
- The centered gcd restriction (C) is correct and new.
- The logarithmic strip (A) is correct, parity-free, and new.  The module also
  proves the stronger logarithmic endpoint
  `3*d <= k*(floor(log2 k)-4)`.
- The newest interval theorem
  `m! * L(a,...,a+m-1) | product(a,...,a+m-1) * lcm(1,...,m)`
  is correct.  Together with the new sharp elementary bound
  `lcm(1,...,m) <= 4^m`, it supplies the quadratic strip.

The exact remaining large-row region is now `18*d > k^2`, subject to all
other banked owner, smoothness, component, and matching restrictions.  No
global contradiction-producing owner or aggregation theorem is supplied for
that region.

## New Lean surface

`ErdosProblems/Erdos686CenterComponentLogStrip.lean` proves, among other
supporting lemmas:

- `gcd_gap_reflectionCenter_dvd_oddDoubleFactorial`;
- `prime_ge_row_dvd_gap_not_dvd_reflectionCenter`;
- `even_large_prime_reflection_center_power_two_sq_lt_five_center`;
- `no_four_solution_of_even_dominant_reflection_center_component` and its
  cofactor forms;
- `initialLcm_le_eight_pow` and the sharper `initialLcm_le_four_pow`;
- `factorial_mul_intervalLcm_dvd_ascFactorial_mul_initialLcm`;
- `factorial_mul_centeredDiffLcm_dvd_centeredDiffProduct_mul_initialLcm`;
- `centeredDiffProduct_lt_gap_pow`;
- the even and odd factorial-tail pairing bounds;
- `factorial_scaled_ratio_lt_interval_bound_of_solution`;
- `quadratic_strip_certificate`;
- `no_four_solution_of_quadratic_strip`;
- `no_four_solution_of_extended_logarithmic_strip`;
- `no_four_solution_of_logarithmic_strip`.

All printed headline theorems have axiom set
`[propext, Classical.choice, Quot.sound]`.  The module contains no
`native_decide`.

## Corrections and strengthenings to the submitted prose

1. The newest boxed theorem was stated only for even `k`.  The same pairing
   closes odd `k`: pair the `2r` extreme tail terms and retain the one
   unpaired term, which is at least `k`.  Thus the proved result is
   parity-free.
2. The nominal threshold `k>=16` has an empty gap range at `k=16,17`; the
   first nonempty boundary is exactly `(18,18)`.
3. The submitted interval valuation argument is valid.  The Lean proof uses
   Kummer carries to show each interval term divides
   `choose(a+m-1,m)*lcm(1,...,m)`, then restores the factorial by the exact
   ascending-factorial identity.
4. The standalone boxed B statement from the earlier pass is false without
   inherited hypotheses.  The exact counterexample is `(k,n,d)=(3,0,1)`:
   the quotient is four, `H=5`, and `23<=8*5`.
5. The earlier square-lift core is not new.  Reflection sharpens
   `8*q^2<23*H` to `2*q^2<5*H` because
   `H-2(n+i)=d+k+1-2i>=1`.
6. The earlier implication `floor(x)>=6x/7` from only `x>=1` is false, and
   its `(N+1)^2<=2^N` step omitted an induction.  The formal proofs avoid
   both gaps.
7. Every computational reproduction now uses Python integers only; no
   floating point is used.

## Exact reproduction

Run:

```text
PYTHONDONTWRITEBYTECODE=1 python3 \
  compute/campaign686/agent_gptpro_even_uniform/even_uniform_verify.py \
  --max-k 2000 --max-n 1000
PYTHONDONTWRITEBYTECODE=1 python3 -m pytest -q -p no:cacheprovider \
  compute/campaign686/agent_gptpro_even_uniform/test_even_uniform_verify.py
lake env lean ErdosProblems/Erdos686CenterComponentLogStrip.lean
```

The exact verifier checks:

- both initial-lcm recurrences and `Lambda(N)<=4^N` through `N=1000`;
- 2,400 direct interval factorial-lcm divisibilities;
- 5,946 sampled cross-multiplied quadratic certificates across every row
  `16<=k<=2000`, including both parities;
- the exact first nonempty boundary `(18,18)`;
- both named prefix fixtures, which now lie inside the quadratic strip;
- the row-22 pseudo-fixture, which lies outside it;
- both logarithmic strips, the centered gcd fixtures, and the strict
  reflection boundary `d=k,i=k`.
