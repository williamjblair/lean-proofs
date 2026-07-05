# Erdős #699 Progress

## 2026-07-05

- [E] Added exact Python tests for the corrected counterexample criterion. The
  tests explicitly check that primes below `i` are free in the obstruction set.
  Reproduce with: `python3 -m pytest compute/tests/test_criterion.py -q`.
- [R] Added Lean definitions `Erdos699.digit`, `Erdos699.dominated`, and
  `Erdos699.relevantPrime`, plus theorem
  `Erdos699.relevantPrime_ignores_small`. Reproduce with:
  `lake build Erdos699`.
- [R] Proved `Erdos699.dominated_iff_forall_mem_range`,
  `Erdos699.dominated_iff_forall_digits`, and
  `Erdos699.lucas_nonzero_mod_prime_iff_dominated`, giving the first
  sorry-free Lucas bridge for the decidable digit-domination predicate.
- [R] Proved `Erdos699.t1_i_eq_one`: for `2 ≤ j` and `2 * j ≤ n`, there is
  a prime common divisor of `C(n,1)` and `C(n,j)`.
- [R] Proved the top-range lemma
  `Erdos699.commonPrimeDivisor_of_prime_in_top_interval`: if `p` is prime,
  `n - i < p ≤ n`, `i < j`, and `2 * j ≤ n`, then `p` is a relevant common
  prime divisor of `C(n,i)` and `C(n,j)`.
- [R] Proved T3 confinement consequences
  `Erdos699.t3_top_interval_prime_free_of_no_common` and
  `Erdos699.t3_no_large_prime_dvd_fallingWindowProduct_of_no_common`: under a
  no-common-prime hypothesis, `(n - i, n]` is prime-free and no prime
  satisfying `n < 2 * p` divides the numerator window
  `Erdos699.fallingWindowProduct n i`.
- [R] Proved `Erdos699.no_commonPrimeDivisor_iff_obstructionCriterion`, the
  formal corrected counterexample criterion. The predicate quantifies over
  `relevantPrime i p`, so primes `p < i` impose no digit-domination condition.
- [R] Proved `Erdos699.t2_collapse_of_no_common`: under the no-common-prime
  assumption for row `i = 2`, `2 < j`, and `2 * j ≤ n`, the obstruction
  collapses to `n = 2 * j` with `j` odd.
- [R] Proved full T2 as `Erdos699.t2_i_eq_two`: for `2 < j` and
  `2 * j ≤ n`, there is a prime `p ≥ 2` dividing both `C(n,2)` and `C(n,j)`.
- [OPEN] T4 and all later rungs remain unclaimed in this branch.
