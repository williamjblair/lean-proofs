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
- [R] Proved the T5 elementary endpoint
  `Erdos699.eq_three_of_sub_one_sub_two_twoPowers`: if `n - 1` and `n - 2`
  are both powers of two, then `n = 3`. Full T5 remains open.
- [R] Proved `i = 3` window digit-forcing support lemmas
  `Erdos699.i_three_window_one_digit_forcing` and
  `Erdos699.i_three_window_two_digit_forcing`: under a no-common-prime
  hypothesis, primes `p ≥ 5` dividing `n - 1` force `j % p ≤ 1`, and primes
  `p ≥ 5` dividing `n - 2` force `j % p ≤ 2`. Full T4/T5 remain open.
- [R] Proved product-forcing support lemmas
  `Erdos699.dvd_mul_sub_one_of_mod_le_one`,
  `Erdos699.dvd_mul_sub_one_sub_two_of_mod_le_two`,
  `Erdos699.i_three_window_one_product_forcing`, and
  `Erdos699.i_three_window_two_product_forcing`. These turn the existing
  `i = 3` residue bounds into divisibility by `j * (j - 1)` and
  `j * (j - 1) * (j - 2)`. Full T4/T5 remain open.
- [R] Defined `Erdos699.primeRadicalGE` and proved
  `Erdos699.i_three_window_one_primeRadicalGE_dvd` and
  `Erdos699.i_three_window_two_primeRadicalGE_dvd`, packaging the `i = 3`
  per-prime window forcing as radical divisibility for all primes `p ≥ 5`
  dividing `n - 1` and `n - 2`. Full T4/T5 remain open.
- [R] Proved T5 residue-kill support lemmas
  `Erdos699.no_prime_ge_five_dvd_three_mul_sub_one_of_dvd_mul_sub_one` and
  `Erdos699.no_prime_ge_five_dvd_three_mul_sub_two_of_dvd_triple`: in the
  `n = 3 * j` branch, a prime `p ≥ 5` cannot divide both the relevant window
  row and the forced product. Full T5 remains open.
- [OPEN] T4 and all later rungs remain unclaimed in this branch.
