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
- [R] Proved T5 no-large-window-prime bridge lemmas
  `Erdos699.no_prime_ge_five_dvd_sub_one_of_no_common_eq_three_mul` and
  `Erdos699.no_prime_ge_five_dvd_sub_two_of_no_common_eq_three_mul`: under
  the row-3 no-common-prime hypothesis and `n = 3 * j`, no prime `p ≥ 5`
  divides `n - 1` or `n - 2`. Full T5 remains open.
- [R] Proved the conditional T5 endpoint
  `Erdos699.eq_three_of_no_common_eq_three_mul` and contradiction theorem
  `Erdos699.no_common_eq_three_mul_false_of_two_le`: under row-3
  no-common-prime, `n = 3 * j`, and `2 ≤ j`, the branch is impossible. This
  is the endpoint used by the full T5 Case I-A0 proof below.
- [R] Proved full T5 Case I-A0 as
  `Erdos699.t5_i_eq_three_odd_three_exactly_once`: for row `i = 3`,
  `n` odd, `3 ∣ n`, `¬ 9 ∣ n`, `3 < j`, and `2 * j ≤ n`, a relevant common
  prime divisor exists.
- [R] Proved first T6 digit-layer support for the `n - 1` row:
  `Erdos699.digit_zero_eq_one_of_pow_dvd_sub_one`,
  `Erdos699.digit_eq_zero_of_pow_dvd_sub_one`, and row-3 transfer lemmas
  forcing `j`'s units digit to be at most `1` and levels `1..e-1` to vanish
  when `p^e ∣ n - 1`. Full T6 remains open.
- [R] Proved first T6 full-power forcing for the `n - 1` row:
  `Erdos699.i_three_window_one_prime_pow_dvd_mul_sub_one` shows that under
  row-3 no-common-prime hypotheses, every prime power `p^e ∣ n - 1` with
  `p ≥ 5` divides `j * (j - 1)`. Full T6 remains open.
- [R] Proved T6 full-power forcing for the `n - 2` row:
  `Erdos699.i_three_window_two_prime_pow_dvd_mul_sub_one_sub_two` shows that
  under row-3 no-common-prime hypotheses, every prime power `p^e ∣ n - 2`
  with `p ≥ 5` divides `j * (j - 1) * (j - 2)`. Full T6 remains open.
- [R] Proved T6 full-multiplicity large-prime-part packaging:
  `Erdos699.primePowerPartGE`,
  `Erdos699.i_three_window_one_primePowerPartGE_dvd`, and
  `Erdos699.i_three_window_two_primePowerPartGE_dvd` package the existing
  per-prime-power row forcing into full multiplicity for all primes `p ≥ 5`.
  Also proved the case-I row-one bridge
  `Erdos699.i_three_window_one_sub_one_dvd_mul_sub_one_of_even_three_dvd`.
  Full T6/T7 remain open.
- [R] Proved the T6 row-one algebra bridge:
  `Erdos699.i_three_caseI_row_one_sub_one_dvd_t_mul_X_sub_t` turns the
  case-I divisor `n - 1 ∣ j * (j - 1)` into the normalized form
  `n - 1 ∣ t * (X - t)` whenever `n = F * X`, `j = F * t`, and `t ≤ X`.
  Full T6/T7 remain open.
- [R] Proved the T6 row-two algebra bridge:
  `Erdos699.i_three_caseI_row_two_primePowerPartGE_dvd_t_mul_X_sub_t_mul_X_sub_two_t`
  turns the full-multiplicity large-prime part of the `n - 2` row into the
  normalized divisor `primePowerPartGE 5 (n - 2) ∣ t * (X - t) * (X - 2 * t)`.
  The theorem explicitly cancels only an odd divisor, so the row-3-free
  2-adic part remains outside the statement. Full T6/T7 remain open.
- [R] Proved the T6 row-one size squeeze:
  `Erdos699.i_three_caseI_row_one_four_mul_sub_one_le_X_sq` turns the
  normalized case-I divisor into `4 * (n - 1) ≤ X * X` under `2 * t ≤ X`.
  This is the exact-integer version of the `n - 1 ≤ X^2/4` bound. Full T6/T7
  remain open.
- [R] Proved the T6 row-one cofactor squeeze:
  `Erdos699.i_three_caseI_row_one_four_mul_factor_le_X` turns the row-one
  square bound into `4 * F ≤ X` when `n = F * X`, `2 ∣ X`, and `4 ≤ X`.
  This is the exact cofactor form of the first-row thin-family constraint.
  Full T6/T7 remain open.
- [R] Proved the T7 joint-row large-part cancellation:
  `Erdos699.i_three_caseI_joint_large_part_dvd_factor_mul_X_sub_two_t` shows
  that if `t * (X - t) = g * (n - 1)`, then the row-two large-prime part
  divides `g * (X - 2 * t)`. This banks the coprime cancellation core of the
  joint-row squeeze; full T7 remains open.
- [R] Proved the T7 row-one factor-existence wrapper:
  `Erdos699.i_three_caseI_row_one_exists_factor` packages row-one divisibility
  as an explicit `g` with `t * (X - t) = g * (n - 1)`, and
  `Erdos699.i_three_caseI_exists_joint_large_part_factor` combines that factor
  with the row-two large-prime-part cancellation. This states the usable joint
  system for later kernel work; full T7 remains open.
- [R] Proved the T7 non-central large-part size bound:
  `Erdos699.i_three_caseI_joint_large_part_le_factor_mul_X_sub_two_t` and
  `Erdos699.i_three_caseI_exists_joint_large_part_factor_le` show that on the
  explicit branch `0 < X - 2 * t`, the row-two large-prime part is at most
  `g * (X - 2 * t)`. The central branch `X = 2 * t` and full T7 remain open.
- [R] Proved the T7 non-central gap product bound:
  `Erdos699.i_three_caseI_joint_large_part_gap_bound` and
  `Erdos699.i_three_caseI_exists_joint_large_part_gap_bound` combine the
  row-one parabola bound with the large-part size bound to get
  `4 * ((n - 1) * primePowerPartGE 5 (n - 2)) ≤ X * X * (X - 2 * t)` on the
  explicit branch `0 < X - 2 * t`. Full T7 remains open.
- [R] Proved the T7 non-central cube squeeze:
  `Erdos699.i_three_caseI_joint_large_part_cube_bound` and
  `Erdos699.i_three_caseI_exists_joint_large_part_cube_bound` weaken the gap
  product bound to `4 * ((n - 1) * primePowerPartGE 5 (n - 2)) ≤ X * X * X`.
  `Erdos699.i_three_caseI_joint_lower_part_cube_bound` and
  `Erdos699.i_three_caseI_joint_half_sub_one_cube_bound` also specialize this
  under an explicit lower bound on `primePowerPartGE 5 (n - 2)`. The half-row
  lower bound and full T7 remain open.
- [R] Proved the packaged T7 half-row cube bound:
  `Erdos699.i_three_caseI_exists_joint_half_sub_one_cube_bound` packages the
  row-one factor together with the conditional half-row squeeze, and
  `Erdos699.i_three_caseI_noncentral_half_sub_one_cube_bound` projects the
  inequality alone. The required lower bound
  `n / 2 - 1 ≤ primePowerPartGE 5 (n - 2)` remains an explicit open input.
- [R] Proved the T7 non-central factor-square squeeze:
  `Erdos699.two_mul_factor_sq_le_of_even_half_cube_bound` converts the half-row
  cube inequality into `2 * (F * F) ≤ X` when `n = F * X` and `X` is even.
  `Erdos699.i_three_caseI_noncentral_factor_sq_squeeze` packages this for the
  case-I counterexample hypotheses, still assuming the explicit half-row
  lower bound and non-central branch. Full T7 remains open.
- [R] Proved the direct coprime-to-4 half-row squeeze:
  `Erdos699.i_three_caseI_noncentral_factor_sq_squeeze_of_half_coprime_four`
  replaces the explicit lower-bound input
  `n / 2 - 1 ≤ primePowerPartGE 5 (n - 2)` with
  `(n / 2 - 1).Coprime 4`. The supporting lemmas prove
  `n / 2 - 1 ∣ n - 2`, exclude prime divisors `2` and `3` under
  `2 ∣ n`, `3 ∣ n`, and `2 < n`, then force
  `n / 2 - 1 ∣ g * (X - 2 * t)` from the corrected `p ≥ i` row-two
  condition. The non-central branch and full T7 remain open.
- [R] Proved the T7 half-row large-prime-part squeeze:
  `Erdos699.i_three_caseI_half_sub_one_large_part_dvd_row_two_product` shows
  that the forced divisor `primePowerPartGE 5 (n / 2 - 1)` divides
  `j * (j - 1) * (j - 2)`. The normalized and joint-row endpoints
  `Erdos699.i_three_caseI_row_two_half_sub_one_large_part_dvd_t_mul_X_sub_t_mul_X_sub_two_t`,
  `Erdos699.i_three_caseI_joint_half_sub_one_large_part_dvd_factor_mul_X_sub_two_t`,
  `Erdos699.i_three_caseI_joint_half_sub_one_large_part_gap_bound`, and
  `Erdos699.i_three_caseI_joint_half_sub_one_large_part_cube_bound` push this
  2-adic-free half-row factor through the row-two congruence bridge and the
  row-one cancellation. This intentionally does not claim the missing power of
  `2`; full T7 remains open.
- [R] Proved the packaged T7 half-row large-prime-part cube bound:
  `Erdos699.i_three_caseI_exists_joint_half_sub_one_large_part_cube_bound`
  introduces the row-one factor `g` and packages divisibility, size, and cube
  bounds for `primePowerPartGE 5 (n / 2 - 1)`. The projection theorem
  `Erdos699.i_three_caseI_noncentral_half_sub_one_large_part_cube_bound`
  returns the cube inequality alone on the non-central branch. This remains a
  2-adic-free half-row factor theorem, not full T7.
- [R] Proved the T7 central branch kill:
  `Erdos699.central_branch_false_of_sub_one_dvd_t_mul_X_sub_t` shows that
  `2 * t = X` contradicts the row-one divisor `n - 1 ∣ t * (X - t)` when
  `n = F * X` and `2 < n`; `Erdos699.i_three_caseI_central_branch_false`
  packages this under the case-I row-one hypotheses. Full T7 remains open.
- [OPEN] T4, full T6/T7, the kernel, and all later rungs remain unclaimed in
  this branch.
