# Erdős #699 Progress

## 2026-07-05

- [E] Added exact Python tests for the corrected counterexample criterion. The
  tests explicitly check that primes below `i` are free in the obstruction set.
  Reproduce with: `python3 -m pytest compute/tests/test_criterion.py -q`.
- [E] Added and optimized a reproducible exact full-sweep scanner
  `python3 -m compute.scan --limit 2000`. The scan uses the corrected
  Lucas obstruction criterion with bitset domination masks, checks all triples
  `1 ≤ i < j ≤ n / 2` for `n ≤ 2000`, and returned `candidate_count = 0`
  over `332,833,500` triples. This is a local reproduction artifact only; it
  does not claim the historical `n ≤ 8000` perimeter.
- [E] Added a row-specialized exact scanner for fixed-`i` perimeters. The
  command `python3 -m compute.scan --limit 40000 --i 3 --row-scan` returned
  `candidate_count = 0` over `399,880,009` checked triples, and
  `python3 -m compute.scan --limit 30000 --i 4 --row-scan` returned
  `candidate_count = 0` over `224,880,016` checked triples. These reproduce
  the package's `i = 3` and `i = 4` row perimeters with the corrected
  `p ≥ i` obstruction criterion; they do not claim the historical all-row
  `n ≤ 8000` perimeter.
- [E] Added a factorization-backed CRT scanner for the structured family
  `n = 2^A * M`, `M ∈ {1,3,5,7,9,11,13,15,21,25}`. The command
  `python3 -m compute.scan --power-two-family --family-max-exponent 36 --i 3 --i 4 --i 5`
  returned `candidate_count = 0` across `981` row cells, representing
  `1,584,842,928,062` checked triples up to `2^36`; the maximum intermediate
  CRT state count was `18`. This reproduces the package's structured-family
  perimeter for rows `i ∈ {3,4,5}` using full Lucas domination verification on
  every CRT survivor.
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
- [R] Proved row-bound T6 row-one wrappers:
  `Erdos699.t_le_X_of_factorized_half_bound`,
  `Erdos699.i_three_caseI_row_one_sub_one_dvd_t_mul_X_sub_t_from_row_bound`,
  `Erdos699.i_three_caseI_row_one_exists_factor_from_row_bound`,
  `Erdos699.i_three_caseI_row_one_four_mul_sub_one_le_X_sq_from_row_bound`,
  and `Erdos699.i_three_caseI_row_one_four_mul_factor_le_X_from_row_bound`
  package the existing first-row divisibility, factor, square-bound, and
  cofactor-bound results under the original row condition `2 * j ≤ n`.
  Full T6/T7 remain open.
- [R] Proved row-bound T6/T7 row-two wrappers:
  `Erdos699.i_three_caseI_row_two_primePowerPartGE_dvd_t_mul_X_sub_t_mul_X_sub_two_t_from_row_bound`,
  `Erdos699.i_three_caseI_row_two_half_sub_one_dvd_t_mul_X_sub_t_mul_X_sub_two_t_from_row_bound`,
  `Erdos699.i_three_caseI_row_two_half_large_part_dvd_triple_from_row_bound`,
  `Erdos699.i_three_caseI_joint_large_part_dvd_factor_mul_X_sub_two_t_from_row_bound`,
  `Erdos699.i_three_caseI_joint_half_sub_one_dvd_factor_mul_X_sub_two_t_from_row_bound`,
  and `Erdos699.i_three_caseI_joint_half_sub_one_large_part_dvd_factor_mul_X_sub_two_t_from_row_bound`
  package the existing row-two divisibility and joint cancellation bridges
  under the original row condition `2 * j ≤ n`. The joint wrappers still keep
  the explicit row-one factor `t * (X - t) = g * (n - 1)`. Full T7 remains open.
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
- [R] Proved branch-free row-bound joint-row packages:
  `Erdos699.x_sub_two_t_pos_of_row_bound` derives `0 < X - 2 * t` from the
  original row condition `2 * j ≤ n`, `n = F * X`, `j = F * t`, and the
  central-branch contradiction. The wrappers
  `Erdos699.i_three_caseI_exists_joint_large_part_factor_le_from_row_bound`,
  `Erdos699.i_three_caseI_exists_joint_large_part_gap_bound_from_row_bound`,
  `Erdos699.i_three_caseI_exists_joint_large_part_cube_bound_from_row_bound`,
  `Erdos699.i_three_caseI_exists_joint_half_large_part_cube_from_row_bound`,
  and `Erdos699.i_three_caseI_half_large_part_cube_from_row_bound` remove the
  explicit non-central branch from the packaged joint-row consequences under
  the original row bound. The half-row lower-bound obstruction and full T7
  remain open.
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
- [R] Proved branch-free T7 factor-square wrappers:
  `Erdos699.i_three_caseI_factor_sq_squeeze_of_half_bound` combines the central
  branch contradiction with `Erdos699.i_three_caseI_noncentral_factor_sq_squeeze`
  under `2 * t ≤ X`, removing the explicit `0 < X - 2 * t` input while still
  assuming `n / 2 - 1 ≤ primePowerPartGE 5 (n - 2)`. The coprime-to-4 version
  `Erdos699.i_three_caseI_factor_sq_squeeze_of_half_coprime_four` does the same
  for `(n / 2 - 1).Coprime 4`. Full T7 remains open.
- [R] Proved row-bound T7 factor-square wrappers:
  `Erdos699.two_mul_t_le_X_of_factorized_half_bound` derives the normalized
  `2 * t ≤ X` hypothesis from the original row bound `2 * j ≤ n`, using
  `n = F * X`, `j = F * t`, and `0 < j` to cancel the positive factor `F`.
  `Erdos699.i_three_caseI_factor_sq_squeeze_of_half_bound_from_row_bound` and
  `Erdos699.i_three_caseI_factor_sq_squeeze_of_half_coprime_four_from_row_bound`
  package the existing branch-free wrappers under the original row-bound
  hypothesis. Full T7 remains open.
- [R] Proved the `4 ∣ n` half-row wrapper:
  `Erdos699.half_sub_one_coprime_four_of_four_dvd` shows that
  `(n / 2 - 1).Coprime 4` is automatic when `4 ∣ n` and `2 < n`, and
  `Erdos699.i_three_caseI_factor_sq_squeeze_of_four_dvd_from_row_bound`
  removes the explicit coprime-four hypothesis from the row-bound
  factor-square squeeze in this subcase. Full T7 remains open.
- [R] Proved the `4 ∣ n` full half-row package:
  `Erdos699.primePowerPartGE_five_half_sub_one_eq_self_of_four_dvd_three_dvd`
  identifies the large-prime part with all of `n / 2 - 1` when `4 ∣ n`,
  `3 ∣ n`, and `2 < n`. The wrappers
  `Erdos699.i_three_caseI_exists_joint_half_sub_one_cube_from_four_dvd_row_bound`
  and `Erdos699.i_three_caseI_half_sub_one_cube_from_four_dvd_row_bound`
  upgrade the existing row-bound large-prime-part cube package to the full
  half-row cube inequality in this subcase. Full T7 remains open outside this
  `4 ∣ n` branch.
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
- [R] Proved odd-cofactor parity wrappers for the normalized `4 ∣ n` Case-I
  branch: `Erdos699.four_dvd_right_factor_of_four_dvd_mul_odd` shows `4 ∣ X`
  from `Odd F` and `4 ∣ F * X`;
  `Erdos699.i_three_caseI_row_one_four_mul_factor_le_X_of_four_dvd_odd_factor_from_row_bound`
  and
  `Erdos699.i_three_caseI_factor_sq_squeeze_of_four_dvd_odd_factor_from_row_bound`
  remove the explicit `X` parity inputs from the row-one cofactor and
  factor-square squeezes under the odd-cofactor normalization. Full T7 remains
  open.
- [R] Bundled the normalized `4 ∣ n`, odd-cofactor Case-I T7 branch:
  `Erdos699.i_three_caseI_four_dvd_odd_factor_joint_package_from_row_bound`
  packages the row-one factor, the half-row divisor/size condition, the
  half-row cube inequality, and both normalized squeeze inequalities. The
  projection
  `Erdos699.i_three_caseI_four_dvd_odd_factor_joint_squeeze_from_row_bound`
  returns `4 * F ≤ X ∧ 2 * (F * F) ≤ X`. This is a branch package, not full
  T7.
- [R] Formalized the consecutive-divisor kernel target:
  `Erdos699.consecutiveDivisorKernel` and
  `Erdos699.consecutiveDivisorKernelBelow` name the two-row kernel and the
  half-row-bounded version. The reduction
  `Erdos699.i_three_caseI_four_dvd_consecutive_kernel_below_from_no_common`
  shows that the `4 ∣ n` Case-I hypotheses force coprime factors
  `n - 1` and `n / 2 - 1` into this bounded kernel. This does not prove the
  kernel empty.
- [E] Added an exact CRT enumerator for the consecutive-divisor kernel:
  `compute.kernel.scan_kernel_crt` factors `N1`, enumerates the `{0,1}`
  residue choices for `N1 ∣ t(t-1)`, then filters
  `N2 ∣ t(t-1)(t-2)` under the half-row bound. Unit tests cross-check CRT
  output against brute force on small kernels. Reproduce the sample with
  `python3 -m compute.kernel --n1 15 --n2 14 --bound 120`; it reports
  `4` row-one CRT classes, `17` row-one candidates, and `8` survivors. This
  is an exact C2 enumerator, not a proof that the kernel is empty.
- [E] Extended the exact kernel enumerator with the problem lower bound and
  the `n = 3 * 2^A` Case-I family wrapper. Reproduce the lower-bound sample
  with `python3 -m compute.kernel --n1 15 --n2 14 --bound 120 --min-t 4`;
  it reports `15` row-one candidates and `6` survivors after excluding
  `t < 4`. Reproduce the small Case-I family scan with
  `python3 -m compute.kernel --case-i-power-two --max-exponent 12`; it checks
  exponents `2..12`, reports `5` total row-one candidates, and `0` kernel
  survivors. This is exact finite evidence for the C2 lane, not a kernel
  emptiness proof.
- [E] Replaced the kernel enumerator's trial-division factorization with
  deterministic 64-bit Miller-Rabin plus Pollard-Rho splitting, keeping exact
  integer arithmetic throughout. The command
  `python3 -m compute.kernel --case-i-power-two --min-exponent 60 --max-exponent 60`
  now scans the Case-I family member `n = 3 * 2^60` locally and reports
  `1` row-one candidate and `0` kernel survivors. This is exact finite
  evidence for the C2 lane, not a proof that the kernel is empty.
- [OPEN] T4, full T6/T7, the kernel, and all later rungs remain unclaimed in
  this branch.
