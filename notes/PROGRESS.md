# Erdős #699 Progress

## 2026-07-05

- [R]/[E] Corrected the normalized-branch trap record. The weakened
  all-quantified kill lemma with hypotheses `Odd F`, `3 ≤ F`, `4 ∣ X`,
  `0 < X - 2 * u`, `4 * F ≤ X`, `2 * F^2 ≤ X`, row one
  `u * (X - u) = g * (F * X - 1)`, and half-row divisibility is false without
  `0 < u`; exact zero-row counterexample:
  `(F, X, u, g) = (3, 20, 0, 0)`. More importantly, adding `0 < u` still does
  not make the global normalized kill true:
  `(F, X, u, g) = (3, 432184014644, 186954166997, 35360510289)` satisfies the
  row-one equation and half-row divisibility with `0 < u` and
  `0 < X - 2 * u`. Lean theorem
  `Erdos699.squeezedNormalizedCaseIKernel_counterexample_positive_t` proves
  this exact positive-row survivor of `Erdos699.squeezedNormalizedCaseIKernel`;
  Python regression
  `test_squeezed_normalized_predicate_has_positive_row_counterexample` verifies
  the same integer equalities. The corresponding original row-3 point has
  `n = 1296552043932`, `j = 560862500991`, and is killed by prime `5`;
  `Erdos699.squeezedNormalizedCounterexample_commonPrimeDivisor_five` proves
  `commonPrimeDivisor n 3 j 5`, while Python regression
  `test_normalized_positive_survivor_fails_original_row_three_digit_constraints`
  verifies the corrected Lucas obstruction criterion. This does not retract a
  banked theorem: the finite-list/gcd filters remain correct, but global
  emptiness of `squeezedNormalizedCaseIKernel` is false and must not be used
  as a kernel attack target without additional original-problem digit
  constraints.
- [E] Added an exact C1-style diagnostic that puts the original row-3 Lucas
  obstruction filter back on top of factorized normalized points:
  `compute.kernel.squeezed_candidate_original_row_three_obstructions(F, X, t,
  prime_limit)` checks primes `3 ≤ p ≤ prime_limit` for the original point
  `n = F * X`, `j = F * t`. For the positive normalized survivor above,
  `python3 -c 'from compute.kernel import squeezed_candidate_original_row_three_obstructions as f; print(f(3, 432184014644, 186954166997, 11))'`
  returns `[5, 11]`. The squeezed-normalized scanner also accepts
  `--original-obstruction-prime-limit`; reproduce a small diagnostic with
  `python3 -m compute.kernel --squeezed-normalized-case-i --max-f 3 --max-x 48 --include-candidate-diagnostics --original-obstruction-prime-limit 11`,
  which reports original row-3 obstruction primes `[3, 11]` for the single
  row-one candidate. This is exact finite-prime-cap evidence and tooling, not
  a proof that every normalized survivor is killed by digit constraints.
- [E] Extended the squeezed-normalized candidate summary with an exact
  original row-3 obstruction aggregate. Reproduce with
  `python3 -m compute.kernel --squeezed-normalized-case-i --max-f 9 --max-x 120 --include-candidate-summary --original-obstruction-prime-limit 11`;
  it reports `candidate_count = 7`, `with_obstruction_count = 7`,
  `without_obstruction_count = 0`, and first-obstruction histogram
  `{3: 5, 5: 1, 7: 1}`. This is still bounded finite evidence under a prime
  cap, not a global digit-compatibility theorem.
- [E] Added a single-candidate normalized/original classifier:
  `python3 -m compute.kernel --diagnose-squeezed-candidate --candidate-f 3 --candidate-x 432184014644 --candidate-t 186954166997 --candidate-g 35360510289 --original-obstruction-prime-limit 11`
  reports `row_one_holds = true`,
  `squeezed_normalized_case_i_kernel_holds = true`,
  `original_row_three_point_in_range = true`, and
  `original_row_three_obstruction_primes = [5, 11]`. This is the exact
  reproducible classification of the positive normalized survivor as outside
  the original no-common-prime surface under the checked finite cap.
- [E] Extended the single-candidate classifier with opt-in digit-level
  obstruction witnesses. Reproduce with
  `python3 -m compute.kernel --diagnose-squeezed-candidate --candidate-f 3 --candidate-x 432184014644 --candidate-t 186954166997 --candidate-g 35360510289 --original-obstruction-prime-limit 11 --include-original-obstruction-witnesses`;
  it reports for `p = 5` the failures `i` at level `0` with digits
  `3 > 2` and `j` at level `1` with digits `3 > 1`, and for `p = 11`
  the failures `i` at level `0` with digits `3 > 2` and `j` at level `1`
  with digits `10 > 2`. This is finite-cap diagnostic evidence, not a global
  digit-forcing theorem.
- [R] Proved the Lean digit-failure bridge
  `Erdos699.not_dominated_of_digit_lt` and
  `Erdos699.commonPrimeDivisor_of_digit_failures`: a certified pair of digit
  inequalities for rows `i` and `j`, at a prime `p ≥ i`, yields
  `commonPrimeDivisor n i j p` through the Lucas bridge. Added
  `Erdos699.squeezedNormalizedCounterexample_commonPrimeDivisor_eleven`, the
  `p = 11` Lean certificate for the positive squeezed-normalized survivor,
  complementing the existing `p = 5` certificate. This is a proof-shaped
  bridge for finite digit witnesses, not a global normalized-kernel theorem.
- [R] Formalized the normalized row-`n` digit-power hypothesis suggested by
  the corrected C1 lane:
  `Erdos699.rowNDigitPowerConstraint X u` states that every prime power
  `p ^ e` with `Nat.Prime p` and `3 ≤ p` dividing `X` must divide `u`, and
  `Erdos699.rowNDigitPowerConstraintExact F X u` adds the exact guard
  `¬ dominated 3 (F * X) p` with the repository's argument order for
  `dominated`. The theorem
  `Erdos699.rowNDigitPowerConstraintExact_of_rowNDigitPowerConstraint` records
  the clean-to-exact implication, and
  `Erdos699.squeezedNormalizedCounterexample_not_rowNDigitPowerConstraint`
  proves the known positive squeezed-normalized survivor is excluded because
  `179 ^ 1 ∣ 432184014644` but `179 ^ 1 ∤ 186954166997`. This banks the
  corrected digit hypothesis and the survivor exclusion; it does not prove
  the remaining power-two quotient lemma.
- [R]/[E] Formalized the reduced power-two quotient target as
  `Erdos699.powerTwoQuotientKernel`, matching the post-digit-reduction system
  with `4 ∣ A`, `A = 2 ^ a`, odd `B ≥ 3`, `0 < v`, `0 < A - 2 * v`, row one
  `v * (A - v) = h * (B * A - 1)`, and half-row divisibility
  `B * (A / 2) - 1 ∣ h * (A - 2 * v)`. Added the exact divisor-split scanner
  `compute.kernel.scan_power_two_quotient_kernel` and CLI flag
  `--power-two-quotient-kernel`; it factors `B * A - 1`, enumerates the
  coprime row-one split classes, and then checks the half-row divisibility.
  Reproduce the bounded perimeter with
  `python3 -c 'from compute.kernel import scan_power_two_quotient_kernel as s; r=s(50, 2001); print(r["instance_count"], r["row_one_candidate_count"], r["survivor_count"])'`,
  which reports `49000 404 0` for `2 ≤ a ≤ 50` and odd `3 ≤ B ≤ 2001`.
  This is exact bounded evidence and a formal target definition, not a proof
  that `powerTwoQuotientKernel` is empty.
- [R] Proved the quotient algebra from the corrected squeezed kernel into the
  pure target. `Erdos699.powerTwoQuotientKernel_of_squeezedNormalized_decomposition`
  shows that, given `X = A * H`, `u = H * v`, `g = H * H * h`, `4 ∣ A`,
  `A = 2 ^ a`, odd `H`, and `H` coprime to the half-row modulus, a squeezed
  normalized kernel point yields `powerTwoQuotientKernel A (F * H) v h`.
  `Erdos699.exists_powerTwoQuotientKernel_of_squeezedNormalized_decomposition`
  also derives the quotient `h` from row-one coprimality by proving
  `H * H ∣ g`. This banks the algebraic quotient step only; the extraction of
  the odd digit-forced factor `H` from `rowNDigitPowerConstraint`, and the
  empty-kernel theorem for `powerTwoQuotientKernel`, remain open.
- [R] Removed the manual coprimality assumptions from the natural quotient
  interface. `Erdos699.coprime_left_mul_right_sub_one` proves that a positive
  `H` is coprime to `K * H - 1` for positive `K`, and
  `Erdos699.exists_powerTwoQuotientKernel_of_squeezedNormalized_factor_dvd`
  shows that a squeezed normalized kernel point plus `X = A * H`, `H ∣ u`,
  `4 ∣ A`, `A = 2 ^ a`, and odd `H` already yields
  `∃ v h, powerTwoQuotientKernel A (F * H) v h`. The remaining digit-work is
  now narrowed to constructing such an odd factor `H` from
  `rowNDigitPowerConstraint X u` and the power-of-two quotient of `X`.
- [R] Proved the all-odd-prime-powers-forced divisor extraction. The theorem
  `Erdos699.rowNDigitPowerConstraint.dvd_of_factor_dvd` shows that if
  `H ∣ X`, `H ≠ 0`, and every prime divisor of `H` is at least `3`, then
  `rowNDigitPowerConstraint X u` forces `H ∣ u`. The helper
  `Erdos699.odd_prime_divisor_ge_three` discharges the prime-divisor condition
  when `H` is odd, and
  `Erdos699.exists_powerTwoQuotientKernel_of_squeezedNormalized_rowNDigit_factor`
  combines this with the quotient bridge to produce
  `∃ v h, powerTwoQuotientKernel A (F * H) v h` from a squeezed normalized
  kernel point plus `rowNDigitPowerConstraint X u`, `X = A * H`, `4 ∣ A`,
  `A = 2 ^ a`, and odd `H`. This is the unguarded/all-forced branch; the
  globally guarded row-`n` reduction still needs its branch condition.
- [R] Formalized the current split/gcd obstruction target without claiming it.
  `Erdos699.powerTwoSplitGcdObstruction A B` is the hypothesis surface saying
  that, for `A = 2 ^ a`, `4 ∣ A`, odd `B ≥ 3`, and any positive split
  `r * s = B * A - 1` with `r * l + s * m = A` and `r * l < s * m`, the
  half-row divisor does not divide
  `Nat.gcd (r - B * m) (s - B * l) * (l * m)`.
  `Erdos699.powerTwoSplitGcdObstruction.not_dvd` is only the direct consumer
  of that hypothesis. Separately,
  `Erdos699.powerTwoSplitAdditive_alpha_beta_mul` proves the exact additive
  split identity `alpha * beta + 1 = B * B * (l * m)` from
  `r * s = B * A - 1`, `r * l + s * m = A`, `r = B * m + alpha`, and
  `s = B * l + beta`. The global obstruction theorem remains open.
- [R] Proved the canonical row-one split extraction for the pure quotient
  kernel. The generic lemma `Erdos699.dvd_div_gcd_of_dvd_mul` shows that
  if `0 < D` and `D ∣ x * y`, then `D / Nat.gcd D x ∣ y`. The specialization
  `Erdos699.powerTwoQuotientKernel.row_one_split_right_dvd` applies this to
  `D = B * A - 1`, proving that
  `(B * A - 1) / Nat.gcd (B * A - 1) v ∣ A - v` for every
  `powerTwoQuotientKernel A B v h`. Finally,
  `Erdos699.powerTwoQuotientKernel.exists_row_one_split` packages the
  canonical witnesses `r, s, l, m` with `0 < r`, `0 < s`, `0 < l`,
  `0 < m`, `r * s = B * A - 1`, `v = r * l`, `A - v = s * m`,
  `r * l + s * m = A`, `r * l < s * m`, and `h = l * m`. This proves the
  row-one split part of the conditional Task A bridge; the half-row reduction
  to `B * (A / 2) - 1 ∣ Nat.gcd alpha beta * (l * m)` is closed below.
- [R] Proved the first half-row split bridge for the pure quotient kernel.
  `Erdos699.powerTwoQuotientKernel.row_two_split_dvd` rewrites the kernel
  half-row divisor through split equations `v = r * l`, `A - v = s * m`, and
  `h = l * m`, giving
  `B * (A / 2) - 1 ∣ (l * m) * (s * m - r * l)`. The packaged theorem
  `Erdos699.powerTwoQuotientKernel.exists_row_one_split_with_row_two`
  combines the canonical positive row-one split with this split-form row-two
  divisibility. This is still short of the needed alpha/beta/gcd reduction to
  `B * (A / 2) - 1 ∣ Nat.gcd alpha beta * (l * m)`, and does not prove
  Task A; the exact alpha/beta/gcd reduction is closed below.
- [R] Proved the subtractive alpha/beta non-truncation bridge for positive
  row-one splits. The integer identities
  `Erdos699.powerTwoSplit_alpha_int_identity` and
  `Erdos699.powerTwoSplit_beta_int_identity` state
  `s * (r - B*m) = B*r*l - 1` and `r * (s - B*l) = B*s*m - 1` over `ℤ`.
  From these,
  `Erdos699.powerTwoSplitSubtractive_lt` proves `B * m < r` and
  `B * l < s` under `B ≥ 3` and positive `r, s, l, m`.
  Consequently, `Erdos699.powerTwoSplitSubtractive_to_additive` converts the
  split/gcd obstruction's natural-subtraction definitions
  `alpha = r - B * m`, `beta = s - B * l` into the additive equalities
  `r = B * m + alpha`, `s = B * l + beta`, and
  `Erdos699.powerTwoSplitSubtractive_alpha_beta_mul` proves
  `alpha * beta + 1 = B * B * (l * m)` directly from the subtractive form.
  The half-row identities
  `Erdos699.powerTwoSplitHalfRow_alpha_beta_identity` and
  `Erdos699.powerTwoSplitSubtractive_half_row_alpha_beta_identity` prove
  `2 * (B * (A / 2) - 1) =
  2 * (alpha * beta) + B * (alpha * l + beta * m)`, and
  `Erdos699.powerTwoSplitRowTwo_alpha_identity` plus
  `Erdos699.powerTwoSplitSubtractive_row_two_alpha_identity` prove
  `B * (s * m - r * l) + 2 * s * alpha =
  2 * (B * (A / 2) - 1)`. This closes the earlier gap in using the
  additive identity and banks the congruence arithmetic needed for row two,
  but still does not prove the row-two-to-gcd equivalence or Task A.
- [R] Proved the first exact row-two divisibility cancellation, reducing the
  split delta divisor to the alpha divisor. The generic lemma
  `Erdos699.rowTwoDeltaDvd_iff_alphaDvd_of_identity` proves that if
  `B * delta + 2 * s * alpha = 2 * M`, `M.Coprime B`, and
  `M.Coprime (2 * s)`, then
  `M ∣ (l * m) * delta ↔ M ∣ (l * m) * alpha`. The supporting lemmas
  `Erdos699.coprime_of_dvd_two_mul_add_one`,
  `Erdos699.powerTwoSplit_s_dvd_two_half_row_add_one`,
  `Erdos699.powerTwoSplit_s_coprime_half_row`,
  `Erdos699.powerTwoSplit_half_row_coprime_B`,
  `Erdos699.powerTwoSplit_half_row_coprime_two_of_four_dvd`, and
  `Erdos699.powerTwoSplit_half_row_coprime_two_mul_s` discharge the needed
  coprimality conditions for the half-row modulus. Consequently,
  `Erdos699.powerTwoSplit_row_two_delta_dvd_iff_alpha_dvd` and
  `Erdos699.powerTwoSplitSubtractive_row_two_delta_dvd_iff_alpha_dvd` prove
  the concrete bridge
  `B * (A / 2) - 1 ∣ (l * m) * (s * m - r * l) ↔
  B * (A / 2) - 1 ∣ (l * m) * alpha`. The remaining unproved step is the
  final split/gcd obstruction; the alpha-to-`Nat.gcd alpha beta` reduction is
  closed below.
- [R] Refuted the proposed auxiliary bound
  `Nat.gcd (Nat.gcd alpha beta) M ≤ B * B` as a possible final obstruction.
  `Erdos699.powerTwoSplit_gcd_bound_counterexample_not_row_two_survival`
  gives an exact power-of-two split with
  `A = 2 ^ 52`, `B = 5`, `r = 32587551572869`, `s = 691`, `l = 29`,
  and `m = 5149870668245`, for which
  `d = Nat.gcd (Nat.gcd alpha beta) M = 39 > 25 = B * B`. The same Lean
  theorem proves this is not row-two survival:
  `M ∤ Nat.gcd alpha beta * (l * m)` and `l * m < M / d`. The surviving
  exact obstruction is therefore the reduced-divisor condition
  `M / d ∤ l * m`, equivalently `M ∤ Nat.gcd alpha beta * (l * m)`.
- [R] Formalized the reduced-divisor cancellation replacing the false
  `d ≤ B * B` target. The generic theorem
  `Erdos699.dvd_mul_iff_div_gcd_dvd` proves, for `0 < M`, the exact
  equivalence `M ∣ c * L ↔ M / Nat.gcd c M ∣ L`. The helper
  `Erdos699.powerTwoSplit_half_row_pos` proves the half-row modulus is
  positive from `4 ∣ A`, `3 ≤ B`, and `0 < A`, and
  `Erdos699.powerTwoSplit_gcd_dvd_iff_reduced_divisor` specializes the
  cancellation to `c = Nat.gcd alpha beta`, `M = B * (A / 2) - 1`, and
  `L = l * m`. Together with the alpha-to-gcd bridge below, row-two survival
  is exactly the reduced-divisor divisibility
  `(B * (A / 2) - 1) / Nat.gcd (Nat.gcd alpha beta) (B * (A / 2) - 1) ∣
  l * m`.
- [R] Added explicit survival and obstruction wrappers for the corrected
  reduced-divisor target. `Erdos699.powerTwoSplit_row_two_survival_iff_reduced_divisor`
  names `d = Nat.gcd c M` and proves row-two survival is equivalent to
  `M / d ∣ l * m`; `Erdos699.not_dvd_mul_iff_not_div_gcd_dvd` and
  `Erdos699.powerTwoSplit_row_two_obstruction_iff_reduced_divisor` prove the
  negated form `M ∤ c * (l * m) ↔ M / d ∤ l * m`. This is an exact
  restatement of the remaining obstruction, not a proof that the obstruction
  always holds.
- [R] Closed the alpha-to-gcd half-row bridge and the conditional Task A
  consumer. The generic theorem
  `Erdos699.gcd_alpha_half_row_eq_gcd_gcd_of_identities` proves from
  `2 * M = 2 * (alpha * beta) + B * (alpha * l + beta * m)` and
  `alpha * beta + 1 = B * B * (l * m)` that
  `Nat.gcd alpha M = Nat.gcd (Nat.gcd alpha beta) M`. Consequently,
  `Erdos699.alpha_mul_dvd_iff_gcd_mul_dvd_of_split_identities` proves
  `M ∣ (l * m) * alpha ↔ M ∣ Nat.gcd alpha beta * (l * m)`.
  The split-specialized theorem
  `Erdos699.powerTwoSplitSubtractive_row_two_delta_dvd_iff_gcd_dvd` now
  rewrites the quotient-kernel row-two divisor directly into the split/gcd
  obstruction divisor, and
  `Erdos699.powerTwoQuotientKernel.not_of_splitGcdObstruction` proves that
  `powerTwoSplitGcdObstruction A B` rules out every
  `powerTwoQuotientKernel A B v h`. This does not prove the obstruction
  itself; it closes the exact formal bridge from the pure quotient kernel to
  the remaining split/gcd obstruction.
- [R] Composed the row-two bridge all the way to the corrected reduced
  divisor. `Erdos699.powerTwoSplitSubtractive_row_two_alpha_dvd_iff_reduced_divisor`
  rewrites the `alpha` row-two divisor to `M / d ∣ l * m`, and
  `Erdos699.powerTwoSplitSubtractive_row_two_delta_dvd_iff_reduced_divisor`
  rewrites the quotient-kernel delta divisor
  `M ∣ (l * m) * (s * m - r * l)` to the same reduced-divisor condition,
  where `c = Nat.gcd alpha beta`, `M = B * (A / 2) - 1`, and
  `d = Nat.gcd c M`. The negated theorem
  `Erdos699.powerTwoSplitSubtractive_row_two_delta_obstruction_iff_reduced_divisor`
  states the surviving obstruction exactly as `M / d ∤ l * m`. This is an
  exact equivalence for admissible splits, not a proof that the obstruction
  holds universally.
- [R] Lifted reduced-divisor survival to the pure quotient-kernel interface.
  `Erdos699.powerTwoQuotientKernel.exists_row_one_split_with_reduced_divisor_survival`
  proves that every `powerTwoQuotientKernel A B v h` yields positive split
  data `r,s,l,m,alpha,beta` satisfying the row-one split equations and
  `M / d ∣ l * m`, with `c = Nat.gcd alpha beta`,
  `M = B * (A / 2) - 1`, and `d = Nat.gcd c M`. The consumers
  `Erdos699.powerTwoQuotientKernel.not_of_no_reduced_divisor_survival_split`
  and
  `Erdos699.not_exists_powerTwoQuotientKernel_of_no_reduced_divisor_survival_split`
  show that a universal no-survivor theorem for admissible positive splits
  eliminates the pure quotient kernel. This is still a conditional reduction:
  the universal no-survivor statement remains open.
- [R] Proved the converse reduced-divisor construction and the existence-level
  equivalence. `Erdos699.powerTwoQuotientKernel_of_reduced_divisor_survival_split`
  proves that any admissible positive split with
  `r * s = B * A - 1`, `r * l + s * m = A`, `r * l < s * m`,
  `alpha = r - B * m`, `beta = s - B * l`, and
  `M / d ∣ l * m` constructs the quotient-kernel point
  `powerTwoQuotientKernel A B (r * l) (l * m)`, under the global
  `A` power-of-two, `4 ∣ A`, odd `B`, and `3 ≤ B` hypotheses. Consequently,
  `Erdos699.exists_powerTwoQuotientKernel_iff_exists_reduced_divisor_survival_split`
  proves that quotient-kernel existence is equivalent to existence of such a
  surviving reduced-divisor split. This identifies the C2 target exactly; it
  does not prove the no-survivor side.
- [R] Isolated a sufficient inequality certificate for the remaining
  split/gcd obstruction. The generic theorem
  `Erdos699.not_dvd_mul_of_reduced_divisor_gt` proves that, for positive
  `M` and positive `L`, `L < M / Nat.gcd c M` implies
  `¬ M ∣ c * L`. The split specialization
  `Erdos699.powerTwoSplitSubtractive_not_gcd_dvd_of_reduced_divisor_gap`
  applies this to `M = B * (A / 2) - 1`,
  `c = Nat.gcd alpha beta`, and `L = l * m`, while
  `Erdos699.powerTwoSplitGcdObstruction_of_reduced_divisor_gap` proves that
  a universal reduced-divisor gap inequality for all admissible positive
  splits implies `powerTwoSplitGcdObstruction A B`. This is a conditional
  reduction to an inequality target, not a proof of that inequality.
- [R] Added a parity-refined sufficient inequality certificate for the same
  reduced-divisor target. `Erdos699.gcd_le_half_of_even_left_odd_right`
  proves that if `M` is odd and `c` is positive even, then
  `Nat.gcd c M ≤ c / 2`; `Erdos699.powerTwoSplit_half_row_odd` proves the
  half-row modulus `B * (A / 2) - 1` is odd under the split hypotheses; and
  `Erdos699.not_dvd_mul_of_parity_reduced_divisor_gt` plus
  `Erdos699.powerTwoSplitSubtractive_not_gcd_dvd_of_parity_reduced_divisor_gap`
  prove the branch certificate: for odd `c`, `l*m < M/c` suffices, while for
  even `c`, `l*m < M/(c/2)` suffices. This is still conditional; it does not
  prove the branch inequalities.
- [R] Added the direct consumers for the parity-branch target. The theorem
  `Erdos699.powerTwoSplitGcdObstruction_of_parity_reduced_divisor_gap` turns
  a universal parity branch inequality over all admissible positive splits
  into `powerTwoSplitGcdObstruction A B`, deriving
  `0 < Nat.gcd alpha beta` internally from the subtractive split inequalities.
  The theorems `Erdos699.powerTwoQuotientKernel.not_of_parity_reduced_divisor_gap`
  and `Erdos699.not_exists_powerTwoQuotientKernel_of_parity_reduced_divisor_gap`
  compose this all the way to the pure quotient kernel. This changes the
  formal target surface only; it is not a proof of the universal parity gap.
- [R] Proved that the parity branch denominator is exact under the split
  half-row identity, not merely a lower bound. The generic theorem
  `Erdos699.gcd_alpha_beta_dvd_two_half_row_of_identity` proves
  `c | 2*M` for `c = gcd alpha beta`; then
  `Erdos699.gcd_alpha_beta_half_row_eq_self_of_odd` proves
  `gcd c M = c` when `c` is odd, while
  `Erdos699.gcd_alpha_beta_half_row_eq_half_of_even` proves
  `gcd c M = c/2` when `c` is even and `M` is odd. The split wrapper
  `Erdos699.powerTwoSplitSubtractive_reduced_divisor_gap_iff_parity_gap`
  upgrades the parity reduced-divisor gap to an exact equivalence with the
  reduced-divisor gap for admissible power-two splits. This still does not
  prove the universal gap inequality.
- [R] Added the floor-free product form of the parity target. The helper
  `Erdos699.lt_div_of_mul_succ_le` proves that
  `b * (L + 1) ≤ M` implies `L < M / b`; the generic theorem
  `Erdos699.not_dvd_mul_of_parity_product_gap` then proves row-two failure
  from the product branch
  `(Odd c ∧ c * (L + 1) ≤ M) ∨ (Even c ∧ (c / 2) * (L + 1) ≤ M)`. The split
  and quotient consumers
  `Erdos699.powerTwoSplitSubtractive_not_gcd_dvd_of_parity_product_gap`,
  `Erdos699.powerTwoSplitGcdObstruction_of_parity_product_gap`,
  `Erdos699.powerTwoQuotientKernel.not_of_parity_product_gap`, and
  `Erdos699.not_exists_powerTwoQuotientKernel_of_parity_product_gap` compose
  this target all the way to the pure quotient kernel. This is still a
  conditional target, not a proof of the product inequality.
- [R] Proved that the floor-free product form is an exact reformulation of
  the parity/reduced-divisor gap, not just a sufficient certificate. The
  generic theorem `Erdos699.lt_div_iff_mul_succ_le` proves
  `L < M / b ↔ b * (L + 1) ≤ M` for `0 < b`; the generic theorem
  `Erdos699.parity_product_gap_iff_parity_reduced_divisor_gap` lifts this to
  the odd/even parity split; and
  `Erdos699.powerTwoSplitSubtractive_reduced_divisor_gap_iff_parity_product_gap`
  composes it with the split half-row denominator theorem. Thus the current
  product target is equivalent to the reduced-divisor gap under the
  admissible power-two split hypotheses. This still does not prove the
  universal product inequality or the kernel.
- [R] Split off the small parity-denominator branch of the product target.
  The generic theorem `Erdos699.product_gap_of_factor_bound_by_B_sq` proves
  that if a branch denominator `b` satisfies `b ≤ B^2` and is bounded by both
  split factors `alpha` and `beta`, then the product gap
  `b * (l*m + 1) ≤ M` follows from the product identity
  `alpha*beta + 1 = B^2*l*m` and the half-row identity. The split wrapper
  `Erdos699.powerTwoSplitSubtractive_parity_product_gap_of_bound_by_B_sq`
  applies this to the parity denominator `c` in the odd branch and `c/2` in
  the even branch. This does not prove Task A: the remaining exceptional
  branch is exactly the even case with `c/2 > B^2`.
- [R] Added the large-parity-denominator-only reduction. The split theorem
  `Erdos699.powerTwoSplitSubtractive_parity_product_gap_of_large_denominator_product_gap`
  proves the full parity product gap once the odd branch is known for
  `B^2 < c` and the even branch is known for `B^2 < c/2`, because the
  complementary small-denominator cases are discharged by the previous
  `B^2` theorem. The consumers
  `Erdos699.powerTwoSplitGcdObstruction_of_large_parity_denominator_product_gap`,
  `Erdos699.powerTwoQuotientKernel.not_of_large_parity_denominator_product_gap`,
  and
  `Erdos699.not_exists_powerTwoQuotientKernel_of_large_parity_denominator_product_gap`
  compose this restricted target all the way to the pure quotient kernel.
  This is a conditional reduction, not a proof of the large-denominator
  branches.
- [R] Added the normalized gcd-quotient form of the parity product target.
  `Erdos699.parity_product_gap_of_gcd_quotient_ineq` proves that after
  writing `alpha = c*x` and `beta = c*y`, the half-row identity reduces the
  odd branch to
  `2 * (l*m + 1) ≤ 2*c*(x*y) + B*(x*l + y*m)` and the even branch to
  `l*m + 1 ≤ 2*c*(x*y) + B*(x*l + y*m)`. The split and kernel consumers
  `Erdos699.powerTwoSplitSubtractive_parity_product_gap_of_gcd_quotient_ineq`,
  `Erdos699.powerTwoSplitGcdObstruction_of_gcd_quotient_ineq`,
  `Erdos699.powerTwoQuotientKernel.not_of_gcd_quotient_ineq`, and
  `Erdos699.not_exists_powerTwoQuotientKernel_of_gcd_quotient_ineq` compose
  this normalized inequality target all the way to the pure quotient kernel.
  This is conditional; it does not prove the normalized quotient inequality.
- [R] Sharpened the normalized quotient target from a sufficient condition to
  an exact branch equivalence. The theorem
  `Erdos699.parity_reduced_divisor_gap_iff_gcd_quotient_ineq` proves that,
  under the same half-row identity with `alpha = c*x`, `beta = c*y`, and
  `0 < c`, the parity reduced-divisor gap is equivalent to the odd/even
  normalized quotient inequalities above. This confirms the quotient target
  is the exact reduced-divisor obstruction in normalized variables, not a
  stronger replacement. It still does not prove the universal quotient
  inequality.
- [R] Specialized the exact quotient/reduced-divisor equivalence to
  admissible power-two splits with canonical quotient variables. The theorem
  `Erdos699.powerTwoSplitSubtractive_reduced_divisor_gap_iff_canonical_gcd_quotient_ineq`
  proves that, for a positive subtractive split, the reduced-divisor gap
  `l*m < M / gcd c M` is equivalent to the odd/even canonical quotient
  inequalities with `c = gcd alpha beta`,
  `x = alpha / c`, and `y = beta / c`. This removes the remaining
  existential witness layer from the exact equivalence itself; proving the
  universal canonical quotient inequality remains open.
- [R] Lifted the canonical quotient equivalence to the universal hypothesis
  level used by the kernel consumers. The theorem
  `Erdos699.powerTwoSplit_all_reduced_divisor_gap_iff_canonical_gcd_quotient_ineq`
  proves that, for fixed `A, B`, the universal reduced-divisor gap hypothesis
  and the universal canonical normalized gcd-quotient inequality are
  equivalent. This aligns the remaining C2 proof obligation with the
  canonical quotient diagnostics, but it still does not prove that universal
  hypothesis.
- [R] Canonicalized the normalized gcd-quotient target and recorded a Lean
  warning against a false shortcut. The split identities
  `Erdos699.powerTwoSplitSubtractive_gcd_quotient_product_identity`,
  `Erdos699.powerTwoSplitSubtractive_gcd_quotient_A_identity`, and
  `Erdos699.powerTwoSplitSubtractive_gcd_quotient_gap` prove, for
  `alpha = c*x` and `beta = c*y`, the product identity
  `c*c*(x*y)+1 = B*B*(l*m)`, the row-sum identity
  `A = 2*B*(l*m) + c*(x*l + y*m)`, and the oriented quotient gap
  `x*l < y*m`. The canonical consumers
  `Erdos699.powerTwoSplitSubtractive_parity_product_gap_of_canonical_gcd_quotient_ineq`,
  `Erdos699.powerTwoSplitGcdObstruction_of_canonical_gcd_quotient_ineq`,
  `Erdos699.powerTwoQuotientKernel.not_of_canonical_gcd_quotient_ineq`, and
  `Erdos699.not_exists_powerTwoQuotientKernel_of_canonical_gcd_quotient_ineq`
  replace existential quotient witnesses by
  `x = alpha / Nat.gcd alpha beta` and
  `y = beta / Nat.gcd alpha beta`. Separately,
  `Erdos699.gcdQuotientBareIdentity_counterexample_not_quotient_gap` proves
  that the product identity plus `x*l < y*m` alone do not imply the odd-branch
  quotient inequality: the exact counterexample is
  `(B, c, x, y, l, m) = (3, 19, 1, 26, 149, 7)`. The power-two row-sum
  constraint is still essential, and the universal quotient inequality
  remains open.
- [R] Rewrote the canonical linear target as an exact deficit-compensation
  condition. The generic equivalences
  `Erdos699.linear_even_iff_x_compensates_y_deficit` and
  `Erdos699.linear_odd_iff_x_compensates_y_deficit` prove that the even
  branch
  `l*m + 1 ≤ B*(x*l + y*m)` is equivalent to
  `m*(l - B*y) + 1 ≤ B*x*l`, while the odd branch
  `2*(l*m + 1) ≤ B*(x*l + y*m)` is equivalent to
  `m*(2*l - B*y) + 2 ≤ B*x*l`, assuming the necessary positive lower bound
  on `B*x*l`. The split theorem
  `Erdos699.powerTwoSplitSubtractive_canonical_gcd_linear_ineq_iff_deficit_ineq`
  proves this equivalence for the canonical variables
  `c = gcd alpha beta`, `x = alpha / c`, `y = beta / c`; the consumers
  `Erdos699.powerTwoSplitGcdObstruction_of_canonical_gcd_deficit_ineq`,
  `Erdos699.powerTwoQuotientKernel.not_of_canonical_gcd_deficit_ineq`, and
  `Erdos699.not_exists_powerTwoQuotientKernel_of_canonical_gcd_deficit_ineq`
  compose a universal deficit hypothesis to the pure quotient kernel. This
  is a formal target normalization only; the universal deficit inequality is
  still open.
- [R] Added the direct pure-kernel consumers for the inequality target:
  `Erdos699.powerTwoQuotientKernel.not_of_reduced_divisor_gap` and
  `Erdos699.not_exists_powerTwoQuotientKernel_of_reduced_divisor_gap`. These
  compose the reduced-divisor gap criterion all the way to
  `¬ powerTwoQuotientKernel A B v h` and
  `¬ ∃ v h, powerTwoQuotientKernel A B v h`, making the remaining Task A
  proof obligation exactly the universal reduced-divisor gap inequality.
- [E] Extended the power-two quotient scanner with exact reduced-divisor gap
  diagnostics. Reproduce the existing perimeter plus the new gap summary with
  `python3 -c 'from compute.kernel import scan_power_two_quotient_kernel as s; r=s(50,2001); print(r["instance_count"], r["row_one_candidate_count"], r["survivor_count"], r["reduced_divisor_gap_summary"])'`.
  It reports `49000` instances, `404` row-one candidates, `0` row-two
  survivors, and
  `{"candidate_count": 404, "gap_holds_count": 404, "gap_failure_count": 0,
  "min_gap_margin": 726, ...}` with the minimum-margin candidate
  `(a, A, B, v, h, r, s, l, m, alpha, beta, c, d, reduced_divisor, l*m) =
  (9, 512, 3, 205, 41, 5, 307, 41, 1, 2, 184, 2, 1, 767, 41)`. This is exact
  bounded evidence for the inequality certificate, not a global proof.
- [E] Extended the power-two quotient gap diagnostics with the parity-branch
  sufficient target. Reproduce with
  `python3 -c 'from compute.kernel import scan_power_two_quotient_kernel as s; r=s(50,2001); print(r["instance_count"], r["row_one_candidate_count"], r["survivor_count"], r["reduced_divisor_gap_summary"]["parity_branch_gap_summary"])'`.
  It reports `49000` instances, `404` row-one candidates, `0` row-two
  survivors, and parity summary
  `candidate_count = 404`, `odd_c_count = 179`, `even_c_count = 225`,
  `parity_gap_holds_count = 404`, `parity_gap_failure_count = 0`, with
  minimum parity margin `726` at the same `(a, B, v, h) = (9, 3, 205, 41)`
  candidate. This is bounded exact evidence for the parity branch target, not
  a global proof.
- [E] Added product-margin diagnostics for the floor-free parity target.
  Reproduce with
  `python3 -c 'from compute.kernel import scan_power_two_quotient_kernel as s; r=s(50,2001); p=r["reduced_divisor_gap_summary"]["parity_branch_gap_summary"]; print(r["instance_count"], r["row_one_candidate_count"], r["survivor_count"], {k:p[k] for k in ["candidate_count","odd_c_count","even_c_count","parity_product_gap_holds_count","parity_product_gap_failure_count","min_parity_product_margin"]})'`.
  It reports `49000` instances, `404` row-one candidates, `0` row-two
  survivors, and product summary
  `candidate_count = 404`, `odd_c_count = 179`, `even_c_count = 225`,
  `parity_product_gap_holds_count = 404`,
  `parity_product_gap_failure_count = 0`, and minimum product margin `725`.
  This is bounded exact evidence for the product target, not a global proof.
- [E] Upgraded the exact factorizer so row-one moduli above `2^64` are no
  longer skipped merely for size: composites are recursively split when
  possible, and large probable primes are accepted only through exact
  Pocklington witnesses whose `n - 1` factors are recursively certified.
  Reproduce the enlarged power-two quotient perimeter through exponent `70`
  for odd `B <= 2001` with
  `python3 -c 'from compute.kernel import scan_power_two_quotient_kernel as s; r=s(70,2001,skip_factorization_failures=True); p=r["reduced_divisor_gap_summary"]["parity_branch_gap_summary"]; c=r["factorization_certification_summary"]; print(r["instance_count"], r["factorized_instance_count"], r["skipped_instance_count"], r["row_one_candidate_count"], r["survivor_count"], r["reduced_divisor_gap_summary"]["gap_failure_count"], p["parity_product_gap_failure_count"], p["min_parity_product_margin"], c["pocklington_prime_count"], c["largest_pocklington_prime"])'`.
  It reports `69000 69000 0 880 0 0 0 725 2551
  2201803372637972080885759`. This is exact bounded evidence for the listed
  range, not a proof of the universal parity-product gap.
- [E] Added exact diagnostics for the small parity-denominator branch from
  the new Lean lemma. Reproduce the enlarged power-two quotient perimeter and
  denominator split with
  `python3 -c 'from compute.kernel import scan_power_two_quotient_kernel as s; r=s(70,2001,skip_factorization_failures=True); p=r["reduced_divisor_gap_summary"]["parity_branch_gap_summary"]; print(r["instance_count"], r["row_one_candidate_count"], r["survivor_count"], p["parity_denominator_le_B_sq_count"], p["parity_denominator_gt_B_sq_count"], p["odd_parity_denominator_gt_B_sq_count"], p["even_parity_denominator_gt_B_sq_count"], p["max_parity_denominator_over_B_sq_candidate"]["exponent"], p["max_parity_denominator_over_B_sq_candidate"]["B"], p["max_parity_denominator_over_B_sq_candidate"]["parity_gcd_bound"], p["max_parity_denominator_over_B_sq_candidate"]["parity_product_gap_holds"])'`.
  It reports `69000 880 0 878 2 0 2 52 5 39 True`. Thus all but two
  candidates in the range are covered by the new `b ≤ B^2` sufficient branch,
  and both large-denominator exceptions are even-branch cases. The largest
  exceptional denominator is the known `A = 2^52`, `B = 5`, `c/2 = 39` case,
  which still satisfies the product gap in the diagnostic. This is exact
  bounded evidence and a branch split, not a proof of the exceptional branch.
- [E] Added exact diagnostics for the normalized gcd-quotient target. For
  each row-one split the scanner now records `x = alpha / c`,
  `y = beta / c`, the branch-required left side, the quotient right side
  `2*c*(x*y) + B*(x*l + y*m)`, and the exact margin. Reproduce over the
  enlarged power-two quotient perimeter with
  `python3 -c 'from compute.kernel import scan_power_two_quotient_kernel as s; r=s(70,2001,skip_factorization_failures=True); p=r["reduced_divisor_gap_summary"]["parity_branch_gap_summary"]; q=p["min_quotient_gap_candidate"]; e=p["max_parity_denominator_over_B_sq_candidate"]; print(r["instance_count"], r["row_one_candidate_count"], r["survivor_count"], p["quotient_gap_holds_count"], p["quotient_gap_failure_count"], p["min_quotient_gap_margin"], q["exponent"], q["B"], q["c_parity"], q["quotient_gap_rhs"], q["quotient_gap_required"], e["exponent"], e["B"], e["gcd_quotient_x"], e["gcd_quotient_y"], e["quotient_gap_margin"])'`.
  It reports `69000 880 0 880 0 725 9 3 even 767 42 52 5 87669208098 7
  139346034426695`. Thus the normalized quotient inequality holds for all
  880 bounded row-one candidates in this perimeter; the known large
  denominator exception has quotient variables `x = 87669208098`, `y = 7`
  and a positive quotient margin. This is exact bounded evidence, not a
  proof of the universal quotient inequality.
- [R]/[E] Split out a stronger linear subtarget for the canonical quotient
  inequality. The Lean theorem
  `Erdos699.parity_product_gap_of_gcd_linear_ineq` proves that it is enough
  to prove the same branch-required left side against only
  `B * (x*l + y*m)`, discarding the nonnegative `2*c*x*y` term. The split and
  kernel consumers
  `Erdos699.powerTwoSplitSubtractive_parity_product_gap_of_canonical_gcd_linear_ineq`,
  `Erdos699.powerTwoSplitGcdObstruction_of_canonical_gcd_linear_ineq`,
  `Erdos699.powerTwoQuotientKernel.not_of_canonical_gcd_linear_ineq`, and
  `Erdos699.not_exists_powerTwoQuotientKernel_of_canonical_gcd_linear_ineq`
  compose this stronger linear target all the way to the pure quotient
  kernel. The scanner now records `linear_gap_rhs`, `linear_gap_required`,
  and `linear_gap_margin`. Reproduce the enlarged perimeter with
  `python3 -c 'from compute.kernel import scan_power_two_quotient_kernel as s; r=s(70,2001,skip_factorization_failures=True); p=r["reduced_divisor_gap_summary"]["parity_branch_gap_summary"]; q=p["min_linear_gap_candidate"]; print(r["instance_count"], r["row_one_candidate_count"], r["survivor_count"], p["linear_gap_holds_count"], p["linear_gap_failure_count"], p["min_linear_gap_margin"], q["exponent"], q["B"], q["c_parity"], q["linear_gap_rhs"], q["linear_gap_required"])'`.
  It reports `69000 880 0 880 0 357 9 3 even 399 42`. This is a
  conditional formal target plus exact bounded evidence; it does not prove
  the universal linear inequality.
- [R] Recorded a Lean warning against weakening the linear target's row-sum
  hypothesis to mere four-divisibility. The theorem
  `Erdos699.gcdQuotientFourDvdRowSum_counterexample_not_linear_gap` gives
  the exact tuple
  `(A, B, c, x, y, l, m) = (73176, 3, 38, 1, 38, 469, 13)`, satisfying
  `4 ∣ A`, `Odd B`, `3 ≤ B`, `Even c`, `Nat.Coprime x y`, the quotient
  product identity `c*c*(x*y)+1 = B*B*(l*m)`, the quotient row-sum identity
  `A = 2*B*(l*m) + c*(x*l + y*m)`, and the orientation `x*l < y*m`, while
  refuting the linear conclusion `l*m + 1 ≤ B*(x*l + y*m)`. Thus
  four-divisibility plus the normalized identities is not enough; the actual
  power-of-two row-sum hypothesis remains essential.
- [E] Added opt-in skip/reporting for factorization-limited power-two quotient
  scans. The default remains strict: if factoring `B * 2^a - 1` leaves an
  uncertified prime factor at least `2^64`, the scan raises. With
  `--skip-factorization-failures`, skipped instances are listed explicitly and
  are not counted as factorized evidence. Reproduce the now-certified
  large-prime boundary
  check with
  `python3 -m compute.kernel --power-two-quotient-kernel --min-exponent 60 --max-exponent 60 --max-b 17 --skip-factorization-failures`;
  it reports `instance_count = 8`, `factorized_instance_count = 8`,
  `skipped_instance_count = 0`, `row_one_candidate_count = 3`,
  `survivor_count = 0`, and reduced-divisor gap summary
  `candidate_count = 3`, `gap_failure_count = 0`,
  `min_gap_margin = 1654181948285415974`.
- [OPEN] Task A/pure `powerTwoQuotientKernel` is not proved. The current
  sharp target from the split analysis is the obstruction
  `B * (A / 2) - 1 ∤ Nat.gcd (r - B * m) (s - B * l) * (l * m)` under
  `A = 2 ^ a`, `4 ∣ A`, odd `B ≥ 3`, `r * s = B * A - 1`,
  `r * l + s * m = A`, and `r * l < s * m`. This is a research target, not a
  banked theorem.
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
- [R] Formalized the squeezed normalized Case-I kernel target:
  `Erdos699.squeezedNormalizedCaseIKernel` records the exact normalized
  `4 ∣ n`, odd-cofactor system with `0 < t`, `Odd F`, `4 ∣ X`, `3 ≤ F`,
  `2 * t < X`, the two squeeze inequalities, the row-one factor equation, and
  the half-row divisor `F * X / 2 - 1 ∣ g * (X - 2 * t)`.
  `Erdos699.i_three_caseI_four_dvd_odd_factor_squeezedNormalized_from_row_bound`
  extracts this predicate from the existing row-bound hypotheses, and
  `Erdos699.i_three_caseI_four_dvd_odd_factor_false_of_no_squeezedNormalized`
  is a conditional kill wrapper under an explicit no-squeezed hypothesis.
  The global no-squeezed hypothesis is now known false by
  `Erdos699.squeezedNormalizedCaseIKernel_counterexample_positive_t`; any
  usable theorem must add further original-problem digit constraints.
- [R] Proved the squeezed normalized Pell/discriminant package:
  `Erdos699.squeezedNormalized_gap_pos` extracts `0 < X - 2 * t` from the
  strict noncentral branch, `Erdos699.squeezedNormalized_gap_sq_eq_sq`
  specializes the row-one factor identity to
  `4 * (g * (F * X - 1)) + (X - 2 * t)^2 = X^2`, and
  `Erdos699.squeezedNormalized_discriminant_eq_gap_sq` gives the C4-ready
  form `X^2 - 4 * g * (F * X - 1) = (X - 2 * t)^2`. This is exact algebra
  for the Pell/discriminant lane, not a squeezed-kernel emptiness proof.
- [R] Formalized the squeezed row-one candidate and half-row gcd filter:
  `Erdos699.squeezedNormalizedRowOneCandidate` drops only the final half-row
  divisor from `Erdos699.squeezedNormalizedCaseIKernel`.
  `Erdos699.squeezedNormalizedCaseIKernel_iff_rowOneCandidate_and_halfRow_gcd_eq`
  proves that a row-one candidate is a full squeezed kernel point exactly when
  `gcd (g * (X - 2 * t)) (F * X / 2 - 1) = F * X / 2 - 1`, and
  `Erdos699.squeezedNormalizedRowOneCandidate_not_caseIKernel_of_halfRow_gcd_lt`
  packages the strict gcd obstruction used by the compute diagnostics. This
  is a filter bridge, not an emptiness proof.
- [R] Lifted the squeezed half-row gcd filter to finite-list certificates:
  `Erdos699.exists_squeezedNormalizedCaseIKernel_iff_exists_mem_rowOneCandidate_halfRow_gcd_eq_of_list_exact`
  says that for an exact finite list of row-one squeezed candidates, existence
  of a full squeezed kernel is equivalent to a listed pair whose half-row gcd
  is the full half-row modulus. The wrapper
  `Erdos699.not_exists_squeezedNormalizedCaseIKernel_of_list_covers_rowOneCandidate_halfRow_gcd_lt`
  proves emptiness from a list cover and strict half-row gcd failure for every
  listed candidate. This is the Lean consumer for finite certificates; it does
  not prove the list cover or the candidate inequalities by itself.
- [E] Added an exact bounded scanner for the squeezed normalized Case-I kernel:
  `compute.kernel.scan_squeezed_normalized_case_i_kernel` enumerates odd
  `F ≥ 3`, `4 ∣ X`, `4 * F ≤ X`, `2 * F^2 ≤ X`, row-one factor candidates
  `t * (X - t) = g * (F * X - 1)` with `0 < t` and `2 * t < X`, then filters
  the half-row divisor `F * X / 2 - 1 ∣ g * (X - 2 * t)`. Reproduce with
  `python3 -m compute.kernel --squeezed-normalized-case-i --max-f 99 --max-x 5000`;
  it reports `1564` row-one factor candidates and `0` full squeezed survivors.
  With `--include-candidate-summary`, the same run reports
  `surviving_half_row_count = 0`; its half-row gcd histogram begins with
  `1191` candidates at gcd `1`, `179` at gcd `3`, `72` at gcd `5`, and `45`
  at gcd `7`. This is exact bounded finite evidence for the normalized scan,
  not an emptiness proof; the global normalized predicate is known nonempty.
- [E] Replaced the squeezed scanner's row-one stage with the exact
  discriminant formulation `X^2 - 4 * g * (F * X - 1) = (X - 2 * t)^2`,
  matching the Lean theorem `Erdos699.squeezedNormalized_discriminant_eq_gap_sq`.
  Unit tests cross-check the discriminant generator against brute force for
  `F ≤ 9`, `X ≤ 120`. The command
  `python3 -m compute.kernel --squeezed-normalized-case-i --max-f 501 --max-x 100000 --include-candidate-summary`
  reports `68076` row-one discriminant candidates and `0` full squeezed
  survivors; the half-row gcd histogram begins with `49283` candidates at
  gcd `1`, `7815` at gcd `3`, `3423` at gcd `5`, and `1924` at gcd `7`.
  This is exact bounded finite evidence for the discriminant/Pell lane, not an
  emptiness proof; the global normalized predicate is known nonempty.
- [R] Formalized the consecutive-divisor kernel target:
  `Erdos699.consecutiveDivisorKernel` and
  `Erdos699.consecutiveDivisorKernelBelow` name the two-row kernel and the
  half-row-bounded version. The reduction
  `Erdos699.i_three_caseI_four_dvd_consecutive_kernel_below_from_no_common`
  shows that the `4 ∣ n` Case-I hypotheses force coprime factors
  `n - 1` and `n / 2 - 1` into this bounded kernel. This does not prove the
  kernel empty. The follow-up
  `Erdos699.i_three_caseI_four_dvd_consecutive_kernel_in_range_from_no_common`
  adds the original row lower bound `3 < j` and lands in
  `Erdos699.consecutiveDivisorKernelInRange ... 4 n j`, matching the
  lower-bounded certificate interface. This still does not prove the kernel
  empty.
- [R] Formalized the C2 row-one split interface:
  `Erdos699.rowOneDivisorSplit` records a factor split
  `zeroPart * onePart = N1` with `zeroPart ∣ t` and
  `onePart ∣ t - 1`. Theorems
  `Erdos699.rowOneDivisorSplit_dvd_mul_sub_one` and
  `Erdos699.rowOneDivisorSplit_kernel_iff_row_two` connect this split to the
  first row of `consecutiveDivisorKernel`. Theorems
  `Erdos699.not_consecutiveDivisorKernel_of_row_two_gcd_lt`,
  `Erdos699.rowOneDivisorSplit_not_consecutiveDivisorKernel_of_row_two_gcd_lt`,
  `Erdos699.not_consecutiveDivisorKernelBelow_of_row_two_gcd_lt`, and
  `Erdos699.rowOneDivisorSplit_not_consecutiveDivisorKernelBelow_of_row_two_gcd_lt`
  formalize the exact row-two gcd obstruction used by the C2 split
  diagnostics. This is a conditional kernel tool, not a proof that the kernel
  is empty.
- [R] Proved the C2 row-one split congruence bridge:
  `Erdos699.rowOneDivisorSplit_modEq_zero`,
  `Erdos699.rowOneDivisorSplit_modEq_one_of_one_le`,
  `Erdos699.rowOneDivisorSplit_of_modEq`, and
  `Erdos699.rowOneDivisorSplit_iff_modEq_of_one_le` identify the formal split
  with the CRT congruences `t ≡ 0 [MOD zeroPart]` and
  `t ≡ 1 [MOD onePart]` under the explicit hypothesis `1 ≤ t`. This is the
  Lean bridge from the C2 `{0,1}` residue enumeration to the divisor-split
  predicate; it is not a proof that the kernel is empty.
- [R] Proved fixed-split CRT uniqueness for C2:
  `Erdos699.rowOneDivisorSplit_modEq_chineseRemainder_of_coprime` shows that
  a candidate with a coprime split is congruent modulo `N1` to the corresponding
  `Nat.chineseRemainder` representative, and
  `Erdos699.rowOneDivisorSplit_modEq_unique_of_coprime` shows that any two
  candidates with the same coprime split are congruent modulo `N1`. This
  formalizes the "one residue class per `{0,1}` split" side of the C2 CRT
  enumeration; it is not a proof that the kernel is empty.
- [R] Proved automatic coprimality for positive row-one splits:
  `Erdos699.rowOneDivisorSplit_coprime_of_one_le` derives
  `zeroPart.Coprime onePart` from a split and `1 ≤ t`, and
  `Erdos699.rowOneDivisorSplit_modEq_unique` removes the explicit coprime
  input from fixed-split uniqueness. This matches the C2 setting where
  `t ≥ 4`; it is not a proof that the kernel is empty.
- [R] Proved bounded fixed-split uniqueness for C2:
  `Erdos699.rowOneDivisorSplit_eq_of_lt` upgrades same-split modular
  uniqueness to equality when both candidates are below `N1`,
  `Erdos699.rowOneDivisorSplit_eq_of_half_bound` derives that condition from
  `2 * t ≤ bound`, `2 * u ≤ bound`, and `bound < 2 * N1`, and
  `Erdos699.rowOneDivisorSplit_eq_of_consecutiveDivisorKernelBelow_short`
  packages the same conclusion for `consecutiveDivisorKernelBelow`. This
  formalizes the "at most one bounded candidate per split" side of C2 under
  the explicit short-interval hypothesis; it is not a proof that the kernel is
  empty.
- [R] Specialized bounded fixed-split uniqueness to the Case-I row-one
  modulus `n - 1`: `Erdos699.sub_one_short_bound_of_two_lt` proves
  `n < 2 * (n - 1)` from `2 < n`, and
  `Erdos699.rowOneDivisorSplit_eq_of_sub_one_consecutiveDivisorKernelBelow`
  shows that two positive bounded kernel candidates with the same
  `rowOneDivisorSplit (n - 1) zeroPart onePart` are equal. This is the
  problem-shape version of "at most one bounded candidate per split"; it is
  not a proof that the kernel is empty.
- [R] Proved the canonical row-one split bridge for C2:
  `Erdos699.rowOneDivisorSplit_gcdDiv_of_dvd_mul_sub_one` shows that if
  `0 < N1` and `N1 ∣ t * (t - 1)`, then `t` induces the canonical split
  `zeroPart = gcd N1 t` and `onePart = N1 / gcd N1 t`. The kernel wrappers
  `Erdos699.rowOneDivisorSplit_gcdDiv_of_consecutiveDivisorKernel` and
  `Erdos699.rowOneDivisorSplit_gcdDiv_of_consecutiveDivisorKernelBelow`
  package the same fact for the two C2 kernel predicates. This formalizes the
  "every row-one kernel candidate lies in a CRT split class" direction; it is
  not a proof that the kernel is empty.
- [R] Proved the reverse split-to-canonical identification:
  `Erdos699.rowOneDivisorSplit_gcd_eq_zeroPart_of_one_le` and
  `Erdos699.rowOneDivisorSplit_div_gcd_eq_onePart_of_one_le` show that any
  positive `rowOneDivisorSplit N1 zeroPart onePart t` has
  `zeroPart = gcd N1 t` and `onePart = N1 / gcd N1 t`; the paired wrapper is
  `Erdos699.rowOneDivisorSplit_eq_gcdDiv_parts_of_one_le`. This completes the
  formal equivalence between positive row-one split records and the canonical
  gcd/div split class, still without proving any row-two incompatibility or
  kernel emptiness.
- [R] Proved the exact row-two gcd filter used by the C2 enumerator:
  `Erdos699.rowTwo_dvd_iff_gcd_eq_right` identifies
  `N2 ∣ t * (t - 1) * (t - 2)` with
  `gcd (t * (t - 1) * (t - 2)) N2 = N2`; the wrappers
  `Erdos699.consecutiveDivisorKernel_iff_row_two_gcd_eq_of_row_one`,
  `Erdos699.rowOneDivisorSplit_consecutiveDivisorKernel_iff_row_two_gcd_eq`,
  and
  `Erdos699.rowOneDivisorSplit_consecutiveDivisorKernelBelow_iff_bound_and_row_two_gcd_eq`
  package this under row-one divisibility, a split, and the half-row bound.
  This formalizes the scanner's row-two survivor predicate, not a proof that
  no survivors exist.
- [R] Proved bounded-candidate survivor/non-survivor forms for C2:
  `Erdos699.rowOneDivisorSplit_consecutiveDivisorKernelBelow_iff_row_two_gcd_eq_of_bound`
  reduces kernel survival to the row-two gcd equality once a row-one split and
  half-row bound are already known. The negated forms
  `Erdos699.rowOneDivisorSplit_not_consecutiveDivisorKernelBelow_iff_row_two_gcd_ne_of_bound`
  and
  `Erdos699.rowOneDivisorSplit_not_consecutiveDivisorKernelBelow_iff_row_two_gcd_lt_of_bound`
  identify non-survival with `gcd ≠ N2`, and with `gcd < N2` when `0 < N2`.
  This is the exact per-candidate pass/fail predicate used by the C2 scanner,
  not a proof that all candidates fail.
- [R] Proved the combined canonical kernel characterization for C2:
  `Erdos699.consecutiveDivisorKernel_iff_gcdDiv_split_and_row_two_gcd_eq`
  states that, for `0 < N1`, the two-row kernel is equivalent to the
  canonical row-one gcd/div split plus the row-two gcd equality. The bounded
  wrapper
  `Erdos699.consecutiveDivisorKernelBelow_iff_bound_gcdDiv_split_and_row_two_gcd_eq`
  adds the half-row bound. This packages the exact logical contract of the C2
  CRT scanner; it is not a proof that the kernel is empty.
- [R] Lifted the C2 canonical characterization to whole-kernel certificate
  form:
  `Erdos699.exists_consecutiveDivisorKernelBelow_iff_exists_bound_gcdDiv_split_and_row_two_gcd_eq`
  rewrites bounded kernel nonemptiness as the existence of a bounded canonical
  row-one gcd/div split passing the row-two gcd equality. The no-survivor
  wrappers
  `Erdos699.not_exists_consecutiveDivisorKernelBelow_of_forall_bound_gcdDiv_split_row_two_gcd_ne`
  and
  `Erdos699.not_exists_consecutiveDivisorKernelBelow_of_forall_bound_gcdDiv_split_row_two_gcd_lt`
  turn a per-candidate row-two failure certificate into kernel emptiness. This
  is a conditional certificate interface, not a proof that the kernel is empty.
- [R] Added finite-list C2 certificate bridges:
  `Erdos699.not_exists_consecutiveDivisorKernelBelow_of_list_covers_bound_gcdDiv_split_row_two_gcd_ne`
  and
  `Erdos699.not_exists_consecutiveDivisorKernelBelow_of_list_covers_bound_gcdDiv_split_row_two_gcd_lt`
  show that a list covering all bounded canonical row-one gcd/div split
  candidates, together with a row-two gcd failure proof for every list member,
  proves bounded kernel emptiness. This is the formal interface for turning a
  future checked CRT candidate list into a Lean no-survivor certificate; it is
  not a proof that the kernel is empty.
- [R] Added finite-list C2 survivor equivalences:
  `Erdos699.exists_kernelBelow_iff_exists_mem_cert_of_list_covers`
  shows that, under a list-cover hypothesis, bounded kernel nonemptiness is
  equivalent to a listed candidate that still satisfies the bound, canonical
  row-one split, and row-two gcd equality. The exact-list version
  `Erdos699.exists_kernelBelow_iff_exists_mem_row_two_gcd_eq_of_list_exact`
  adds a list-soundness hypothesis and reduces the finite search side to
  membership plus row-two gcd equality. This is the formal survivor-extraction
  contract for checked CRT candidate lists; it is not a proof that the kernel
  is empty.
- [R] Added exact-list C2 no-survivor equivalences:
  `Erdos699.not_exists_kernelBelow_iff_forall_mem_gcd_ne_of_list_exact`
  turns bounded kernel emptiness into the finite condition that every member
  of an exact canonical candidate list has row-two gcd not equal to `N2`. The
  positive-modulus wrapper
  `Erdos699.not_exists_kernelBelow_iff_forall_mem_gcd_lt_of_list_exact`
  replaces inequality by the stronger finite check `gcd < N2`. This is an
  exact finite-list certificate contract, still conditional on the list cover
  and soundness hypotheses.
- [R] Proved the odd quotient-gap row-two factorization:
  `Erdos699.rowTwo_gcd_eq_rowOneQuotient_gap_gcd_mul_of_odd` shows that if
  `N1 ∣ t * (t - 1)`, `N1.Coprime N2`, `Odd N2`, and `2 ≤ t`, then
  `gcd (t * (t - 1) * (t - 2)) N2` factors as
  `gcd ((t * (t - 1)) / N1) N2 * gcd (t - 2) N2`. The strict wrapper
  `Erdos699.rowTwo_gcd_lt_of_rowOneQuotient_gap_gcd_mul_lt_of_odd` and the
  split-facing wrapper
  `Erdos699.rowOneDivisorSplit_rowTwo_gcd_lt_of_rowOneQuotient_gap_gcd_mul_lt_of_odd`
  turn the quotient-gap product inequality into the existing C2 row-two gcd
  obstruction. This is a conditional obstruction interface, not a proof that
  the kernel is empty.
- [R] Added the exact-list quotient-gap C2 certificate:
  `Erdos699.not_exists_kernelBelow_iff_forall_mem_quotient_gap_gcd_mul_lt_of_list_exact_odd`
  rewrites bounded kernel emptiness, for an exact finite canonical row-one
  candidate list and odd coprime `N2`, as the finite inequality
  `gcd ((t * (t - 1)) / N1) N2 * gcd (t - 2) N2 < N2` for every listed
  candidate. This composes the finite-list certificate contract with the
  odd quotient-gap factorization; it is still conditional on list cover,
  list soundness, and `2 ≤ t` for listed candidates.
- [R] Added the universal quotient-gap C2 obstruction wrapper:
  `Erdos699.not_exists_kernelBelow_of_forall_bound_quotient_gap_gcd_mul_lt_odd`
  shows that if every bounded canonical row-one split candidate has
  `2 ≤ t` and satisfies
  `gcd ((t * (t - 1)) / N1) N2 * gcd (t - 2) N2 < N2`, then the bounded
  consecutive-divisor kernel is empty for odd `N2` coprime to `N1`. This is
  a conditional consumer of the quotient-gap inequality, not a proof that the
  inequality holds in pure C2.
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
- [E] Added opt-in row-one candidate output to the exact CRT kernel
  enumerator via `--include-row-one-candidates`, so C2 split survivors can be
  inspected without bloating default logs. The full deterministic 64-bit
  supported scan
  `python3 -c 'from compute.kernel import scan_case_i_power_two_kernel as s; r=s(62); print(r["instance_count"], r["total_row_one_candidate_count"], r["survivor_count"])'`
  checks exponents `2..62` in the `n = 3 * 2^A` Case-I family and reports
  `61` instances, `130` row-one candidates, and `0` kernel survivors. The
  largest row-one candidate count in this range is `7`, attained at exponent
  `61`. This is exact finite evidence for the C2 lane, not a proof that the
  kernel is empty.
- [E] Added opt-in divisor-split diagnostics via `--include-row-one-splits`.
  Each row-one CRT candidate now records the exact prime-power product forced
  into `t`, the product forced into `t - 1`, the row-two remainder, the
  row-two gcd, and whether the candidate survives. The command
  `python3 -m compute.kernel --case-i-power-two --min-exponent 61 --max-exponent 61 --include-row-one-splits`
  reports `7` row-one split candidates at exponent `61`; all have
  `row_two_gcd = 1` and `survivor_count = 0`. This is exact finite evidence
  for the C2 divisor-split lane, not a proof that the kernel is empty.
- [E] Added opt-in row-one split summaries via
  `--include-row-one-split-summary`. The command
  `python3 -m compute.kernel --case-i-power-two --max-exponent 62 --include-row-one-split-summary`
  reports `130` row-one split candidates across exponents `2..62`, with
  `0` surviving row two. The aggregate row-two gcd histogram is
  `{1: 108, 5: 15, 11: 2, 23: 2, 29: 1, 101: 1, 115: 1}`. This is exact
  finite evidence for the C2 divisor-split lane, not a proof that the kernel
  is empty.
- [E] Extended row-one split diagnostics with the exact quotient-gap finite
  certificate terms used by the Lean theorem
  `Erdos699.not_exists_kernelBelow_iff_forall_mem_quotient_gap_gcd_mul_lt_of_list_exact_odd`:
  `row_one_quotient`, `row_one_quotient_gcd`, `gap_gcd`,
  `quotient_gap_gcd_product`, and the strict flag
  `quotient_gap_gcd_product_lt_n2`. The command
  `python3 -m compute.kernel --case-i-power-two --min-exponent 61 --max-exponent 61 --include-row-one-splits`
  reports `7` row-one split candidates, `0` survivors, and
  `quotient_gap_gcd_product = 1 < N2` for every listed candidate. This is
  exact finite evidence aligned to the quotient-gap certificate interface,
  not a proof that the kernel is empty.
- [E] Added compact opt-in quotient-gap aggregate summaries via
  `--include-quotient-gap-summary`, so finite scans can report exactly whether
  the Lean-facing inequality
  `gcd ((t * (t - 1)) / N1) N2 * gcd (t - 2) N2 < N2` holds for every
  enumerated row-one CRT candidate without emitting every split row. The
  command
  `python3 -c 'from compute.kernel import scan_case_i_power_two_kernel as s; r=s(62, include_quotient_gap_summary=True); print(r["instance_count"], r["total_row_one_candidate_count"], r["survivor_count"]); print(r["quotient_gap_summary"])'`
  reports `61` instances, `130` row-one candidates, `0` survivors,
  `strict_lt_n2_count = 130`, and `all_strict_lt_n2 = True`. The quotient-gap
  product histogram is `{1: 108, 5: 15, 11: 2, 23: 2, 29: 1, 101: 1,
  115: 1}`, with max product `115`; the max relative product is the exponent
  `5` candidate `t = 20`, where the product is `1 < 47`. As a sanity contrast,
  `python3 -m compute.kernel --n1 15 --n2 14 --bound 120 --min-t 4 --include-quotient-gap-summary`
  reports `15` row-one candidates, `6` row-two survivors, and
  `all_strict_lt_n2 = False`. This is exact finite evidence for the
  quotient-gap certificate lane, not a proof that the kernel is empty.
- [R]/[E] Formalized the lower-bounded kernel target needed by compute
  certificates that use `min_t`. The old predicate
  `Erdos699.consecutiveDivisorKernelBelow` intentionally has no lower bound;
  the new Lean witnesses `Erdos699.consecutiveDivisorKernelBelow_zero` and
  `Erdos699.consecutiveDivisorKernelBelow_one` show why it cannot consume
  `min_t = 4` certificates directly. The new predicate
  `Erdos699.consecutiveDivisorKernelInRange` adds `minT ≤ t`, and
  `Erdos699.consecutiveDivisorKernelInRange_iff_bounds_gcdDiv_split_and_row_two_gcd_eq`
  gives its row-one split/gcd characterization. The consumer
  `Erdos699.not_exists_kernelInRange_of_list_covers_quotient_gap_gcd_mul_lt_odd`
  turns an exact lower-bounded row-one list cover plus quotient-gap failures
  into lower-bounded kernel emptiness. As a first concrete certificate,
  `Erdos699.not_exists_kernelInRange_95_47_4_96` proves in Lean that there is
  no `4 ≤ t`, `2 * t ≤ 96` kernel point for `N1 = 95`, `N2 = 47`, using the
  finite row-one list `[20]`. The matching exact compute command
  `python3 -m compute.kernel --n1 95 --n2 47 --bound 96 --min-t 4 --include-row-one-candidates --include-quotient-gap-summary`
  reports `row_one_candidates = [20]`, `survivor_count = 0`, and
  `all_strict_lt_n2 = True`. This is a small Lean-certified finite
  certificate bridge, not a proof of the general kernel.
- [R] Added the reusable problem-surface consumer for lower-bounded Case-I
  kernel certificates:
  `Erdos699.i_three_caseI_not_no_common_from_kernelInRange_empty` and
  `Erdos699.i_three_caseI_exists_common_from_kernelInRange_empty` turn
  `¬ ∃ t, consecutiveDivisorKernelInRange (n - 1) (n / 2 - 1) 4 n t` plus
  the explicit `3 ∣ n`, `4 ∣ n`, `3 < j`, `2 * j ≤ n` hypotheses into the
  original common-prime conclusion. This is a certificate consumer, not a
  proof that the kernel is empty.
- [R]/[E] Added the prime row-one short-interval kernel consumer:
  `Erdos699.not_exists_kernelInRange_of_prime_row_one_short` proves that if
  `N1` is prime, `2 ≤ minT`, and `bound < 2 * (N1 - 1)`, then the
  lower-bounded kernel `consecutiveDivisorKernelInRange N1 N2 minT bound` is
  empty. The Lean theorem `Erdos699.prime_6143` certifies `Nat.Prime 6143`
  via Mathlib's `norm_num` prime certificate, and
  `Erdos699.not_exists_kernelInRange_6143_3071_4_6144` applies the consumer
  to the `A = 11`, `n = 3 * 2^11` Case-I numbers. The surface wrappers
  `Erdos699.i_three_caseI_6144_not_no_common_from_row_bounds` and
  `Erdos699.i_three_caseI_6144_exists_common_from_row_bounds` give the
  original row-3 common-prime conclusion for every `j` with `3 < j` and
  `2 * j ≤ 6144`. The exact compute command
  `python3 -m compute.kernel --n1 6143 --n2 3071 --bound 6144 --min-t 4 --include-row-one-candidates --include-row-one-splits --include-quotient-gap-summary`
  reports `row_one_candidates = []`, `survivor_count = 0`, and
  `all_strict_lt_n2 = True`. This is an end-to-end Lean-certified finite
  instance, not a general Case-I theorem.
- [R]/[E] Connected finite lower-bounded certificates back to the original
  problem surface for seven `n = 3 * 2^A` Case-I members. For `A = 5`,
  `Erdos699.i_three_caseI_96_not_no_common_from_row_bounds` rules out the
  no-common-prime counterexample criterion for every `j` with `3 < j` and
  `2 * j ≤ 96`, and
  `Erdos699.i_three_caseI_96_exists_common_from_row_bounds` gives the
  corresponding witness statement `∃ q, commonPrimeDivisor 96 3 j q`. For
  `A = 8`, `Erdos699.not_exists_kernelInRange_767_383_4_768` proves the
  exact lower-bounded kernel certificate with row-one list `[118]`, and
  `Erdos699.i_three_caseI_768_exists_common_from_row_bounds` gives the
  analogous common-prime witness statement for every `j` with `3 < j` and
  `2 * j ≤ 768`. For `A = 9`,
  `Erdos699.not_exists_kernelInRange_1535_767_4_1536` proves the exact
  lower-bounded kernel certificate with row-one list `[615]`, using a modular
  split over `5` and `307` rather than full row enumeration, and
  `Erdos699.i_three_caseI_1536_exists_common_from_row_bounds` gives the
  analogous common-prime witness statement for every `j` with `3 < j` and
  `2 * j ≤ 1536`. For `A = 10`,
  `Erdos699.not_exists_kernelInRange_3071_1535_4_3072` proves the exact
  lower-bounded kernel certificate with row-one list `[333]`, using a modular
  split over `37` and `83`, and
  `Erdos699.i_three_caseI_3072_exists_common_from_row_bounds` gives the
  analogous common-prime witness statement for every `j` with `3 < j` and
  `2 * j ≤ 3072`. For `A = 11`,
  `Erdos699.not_exists_kernelInRange_6143_3071_4_6144` proves the exact
  lower-bounded kernel certificate with empty row-one list, using
  `Erdos699.prime_6143` and the short-prime-modulus consumer, and
  `Erdos699.i_three_caseI_6144_exists_common_from_row_bounds` gives the
  analogous common-prime witness statement for every `j` with `3 < j` and
  `2 * j ≤ 6144`. For `A = 12`,
  `Erdos699.not_exists_kernelInRange_12287_6143_4_12288` proves the exact
  lower-bounded kernel certificate with row-one list `[2234]`, using a
  modular split over `11` and `1117`, and
  `Erdos699.i_three_caseI_12288_exists_common_from_row_bounds` gives the
  analogous common-prime witness statement for every `j` with `3 < j` and
  `2 * j ≤ 12288`. For `A = 13`,
  `Erdos699.not_exists_kernelInRange_24575_12287_4_24576` proves the exact
  lower-bounded kernel certificate with row-one list `[2950]`, using the
  `25` residue filter and the prime split at `983`, and
  `Erdos699.i_three_caseI_24576_exists_common_from_row_bounds` gives the
  analogous common-prime witness statement for every `j` with `3 < j` and
  `2 * j ≤ 24576`. Reproduce the exact `A = 9` scan with
  `python3 -m compute.kernel --n1 1535 --n2 767 --bound 1536 --min-t 4 --include-row-one-candidates --include-quotient-gap-summary`,
  which reports `row_one_candidates = [615]`, `survivor_count = 0`, and
  `all_strict_lt_n2 = True`. Reproduce the exact `A = 10` scan with
  `python3 -m compute.kernel --n1 3071 --n2 1535 --bound 3072 --min-t 4 --include-row-one-candidates --include-quotient-gap-summary`,
  which reports `row_one_candidates = [333]`, `survivor_count = 0`, and
  `all_strict_lt_n2 = True`. Reproduce the exact `A = 12` scan with
  `python3 -m compute.kernel --n1 12287 --n2 6143 --bound 12288 --min-t 4 --include-row-one-candidates --include-row-one-splits --include-quotient-gap-summary`,
  which reports `row_one_candidates = [2234]`, `survivor_count = 0`, and
  `all_strict_lt_n2 = True`. Reproduce the exact `A = 13` scan with
  `python3 -m compute.kernel --n1 24575 --n2 12287 --bound 24576 --min-t 4 --include-row-one-candidates --include-row-one-splits --include-quotient-gap-summary`,
  which reports `row_one_candidates = [2950]`, `survivor_count = 0`, and
  `all_strict_lt_n2 = True`. These are end-to-end Lean-certified finite
  instances, not a general Case-I theorem.
- [R]/[E] Extended the lower-bounded Case-I finite certificate chain through
  three more `n = 3 * 2^A` members. `Erdos699.not_exists_kernelInRange_49151_24575_4_49152`,
  `Erdos699.not_exists_kernelInRange_98303_49151_4_98304`, and
  `Erdos699.not_exists_kernelInRange_196607_98303_4_196608` prove the exact
  lower-bounded C2 kernel is empty for `A = 14`, `A = 15`, and `A = 16`,
  using singleton row-one lists `[23507]`, `[7486]`, and `[55573]`
  respectively. The wrappers
  `Erdos699.i_three_caseI_49152_exists_common_from_row_bounds`,
  `Erdos699.i_three_caseI_98304_exists_common_from_row_bounds`, and
  `Erdos699.i_three_caseI_196608_exists_common_from_row_bounds` give the
  original row-3 common-prime conclusion for every `j` with `3 < j` and
  `2 * j ≤ n` at those three `n`. Reproduce the exact scan with
  `python3 -m compute.kernel --case-i-power-two --min-exponent 14 --max-exponent 16 --include-row-one-candidates --include-row-one-splits --include-quotient-gap-summary`;
  it reports three instances, row-one candidates `[23507]`, `[7486]`, and
  `[55573]`, `survivor_count = 0`, and `all_strict_lt_n2 = True`. These are
  additional end-to-end Lean-certified finite instances, not a general Case-I
  theorem.
- [R]/[E] Extended the lower-bounded Case-I finite certificate chain through
  four further `n = 3 * 2^A` members. `Erdos699.not_exists_kernelInRange_393215_196607_4_393216`,
  `Erdos699.not_exists_kernelInRange_786431_393215_4_786432`,
  `Erdos699.not_exists_kernelInRange_1572863_786431_4_1572864`, and
  `Erdos699.not_exists_kernelInRange_3145727_1572863_4_3145728` prove the
  exact lower-bounded C2 kernel is empty for `A = 17`, `A = 18`, `A = 19`,
  and `A = 20`, using row-one lists `[157286]`, `[]`, `[22153]`, and
  `[967916]` respectively. The wrappers
  `Erdos699.i_three_caseI_393216_exists_common_from_row_bounds`,
  `Erdos699.i_three_caseI_786432_exists_common_from_row_bounds`,
  `Erdos699.i_three_caseI_1572864_exists_common_from_row_bounds`, and
  `Erdos699.i_three_caseI_3145728_exists_common_from_row_bounds` give the
  original row-3 common-prime conclusion for every `j` with `3 < j` and
  `2 * j ≤ n` at those four `n`. Reproduce the exact scan with
  `python3 -m compute.kernel --case-i-power-two --min-exponent 17 --max-exponent 20 --include-row-one-candidates --include-row-one-splits --include-quotient-gap-summary`;
  it reports four instances, row-one candidates `[157286]`, `[]`, `[22153]`,
  and `[967916]`, `survivor_count = 0`, and `all_strict_lt_n2 = True`. These
  are additional end-to-end Lean-certified finite instances, not a general
  Case-I theorem.
- [R]/[E] Extended the lower-bounded Case-I finite certificate chain through
  four more `n = 3 * 2^A` members. `Erdos699.primePow_dvd_mul_sub_one_iff`
  and `Erdos699.eq_mul_add_one_of_sub_one_eq_mul` support the larger
  row-one covers without large quotient enumeration. The theorems
  `Erdos699.not_exists_kernelInRange_6291455_3145727_4_6291456`,
  `Erdos699.not_exists_kernelInRange_12582911_6291455_4_12582912`,
  `Erdos699.not_exists_kernelInRange_25165823_12582911_4_25165824`, and
  `Erdos699.not_exists_kernelInRange_50331647_25165823_4_50331648` prove the
  exact lower-bounded C2 kernel is empty for `A = 21`, `A = 22`, `A = 23`,
  and `A = 24`, using row-one lists `[1258291]`, `[727937]`,
  `[4612973, 9271620, 11281232]`, and `[13788863]` respectively. The wrappers
  `Erdos699.i_three_caseI_6291456_exists_common_from_row_bounds`,
  `Erdos699.i_three_caseI_12582912_exists_common_from_row_bounds`,
  `Erdos699.i_three_caseI_25165824_exists_common_from_row_bounds`, and
  `Erdos699.i_three_caseI_50331648_exists_common_from_row_bounds` give the
  original row-3 common-prime conclusion for every `j` with `3 < j` and
  `2 * j ≤ n` at those four `n`. Reproduce the exact scan with
  `python3 -m compute.kernel --case-i-power-two --min-exponent 21 --max-exponent 24 --include-row-one-candidates --include-row-one-splits --include-quotient-gap-summary`;
  it reports four instances, row-one candidates `[1258291]`, `[727937]`,
  `[4612973, 9271620, 11281232]`, and `[13788863]`,
  `total_row_one_candidate_count = 6`, `survivor_count = 0`, and
  `all_strict_lt_n2 = True`. These are additional end-to-end Lean-certified
  finite instances, not a general Case-I theorem.
- [R]/[E] Extended the lower-bounded Case-I finite certificate chain through
  four further `n = 3 * 2^A` members. The helper
  `Erdos699.coprime_mul_dvd_of_dvd_of_dvd` lets the row-one split covers use
  CRT uniqueness instead of large quotient enumeration. The theorems
  `Erdos699.not_exists_kernelInRange_100663295_50331647_4_100663296`,
  `Erdos699.not_exists_kernelInRange_201326591_100663295_4_201326592`,
  `Erdos699.not_exists_kernelInRange_402653183_201326591_4_402653184`, and
  `Erdos699.not_exists_kernelInRange_805306367_402653183_4_805306368` prove
  the exact lower-bounded C2 kernel is empty for `A = 25`, `A = 26`,
  `A = 27`, and `A = 28`, using row-one lists
  `[19257326, 20132660, 39389985]`, `[33417252]`,
  `[17134179, 24038997, 41173175]`, and `[365758927]` respectively. The
  wrappers `Erdos699.i_three_caseI_100663296_exists_common_from_row_bounds`,
  `Erdos699.i_three_caseI_201326592_exists_common_from_row_bounds`,
  `Erdos699.i_three_caseI_402653184_exists_common_from_row_bounds`, and
  `Erdos699.i_three_caseI_805306368_exists_common_from_row_bounds` give the
  original row-3 common-prime conclusion for every `j` with `3 < j` and
  `2 * j ≤ n` at those four `n`. Reproduce the exact scan with
  `python3 -m compute.kernel --case-i-power-two --min-exponent 25 --max-exponent 28 --include-row-one-candidates --include-row-one-splits --include-quotient-gap-summary`;
  it reports four instances, `total_row_one_candidate_count = 8`,
  `survivor_count = 0`, and `all_strict_lt_n2 = True`. These are additional
  end-to-end Lean-certified finite instances, not a general Case-I theorem.
- [E] Verified the GPT Pro pure-C2 survivor showing that the quotient-gap
  product inequality is false under C2 shape hypotheses alone:
  `n = 54,734,052`, `N1 = n - 1`, `N2 = n / 2 - 1`, and
  `t = 8,748,251` satisfy `3 ∣ n`, `4 ∣ n`, `Odd N2`, `N1.Coprime N2`,
  `2 * t ≤ n`, `N1 ∣ t * (t - 1)`, and
  `N2 ∣ t * (t - 1) * (t - 2)`. Exact tests also verify
  `(t * (t - 1) / N1) = 1,398,250`,
  `gcd ((t * (t - 1)) / N1) N2 = 2,975`,
  `gcd (t - 2) N2 = 9,199`, and the product is exactly `N2`. The same tests
  verify this is not a row-3 obstruction candidate because primes `541` and
  `8431` divide `n` and violate Lucas digit domination for `j = t`. Reproduce
  with `python3 -m pytest compute/tests/test_kernel.py compute/tests/test_criterion.py -q`.
- [R] Proved the normalized Case-I gap-square identity:
  `Erdos699.four_mul_t_mul_X_sub_t_add_gap_sq_eq_sq` formalizes
  `4 * t * (X - t) + (X - 2 * t)^2 = X^2` under `2 * t ≤ X`, and
  `Erdos699.row_one_factor_gap_sq_eq_sq` specializes it to the row-one factor
  equation `t * (X - t) = g * (n - 1)`. This banks the exact algebra used by
  the squeezed normalized/Pell-style C2 lane; it is not a kernel contradiction.
- [OPEN] T4, full T6/T7, the kernel, and all later rungs remain unclaimed in
  this branch.
