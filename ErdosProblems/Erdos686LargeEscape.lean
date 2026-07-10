/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686Reduction

/-!
# Erdős Problem 686: the anatomical form of the large-`k` escape

A complete census (k ≤ 6500, n ≤ 3·10⁷) shows that every deep
row-prefix survivor of the `N = 4` ratio window fails some row `j` by a
single mechanism: a prime `p ∣ n + j` with no multiple of `p` in the
row-`j` interval `[d+1−j, d+k−j]` — and 64–69 % of all rows of the deep
points carry such a prime.  This module banks the elementary reduction
from that anatomical statement to `LargeKEscapeHypothesis`, so the open
large-`k` core becomes purely a statement about the multiplicative
anatomy of `k` consecutive integers against a sliding window.
-/

namespace Erdos686

namespace Erdos686Variant

/-- If a prime divisor of `n + j` divides no element of the row-`j`
interval, row `j` of the divisor skeleton fails. -/
theorem row_escape_of_no_multiple_prime
    {k n d j p : ℕ}
    (hp : p.Prime)
    (hpdiv : p ∣ n + j)
    (hnomult : ∀ i, i ∈ Finset.Icc 1 k → ¬ p ∣ (d + i - j)) :
    ¬ (n + j ∣ shiftedDiffProductAt k d j) := by
  intro hrow
  have hp_prod : p ∣ ∏ i ∈ Finset.Icc 1 k, (d + i - j) := by
    simpa [shiftedDiffProductAt] using dvd_trans hpdiv hrow
  obtain ⟨i, hi, hpi⟩ := prime_dvd_finset_prod_exists hp hp_prod
  exact hnomult i hi hpi

/-- **The anatomical large-`k` hypothesis**: every `k ≥ 16` point of
the exact ratio window has a row `j` whose modulus `n + j` carries a
prime with no multiple in the row-`j` interval. -/
def NoMultiplePrimeHypothesis : Prop :=
  ∀ k n d : ℕ, 16 ≤ k → k ≤ d →
    (n + d + k) ^ k ≤ 4 * (n + k) ^ k →
    4 * (n + 1) ^ k ≤ (n + d + 1) ^ k →
    ∃ j, j ∈ Finset.Icc 1 k ∧ ∃ p, p.Prime ∧ p ∣ n + j ∧
      ∀ i, i ∈ Finset.Icc 1 k → ¬ p ∣ (d + i - j)

/-- The anatomical hypothesis implies the unrestricted large-`k`
escape. -/
theorem largeKEscape_of_noMultiplePrime
    (h : NoMultiplePrimeHypothesis) : LargeKEscapeHypothesis := by
  intro k n d hk16 hkd hup hlo
  obtain ⟨j, hj, p, hp, hpdiv, hnomult⟩ := h k n d hk16 hkd hup hlo
  exact ⟨j, hj, row_escape_of_no_multiple_prime hp hpdiv hnomult⟩

/-- The complete conditional reduction in anatomical form: the
seven-pair constant-quotient bound and the no-multiple-prime anatomy
refute the universal Erdős 686 statement. -/
theorem erdos686_false_of_odd14_bound_and_no_multiple_prime
    (hbound : ConstantCaseBoundHypothesisOdd14)
    (hanat : NoMultiplePrimeHypothesis) :
    ¬ ∀ N : ℕ, 2 ≤ N → ∃ k n m : ℕ,
      2 ≤ k ∧ m ≥ n + k ∧
      (N : ℚ) =
        (∏ i ∈ Finset.Icc 1 k, (((m + i : ℕ) : ℚ))) /
          (∏ i ∈ Finset.Icc 1 k, (((n + i : ℕ) : ℚ))) :=
  erdos686_false_of_odd14_bound_and_large_escape hbound
    (largeKEscape_of_noMultiplePrime hanat)

end Erdos686Variant

end Erdos686
