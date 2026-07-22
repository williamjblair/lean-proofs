/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.Core.LargeEscape

/-!
# Erdős Problem 686: the equation-level prime obstruction

A prime `q ≥ d + k` cannot divide elements of both blocks of the
`N = 4` equation: it would divide a positive difference
`(n + d + j) − (n + i) < d + k ≤ q`.  Hence if such a prime divides any
element of either block, the equation fails.  Consequently the equation
forces **every element of both blocks to be `(d+k)`-smooth**, which
collapses the open large-`k` core from a row-escape statement to an
extreme double-smoothness configuration.
-/

namespace Erdos686

namespace Erdos686Variant

/-- **Prime obstruction, lower block.**  A prime `q ≥ d + k` dividing
some element of the lower block refutes the `N = 4` block-product
equation. -/
theorem no_gap_solution_four_of_large_prime_factor
    {k n d q : ℕ} (hq : q.Prime) (hd : k ≤ d) (hqB : d + k ≤ q)
    (hdvd : ∃ i, i ∈ Finset.Icc 1 k ∧ q ∣ n + i) :
    blockProduct k (n + d) ≠ 4 * blockProduct k n := by
  intro heq
  obtain ⟨i, hi, hqi⟩ := hdvd
  have hi' := Finset.mem_Icc.mp hi
  have hq_low : q ∣ blockProduct k n :=
    dvd_trans hqi (Finset.dvd_prod_of_mem (fun j => n + j) hi)
  have hq_up : q ∣ blockProduct k (n + d) := by
    rw [heq]
    exact Dvd.dvd.mul_left hq_low 4
  obtain ⟨j, hj, hqj⟩ := prime_dvd_finset_prod_exists hq
    (by simpa [blockProduct] using hq_up)
  have hj' := Finset.mem_Icc.mp hj
  have hdiff : q ∣ (n + d + j) - (n + i) := Nat.dvd_sub hqj hqi
  have hpos : 0 < (n + d + j) - (n + i) := by omega
  have hle := Nat.le_of_dvd hpos hdiff
  omega

/-- **Prime obstruction, upper block.** -/
theorem no_gap_solution_four_of_large_prime_factor_upper
    {k n d q : ℕ} (hq : q.Prime) (hk2 : 2 ≤ k) (hd : k ≤ d)
    (hqB : d + k ≤ q)
    (hdvd : ∃ i, i ∈ Finset.Icc 1 k ∧ q ∣ n + d + i) :
    blockProduct k (n + d) ≠ 4 * blockProduct k n := by
  intro heq
  obtain ⟨i, hi, hqi⟩ := hdvd
  have hi' := Finset.mem_Icc.mp hi
  have hq_up : q ∣ blockProduct k (n + d) :=
    dvd_trans hqi (Finset.dvd_prod_of_mem (fun j => n + d + j) hi)
  have hq_4low : q ∣ 4 * blockProduct k n := by rw [← heq]; exact hq_up
  have hq_low : q ∣ blockProduct k n := by
    rcases (Nat.Prime.dvd_mul hq).mp hq_4low with h4 | h
    · have h22 : q ∣ 2 ^ 2 := by
        have h42 : (4 : ℕ) = 2 ^ 2 := by norm_num
        rwa [h42] at h4
      have hq2 : q ∣ 2 := hq.dvd_of_dvd_pow h22
      have := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hq2
      omega
    · exact h
  obtain ⟨j, hj, hqj⟩ := prime_dvd_finset_prod_exists hq
    (by simpa [blockProduct] using hq_low)
  have hj' := Finset.mem_Icc.mp hj
  have hdiff : q ∣ (n + d + i) - (n + j) := Nat.dvd_sub hqi hqj
  have hpos : 0 < (n + d + i) - (n + j) := by omega
  have hle := Nat.le_of_dvd hpos hdiff
  omega

/-- **The double-smoothness open hypothesis**: no `N = 4` equation
solution with `k ≥ 16` can have every element of its lower block
`(d+k)`-smooth.  (By the prime obstruction this is all that remains of
the large-`k` branch.) -/
def LargeKSmoothHypothesis : Prop :=
  ∀ k n d : ℕ, 16 ≤ k → k ≤ d →
    blockProduct k (n + d) = 4 * blockProduct k n →
    (∀ i, i ∈ Finset.Icc 1 k → ∀ q, q.Prime → q ∣ n + i → q < d + k) →
    False

/-- The double-smoothness hypothesis suffices for the large-`k`
branch at the equation level: every equation solution with `k ≥ 16`
is refuted. -/
theorem no_gap_solution_large_k_of_smooth
    (hsmooth : LargeKSmoothHypothesis)
    {k n d : ℕ} (hk : 16 ≤ k) (hd : k ≤ d) :
    blockProduct k (n + d) ≠ 4 * blockProduct k n := by
  intro heq
  by_cases hall : ∀ i, i ∈ Finset.Icc 1 k → ∀ q, q.Prime → q ∣ n + i →
      q < d + k
  · exact hsmooth k n d hk hd heq hall
  · simp only [not_forall, not_lt] at hall
    obtain ⟨i, hi, q, hq, hqi, hqB⟩ := hall
    exact no_gap_solution_four_of_large_prime_factor hq hd (by omega)
      ⟨i, hi, hqi⟩ heq

/-- For odd `k ∈ [5,15]`, the tabulated pair lies in the six-pair
list (local copy of the private lemma in the reduction module). -/
private lemma pairMemOdd_of_odd' {k : ℕ}
    (hk5 : 5 ≤ k) (hk15 : k ≤ 15)
    (h6 : k ≠ 6) (h8 : k ≠ 8) (h10 : k ≠ 10) (h12 : k ≠ 12)
    (h14 : k ≠ 14) :
    constantQuotientPairMemOdd k (constantQuotientOf k) := by
  interval_cases k <;>
    simp_all [constantQuotientPairMemOdd, constantQuotientOf]

/-- **The final conditional reduction, smoothness form**: the six-pair
odd constant-quotient bound plus the large-`k` double-smoothness
hypothesis refute the universal Erdős 686 statement. -/
theorem erdos686_false_of_odd_bound_and_smooth
    (hbound : ConstantCaseBoundHypothesisOdd)
    (hsmooth : LargeKSmoothHypothesis) :
    ¬ ∀ N : ℕ, 2 ≤ N → ∃ k n m : ℕ,
      2 ≤ k ∧ m ≥ n + k ∧
      (N : ℚ) =
        (∏ i ∈ Finset.Icc 1 k, (((m + i : ℕ) : ℚ))) /
          (∏ i ∈ Finset.Icc 1 k, (((n + i : ℕ) : ℚ))) := by
  intro hall
  rcases hall 4 (by norm_num) with ⟨k, n, m, hk2, hm, hq⟩
  rcases Nat.lt_or_ge k 5 with hk4 | hk5
  · exact no_solution_four_le_four ⟨k, n, m, hk2, by omega, hm, hq⟩
  obtain ⟨d, hkd, rfl, heq⟩ := four_solution_with_gap_of_solution hm hq
  rcases Nat.lt_or_ge k 16 with hk16 | hk16
  · -- 5 ≤ k ≤ 15: reuse the banked solution-level dispatch by feeding
    -- the large-k escape vacuously restricted... instead reuse the
    -- existing reduction theorem applied to a singleton universal:
    obtain ⟨hup, hlo⟩ := ratio_window_four_nat heq
    have hrows : ∀ j, j ∈ Finset.Icc 1 k →
        n + j ∣ shiftedDiffProductAt k d j :=
      fun j hj => individual_divisor_skeleton_four hkd hj heq
    by_cases heven : k ∈ ({6, 8, 10, 12, 14} : Finset ℕ)
    · rcases Nat.lt_or_ge d 221 with hd | hd
      · obtain ⟨j, hj, hnot⟩ := row_full_escape_small_k_d_le_220 hk5
          (by omega) hkd (by omega) hup hlo
        exact hnot (hrows j hj)
      · exact no_gap_solution_four_even_k heven hd heq
    · have h6 : k ≠ 6 := fun h => heven (by simp [h])
      have h8 : k ≠ 8 := fun h => heven (by simp [h])
      have h10 : k ≠ 10 := fun h => heven (by simp [h])
      have h12 : k ≠ 12 := fun h => heven (by simp [h])
      have h14 : k ≠ 14 := fun h => heven (by simp [h])
      obtain ⟨j, hj, hnot⟩ := row_full_escape_small_k_core hk5 (by omega)
        hkd hup hlo
        (fun d' u A n' => hbound k (constantQuotientOf k) d' u A n'
          (pairMemOdd_of_odd' hk5 (by omega) h6 h8 h10 h12 h14))
      exact hnot (hrows j hj)
  · exact no_gap_solution_large_k_of_smooth hsmooth hk16 hkd heq

end Erdos686Variant

end Erdos686
