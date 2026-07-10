/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686SmallBranch
import ErdosProblems.Erdos686EvenK

/-!
# Erdős Problem 686: refined conditional reduction

With the even cases `k ∈ {6, 8, 10, 12}` closed unconditionally at the
equation level (`Erdos686EvenK`), the open constant-quotient bound
hypothesis shrinks from eleven pairs to the seven pairs
`(5,3), (7,4), (9,6), (11,7), (13,8), (14,9), (15,10)` — the odd cases
plus `k = 14`, whose Runge argument currently reaches only
`d ≥ 663000`.  Because the even-`k` theorems refute the *equation*
rather than providing a window-only row escape, the refined reduction
splits at the solution level, where the block-product equation is in
hand.
-/

namespace Erdos686

namespace Erdos686Variant

/-- The seven constant pairs not yet closed at the equation level:
the odd `k` together with `(14, 9)`. -/
def constantQuotientPairMemOdd14 (k q : ℕ) : Prop :=
  (k, q) ∈ ([(5, 3), (7, 4), (9, 6), (11, 7), (13, 8), (14, 9), (15, 10)] :
    List (ℕ × ℕ))

/-- **The refined open constant-quotient bound**, now demanded only for
the seven pairs not closed by the even-`k` Runge theorems. -/
def ConstantCaseBoundHypothesisOdd14 : Prop :=
  ∀ k q d u A n : ℕ,
    constantQuotientPairMemOdd14 k q →
    221 ≤ d → 1 ≤ u → u < d →
    A = (q + 1) * d - u →
    n + 1 = A →
    (n + d + k) ^ k ≤ 4 * (n + k) ^ k →
    4 * (n + 1) ^ k ≤ (n + d + 1) ^ k →
    ((A : ℤ) ∣ residualRowPoly k q (d - u)) →
    (((A + 1 : ℕ) : ℤ) ∣ residualRowPoly k q (d - u + (q + 1))) →
    (((A + 2 : ℕ) : ℤ) ∣ residualRowPoly k q (d - u + 2 * (q + 1))) →
    d ≤ constantPrefixThreeBound k q

/-- The full-table hypothesis implies the seven-pair one. -/
theorem constantCaseBoundHypothesisOdd14_of_full
    (h : ConstantCaseBoundHypothesis) : ConstantCaseBoundHypothesisOdd14 := by
  intro k q d u A n hkq
  refine h k q d u A n ?_
  have hcases : (k = 5 ∧ q = 3) ∨ (k = 7 ∧ q = 4) ∨ (k = 9 ∧ q = 6) ∨
      (k = 11 ∧ q = 7) ∨ (k = 13 ∧ q = 8) ∨ (k = 14 ∧ q = 9) ∨
      (k = 15 ∧ q = 10) := by
    simpa [constantQuotientPairMemOdd14, List.mem_cons, Prod.mk.injEq]
      using hkq
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [constantQuotientPairMem, constantQuotientPairs]

/-- For `k ∈ [5,15]` outside `{6, 8, 10, 12}`, the tabulated pair lies
in the seven-pair list. -/
private lemma pairMemOdd14_of_not_even4 {k : ℕ}
    (hk5 : 5 ≤ k) (hk15 : k ≤ 15)
    (h6 : k ≠ 6) (h8 : k ≠ 8) (h10 : k ≠ 10) (h12 : k ≠ 12) :
    constantQuotientPairMemOdd14 k (constantQuotientOf k) := by
  interval_cases k <;>
    simp_all [constantQuotientPairMemOdd14, constantQuotientOf]

/-- **The refined conditional `N = 4` exclusion.**  Only the seven-pair
constant-quotient bound and the unrestricted large-`k` escape remain;
`k ∈ {6, 8, 10, 12}` is handled unconditionally by the even-`k` Runge
theorems together with the `d ≤ 220` finite core. -/
theorem no_solution_four_of_odd14_bound_and_large_escape
    (hbound : ConstantCaseBoundHypothesisOdd14)
    (hlarge : LargeKEscapeHypothesis) :
    ¬ ∃ k n m : ℕ,
      2 ≤ k ∧ m ≥ n + k ∧
      (4 : ℚ) =
        (∏ i ∈ Finset.Icc 1 k, (((m + i : ℕ) : ℚ))) /
          (∏ i ∈ Finset.Icc 1 k, (((n + i : ℕ) : ℚ))) := by
  rintro ⟨k, n, m, hk2, hm, hq⟩
  rcases Nat.lt_or_ge k 5 with hk4 | hk5
  · exact no_solution_four_le_four ⟨k, n, m, hk2, by omega, hm, hq⟩
  obtain ⟨d, hkd, rfl, heq⟩ := four_solution_with_gap_of_solution hm hq
  obtain ⟨hup, hlo⟩ := ratio_window_four_nat heq
  have hrows : ∀ j, j ∈ Finset.Icc 1 k →
      n + j ∣ shiftedDiffProductAt k d j :=
    fun j hj => individual_divisor_skeleton_four hkd hj heq
  -- a failing row yields the contradiction
  have hclose : (∃ j, j ∈ Finset.Icc 1 k ∧
      ¬ n + j ∣ shiftedDiffProductAt k d j) → False := by
    rintro ⟨j, hj, hnot⟩
    exact hnot (hrows j hj)
  rcases Nat.lt_or_ge k 16 with hk16 | hk16
  · -- 5 ≤ k ≤ 15
    by_cases h6 : k = 6
    · subst h6
      rcases Nat.lt_or_ge d 221 with hd | hd
      · exact hclose (row_full_escape_small_k_d_le_220 (by norm_num)
          (by norm_num) hkd (by omega) hup hlo)
      · exact no_gap_solution_four_even_six hd heq
    by_cases h8 : k = 8
    · subst h8
      rcases Nat.lt_or_ge d 221 with hd | hd
      · exact hclose (row_full_escape_small_k_d_le_220 (by norm_num)
          (by norm_num) hkd (by omega) hup hlo)
      · exact no_gap_solution_four_even_eight hd heq
    by_cases h10 : k = 10
    · subst h10
      rcases Nat.lt_or_ge d 221 with hd | hd
      · exact hclose (row_full_escape_small_k_d_le_220 (by norm_num)
          (by norm_num) hkd (by omega) hup hlo)
      · exact no_gap_solution_four_even_ten hd heq
    by_cases h12 : k = 12
    · subst h12
      rcases Nat.lt_or_ge d 221 with hd | hd
      · exact hclose (row_full_escape_small_k_d_le_220 (by norm_num)
          (by norm_num) hkd (by omega) hup hlo)
      · exact no_gap_solution_four_even_twelve hd heq
    · -- the seven remaining pairs
      exact hclose (row_full_escape_small_k_core hk5 (by omega) hkd hup hlo
        (fun d' u A n' => hbound k (constantQuotientOf k) d' u A n'
          (pairMemOdd14_of_not_even4 hk5 (by omega) h6 h8 h10 h12)))
  · exact hclose (hlarge k n d hk16 hkd hup hlo)

/-- **The refined complete conditional reduction of Erdős 686.** -/
theorem erdos686_false_of_odd14_bound_and_large_escape
    (hbound : ConstantCaseBoundHypothesisOdd14)
    (hlarge : LargeKEscapeHypothesis) :
    ¬ ∀ N : ℕ, 2 ≤ N → ∃ k n m : ℕ,
      2 ≤ k ∧ m ≥ n + k ∧
      (N : ℚ) =
        (∏ i ∈ Finset.Icc 1 k, (((m + i : ℕ) : ℚ))) /
          (∏ i ∈ Finset.Icc 1 k, (((n + i : ℕ) : ℚ))) := by
  intro hall
  exact no_solution_four_of_odd14_bound_and_large_escape hbound hlarge
    (hall 4 (by norm_num))

end Erdos686Variant

end Erdos686
