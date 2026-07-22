/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.Core.PrimeObstruction
import ErdosProblems.Erdos686.Core.FiveThue
import ErdosProblems.Erdos686.Core.SevenThue
import ErdosProblems.Erdos686.Core.NineThue
import ErdosProblems.Erdos686.Core.ElevenThue
import ErdosProblems.Erdos686.Core.ThirteenThue
import ErdosProblems.Erdos686.Core.FifteenThue

/-!
# Erdős Problem 686: the terminal conditional reduction

Every piece of the `N = 4` refutation is now unconditional except:

* six Diophantine **tails** — for odd `k ∈ {5, 7, 9, 11, 13, 15}`, the
  centered equation `P_k(X) = 4·P_k(Y)` has no solution with gap
  `d ≥ 10^120` (all solutions with `d < 10^120` are already refuted by
  the banked Farey-descent certificates);
* the **large-`k` double-smoothness** statement — no equation solution
  with `k ≥ 16` has an entirely `(d+k)`-smooth lower block (any
  non-smooth element is refuted by the banked prime obstruction).

This module assembles the terminal theorem: those seven hypotheses
refute the universal Erdős 686 statement.
-/

namespace Erdos686

namespace Erdos686Variant

/-- **The six odd Thue tails**: no `N = 4` equation solution with gap
`d ≥ 10^120` for odd `k ∈ {5, 7, 9, 11, 13, 15}`. -/
def OddThueTailHypothesis : Prop :=
  ∀ k, k ∈ ({5, 7, 9, 11, 13, 15} : Finset ℕ) →
    NoLargeGapSolutionFour k (10 ^ 120)

/-- Unconditional small-`k` equation exclusion below the tails: for
every `5 ≤ k ≤ 15` and `221 ≤ d < 10^120` the `N = 4` block-product
equation is impossible. -/
theorem no_gap_solution_four_small_k_below
    {k n d : ℕ} (hk5 : 5 ≤ k) (hk15 : k ≤ 15)
    (hd : 221 ≤ d) (hB : d < 10 ^ 120) :
    blockProduct k (n + d) ≠ 4 * blockProduct k n := by
  by_cases heven : k ∈ ({6, 8, 10, 12, 14} : Finset ℕ)
  · exact no_gap_solution_four_even_k heven hd
  · have hodd : k = 5 ∨ k = 7 ∨ k = 9 ∨ k = 11 ∨ k = 13 ∨ k = 15 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at heven
      omega
    rcases hodd with rfl | rfl | rfl | rfl | rfl | rfl
    · exact no_gap_solution_four_five_below_ext hd hB
    · exact no_gap_solution_four_seven_below_ext hd hB
    · exact no_gap_solution_four_nine_below_ext hd hB
    · exact no_gap_solution_four_eleven_below_ext hd hB
    · exact no_gap_solution_four_thirteen_below_ext hd hB
    · exact no_gap_solution_four_fifteen_below_ext hd hB

/-- **The terminal conditional reduction of Erdős 686.**  The six odd
Thue tails and the large-`k` double-smoothness hypothesis refute the
universal positive statement. -/
theorem erdos686_false_of_thue_tails_and_smooth
    (htails : OddThueTailHypothesis)
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
  · -- 5 ≤ k ≤ 15
    rcases Nat.lt_or_ge d 221 with hd | hd
    · -- finite core: some row fails, contradicting the skeleton
      obtain ⟨hup, hlo⟩ := ratio_window_four_nat heq
      obtain ⟨j, hj, hnot⟩ := row_full_escape_small_k_d_le_220 hk5
        (by omega) hkd (by omega) hup hlo
      exact hnot (individual_divisor_skeleton_four hkd hj heq)
    · rcases Nat.lt_or_ge d (10 ^ 120) with hB | hB
      · exact no_gap_solution_four_small_k_below hk5 (by omega) hd hB heq
      · -- the tails
        by_cases heven : k ∈ ({6, 8, 10, 12, 14} : Finset ℕ)
        · exact no_gap_solution_four_even_k heven hd heq
        · have hodd : k ∈ ({5, 7, 9, 11, 13, 15} : Finset ℕ) := by
            simp only [Finset.mem_insert, Finset.mem_singleton] at heven ⊢
            omega
          exact htails k hodd n d hB heq
  · exact no_gap_solution_large_k_of_smooth hsmooth hk16 hkd heq

/-- The terminal `N = 4` exclusion under the same seven hypotheses. -/
theorem no_solution_four_of_thue_tails_and_smooth
    (htails : OddThueTailHypothesis)
    (hsmooth : LargeKSmoothHypothesis) :
    ¬ ∃ k n m : ℕ,
      2 ≤ k ∧ m ≥ n + k ∧
      (4 : ℚ) =
        (∏ i ∈ Finset.Icc 1 k, (((m + i : ℕ) : ℚ))) /
          (∏ i ∈ Finset.Icc 1 k, (((n + i : ℕ) : ℚ))) := by
  rintro ⟨k, n, m, hk2, hm, hq⟩
  rcases Nat.lt_or_ge k 5 with hk4 | hk5
  · exact no_solution_four_le_four ⟨k, n, m, hk2, by omega, hm, hq⟩
  obtain ⟨d, hkd, rfl, heq⟩ := four_solution_with_gap_of_solution hm hq
  rcases Nat.lt_or_ge k 16 with hk16 | hk16
  · rcases Nat.lt_or_ge d 221 with hd | hd
    · obtain ⟨hup, hlo⟩ := ratio_window_four_nat heq
      obtain ⟨j, hj, hnot⟩ := row_full_escape_small_k_d_le_220 hk5
        (by omega) hkd (by omega) hup hlo
      exact hnot (individual_divisor_skeleton_four hkd hj heq)
    · rcases Nat.lt_or_ge d (10 ^ 120) with hB | hB
      · exact no_gap_solution_four_small_k_below hk5 (by omega) hd hB heq
      · by_cases heven : k ∈ ({6, 8, 10, 12, 14} : Finset ℕ)
        · exact no_gap_solution_four_even_k heven hd heq
        · have hodd : k ∈ ({5, 7, 9, 11, 13, 15} : Finset ℕ) := by
            simp only [Finset.mem_insert, Finset.mem_singleton] at heven ⊢
            omega
          exact htails k hodd n d hB heq
  · exact no_gap_solution_large_k_of_smooth hsmooth hk16 hkd heq

end Erdos686Variant

end Erdos686
