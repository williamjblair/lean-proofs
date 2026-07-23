import Research.FourthIncrementAxisBridge
import Research.FourthPerturbationLateTail
import Research.FourthCoordinateReduction
import Mathlib.Tactic

namespace Erdos521

noncomputable local instance fourthEvenCoordinateDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

noncomputable def fourthEvenHorizontalSmallWords (m : ℕ) (T : ℝ) :
    Finset (AxisWord (m + 1)) :=
  Finset.univ.filter fun w ↦ |fourthHorizontalEven (axisWordCoefficients w) m| ≤ 2 * T

noncomputable def fourthEvenHorizontalJumpWords (m : ℕ) (T : ℝ) :
    Finset (AxisWord (m + 1)) :=
  Finset.univ.filter fun w ↦ T ≤
    |fourthHorizontalOdd (axisWordCoefficients w) m -
      fourthHorizontalEven (axisWordCoefficients w) m|

lemma card_le_add_of_subset_union {α : Type*} [DecidableEq α]
    (A B C : Finset α) (h : A ⊆ B ∪ C) : A.card ≤ B.card + C.card := by
  exact (Finset.card_le_card h).trans (Finset.card_union_le B C)

lemma card_le_add_three_of_subset {α : Type*} [DecidableEq α]
    (A B C D : Finset α) (h : A ⊆ B ∪ C ∪ D) :
    A.card ≤ B.card + C.card + D.card := by
  exact (Finset.card_le_card h).trans
    ((Finset.card_union_le (B ∪ C) D).trans (Nat.add_le_add_right (Finset.card_union_le B C) _))

lemma fourthEvenHorizontalSmallWords_density_le (m : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    ((fourthEvenHorizontalSmallWords m T).card : ℝ) / (4 : ℝ) ^ (m + 1) ≤
      ((fourthIntegratedStripAxisWords (m + 1) (2 * m) (3 * T)).card : ℝ) /
          (4 : ℝ) ^ (m + 1) +
      ((fourthEvenPerturbationWords m T).card : ℝ) / (4 : ℝ) ^ (m + 1) := by
  have hsub : fourthEvenHorizontalSmallWords m T ⊆
      fourthIntegratedStripAxisWords (m + 1) (2 * m) (3 * T) ∪
        fourthEvenPerturbationWords m T := by
    intro w hw
    rw [fourthEvenHorizontalSmallWords, Finset.mem_filter] at hw
    rw [Finset.mem_union]
    have hred := fourthHorizontalEven_small_reduce (axisWordCoefficients w) m
      (T := T / 3) (by positivity) (by nlinarith [hw.2])
    rcases hred with hsmall | hp
    · left
      simp [fourthIntegratedStripAxisWords]
      nlinarith
    · right
      simp [fourthEvenPerturbationWords]
      nlinarith
  have hc := card_le_add_of_subset_union _ _ _ hsub
  have hden : 0 < (4 : ℝ) ^ (m + 1) := by positivity
  calc
    ((fourthEvenHorizontalSmallWords m T).card : ℝ) / (4 : ℝ) ^ (m + 1) ≤
        (((fourthIntegratedStripAxisWords (m + 1) (2 * m) (3 * T)).card +
          (fourthEvenPerturbationWords m T).card : ℕ) : ℝ) /
          (4 : ℝ) ^ (m + 1) := by
      apply div_le_div_of_nonneg_right _ hden.le
      exact_mod_cast hc
    _ = _ := by push_cast; ring

lemma fourthEvenHorizontalJumpWords_density_le (m : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    ((fourthEvenHorizontalJumpWords m T).card : ℝ) / (4 : ℝ) ^ (m + 1) ≤
      ((fourthIncrementAxisWords (m + 1) (2 * m) (T / 3)).card : ℝ) /
          (4 : ℝ) ^ (m + 1) +
      ((fourthOddPerturbationWords m (T / 3)).card : ℝ) / (4 : ℝ) ^ (m + 1) +
      ((fourthEvenPerturbationWords m (T / 3)).card : ℝ) / (4 : ℝ) ^ (m + 1) := by
  have hsub : fourthEvenHorizontalJumpWords m T ⊆
      fourthIncrementAxisWords (m + 1) (2 * m) (T / 3) ∪
        fourthOddPerturbationWords m (T / 3) ∪
          fourthEvenPerturbationWords m (T / 3) := by
    intro w hw
    rw [fourthEvenHorizontalJumpWords, Finset.mem_filter] at hw
    rw [Finset.mem_union, Finset.mem_union]
    have hred := fourthHorizontal_even_increment_large_reduce
      (axisWordCoefficients w) m (T := T / 3) (by nlinarith [hw.2])
    rcases hred with hd | hp | hp
    · left; left
      simp [fourthIncrementAxisWords]
      exact hd
    · left; right
      simp [fourthOddPerturbationWords]
      exact hp
    · right
      simp [fourthEvenPerturbationWords]
      exact hp
  have hc := card_le_add_three_of_subset _ _ _ _ hsub
  have hden : 0 < (4 : ℝ) ^ (m + 1) := by positivity
  calc
    ((fourthEvenHorizontalJumpWords m T).card : ℝ) / (4 : ℝ) ^ (m + 1) ≤
        (((fourthIncrementAxisWords (m + 1) (2 * m) (T / 3)).card +
          (fourthOddPerturbationWords m (T / 3)).card +
          (fourthEvenPerturbationWords m (T / 3)).card : ℕ) : ℝ) /
          (4 : ℝ) ^ (m + 1) := by
      apply div_le_div_of_nonneg_right _ hden.le
      exact_mod_cast hc
    _ = _ := by push_cast; ring

lemma fourthEvenHorizontalSmall_late_density_le (m : ℕ) (hm : 1 ≤ m) :
    ((fourthEvenHorizontalSmallWords m (fourthLateCutoff (2 * m - 2))).card : ℝ) /
        (4 : ℝ) ^ (m + 1) ≤
      fourthSignedStripProbability (2 * m) (3 * fourthLateCutoff (2 * m - 2)) +
        2 / (2 * m + 1 : ℝ) ^ 4 := by
  have h := fourthEvenHorizontalSmallWords_density_le m
    (T := (fourthLateCutoff (2 * m - 2) : ℝ)) (by positivity)
  have hcast : 3 * (fourthLateCutoff (2 * m - 2) : ℝ) =
      ((3 * fourthLateCutoff (2 * m - 2) : ℕ) : ℝ) := by norm_num
  rw [hcast, fourthIntegratedStripAxisWords_density_eq (2 * m) (m + 1)
      (3 * fourthLateCutoff (2 * m - 2)) (by omega)] at h
  have hp := fourthEvenPerturbation_late_density_le m hm
  exact h.trans (add_le_add_right hp _) 

lemma fourthOddPerturbation_evenCutoff_third_density_le (m : ℕ) (hm : 1 ≤ m) :
    ((fourthOddPerturbationWords m
      ((fourthLateCutoff (2 * m - 2) : ℝ) / 3)).card : ℝ) /
        (4 : ℝ) ^ (m + 1) ≤ 2 / (2 * m + 1 : ℝ) ^ 4 := by
  rw [fourthOddPerturbationWords_density_eq]
  have hn : 2 * m - 2 + 3 = 2 * m + 1 := by omega
  have hnr : (((2 * m - 2 : ℕ) : ℝ) + 3) = (2 * m + 1 : ℕ) := by exact_mod_cast hn
  have hV0 := fourthOddPerturbationVariance_le m
  have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hV : finiteRademacherVariance (fourthOddPerturbationWeight m) ≤
      128 * (((2 * m - 2 : ℕ) : ℝ) + 3) ^ 5 := by
    rw [hnr]
    exact hV0.trans (by gcongr; push_cast; linarith)
  have h := finiteRademacher_lateCutoff_third_tail_le
    (fourthOddPerturbationWeight m) (2 * m - 2)
    (fourthOddPerturbationVariance_pos m) hV
  rw [hnr] at h
  convert h using 1 <;> norm_num

lemma fourthEvenHorizontalJump_late_density_le (m : ℕ) (hm : 1 ≤ m) :
    ((fourthEvenHorizontalJumpWords m (fourthLateCutoff (2 * m - 2))).card : ℝ) /
        (4 : ℝ) ^ (m + 1) ≤ 6 / (2 * m + 1 : ℝ) ^ 4 := by
  have h := fourthEvenHorizontalJumpWords_density_le m
    (T := (fourthLateCutoff (2 * m - 2) : ℝ)) (by positivity)
  have hinc := fourthLateIncrement_third_tail_le (2 * m - 2)
  have hodd := fourthOddPerturbation_evenCutoff_third_density_le m hm
  have heven := fourthEvenPerturbation_third_late_density_le m hm
  rw [fourthIncrementAxisWords_density_eq (2 * m) (m + 1)
      ((fourthLateCutoff (2 * m - 2) : ℝ) / 3) (by omega)] at h
  have hn : 2 * m - 2 + 3 = 2 * m + 1 := by omega
  have hnr : (((2 * m - 2 : ℕ) : ℝ) + 3) = (2 * m + 1 : ℕ) := by exact_mod_cast hn
  rw [hnr] at hinc
  have hk : 2 * m - 2 + 2 = 2 * m := by omega
  rw [hk] at hinc
  have hinc' : finiteRademacherAbsTailProbability (fourthIncrementWeight (2 * m))
      ((fourthLateCutoff (2 * m - 2) : ℝ) / 3) ≤
      2 / (2 * m + 1 : ℝ) ^ 4 := by
    convert hinc using 1 <;> norm_num
  calc
    _ ≤ finiteRademacherAbsTailProbability (fourthIncrementWeight (2 * m))
          ((fourthLateCutoff (2 * m - 2) : ℝ) / 3) +
        ((fourthOddPerturbationWords m
          ((fourthLateCutoff (2 * m - 2) : ℝ) / 3)).card : ℝ) / (4 : ℝ) ^ (m + 1) +
        ((fourthEvenPerturbationWords m
          ((fourthLateCutoff (2 * m - 2) : ℝ) / 3)).card : ℝ) / (4 : ℝ) ^ (m + 1) := h
    _ ≤ 2 / (2 * m + 1 : ℝ) ^ 4 + 2 / (2 * m + 1 : ℝ) ^ 4 +
        2 / (2 * m + 1 : ℝ) ^ 4 := add_le_add (add_le_add hinc' hodd) heven
    _ = 6 / (2 * m + 1 : ℝ) ^ 4 := by ring

end Erdos521
