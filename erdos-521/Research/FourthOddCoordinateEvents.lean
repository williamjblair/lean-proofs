import Research.FourthOddPerturbationExtension
import Mathlib.Tactic

namespace Erdos521

noncomputable local instance fourthOddCoordinateDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

noncomputable def fourthOddHorizontalSmallWords (m : ℕ) (T : ℝ) :
    Finset (AxisWord (m + 2)) :=
  Finset.univ.filter fun w ↦ |fourthHorizontalOdd (axisWordCoefficients w) m| ≤ 2 * T

noncomputable def fourthOddHorizontalJumpWords (m : ℕ) (T : ℝ) :
    Finset (AxisWord (m + 2)) :=
  Finset.univ.filter fun w ↦ T ≤
    |fourthHorizontalEven (axisWordCoefficients w) (m + 1) -
      fourthHorizontalOdd (axisWordCoefficients w) m|

lemma fourthOddHorizontalSmallWords_density_le (m : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    ((fourthOddHorizontalSmallWords m T).card : ℝ) / (4 : ℝ) ^ (m + 2) ≤
      ((fourthIntegratedStripAxisWords (m + 2) (2 * m + 1) (3 * T)).card : ℝ) /
          (4 : ℝ) ^ (m + 2) +
      ((fourthOddPerturbationExtendedWords m T).card : ℝ) / (4 : ℝ) ^ (m + 2) := by
  have hsub : fourthOddHorizontalSmallWords m T ⊆
      fourthIntegratedStripAxisWords (m + 2) (2 * m + 1) (3 * T) ∪
        fourthOddPerturbationExtendedWords m T := by
    intro w hw
    rw [fourthOddHorizontalSmallWords, Finset.mem_filter] at hw
    rw [Finset.mem_union]
    have hred := fourthHorizontalOdd_small_reduce (axisWordCoefficients w) m
      (T := T / 3) (by positivity) (by nlinarith [hw.2])
    rcases hred with hsmall | hp
    · left
      simp [fourthIntegratedStripAxisWords]
      nlinarith
    · right
      simp [fourthOddPerturbationExtendedWords]
      nlinarith
  have hc := card_le_add_of_subset_union _ _ _ hsub
  have hden : 0 < (4 : ℝ) ^ (m + 2) := by positivity
  calc
    ((fourthOddHorizontalSmallWords m T).card : ℝ) / (4 : ℝ) ^ (m + 2) ≤
        (((fourthIntegratedStripAxisWords (m + 2) (2 * m + 1) (3 * T)).card +
          (fourthOddPerturbationExtendedWords m T).card : ℕ) : ℝ) /
          (4 : ℝ) ^ (m + 2) := by
      apply div_le_div_of_nonneg_right _ hden.le
      exact_mod_cast hc
    _ = _ := by push_cast; ring

lemma fourthOddHorizontalJumpWords_density_le (m : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    ((fourthOddHorizontalJumpWords m T).card : ℝ) / (4 : ℝ) ^ (m + 2) ≤
      ((fourthIncrementAxisWords (m + 2) (2 * m + 1) (T / 3)).card : ℝ) /
          (4 : ℝ) ^ (m + 2) +
      ((fourthEvenPerturbationWords (m + 1) (T / 3)).card : ℝ) / (4 : ℝ) ^ (m + 2) +
      ((fourthOddPerturbationExtendedWords m (T / 3)).card : ℝ) /
        (4 : ℝ) ^ (m + 2) := by
  have hsub : fourthOddHorizontalJumpWords m T ⊆
      fourthIncrementAxisWords (m + 2) (2 * m + 1) (T / 3) ∪
        fourthEvenPerturbationWords (m + 1) (T / 3) ∪
          fourthOddPerturbationExtendedWords m (T / 3) := by
    intro w hw
    rw [fourthOddHorizontalJumpWords, Finset.mem_filter] at hw
    rw [Finset.mem_union, Finset.mem_union]
    have hred := fourthHorizontal_odd_increment_large_reduce
      (axisWordCoefficients w) m (T := T / 3) (by nlinarith [hw.2])
    rcases hred with hd | hp | hp
    · left; left
      simp [fourthIncrementAxisWords]
      exact hd
    · left; right
      simp [fourthEvenPerturbationWords]
      exact hp
    · right
      simp [fourthOddPerturbationExtendedWords]
      exact hp
  have hc := card_le_add_three_of_subset _ _ _ _ hsub
  have hden : 0 < (4 : ℝ) ^ (m + 2) := by positivity
  calc
    ((fourthOddHorizontalJumpWords m T).card : ℝ) / (4 : ℝ) ^ (m + 2) ≤
        (((fourthIncrementAxisWords (m + 2) (2 * m + 1) (T / 3)).card +
          (fourthEvenPerturbationWords (m + 1) (T / 3)).card +
          (fourthOddPerturbationExtendedWords m (T / 3)).card : ℕ) : ℝ) /
          (4 : ℝ) ^ (m + 2) := by
      apply div_le_div_of_nonneg_right _ hden.le
      exact_mod_cast hc
    _ = _ := by push_cast; ring

lemma fourthOddHorizontalSmall_late_density_le (m : ℕ) (hm : 1 ≤ m) :
    ((fourthOddHorizontalSmallWords m (fourthLateCutoff (2 * m - 1))).card : ℝ) /
        (4 : ℝ) ^ (m + 2) ≤
      fourthSignedStripProbability (2 * m + 1) (3 * fourthLateCutoff (2 * m - 1)) +
        2 / (2 * m + 2 : ℝ) ^ 4 := by
  have h := fourthOddHorizontalSmallWords_density_le m
    (T := (fourthLateCutoff (2 * m - 1) : ℝ)) (by positivity)
  have hcast : 3 * (fourthLateCutoff (2 * m - 1) : ℝ) =
      ((3 * fourthLateCutoff (2 * m - 1) : ℕ) : ℝ) := by norm_num
  rw [hcast, fourthIntegratedStripAxisWords_density_eq (2 * m + 1) (m + 2)
      (3 * fourthLateCutoff (2 * m - 1)) (by omega),
    fourthOddPerturbationExtendedWords_density_eq] at h
  have hp := fourthOddPerturbation_late_density_le m hm
  exact h.trans (add_le_add_right hp _)

lemma fourthEvenPerturbation_oddCutoff_third_density_le (m : ℕ) (hm : 1 ≤ m) :
    ((fourthEvenPerturbationWords (m + 1)
      ((fourthLateCutoff (2 * m - 1) : ℝ) / 3)).card : ℝ) /
        (4 : ℝ) ^ (m + 2) ≤ 2 / (2 * m + 2 : ℝ) ^ 4 := by
  rw [fourthEvenPerturbationWords_density_eq]
  have hn : 2 * m - 1 + 3 = 2 * m + 2 := by omega
  have hnr : (((2 * m - 1 : ℕ) : ℝ) + 3) = (2 * m + 2 : ℕ) := by exact_mod_cast hn
  have hV0 := fourthEvenPerturbationVariance_le (m + 1)
  have hV : finiteRademacherVariance (fourthEvenPerturbationWeight (m + 1)) ≤
      128 * (((2 * m - 1 : ℕ) : ℝ) + 3) ^ 5 := by
    rw [hnr]
    exact hV0.trans (by gcongr; push_cast; linarith)
  have h := finiteRademacher_lateCutoff_third_tail_le
    (fourthEvenPerturbationWeight (m + 1)) (2 * m - 1)
    (fourthEvenPerturbationVariance_pos (m + 1)) hV
  rw [hnr] at h
  convert h using 1 <;> norm_num

lemma fourthOddHorizontalJump_late_density_le (m : ℕ) (hm : 1 ≤ m) :
    ((fourthOddHorizontalJumpWords m (fourthLateCutoff (2 * m - 1))).card : ℝ) /
        (4 : ℝ) ^ (m + 2) ≤ 6 / (2 * m + 2 : ℝ) ^ 4 := by
  have h := fourthOddHorizontalJumpWords_density_le m
    (T := (fourthLateCutoff (2 * m - 1) : ℝ)) (by positivity)
  rw [fourthIncrementAxisWords_density_eq (2 * m + 1) (m + 2)
      ((fourthLateCutoff (2 * m - 1) : ℝ) / 3) (by omega),
    fourthOddPerturbationExtendedWords_density_eq] at h
  have hinc := fourthLateIncrement_third_tail_le (2 * m - 1)
  have heven := fourthEvenPerturbation_oddCutoff_third_density_le m hm
  have hodd := fourthOddPerturbation_third_late_density_le m hm
  have hn : 2 * m - 1 + 3 = 2 * m + 2 := by omega
  have hnr : (((2 * m - 1 : ℕ) : ℝ) + 3) = (2 * m + 2 : ℕ) := by exact_mod_cast hn
  rw [hnr] at hinc
  have hk : 2 * m - 1 + 2 = 2 * m + 1 := by omega
  rw [hk] at hinc
  have hinc' : finiteRademacherAbsTailProbability (fourthIncrementWeight (2 * m + 1))
      ((fourthLateCutoff (2 * m - 1) : ℝ) / 3) ≤ 2 / (2 * m + 2 : ℝ) ^ 4 := by
    convert hinc using 1 <;> norm_num
  calc
    _ ≤ finiteRademacherAbsTailProbability (fourthIncrementWeight (2 * m + 1))
          ((fourthLateCutoff (2 * m - 1) : ℝ) / 3) +
        ((fourthEvenPerturbationWords (m + 1)
          ((fourthLateCutoff (2 * m - 1) : ℝ) / 3)).card : ℝ) / (4 : ℝ) ^ (m + 2) +
        ((fourthOddPerturbationWords m
          ((fourthLateCutoff (2 * m - 1) : ℝ) / 3)).card : ℝ) / (4 : ℝ) ^ (m + 1) := h
    _ ≤ 2 / (2 * m + 2 : ℝ) ^ 4 + 2 / (2 * m + 2 : ℝ) ^ 4 +
        2 / (2 * m + 2 : ℝ) ^ 4 := add_le_add (add_le_add hinc' heven) hodd
    _ = 6 / (2 * m + 2 : ℝ) ^ 4 := by ring

end Erdos521
