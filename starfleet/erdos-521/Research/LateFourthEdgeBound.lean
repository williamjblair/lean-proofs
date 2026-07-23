import Research.AxisVerticalEventTransfer
import Research.FourthLateStripRate
import Mathlib.Tactic

open Filter
open scoped BigOperators Topology

set_option maxHeartbeats 1000000

namespace Erdos521

noncomputable local instance lateFourthEdgeDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

lemma natCard_subtype_eq_filter {α : Type*} [Fintype α] (P : α → Prop) :
    Nat.card {x : α // P x} = (Finset.univ.filter P).card := by
  rw [Nat.card_eq_fintype_card, card_subtype_eq_filter]

lemma natCard_subtype_le_add_four {α : Type*} [Fintype α]
    (P A B C D : α → Prop)
    (h : ∀ x, P x → A x ∨ B x ∨ C x ∨ D x) :
    Nat.card {x : α // P x} ≤ Nat.card {x : α // A x} +
      Nat.card {x : α // B x} + Nat.card {x : α // C x} +
        Nat.card {x : α // D x} := by
  simp_rw [natCard_subtype_eq_filter]
  have hsub : Finset.univ.filter P ⊆
      ((Finset.univ.filter A ∪ Finset.univ.filter B) ∪ Finset.univ.filter C) ∪
        Finset.univ.filter D := by
    intro x hx
    have hxP := (Finset.mem_filter.mp hx).2
    rcases h x hxP with hA | hB | hC | hD
    · simp [hA]
    · simp [hB]
    · simp [hC]
    · simp [hD]
  exact (Finset.card_le_card hsub).trans <| by
    calc
      ((((Finset.univ.filter A ∪ Finset.univ.filter B) ∪ Finset.univ.filter C) ∪
          Finset.univ.filter D).card) ≤
          ((Finset.univ.filter A ∪ Finset.univ.filter B) ∪
            Finset.univ.filter C).card + (Finset.univ.filter D).card :=
        Finset.card_union_le _ _
      _ ≤ (Finset.univ.filter A ∪ Finset.univ.filter B).card +
          (Finset.univ.filter C).card + (Finset.univ.filter D).card :=
        Nat.add_le_add_right
          (Finset.card_union_le
            (Finset.univ.filter A ∪ Finset.univ.filter B) (Finset.univ.filter C)) _
      _ ≤ (Finset.univ.filter A).card + (Finset.univ.filter B).card +
          (Finset.univ.filter C).card + (Finset.univ.filter D).card :=
        Nat.add_le_add_right
          (Nat.add_le_add_right
            (Finset.card_union_le (Finset.univ.filter A) (Finset.univ.filter B)) _) _

lemma evenFourthCrossing_axisGood_density_le (s m : ℕ) (hm : 1 ≤ m) :
    (Nat.card {p : AxisGoodPath (s + (m + 1)) //
        fourthIntegratedRademacherSum (axisWordCoefficients (axisSuffix p)) (2 * m) *
          fourthIntegratedRademacherSum (axisWordCoefficients (axisSuffix p)) (2 * m + 1) ≤ 0} : ℝ) /
        Nat.card (AxisGoodPath (s + (m + 1))) ≤
      128 * Real.sqrt (((s : ℝ) + ((m + 1 : ℕ) : ℝ) + 1) / (s + 1 : ℝ)) *
        (fourthSignedStripProbability (2 * m)
            (3 * fourthLateCutoff (2 * m - 2)) +
          12 / (2 * m + 1 : ℝ) ^ 4) +
      64 * ((s : ℝ) + ((m + 1 : ℕ) : ℝ) + 1) *
        Real.exp (-((s : ℝ) + ((m + 1 : ℕ) : ℝ)) / 8) := by
  let T : ℝ := fourthLateCutoff (2 * m - 2)
  let Cross : AxisGoodPath (s + (m + 1)) → Prop := fun p ↦
    fourthIntegratedRademacherSum (axisWordCoefficients (axisSuffix p)) (2 * m) *
      fourthIntegratedRademacherSum (axisWordCoefficients (axisSuffix p)) (2 * m + 1) ≤ 0
  let A : AxisGoodPath (s + (m + 1)) → Prop := fun p ↦
    axisSuffix p ∈ fourthEvenHorizontalSmallWords m T
  let B : AxisGoodPath (s + (m + 1)) → Prop := fun p ↦
    axisSuffix p ∈ fourthEvenHorizontalJumpWords m T
  let C : AxisGoodPath (s + (m + 1)) → Prop := fun p ↦
    axisSuffix p ∈ fourthEvenPerturbationWords m T
  let D : AxisGoodPath (s + (m + 1)) → Prop := fun p ↦
    axisSuffix p ∈ fourthOddPerturbationWords m T
  have hsplit : ∀ p, Cross p → A p ∨ B p ∨ C p ∨ D p := by
    intro p hp
    have hs := fourth_even_crossing_threshold_split
      (axisWordCoefficients (axisSuffix p)) m (T := T) (by positivity) hp
    simpa [A, B, C, D, fourthEvenHorizontalSmallWords,
      fourthEvenHorizontalJumpWords, fourthEvenPerturbationWords,
      fourthOddPerturbationWords] using hs
  have hcard := natCard_subtype_le_add_four Cross A B C D hsplit
  have hA := fourthEvenHorizontalSmall_axisGood_density_le s m T
  have hB := fourthEvenHorizontalJump_axisGood_density_le s m T
  have hC0 := fourthVerticalEven_axisGood_density_le s (m + 1) m (by omega) T
  have hD0 := fourthVerticalOdd_axisGood_density_le s (m + 1) m (by omega) T
  have hC : (Nat.card {p : AxisGoodPath (s + (m + 1)) // C p} : ℝ) /
      Nat.card (AxisGoodPath (s + (m + 1))) ≤
      128 * Real.sqrt (((s : ℝ) + ((m + 1 : ℕ) : ℝ) + 1) / (s + 1 : ℝ)) *
        (((fourthEvenPerturbationWords m T).card : ℝ) / (4 : ℝ) ^ (m + 1)) +
      16 * ((s : ℝ) + ((m + 1 : ℕ) : ℝ) + 1) *
        Real.exp (-((s : ℝ) + ((m + 1 : ℕ) : ℝ)) / 8) := by
    simpa [C, fourthEvenPerturbationWords] using hC0
  have hD : (Nat.card {p : AxisGoodPath (s + (m + 1)) // D p} : ℝ) /
      Nat.card (AxisGoodPath (s + (m + 1))) ≤
      128 * Real.sqrt (((s : ℝ) + ((m + 1 : ℕ) : ℝ) + 1) / (s + 1 : ℝ)) *
        (((fourthOddPerturbationWords m T).card : ℝ) / (4 : ℝ) ^ (m + 1)) +
      16 * ((s : ℝ) + ((m + 1 : ℕ) : ℝ) + 1) *
        Real.exp (-((s : ℝ) + ((m + 1 : ℕ) : ℝ)) / 8) := by
    simpa [D, fourthOddPerturbationWords] using hD0
  have hAid := fourthEvenHorizontalSmall_late_density_le m hm
  have hBid := fourthEvenHorizontalJump_late_density_le m hm
  have hCid := fourthEvenPerturbation_late_density_le m hm
  have hDid :
      ((fourthOddPerturbationWords m T).card : ℝ) / (4 : ℝ) ^ (m + 1) ≤
        2 / (2 * m + 1 : ℝ) ^ 4 := by
    have hthird := fourthOddPerturbation_evenCutoff_third_density_le m hm
    have hsub : fourthOddPerturbationWords m T ⊆
        fourthOddPerturbationWords m (T / 3) := by
      intro w hw
      simp only [fourthOddPerturbationWords, Finset.mem_filter,
        Finset.mem_univ, true_and] at hw ⊢
      have hT : 0 ≤ T := by positivity
      linarith
    have hc : ((fourthOddPerturbationWords m T).card : ℝ) ≤
        (fourthOddPerturbationWords m (T / 3)).card := by
      exact_mod_cast Finset.card_le_card hsub
    exact (div_le_div_of_nonneg_right hc (by positivity)).trans (by
      simpa [T] using hthird)
  have hden : (0 : ℝ) < Nat.card (AxisGoodPath (s + (m + 1))) := by
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast card_axisGoodPath_pos (s + (m + 1))
  have hcross : (Nat.card {p : AxisGoodPath (s + (m + 1)) // Cross p} : ℝ) /
      Nat.card (AxisGoodPath (s + (m + 1))) ≤
      (Nat.card {p : AxisGoodPath (s + (m + 1)) // A p} : ℝ) /
          Nat.card (AxisGoodPath (s + (m + 1))) +
      (Nat.card {p : AxisGoodPath (s + (m + 1)) // B p} : ℝ) /
          Nat.card (AxisGoodPath (s + (m + 1))) +
      (Nat.card {p : AxisGoodPath (s + (m + 1)) // C p} : ℝ) /
          Nat.card (AxisGoodPath (s + (m + 1))) +
      (Nat.card {p : AxisGoodPath (s + (m + 1)) // D p} : ℝ) /
          Nat.card (AxisGoodPath (s + (m + 1))) := by
    rw [← add_div, ← add_div, ← add_div]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) hden.le
  dsimp [T] at hDid
  have hbase :
      (((fourthEvenHorizontalSmallWords m T).card : ℝ) / (4 : ℝ) ^ (m + 1)) +
      (((fourthEvenHorizontalJumpWords m T).card : ℝ) / (4 : ℝ) ^ (m + 1)) +
      (((fourthEvenPerturbationWords m T).card : ℝ) / (4 : ℝ) ^ (m + 1)) +
      (((fourthOddPerturbationWords m T).card : ℝ) / (4 : ℝ) ^ (m + 1)) ≤
        fourthSignedStripProbability (2 * m) (3 * fourthLateCutoff (2 * m - 2)) +
          12 / (2 * m + 1 : ℝ) ^ 4 := by
    dsimp [T]
    calc
      _ ≤ (fourthSignedStripProbability (2 * m)
              (3 * fourthLateCutoff (2 * m - 2)) +
            2 / (2 * m + 1 : ℝ) ^ 4) +
          6 / (2 * m + 1 : ℝ) ^ 4 +
          2 / (2 * m + 1 : ℝ) ^ 4 +
          2 / (2 * m + 1 : ℝ) ^ 4 :=
        add_le_add (add_le_add (add_le_add hAid hBid) hCid) hDid
      _ = _ := by ring
  exact hcross.trans (by
    have hsqrt : 0 ≤ 128 * Real.sqrt
        (((s : ℝ) + ((m + 1 : ℕ) : ℝ) + 1) / (s + 1 : ℝ)) := by positivity
    have := mul_le_mul_of_nonneg_left hbase hsqrt
    linarith)

lemma oddFourthCrossing_axisGood_density_le (s m : ℕ) (hm : 1 ≤ m) :
    (Nat.card {p : AxisGoodPath (s + (m + 2)) //
        fourthIntegratedRademacherSum (axisWordCoefficients (axisSuffix p)) (2 * m + 1) *
          fourthIntegratedRademacherSum (axisWordCoefficients (axisSuffix p)) (2 * m + 2) ≤ 0} : ℝ) /
        Nat.card (AxisGoodPath (s + (m + 2))) ≤
      128 * Real.sqrt (((s : ℝ) + ((m + 2 : ℕ) : ℝ) + 1) / (s + 1 : ℝ)) *
        (fourthSignedStripProbability (2 * m + 1)
            (3 * fourthLateCutoff (2 * m - 1)) +
          12 / (2 * m + 2 : ℝ) ^ 4) +
      64 * ((s : ℝ) + ((m + 2 : ℕ) : ℝ) + 1) *
        Real.exp (-((s : ℝ) + ((m + 2 : ℕ) : ℝ)) / 8) := by
  let T : ℝ := fourthLateCutoff (2 * m - 1)
  let Cross : AxisGoodPath (s + (m + 2)) → Prop := fun p ↦
    fourthIntegratedRademacherSum (axisWordCoefficients (axisSuffix p)) (2 * m + 1) *
      fourthIntegratedRademacherSum (axisWordCoefficients (axisSuffix p)) (2 * m + 2) ≤ 0
  let A : AxisGoodPath (s + (m + 2)) → Prop := fun p ↦
    axisSuffix p ∈ fourthOddHorizontalSmallWords m T
  let B : AxisGoodPath (s + (m + 2)) → Prop := fun p ↦
    axisSuffix p ∈ fourthOddHorizontalJumpWords m T
  let C : AxisGoodPath (s + (m + 2)) → Prop := fun p ↦
    axisSuffix p ∈ fourthOddPerturbationExtendedWords m T
  let D : AxisGoodPath (s + (m + 2)) → Prop := fun p ↦
    axisSuffix p ∈ fourthEvenPerturbationWords (m + 1) T
  have hsplit : ∀ p, Cross p → A p ∨ B p ∨ C p ∨ D p := by
    intro p hp
    have hs := fourth_odd_crossing_threshold_split
      (axisWordCoefficients (axisSuffix p)) m (T := T) (by positivity) hp
    simpa [A, B, C, D, fourthOddHorizontalSmallWords,
      fourthOddHorizontalJumpWords, fourthOddPerturbationExtendedWords,
      fourthEvenPerturbationWords] using hs
  have hcard := natCard_subtype_le_add_four Cross A B C D hsplit
  have hA := fourthOddHorizontalSmall_axisGood_density_le s m T
  have hB := fourthOddHorizontalJump_axisGood_density_le s m T
  have hC0 := fourthVerticalOdd_axisGood_density_le s (m + 2) m (by omega) T
  have hD0 := fourthVerticalEven_axisGood_density_le s (m + 2) (m + 1) (by omega) T
  have hC : (Nat.card {p : AxisGoodPath (s + (m + 2)) // C p} : ℝ) /
      Nat.card (AxisGoodPath (s + (m + 2))) ≤
      128 * Real.sqrt (((s : ℝ) + ((m + 2 : ℕ) : ℝ) + 1) / (s + 1 : ℝ)) *
        (((fourthOddPerturbationExtendedWords m T).card : ℝ) / (4 : ℝ) ^ (m + 2)) +
      16 * ((s : ℝ) + ((m + 2 : ℕ) : ℝ) + 1) *
        Real.exp (-((s : ℝ) + ((m + 2 : ℕ) : ℝ)) / 8) := by
    simpa [C, fourthOddPerturbationExtendedWords] using hC0
  have hD : (Nat.card {p : AxisGoodPath (s + (m + 2)) // D p} : ℝ) /
      Nat.card (AxisGoodPath (s + (m + 2))) ≤
      128 * Real.sqrt (((s : ℝ) + ((m + 2 : ℕ) : ℝ) + 1) / (s + 1 : ℝ)) *
        (((fourthEvenPerturbationWords (m + 1) T).card : ℝ) / (4 : ℝ) ^ (m + 2)) +
      16 * ((s : ℝ) + ((m + 2 : ℕ) : ℝ) + 1) *
        Real.exp (-((s : ℝ) + ((m + 2 : ℕ) : ℝ)) / 8) := by
    simpa [D, fourthEvenPerturbationWords] using hD0
  have hAid := fourthOddHorizontalSmall_late_density_le m hm
  have hBid := fourthOddHorizontalJump_late_density_le m hm
  have hCid :
      ((fourthOddPerturbationExtendedWords m T).card : ℝ) / (4 : ℝ) ^ (m + 2) ≤
        2 / (2 * m + 2 : ℝ) ^ 4 := by
    rw [fourthOddPerturbationExtendedWords_density_eq]
    simpa [T] using fourthOddPerturbation_late_density_le m hm
  have hDid :
      ((fourthEvenPerturbationWords (m + 1) T).card : ℝ) / (4 : ℝ) ^ (m + 2) ≤
        2 / (2 * m + 2 : ℝ) ^ 4 := by
    have hthird := fourthEvenPerturbation_oddCutoff_third_density_le m hm
    have hsub : fourthEvenPerturbationWords (m + 1) T ⊆
        fourthEvenPerturbationWords (m + 1) (T / 3) := by
      intro w hw
      simp only [fourthEvenPerturbationWords, Finset.mem_filter,
        Finset.mem_univ, true_and] at hw ⊢
      have hT : 0 ≤ T := by positivity
      linarith
    have hc : ((fourthEvenPerturbationWords (m + 1) T).card : ℝ) ≤
        (fourthEvenPerturbationWords (m + 1) (T / 3)).card := by
      exact_mod_cast Finset.card_le_card hsub
    exact (div_le_div_of_nonneg_right hc (by positivity)).trans (by
      simpa [T] using hthird)
  have hden : (0 : ℝ) < Nat.card (AxisGoodPath (s + (m + 2))) := by
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast card_axisGoodPath_pos (s + (m + 2))
  have hcross : (Nat.card {p : AxisGoodPath (s + (m + 2)) // Cross p} : ℝ) /
      Nat.card (AxisGoodPath (s + (m + 2))) ≤
      (Nat.card {p : AxisGoodPath (s + (m + 2)) // A p} : ℝ) /
          Nat.card (AxisGoodPath (s + (m + 2))) +
      (Nat.card {p : AxisGoodPath (s + (m + 2)) // B p} : ℝ) /
          Nat.card (AxisGoodPath (s + (m + 2))) +
      (Nat.card {p : AxisGoodPath (s + (m + 2)) // C p} : ℝ) /
          Nat.card (AxisGoodPath (s + (m + 2))) +
      (Nat.card {p : AxisGoodPath (s + (m + 2)) // D p} : ℝ) /
          Nat.card (AxisGoodPath (s + (m + 2))) := by
    rw [← add_div, ← add_div, ← add_div]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) hden.le
  dsimp [T] at hCid hDid
  have hbase :
      (((fourthOddHorizontalSmallWords m T).card : ℝ) / (4 : ℝ) ^ (m + 2)) +
      (((fourthOddHorizontalJumpWords m T).card : ℝ) / (4 : ℝ) ^ (m + 2)) +
      (((fourthOddPerturbationExtendedWords m T).card : ℝ) / (4 : ℝ) ^ (m + 2)) +
      (((fourthEvenPerturbationWords (m + 1) T).card : ℝ) / (4 : ℝ) ^ (m + 2)) ≤
        fourthSignedStripProbability (2 * m + 1) (3 * fourthLateCutoff (2 * m - 1)) +
          12 / (2 * m + 2 : ℝ) ^ 4 := by
    dsimp [T]
    calc
      _ ≤ (fourthSignedStripProbability (2 * m + 1)
              (3 * fourthLateCutoff (2 * m - 1)) +
            2 / (2 * m + 2 : ℝ) ^ 4) +
          6 / (2 * m + 2 : ℝ) ^ 4 +
          2 / (2 * m + 2 : ℝ) ^ 4 +
          2 / (2 * m + 2 : ℝ) ^ 4 :=
        add_le_add (add_le_add (add_le_add hAid hBid) hCid) hDid
      _ = _ := by ring
  exact hcross.trans (by
    have hsqrt : 0 ≤ 128 * Real.sqrt
        (((s : ℝ) + ((m + 2 : ℕ) : ℝ) + 1) / (s + 1 : ℝ)) := by positivity
    have := mul_le_mul_of_nonneg_left hbase hsqrt
    linarith)

end Erdos521
