import Research.HorizontalCoreForms
import Mathlib.Tactic

set_option maxHeartbeats 1000000

namespace Erdos521

noncomputable local instance axisHorizontalEventDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

lemma fourthEvenHorizontalSmall_axisGood_density_le (s m : ℕ) (T : ℝ) :
    (Nat.card {p : AxisGoodPath (s + (m + 1)) //
        axisSuffix p ∈ fourthEvenHorizontalSmallWords m T} : ℝ) /
        Nat.card (AxisGoodPath (s + (m + 1))) ≤
      128 * Real.sqrt (((s : ℝ) + ((m + 1 : ℕ) : ℝ) + 1) / (s + 1 : ℝ)) *
          (((fourthEvenHorizontalSmallWords m T).card : ℝ) / (4 : ℝ) ^ (m + 1)) +
        16 * ((s : ℝ) + ((m + 1 : ℕ) : ℝ) + 1) *
          Real.exp (-((s : ℝ) + ((m + 1 : ℕ) : ℝ)) / 8) := by
  have haxis : ∀ p : AxisGoodPath (s + (m + 1)),
      axisSuffix p ∈ fourthEvenHorizontalSmallWords m T ↔
        horizontalCoreCanonicalSuffix (axisHorizontalCore p) ∈
          fourthEvenHorizontalSmallWords m T := by
    intro p
    simp only [fourthEvenHorizontalSmallWords, Finset.mem_filter, Finset.mem_univ,
      true_and]
    rw [fourthHorizontalEven_axisSuffix_eq_core (by omega) p]
  have hhoriz : ∀ p : HorizontalGoodPath (s + (m + 1)),
      horizontalAxisSuffix p ∈ fourthEvenHorizontalSmallWords m T ↔
        horizontalCoreCanonicalSuffix (oneCoordinateHorizontalCore p) ∈
          fourthEvenHorizontalSmallWords m T := by
    intro p
    simp only [fourthEvenHorizontalSmallWords, Finset.mem_filter, Finset.mem_univ,
      true_and]
    rw [fourthHorizontalEven_horizontalSuffix_eq_core (by omega) p]
  exact axisGood_horizontal_terminal_event_natCard_density_le s (m + 1) (by omega)
    (fourthEvenHorizontalSmallWords m T)
    (fun c ↦ horizontalCoreCanonicalSuffix c ∈ fourthEvenHorizontalSmallWords m T)
    (fun p ↦ axisSuffix p ∈ fourthEvenHorizontalSmallWords m T) haxis hhoriz

lemma fourthEvenHorizontalJump_axisGood_density_le (s m : ℕ) (T : ℝ) :
    (Nat.card {p : AxisGoodPath (s + (m + 1)) //
        axisSuffix p ∈ fourthEvenHorizontalJumpWords m T} : ℝ) /
        Nat.card (AxisGoodPath (s + (m + 1))) ≤
      128 * Real.sqrt (((s : ℝ) + ((m + 1 : ℕ) : ℝ) + 1) / (s + 1 : ℝ)) *
          (((fourthEvenHorizontalJumpWords m T).card : ℝ) / (4 : ℝ) ^ (m + 1)) +
        16 * ((s : ℝ) + ((m + 1 : ℕ) : ℝ) + 1) *
          Real.exp (-((s : ℝ) + ((m + 1 : ℕ) : ℝ)) / 8) := by
  have haxis : ∀ p : AxisGoodPath (s + (m + 1)),
      axisSuffix p ∈ fourthEvenHorizontalJumpWords m T ↔
        horizontalCoreCanonicalSuffix (axisHorizontalCore p) ∈
          fourthEvenHorizontalJumpWords m T := by
    intro p
    simp only [fourthEvenHorizontalJumpWords, Finset.mem_filter, Finset.mem_univ,
      true_and]
    rw [fourthHorizontalOdd_axisSuffix_eq_core (by omega) p,
      fourthHorizontalEven_axisSuffix_eq_core (by omega) p]
  have hhoriz : ∀ p : HorizontalGoodPath (s + (m + 1)),
      horizontalAxisSuffix p ∈ fourthEvenHorizontalJumpWords m T ↔
        horizontalCoreCanonicalSuffix (oneCoordinateHorizontalCore p) ∈
          fourthEvenHorizontalJumpWords m T := by
    intro p
    simp only [fourthEvenHorizontalJumpWords, Finset.mem_filter, Finset.mem_univ,
      true_and]
    rw [fourthHorizontalOdd_horizontalSuffix_eq_core (by omega) p,
      fourthHorizontalEven_horizontalSuffix_eq_core (by omega) p]
  exact axisGood_horizontal_terminal_event_natCard_density_le s (m + 1) (by omega)
    (fourthEvenHorizontalJumpWords m T)
    (fun c ↦ horizontalCoreCanonicalSuffix c ∈ fourthEvenHorizontalJumpWords m T)
    (fun p ↦ axisSuffix p ∈ fourthEvenHorizontalJumpWords m T) haxis hhoriz

lemma fourthOddHorizontalSmall_axisGood_density_le (s m : ℕ) (T : ℝ) :
    (Nat.card {p : AxisGoodPath (s + (m + 2)) //
        axisSuffix p ∈ fourthOddHorizontalSmallWords m T} : ℝ) /
        Nat.card (AxisGoodPath (s + (m + 2))) ≤
      128 * Real.sqrt (((s : ℝ) + ((m + 2 : ℕ) : ℝ) + 1) / (s + 1 : ℝ)) *
          (((fourthOddHorizontalSmallWords m T).card : ℝ) / (4 : ℝ) ^ (m + 2)) +
        16 * ((s : ℝ) + ((m + 2 : ℕ) : ℝ) + 1) *
          Real.exp (-((s : ℝ) + ((m + 2 : ℕ) : ℝ)) / 8) := by
  have haxis : ∀ p : AxisGoodPath (s + (m + 2)),
      axisSuffix p ∈ fourthOddHorizontalSmallWords m T ↔
        horizontalCoreCanonicalSuffix (axisHorizontalCore p) ∈
          fourthOddHorizontalSmallWords m T := by
    intro p
    simp only [fourthOddHorizontalSmallWords, Finset.mem_filter, Finset.mem_univ,
      true_and]
    rw [fourthHorizontalOdd_axisSuffix_eq_core (by omega) p]
  have hhoriz : ∀ p : HorizontalGoodPath (s + (m + 2)),
      horizontalAxisSuffix p ∈ fourthOddHorizontalSmallWords m T ↔
        horizontalCoreCanonicalSuffix (oneCoordinateHorizontalCore p) ∈
          fourthOddHorizontalSmallWords m T := by
    intro p
    simp only [fourthOddHorizontalSmallWords, Finset.mem_filter, Finset.mem_univ,
      true_and]
    rw [fourthHorizontalOdd_horizontalSuffix_eq_core (by omega) p]
  exact axisGood_horizontal_terminal_event_natCard_density_le s (m + 2) (by omega)
    (fourthOddHorizontalSmallWords m T)
    (fun c ↦ horizontalCoreCanonicalSuffix c ∈ fourthOddHorizontalSmallWords m T)
    (fun p ↦ axisSuffix p ∈ fourthOddHorizontalSmallWords m T) haxis hhoriz

lemma fourthOddHorizontalJump_axisGood_density_le (s m : ℕ) (T : ℝ) :
    (Nat.card {p : AxisGoodPath (s + (m + 2)) //
        axisSuffix p ∈ fourthOddHorizontalJumpWords m T} : ℝ) /
        Nat.card (AxisGoodPath (s + (m + 2))) ≤
      128 * Real.sqrt (((s : ℝ) + ((m + 2 : ℕ) : ℝ) + 1) / (s + 1 : ℝ)) *
          (((fourthOddHorizontalJumpWords m T).card : ℝ) / (4 : ℝ) ^ (m + 2)) +
        16 * ((s : ℝ) + ((m + 2 : ℕ) : ℝ) + 1) *
          Real.exp (-((s : ℝ) + ((m + 2 : ℕ) : ℝ)) / 8) := by
  have haxis : ∀ p : AxisGoodPath (s + (m + 2)),
      axisSuffix p ∈ fourthOddHorizontalJumpWords m T ↔
        horizontalCoreCanonicalSuffix (axisHorizontalCore p) ∈
          fourthOddHorizontalJumpWords m T := by
    intro p
    simp only [fourthOddHorizontalJumpWords, Finset.mem_filter, Finset.mem_univ,
      true_and]
    rw [fourthHorizontalEven_axisSuffix_eq_core (by omega) p,
      fourthHorizontalOdd_axisSuffix_eq_core (by omega) p]
  have hhoriz : ∀ p : HorizontalGoodPath (s + (m + 2)),
      horizontalAxisSuffix p ∈ fourthOddHorizontalJumpWords m T ↔
        horizontalCoreCanonicalSuffix (oneCoordinateHorizontalCore p) ∈
          fourthOddHorizontalJumpWords m T := by
    intro p
    simp only [fourthOddHorizontalJumpWords, Finset.mem_filter, Finset.mem_univ,
      true_and]
    rw [fourthHorizontalEven_horizontalSuffix_eq_core (by omega) p,
      fourthHorizontalOdd_horizontalSuffix_eq_core (by omega) p]
  exact axisGood_horizontal_terminal_event_natCard_density_le s (m + 2) (by omega)
    (fourthOddHorizontalJumpWords m T)
    (fun c ↦ horizontalCoreCanonicalSuffix c ∈ fourthOddHorizontalJumpWords m T)
    (fun p ↦ axisSuffix p ∈ fourthOddHorizontalJumpWords m T) haxis hhoriz

end Erdos521
