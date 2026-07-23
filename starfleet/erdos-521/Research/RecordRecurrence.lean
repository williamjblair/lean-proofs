import Research.KochenStone
import Mathlib.Tactic

open MeasureTheory Set
open scoped BigOperators

namespace Erdos521

section RecordRecurrence

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]

/-- A specialization of Kochen--Stone tailored to record events.  The assumed correlation bound
is the one produced by the exact fresh-block record decomposition. -/
lemma positive_limsup_of_record_correlation {A : ℕ → Set Ω} (hA : ∀ n, MeasurableSet (A n))
    (q : ℕ → ℝ) (hq : ∀ n, 0 ≤ q n)
    (hmarginal : ∀ n, μ.real (A n) = q n)
    (htailLarge : ∀ K : ℕ, ∃ N ≥ K,
      let s := Finset.Icc K N
      let S := ∑ i ∈ s, q i
      let T := ∑ i ∈ Finset.range (N + 1), q i
      1 ≤ S ∧ T ≤ 2 * S)
    (hcorrelation : ∀ K N : ℕ, K ≤ N →
      let s := Finset.Icc K N
      let S := ∑ i ∈ s, q i
      let T := ∑ i ∈ Finset.range (N + 1), q i
      (∑ i ∈ s, ∑ j ∈ s, μ.real (A i ∩ A j)) ≤ S + 2 * S * T) :
    0 < μ (eventLimsup A) := by
  apply kochenStone_of_finite_blocks μ hA (C := 5) (by norm_num)
  intro K
  obtain ⟨N, hKN, hS, hT⟩ := htailLarge K
  refine ⟨N, hKN, ?_⟩
  let s := Finset.Icc K N
  let S := ∑ i ∈ s, μ.real (A i)
  let D := ∑ i ∈ s, ∑ j ∈ s, μ.real (A i ∩ A j)
  let Sq := ∑ i ∈ s, q i
  let T := ∑ i ∈ Finset.range (N + 1), q i
  have hSeq : S = Sq := by
    dsimp [S, Sq]
    apply Finset.sum_congr rfl
    intro i hi
    exact hmarginal i
  change 1 ≤ Sq at hS
  change T ≤ 2 * Sq at hT
  have hcorr : D ≤ Sq + 2 * Sq * T := by
    exact hcorrelation K N hKN
  have hSq0 : 0 ≤ Sq := le_trans zero_le_one hS
  have hT0 : 0 ≤ T := by
    dsimp [T]
    exact Finset.sum_nonneg fun i hi ↦ hq i
  change 0 < S ∧ D ≤ 5 * S ^ 2
  constructor
  · rw [hSeq]
    linarith
  · rw [hSeq]
    nlinarith

end RecordRecurrence

end Erdos521
