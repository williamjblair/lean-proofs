import Research.RecordRecurrence
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

open Filter
open scoped BigOperators

namespace Erdos521

/-- Divergence of nonnegative partial sums supplies the large-tail blocks required in F-008. -/
lemma tailLarge_of_partialSums_tendsto_atTop (q : ℕ → ℝ) (hq : ∀ n, 0 ≤ q n)
    (hdiv : Tendsto (fun N ↦ ∑ i ∈ Finset.range (N + 1), q i) atTop atTop) :
    ∀ K : ℕ, ∃ N ≥ K,
      let s := Finset.Icc K N
      let S := ∑ i ∈ s, q i
      let T := ∑ i ∈ Finset.range (N + 1), q i
      1 ≤ S ∧ T ≤ 2 * S := by
  intro K
  let E := ∑ i ∈ Finset.range K, q i
  obtain ⟨i, hi⟩ := (Filter.tendsto_atTop_atTop.mp hdiv) (2 * (E + 1))
  let N := max K i
  have hKN : K ≤ N := le_max_left _ _
  have hiN : i ≤ N := le_max_right _ _
  have hlarge : 2 * (E + 1) ≤ ∑ j ∈ Finset.range (N + 1), q j := hi N hiN
  refine ⟨N, hKN, ?_⟩
  let S := ∑ j ∈ Finset.Icc K N, q j
  let T := ∑ j ∈ Finset.range (N + 1), q j
  have hid : E + S = T := by
    dsimp [E, S, T]
    rw [← Finset.Ico_add_one_right_eq_Icc]
    exact Finset.sum_range_add_sum_Ico q (by omega)
  have hE0 : 0 ≤ E := by
    dsimp [E]
    exact Finset.sum_nonneg fun j hj ↦ hq j
  have hS0 : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg fun j hj ↦ hq j
  change 1 ≤ S ∧ T ≤ 2 * S
  constructor <;> nlinarith

end Erdos521
