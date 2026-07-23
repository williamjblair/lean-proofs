import Mathlib.Tactic

open scoped BigOperators

namespace Erdos521

lemma sum_range_triangle_swap {M : Type*} [AddCommMonoid M]
    (j : ℕ) (f : ℕ → ℕ → M) :
    (∑ r ∈ Finset.range (j + 1), ∑ i ∈ Finset.range (r + 1), f i r) =
      ∑ i ∈ Finset.range (j + 1), ∑ r ∈ Finset.Icc i j, f i r := by
  have hrow (r : ℕ) (hr : r ∈ Finset.range (j + 1)) :
      (∑ i ∈ Finset.range (r + 1), f i r) =
        ∑ i ∈ Finset.range (j + 1), if i ≤ r then f i r else 0 := by
    have hset : Finset.range (r + 1) =
        (Finset.range (j + 1)).filter (fun i ↦ i ≤ r) := by
      ext i
      simp only [Finset.mem_range, Finset.mem_filter]
      have hrj : r ≤ j := by
        have := Finset.mem_range.mp hr
        omega
      omega
    rw [hset, Finset.sum_filter]
  have hcol (i : ℕ) (hi : i ∈ Finset.range (j + 1)) :
      (∑ r ∈ Finset.Icc i j, f i r) =
        ∑ r ∈ Finset.range (j + 1), if i ≤ r then f i r else 0 := by
    have hset : Finset.Icc i j =
        (Finset.range (j + 1)).filter (fun r ↦ i ≤ r) := by
      ext r
      simp only [Finset.mem_Icc, Finset.mem_filter, Finset.mem_range]
      omega
    rw [hset, Finset.sum_filter]
  calc
    _ = ∑ r ∈ Finset.range (j + 1),
          ∑ i ∈ Finset.range (j + 1), if i ≤ r then f i r else 0 := by
      apply Finset.sum_congr rfl
      exact hrow
    _ = ∑ i ∈ Finset.range (j + 1),
          ∑ r ∈ Finset.range (j + 1), if i ≤ r then f i r else 0 := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (hcol i hi).symm

end Erdos521
