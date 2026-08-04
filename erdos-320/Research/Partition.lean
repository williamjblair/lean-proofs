import Mathlib

/-!
# Partitioning finite subset-sum supports

The large-prime recurrence uses only the following finite algebra: subset sums
on a disjoint union are the Minkowski sum of the supports on its two blocks.
This file proves that statement for arbitrary commutative additive weights.
-/

namespace Research

open scoped Pointwise

section Partition

variable {α M : Type*} [DecidableEq α] [AddCommMonoid M] [DecidableEq M]

/-- The set of values of all subset sums of weights indexed by `D`. -/
def subsetSumValues (w : α → M) (D : Finset α) : Finset M :=
  D.powerset.image (fun A => ∑ a ∈ A, w a)

/-- Subset-sum supports turn a disjoint union of index sets into a Minkowski
sum of value sets. -/
theorem subsetSumValues_union (w : α → M) {D E : Finset α}
    (hDE : Disjoint D E) :
    subsetSumValues w (D ∪ E) = subsetSumValues w D + subsetSumValues w E := by
  ext x
  constructor
  · intro hx
    rw [subsetSumValues, Finset.mem_image] at hx
    obtain ⟨U, hU, rfl⟩ := hx
    rw [Finset.mem_powerset] at hU
    let A := U ∩ D
    let B := U ∩ E
    have hA : A ⊆ D := Finset.inter_subset_right
    have hB : B ⊆ E := Finset.inter_subset_right
    have hAB : Disjoint A B := hDE.mono hA hB
    have hUeq : A ∪ B = U := by
      ext u
      constructor
      · intro hu
        rcases Finset.mem_union.mp hu with huA | huB
        · exact (Finset.mem_inter.mp huA).1
        · exact (Finset.mem_inter.mp huB).1
      · intro hu
        have huDE := hU hu
        rcases Finset.mem_union.mp huDE with huD | huE
        · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hu, huD⟩)
        · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hu, huE⟩)
    rw [Finset.mem_add]
    refine ⟨∑ a ∈ A, w a, ?_, ∑ a ∈ B, w a, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨A, Finset.mem_powerset.mpr hA, rfl⟩
    · exact Finset.mem_image.mpr ⟨B, Finset.mem_powerset.mpr hB, rfl⟩
    · rw [← Finset.sum_union hAB, hUeq]
  · intro hx
    rw [Finset.mem_add] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    rw [subsetSumValues, Finset.mem_image] at ha hb
    obtain ⟨A, hA, rfl⟩ := ha
    obtain ⟨B, hB, rfl⟩ := hb
    rw [Finset.mem_powerset] at hA hB
    have hAB : Disjoint A B := hDE.mono hA hB
    rw [subsetSumValues, Finset.mem_image]
    refine ⟨A ∪ B, ?_, ?_⟩
    · rw [Finset.mem_powerset]
      exact Finset.union_subset_union hA hB
    · rw [Finset.sum_union hAB]

/-- Consequently, the number of subset sums on a disjoint union is at most the
product of the numbers on the two blocks. -/
theorem card_subsetSumValues_union_le (w : α → M) {D E : Finset α}
    (hDE : Disjoint D E) :
    (subsetSumValues w (D ∪ E)).card ≤
      (subsetSumValues w D).card * (subsetSumValues w E).card := by
  rw [subsetSumValues_union w hDE]
  exact Finset.card_add_le

variable {ι : Type*} [DecidableEq ι]

/-- Iterating the two-block inequality: the support over a finite family of
pairwise disjoint blocks has cardinality at most the product of the block
support cardinalities. -/
theorem card_subsetSumValues_biUnion_le (w : α → M)
    (I : Finset ι) (block : ι → Finset α)
    (hpair : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (block i) (block j)) :
    (subsetSumValues w (I.biUnion block)).card ≤
      ∏ i ∈ I, (subsetSumValues w (block i)).card := by
  induction I using Finset.induction_on with
  | empty => simp [subsetSumValues]
  | @insert i I hi ih =>
      have hpairI :
          ∀ j ∈ I, ∀ k ∈ I, j ≠ k → Disjoint (block j) (block k) := by
        intro j hj k hk hjk
        exact hpair j (Finset.mem_insert_of_mem hj) k
          (Finset.mem_insert_of_mem hk) hjk
      have hiDisj : Disjoint (block i) (I.biUnion block) := by
        rw [Finset.disjoint_biUnion_right]
        intro j hj
        exact hpair i (Finset.mem_insert_self i I) j
          (Finset.mem_insert_of_mem hj) (by
            intro hij
            apply hi
            rw [hij]
            exact hj)
      rw [Finset.biUnion_insert, Finset.prod_insert hi]
      calc
        (subsetSumValues w (block i ∪ I.biUnion block)).card ≤
            (subsetSumValues w (block i)).card *
              (subsetSumValues w (I.biUnion block)).card :=
          card_subsetSumValues_union_le w hiDisj
        _ ≤ (subsetSumValues w (block i)).card *
              ∏ j ∈ I, (subsetSumValues w (block j)).card :=
          Nat.mul_le_mul_left _ (ih hpairI)

end Partition

end Research
