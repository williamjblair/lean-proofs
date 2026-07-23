import Research.UpperSmooth

namespace Erdos796

section TruncatedTypes

variable {ι : Type*} [DecidableEq ι]

/-- Indices carrying a specified finite fiber type. -/
def typeFiber (I : Finset ι) (D : ι → Finset ℕ) (T : Finset ℕ) : Finset ι :=
  I.filter fun i => D i = T

/-- Types occurring at least twice among the given indices. -/
def repeatedTypes (I : Finset ι) (D : ι → Finset ℕ) : Finset (Finset ℕ) :=
  (I.image D).filter fun T => 2 ≤ (typeFiber I D T).card

/-- Every two repeated truncated types, including a type paired with itself,
are compatible when fibers at distinct indices are pairwise compatible. -/
theorem repeatedTypes_pairwise_compatible
    (I : Finset ι) (D : ι → Finset ℕ)
    (hcompat : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → CrossCompatible (D i) (D j)) :
    ∀ S ∈ repeatedTypes I D, ∀ T ∈ repeatedTypes I D,
      CrossCompatible S T := by
  intro S hS T hT
  have hS' := Finset.mem_filter.mp hS
  have hT' := Finset.mem_filter.mp hT
  by_cases hST : S = T
  · subst T
    have hone : 1 < (typeFiber I D S).card := by omega
    rcases Finset.one_lt_card.mp hone with ⟨i, hi, j, hj, hij⟩
    have hi' := Finset.mem_filter.mp hi
    have hj' := Finset.mem_filter.mp hj
    have hc := hcompat i hi'.1 j hj'.1 hij
    simpa only [hi'.2, hj'.2] using hc
  · rcases Finset.mem_image.mp hS'.1 with ⟨i, hi, hiS⟩
    rcases Finset.mem_image.mp hT'.1 with ⟨j, hj, hjT⟩
    have hij : i ≠ j := by
      intro h
      subst j
      exact hST (hiS.symm.trans hjT)
    rw [← hiS, ← hjT]
    exact hcompat i hi j hj hij

/-- Indices whose exact type occurs only once. -/
def exceptionalTypeIndices (I : Finset ι) (D : ι → Finset ℕ) : Finset ι :=
  I.filter fun i => (typeFiber I D (D i)).card ≤ 1

/-- The number of singleton-occurrence types is bounded by the number of
subsets of the ambient finite core universe. -/
theorem exceptionalTypeIndices_card_le_powerset
    (I : Finset ι) (D : ι → Finset ℕ) (U : Finset ℕ)
    (hD : ∀ i ∈ I, D i ⊆ U) :
    (exceptionalTypeIndices I D).card ≤ 2 ^ U.card := by
  have hinj : Set.InjOn D (exceptionalTypeIndices I D) := by
    intro i hi j hj hij
    have hi' := Finset.mem_filter.mp hi
    have hj' := Finset.mem_filter.mp hj
    apply (Finset.card_le_one.mp hi'.2) i
    · exact Finset.mem_filter.mpr ⟨hi'.1, rfl⟩
    · exact Finset.mem_filter.mpr ⟨hj'.1, hij.symm⟩
  have himage : (exceptionalTypeIndices I D).card =
      ((exceptionalTypeIndices I D).image D).card :=
    (Finset.card_image_iff.mpr hinj).symm
  have hsub : (exceptionalTypeIndices I D).image D ⊆ U.powerset := by
    intro T hT
    rcases Finset.mem_image.mp hT with ⟨i, hi, rfl⟩
    exact Finset.mem_powerset.mpr (hD i (Finset.mem_filter.mp hi).1)
  rw [himage]
  calc
    _ ≤ U.powerset.card := Finset.card_le_card hsub
    _ = 2 ^ U.card := Finset.card_powerset U

end TruncatedTypes

end Erdos796
