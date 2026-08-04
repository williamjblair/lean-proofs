import Research.Definitions

namespace Erdos123

/-- The webpage's literal `a,b,c ≥ 1` wording is false: for `(1,1,1)` the
only available integer is `1`, so no integer at least `2` is representable. -/
theorem not_literalStatement : ¬LiteralStatement := by
  intro h
  have hd := h 1 1 1 (by omega) (by omega) (by omega) (by simp [PairwiseCoprime3])
  rcases hd with ⟨N, hN⟩
  obtain ⟨s, hsA, _hsPrimitive, hsum⟩ := hN (N + 2) (by omega)
  have hs_sub : s ⊆ {1} := by
    intro x hx
    have hxA := hsA x hx
    rcases hxA with ⟨k, l, m, rfl⟩
    simp
  rcases Finset.subset_singleton_iff.mp hs_sub with rfl | rfl <;> simp at hsum <;> omega

end Erdos123
