import Mathlib

namespace Erdos254.CompactSemigroup

/-- A nonempty closed subset of a compact topological additive group which is
closed under addition is the carrier of an additive subgroup. -/
theorem compact_add_subsemigroup_is_addSubgroup
    {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    [CompactSpace G] [T2Space G] [IsTopologicalAddGroup G]
    (S : Set G) (hne : S.Nonempty) (hclosed : IsClosed S)
    (hadd : ∀ x ∈ S, ∀ y ∈ S, x + y ∈ S) :
    ∃ H : AddSubgroup G, (H : Set G) = S := by
  obtain ⟨e, heS, he⟩ := exists_idempotent_in_compact_add_subsemigroup
    (fun r => continuous_id.add continuous_const) S hne hclosed.isCompact hadd
  have he0 : e = 0 := by
    apply add_left_cancel (a := e)
    simpa using he
  have hzero : (0 : G) ∈ S := he0 ▸ heS
  let M : AddSubmonoid G :=
    { carrier := S
      zero_mem' := hzero
      add_mem' := fun hx hy => hadd _ hx _ hy }
  have hneg : ∀ x ∈ S, -x ∈ S := by
    intro x hx
    have hxgen : x ∈ AddSubgroup.closure ({x} : Set G) :=
      AddSubgroup.subset_closure (Set.mem_singleton x)
    have hnxgen : -x ∈ AddSubgroup.closure ({x} : Set G) :=
      (AddSubgroup.closure ({x} : Set G)).neg_mem hxgen
    have hnxclGroup : -x ∈ closure (AddSubgroup.closure ({x} : Set G) : Set G) :=
      subset_closure hnxgen
    have hnxclMonoid : -x ∈ closure (AddSubmonoid.closure ({x} : Set G) : Set G) := by
      rw [closure_addSubmonoidClosure_eq_closure_addSubgroupClosure]
      exact hnxclGroup
    have hmono : (AddSubmonoid.closure ({x} : Set G) : Set G) ⊆ S := by
      intro y hy
      exact (AddSubmonoid.closure_le.mpr (by simpa [M] using hx) :
        AddSubmonoid.closure ({x} : Set G) ≤ M) hy
    exact (closure_minimal hmono hclosed) hnxclMonoid
  let H : AddSubgroup G :=
    { carrier := S
      zero_mem' := hzero
      add_mem' := fun hx hy => hadd _ hx _ hy
      neg_mem' := fun hx => hneg _ hx }
  exact ⟨H, rfl⟩

end Erdos254.CompactSemigroup
