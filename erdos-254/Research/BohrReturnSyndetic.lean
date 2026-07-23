import Mathlib.Topology.Algebra.Group.SubmonoidClosure

namespace Erdos254.BohrReturnSyndetic

open Set Filter Topology
open scoped BigOperators

noncomputable section

/-- Return times of a rotation to an open identity neighborhood in a compact
additive group have uniformly bounded forward gaps. -/
theorem compact_rotation_return_syndetic
    {T : Type*} [TopologicalSpace T] [T2Space T] [AddCommGroup T]
    [IsTopologicalAddGroup T] [CompactSpace T]
    (a : T) (V : Set T) (hVopen : IsOpen V) (hzero : (0 : T) ∈ V) :
    ∃ K : ℕ, ∀ t : ℕ, ∃ q : ℕ, q ≤ K ∧ (t + q) • a ∈ V := by
  let H : Set T := closure (Set.range fun n : ℕ => n • a)
  let O : ℕ → Set T := fun n => {x | x + n • a ∈ V}
  have hOopen : ∀ n : ℕ, IsOpen (O n) := by
    intro n
    exact hVopen.preimage (continuous_id.add continuous_const)
  have hneg {x : T} (hx : x ∈ H) : -x ∈ H := by
    have hxz : x ∈ closure (Set.range fun z : ℤ => z • a) := by
      rw [closure_range_zsmul_eq_nsmul]
      exact hx
    have hxsub : x ∈ (AddSubgroup.zmultiples a).topologicalClosure := by
      change x ∈ ((AddSubgroup.zmultiples a).topologicalClosure : Set T)
      rw [AddSubgroup.topologicalClosure_coe, AddSubgroup.coe_zmultiples]
      exact hxz
    have hnegsub := (AddSubgroup.zmultiples a).topologicalClosure.neg_mem hxsub
    have hnegz : -x ∈ closure (Set.range fun z : ℤ => z • a) := by
      change -x ∈ ((AddSubgroup.zmultiples a).topologicalClosure : Set T) at hnegsub
      rw [AddSubgroup.topologicalClosure_coe, AddSubgroup.coe_zmultiples] at hnegsub
      exact hnegsub
    rw [closure_range_zsmul_eq_nsmul] at hnegz
    exact hnegz
  have hcover : H ⊆ ⋃ n : ℕ, O n := by
    intro x hx
    let W : Set T := {y | x + y ∈ V}
    have hWopen : IsOpen W := hVopen.preimage (continuous_const.add continuous_id)
    have hnegW : -x ∈ W := by
      dsimp [W]
      simpa using hzero
    have hmeet := (mem_closure_iff.mp (hneg hx)) W hWopen hnegW
    obtain ⟨y, hyW, n, rfl⟩ := hmeet
    apply mem_iUnion.mpr
    exact ⟨n, hyW⟩
  have hHcompact : IsCompact H := isClosed_closure.isCompact
  obtain ⟨s, hscover⟩ := hHcompact.elim_finite_subcover O hOopen hcover
  let K : ℕ := ∑ n ∈ s, n
  refine ⟨K, ?_⟩
  intro t
  have htH : t • a ∈ H := subset_closure ⟨t, rfl⟩
  have htcover := hscover htH
  simp only [mem_iUnion] at htcover
  obtain ⟨q, hq⟩ := htcover
  obtain ⟨hqS, hqO⟩ := hq
  refine ⟨q, ?_, ?_⟩
  · dsimp [K]
    exact Finset.single_le_sum (s := s) (f := fun n : ℕ => n)
      (fun _ _ => Nat.zero_le _) hqS
  · change t • a + q • a ∈ V at hqO
    simpa [add_nsmul] using hqO

end

end Erdos254.BohrReturnSyndetic
