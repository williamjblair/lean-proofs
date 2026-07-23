import Mathlib
import Research.PiecewiseAssembly
import Research.BohrReturnSyndetic

namespace Erdos254.PiecewiseFiniteEmbedding

open Filter Topology
open scoped BigOperators
open Erdos254.PiecewiseAssembly Erdos254.BohrReturnSyndetic

noncomputable section

/-- A piecewise-Bohr return set finitely contains a smaller pure Bohr return
set. Thickness supplies a long interval, while syndeticity of the smaller
return set lets the common translating shift be chosen inside that interval. -/
theorem pure_bohr_finitely_embeds_piecewise
    {T : Type*} [TopologicalSpace T] [T2Space T] [AddCommGroup T]
    [IsTopologicalAddGroup T] [CompactSpace T]
    (a : T) (U : Set T) (hUopen : IsOpen U) (hzero : (0 : T) ∈ U)
    (J Q : Set ℕ) (hJ : IsThick J)
    (hQ : ∀ n : ℕ, n • a ∈ U → n ∈ J → n ∈ Q) :
    ∃ V : Set T, IsOpen V ∧ (0 : T) ∈ V ∧
      ∀ F : Finset ℕ, (∀ n ∈ F, n • a ∈ V) →
        ∃ r : ℕ, ∀ n ∈ F, n + r ∈ Q := by
  obtain ⟨V, hVopen, hVzero, hVV⟩ :=
    exists_open_nhds_zero_half (hUopen.mem_nhds hzero)
  obtain ⟨K, hK⟩ := compact_rotation_return_syndetic a V hVopen hVzero
  refine ⟨V, hVopen, hVzero, ?_⟩
  intro F hF
  let R : ℕ := ∑ n ∈ F, n
  obtain ⟨t, ht⟩ := hJ (K + R)
  obtain ⟨q, hqK, hqphase⟩ := hK t
  refine ⟨t + q, ?_⟩
  intro n hnF
  apply hQ (n + (t + q))
  · have hnphase := hF n hnF
    have hadd := hVV _ hnphase _ hqphase
    simpa [add_nsmul, add_assoc, add_comm, add_left_comm] using hadd
  · have hnR : n ≤ R := by
      dsimp [R]
      exact Finset.single_le_sum (s := F) (f := fun m : ℕ => m)
        (fun _ _ => Nat.zero_le _) hnF
    have hqn : q + n ≤ K + R := Nat.add_le_add hqK hnR
    have := ht (q + n) hqn
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this

end

end Erdos254.PiecewiseFiniteEmbedding
