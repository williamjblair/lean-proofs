import Mathlib
import Research.PiecewiseAssembly

namespace Erdos254.CompactCorrectionCover

open scoped BigOperators Topology
open Erdos254.PiecewiseAssembly

noncomputable section

variable {T : Type*} [TopologicalSpace T] [AddCommGroup T]
  [IsTopologicalAddGroup T] [CompactSpace T]

/-- Density of representable correction phases in a closed orbit subgroup
produces one finite correction family covering every orbit point by a fixed
open target. -/
theorem finite_correction_cover
    (C : Set ℕ) (a : T) (H : AddSubgroup T) (hHclosed : IsClosed (H : Set T))
    (haH : a ∈ H)
    (hcorr : ∀ x ∈ H, ∀ O : Set T, IsOpen O → x ∈ O →
      ∃ q : ℕ, Representable C q ∧ q • a ∈ O)
    (U : Set T) (hUopen : IsOpen U)
    (n₀ : ℕ) (hn₀U : n₀ • a ∈ U) :
    ∃ Q : Finset ℕ, ∃ N₀ : ℕ,
      (∀ q ∈ Q, Representable C q) ∧
      (∀ n : ℕ, N₀ ≤ n →
        ∃ q ∈ Q, q ≤ n ∧ (n - q) • a ∈ U) := by
  let I := {q : ℕ // Representable C q}
  let V : I → Set T := fun q => {x | x - q.1 • a ∈ U}
  have hVopen : ∀ q, IsOpen (V q) := by
    intro q
    exact hUopen.preimage (continuous_id.sub continuous_const)
  have hcover : (H : Set T) ⊆ ⋃ q : I, V q := by
    intro x hxH
    have hyH : x - n₀ • a ∈ H := H.sub_mem hxH (H.nsmul_mem haH n₀)
    let O : Set T := {y | x - y ∈ U}
    have hOopen : IsOpen O := hUopen.preimage (continuous_const.sub continuous_id)
    have hyO : x - n₀ • a ∈ O := by
      change x - (x - n₀ • a) ∈ U
      simpa only [sub_sub_cancel] using hn₀U
    obtain ⟨q, hqC, hqO⟩ := hcorr (x - n₀ • a) hyH O hOopen hyO
    exact Set.mem_iUnion.mpr ⟨⟨q, hqC⟩, hqO⟩
  obtain ⟨F, hFcover⟩ := hHclosed.isCompact.elim_finite_subcover
    V hVopen hcover
  let Q : Finset ℕ := F.map ⟨Subtype.val, Subtype.val_injective⟩
  let N₀ : ℕ := ∑ q ∈ Q, q
  refine ⟨Q, N₀, ?_, ?_⟩
  · intro q hqQ
    change q ∈ F.map ⟨Subtype.val, Subtype.val_injective⟩ at hqQ
    rw [Finset.mem_map] at hqQ
    obtain ⟨r, hrF, rfl⟩ := hqQ
    exact r.2
  · intro n hn
    have hnH : n • a ∈ H := H.nsmul_mem haH n
    obtain ⟨r, hrF, hnr⟩ := Set.mem_iUnion₂.mp (hFcover hnH)
    have hrQ : r.1 ∈ Q := by
      change r.1 ∈ F.map ⟨Subtype.val, Subtype.val_injective⟩
      exact Finset.mem_map.mpr ⟨r, hrF, rfl⟩
    have hrN : r.1 ≤ N₀ := by
      calc
        r.1 = ∑ q ∈ ({r.1} : Finset ℕ), q := by simp
        _ ≤ ∑ q ∈ Q, q := Finset.sum_le_sum_of_subset (by simpa using hrQ)
    have hrn : r.1 ≤ n := hrN.trans hn
    refine ⟨r.1, hrQ, hrn, ?_⟩
    have hphase : (n - r.1) • a = n • a - r.1 • a := by
      apply eq_sub_iff_add_eq.mpr
      rw [← add_nsmul]
      congr 1
      exact Nat.sub_add_cancel hrn
    rw [hphase]
    exact hnr

end

end Erdos254.CompactCorrectionCover
