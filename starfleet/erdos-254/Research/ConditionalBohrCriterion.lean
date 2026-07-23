import Mathlib
import Research.PiecewiseAssembly
import Research.CompactCorrectionCover

namespace Erdos254.ConditionalBohrCriterion

open scoped Topology
open Erdos254.PiecewiseAssembly Erdos254.CompactCorrectionCover

noncomputable section

variable {T : Type*} [TopologicalSpace T] [AddCommGroup T]
  [IsTopologicalAddGroup T] [CompactSpace T]

/-- Formal compact-group core of the Bergelson--Simmons completeness
criterion. All use of summands is explicitly disjoint. -/
theorem conditional_piecewise_bohr_completeness
    (B C D : Set ℕ)
    (hBC : Disjoint B C) (hBD : Disjoint B D) (hCD : Disjoint C D)
    (a : T) (H : AddSubgroup T) (hHclosed : IsClosed (H : Set T))
    (haH : a ∈ H)
    (hcorr : ∀ x ∈ H, ∀ O : Set T, IsOpen O → x ∈ O →
      ∃ q : ℕ, Representable C q ∧ q • a ∈ O)
    (U : Set T) (hUopen : IsOpen U)
    (n₀ : ℕ) (hn₀U : n₀ • a ∈ U)
    (J : Set ℕ) (hJ : IsThick J)
    (hpiece : ∀ n : ℕ, n ∈ J → n • a ∈ U → Representable B n)
    (K : ℕ) (hsyndetic : ∀ n : ℕ, ∃ s : ℕ,
      Representable D s ∧ s ≤ n ∧ n ≤ s + K) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Representable (B ∪ C ∪ D) n := by
  obtain ⟨Q, N₁, hQ, hcover⟩ := finite_correction_cover C a H hHclosed haH
    hcorr U hUopen n₀ hn₀U
  exact piecewise_correction_syndetic_assembly B C D hBC hBD hCD J
    (fun n => n • a ∈ U) hJ hpiece Q hQ N₁ hcover K hsyndetic

end

end Erdos254.ConditionalBohrCriterion
