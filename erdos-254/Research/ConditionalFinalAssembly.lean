import Mathlib
import Research.Statement
import Research.PiecewiseAssembly
import Research.ConditionalBohrCriterion
import Research.DisjointCriterionDecomposition
import Research.TorusCorrectionGroup

namespace Erdos254.ConditionalFinalAssembly

open Filter
open scoped Topology BigOperators
open Erdos254
open Erdos254.PiecewiseAssembly Erdos254.ConditionalBohrCriterion
open Erdos254.DisjointCriterionDecomposition Erdos254.TorusCorrectionGroup

noncomputable section

/-- The exact Bergelson--Furstenberg--Weiss interface still needed: sums of two
sets with syndetic distinct-subset sums contain a finite-dimensional
piecewise-Bohr return set. -/
def BFWFiniteSumProperty : Prop :=
  ∀ B₀ B₁ : Set ℕ, Disjoint B₀ B₁ →
    (∀ i : Fin 2, ∃ K : ℕ, ∀ n : ℕ, ∃ t : Finset ℕ,
      (∀ b ∈ t, b ∈ (if i = 0 then B₀ else B₁)) ∧
      (∑ b ∈ t, b) ≤ n ∧ n ≤ (∑ b ∈ t, b) + K) →
    ∃ d : ℕ, ∃ α : Fin d → ℝ,
      ∃ U : Set (UnitAddTorus (Fin d)), IsOpen U ∧
      ∃ n₀ : ℕ, n₀ • (fun i => (α i : UnitAddCircle)) ∈ U ∧
      ∃ J : Set ℕ, IsThick J ∧
      ∀ n : ℕ, n ∈ J → n • (fun i => (α i : UnitAddCircle)) ∈ U →
        Representable (B₀ ∪ B₁) n

/-- Once the standard BFW finite-sum property is supplied, F-071 and the
already formal compact correction assembly prove the canonical Erdős statement. -/
theorem bfw_finite_sum_property_implies_statement
    (hBFW : BFWFiniteSumProperty) : Erdos254.Statement := by
  intro A hdyadic hphase
  obtain ⟨B, C, hBA, hCA, hBpair, hBC, hcover, hBsynd, hCphase⟩ :=
    exists_three_syndetic_classes_and_universal_correction A hdyadic hphase
  let B₀ := B (0 : Fin 3)
  let B₁ := B (1 : Fin 3)
  let D := B (2 : Fin 3)
  have htwo : ∀ i : Fin 2, ∃ K : ℕ, ∀ n : ℕ, ∃ t : Finset ℕ,
      (∀ b ∈ t, b ∈ (if i = 0 then B₀ else B₁)) ∧
      (∑ b ∈ t, b) ≤ n ∧ n ≤ (∑ b ∈ t, b) + K := by
    intro i
    fin_cases i
    · simpa [B₀] using hBsynd (0 : Fin 3)
    · simpa [B₁] using hBsynd (1 : Fin 3)
  have hB01 : Disjoint B₀ B₁ :=
    hBpair (by decide : (0 : Fin 3) ≠ 1)
  obtain ⟨d, α, U, hUopen, n₀, hn₀U, J, hJ, hpiece⟩ :=
    hBFW B₀ B₁ hB01 htwo
  obtain ⟨H, hHclosed, haH, hcorr⟩ :=
    exists_closed_torus_correction_group C hCphase α
  have hB01C : Disjoint (B₀ ∪ B₁) C := by
    rw [Set.disjoint_left]
    intro n hn hnC
    rcases hn with hn0 | hn1
    · exact Set.disjoint_left.mp (hBC (0 : Fin 3)) hn0 hnC
    · exact Set.disjoint_left.mp (hBC (1 : Fin 3)) hn1 hnC
  have hB01D : Disjoint (B₀ ∪ B₁) D := by
    rw [Set.disjoint_left]
    intro n hn hnD
    rcases hn with hn0 | hn1
    · exact Set.disjoint_left.mp (hBpair (by decide : (0 : Fin 3) ≠ 2)) hn0 hnD
    · exact Set.disjoint_left.mp (hBpair (by decide : (1 : Fin 3) ≠ 2)) hn1 hnD
  have hCD : Disjoint C D := (hBC (2 : Fin 3)).symm
  obtain ⟨KD, hDsynd⟩ := hBsynd (2 : Fin 3)
  obtain ⟨N, hN⟩ := conditional_piecewise_bohr_completeness
    (B₀ ∪ B₁) C D hB01C hB01D hCD
    (fun i => (α i : UnitAddCircle)) H hHclosed haH hcorr
    U hUopen n₀ hn₀U J hJ hpiece KD
    (fun n => by
      obtain ⟨t, htD, htlo, hthi⟩ := hDsynd n
      exact ⟨∑ b ∈ t, b, ⟨t, htD, rfl⟩, htlo, hthi⟩)
  refine ⟨N, ?_⟩
  intro m hm
  obtain ⟨s, hs, hsum⟩ := hN m hm
  refine ⟨s, ?_, hsum⟩
  intro x hxs
  have hxUnion := hs x hxs
  rcases hxUnion with hxBC | hxD
  · rcases hxBC with hxB | hxC
    · rcases hxB with hx0 | hx1
      · exact hBA (0 : Fin 3) hx0
      · exact hBA (1 : Fin 3) hx1
    · exact hCA hxC
  · exact hBA (2 : Fin 3) hxD

end

end Erdos254.ConditionalFinalAssembly
