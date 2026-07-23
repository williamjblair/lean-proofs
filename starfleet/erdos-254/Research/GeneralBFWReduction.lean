import Mathlib
import Research.PiecewiseAssembly
import Research.ConditionalFinalAssembly

namespace Erdos254.GeneralBFWReduction

open scoped Topology BigOperators
open Erdos254.PiecewiseAssembly Erdos254.ConditionalFinalAssembly

noncomputable section

/-- Standard set-theoretic BFW theorem in exactly the finite-torus form needed
here. -/
def SyndeticSumsetPiecewiseBohr : Prop :=
  ∀ S₀ S₁ : Set ℕ,
    (∀ i : Fin 2, ∃ K : ℕ, ∀ n : ℕ, ∃ s : ℕ,
      s ∈ (if i = 0 then S₀ else S₁) ∧ s ≤ n ∧ n ≤ s + K) →
    ∃ d : ℕ, ∃ α : Fin d → ℝ,
      ∃ U : Set (UnitAddTorus (Fin d)), IsOpen U ∧
      ∃ n₀ : ℕ, n₀ • (fun i => (α i : UnitAddCircle)) ∈ U ∧
      ∃ J : Set ℕ, IsThick J ∧
      ∀ n : ℕ, n ∈ J → n • (fun i => (α i : UnitAddCircle)) ∈ U →
        ∃ s₀ ∈ S₀, ∃ s₁ ∈ S₁, s₀ + s₁ = n

/-- The standard BFW sumset theorem implies the finite-sum interface, because
representations from two disjoint source classes can be united without reuse. -/
theorem general_bfw_implies_finite_sum_property
    (hBFW : SyndeticSumsetPiecewiseBohr) : BFWFiniteSumProperty := by
  intro B₀ B₁ hBdis hsynd
  let S₀ : Set ℕ := {n | Representable B₀ n}
  let S₁ : Set ℕ := {n | Representable B₁ n}
  have hSsynd : ∀ i : Fin 2, ∃ K : ℕ, ∀ n : ℕ, ∃ s : ℕ,
      s ∈ (if i = 0 then S₀ else S₁) ∧ s ≤ n ∧ n ≤ s + K := by
    intro i
    obtain ⟨K, hK⟩ := hsynd i
    refine ⟨K, fun n => ?_⟩
    obtain ⟨t, ht, htlo, hthi⟩ := hK n
    refine ⟨∑ b ∈ t, b, ?_, htlo, hthi⟩
    fin_cases i
    · exact ⟨t, by simpa using ht, rfl⟩
    · exact ⟨t, by simpa using ht, rfl⟩
  obtain ⟨d, α, U, hU, n₀, hn₀, J, hJ, hpiece⟩ := hBFW S₀ S₁ hSsynd
  refine ⟨d, α, U, hU, n₀, hn₀, J, hJ, ?_⟩
  intro n hnJ hnU
  obtain ⟨s₀, hs₀, s₁, hs₁, hsum⟩ := hpiece n hnJ hnU
  have hrep := representable_add_of_disjoint hBdis hs₀ hs₁
  rwa [hsum] at hrep

end

end Erdos254.GeneralBFWReduction
