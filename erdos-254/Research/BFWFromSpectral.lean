import Mathlib
import Research.GeneralBFWReduction
import Research.FiniteEmbeddingPiecewiseBohrOrbit
import Research.SyndeticCrossSpectralEmbedding
import Research.SpectralAlmostBohr
import Research.CirclePiecewiseToAddCircle
import Research.PiecewiseFiniteEmbedding

namespace Erdos254.BFWFromSpectral

open MeasureTheory
open scoped Topology
open Erdos254.PiecewiseAssembly Erdos254.GeneralBFWReduction
open Erdos254.FiniteEmbeddingPiecewiseBohrOrbit
open Erdos254.SyndeticCrossSpectralEmbedding Erdos254.SpectralAlmostBohr
open Erdos254.CirclePiecewiseToAddCircle Erdos254.PiecewiseFiniteEmbedding

noncomputable section

local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩

/-- The Bergelson--Furstenberg--Weiss piecewise-Bohr sumset theorem, proved by
finite cyclic cross-correlation, compact spectral limits, Wiener's lemma, and
finite-embedding reassembly. -/
theorem general_bfw_from_spectral : SyndeticSumsetPiecewiseBohr := by
  intro S₀ S₁ hsynd
  have h₀ : ∃ K : ℕ, ∀ n : ℕ, ∃ s : ℕ,
      s ∈ S₀ ∧ s ≤ n ∧ n ≤ s + K := by
    simpa using hsynd (0 : Fin 2)
  have h₁ : ∃ K : ℕ, ∀ n : ℕ, ∃ s : ℕ,
      s ∈ S₁ ∧ s ≤ n ∧ n ≤ s + K := by
    simpa using hsynd (1 : Fin 2)
  let S : Set ℕ := {z | ∃ s₀ ∈ S₀, ∃ s₁ ∈ S₁, s₀ + s₁ = z}
  obtain ⟨μ, hμatom, hembedE⟩ :=
    exists_cross_spectral_finite_embedding S₀ S₁ h₀ h₁
  let E : Set ℕ :=
    {n | 0 < (∫ z : Circle, (z : ℂ) ^ n ∂(μ : Measure Circle)).re}
  obtain ⟨d, a, U, hUopen, hone, J, hJ, hpieceE⟩ :=
    spectral_positive_set_contains_piecewise_bohr μ
      ((μ : Measure Circle).real {(1 : Circle)}) hμatom le_rfl E
      (fun n hn => hn)
  obtain ⟨α, V, hVopen, hzeroV, _, hpieceE'⟩ :=
    circle_piecewise_bohr_to_additive a U hUopen hone J E hJ hpieceE
  let avec : UnitAddTorus (Fin d) := fun i => (α i : UnitAddCircle)
  have hzeroV' : (0 : UnitAddTorus (Fin d)) ∈ V := by
    simpa [avec] using hzeroV
  obtain ⟨W, hWopen, hzeroW, hWE⟩ :=
    pure_bohr_finitely_embeds_piecewise avec V hVopen hzeroV' J E hJ
      (fun n hnV hnJ => hpieceE' n hnV hnJ)
  have hWS : ∀ F : Finset ℕ,
      (∀ n ∈ F, n • avec ∈ W) →
      ∃ r : ℕ, ∀ n ∈ F, n + r ∈ S := by
    intro F hF
    obtain ⟨r₁, hr₁⟩ := hWE F hF
    let G : Finset ℕ := F.image (fun n => n + r₁)
    have hGE : ∀ n ∈ G, n ∈ E := by
      intro n hn
      rw [Finset.mem_image] at hn
      obtain ⟨m, hm, rfl⟩ := hn
      exact hr₁ m hm
    obtain ⟨r₂, hr₂⟩ := hembedE G hGE
    refine ⟨r₁ + r₂, ?_⟩
    intro n hn
    have hnG : n + r₁ ∈ G := Finset.mem_image.mpr ⟨n, hn, rfl⟩
    have hthis := hr₂ (n + r₁) hnG
    change ∃ s₀ ∈ S₀, ∃ s₁ ∈ S₁, s₀ + s₁ = n + (r₁ + r₂)
    simpa [Nat.add_assoc] using hthis
  obtain ⟨W', hW'open, n₀, hn₀W', J', hJ', hfinal⟩ :=
    piecewise_bohr_of_finite_embedding_orbit avec W hWopen 0
      (by simpa using hzeroW) S hWS
  refine ⟨d, α, W', hW'open, n₀, hn₀W', J', hJ', ?_⟩
  intro n hnJ hnW
  exact hfinal n hnJ hnW

end

end Erdos254.BFWFromSpectral
