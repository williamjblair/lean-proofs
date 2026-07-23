import Mathlib
import Research.IndicatorCyclicLimit

namespace Erdos254.FiniteBlockSpectral

open MeasureTheory
open scoped BigOperators
open Erdos254.CyclicSpectralLimit Erdos254.IndicatorCyclicLimit

noncomputable section

local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩
local instance (j : ℕ) : NeZero (M j) := ⟨by simp [M]⟩

private def embedBlock (j x : ℕ) : ZMod (M j) := (j + 1 + x : ℕ)

/-- Dense finite blocks whose ordinary positive differences lie in `D` produce
a spectral probability measure whose positive Fourier coefficients lie in `D`. -/
theorem exists_spectral_probability_of_dense_blocks
    (B : ℕ → Finset ℕ) (D : Set ℕ) (δ : ℝ) (hδ : 0 < δ)
    (hBbound : ∀ j x : ℕ, x ∈ B j → x < j + 1)
    (hBnonempty : ∀ j : ℕ, (B j).Nonempty)
    (hdensity : ∀ j : ℕ, δ ≤ (B j).card / (M j : ℝ))
    (hdiff : ∀ j x y n : ℕ,
      x ∈ B j → y ∈ B j → y = x + n → n ∈ D) :
    ∃ μ : ProbabilityMeasure Circle,
      δ ≤ (μ : Measure Circle).real {(1 : Circle)} ∧
      ∀ n : ℕ, 0 < (∫ z : Circle, (z : ℂ) ^ n ∂(μ : Measure Circle)).re → n ∈ D := by
  let P : ∀ j : ℕ, Finset (ZMod (M j)) := fun j =>
    (B j).image (embedBlock j)
  have hinj (j : ℕ) : Set.InjOn (embedBlock j) (B j : Set ℕ) := by
    intro x hx y hy hxy
    have hxlt : j + 1 + x < M j := by
      have := hBbound j x hx
      simp only [M]
      omega
    have hylt : j + 1 + y < M j := by
      have := hBbound j y hy
      simp only [M]
      omega
    have hv := congrArg ZMod.val hxy
    change ((j + 1 + x : ℕ) : ZMod (M j)).val =
      ((j + 1 + y : ℕ) : ZMod (M j)).val at hv
    rw [ZMod.val_natCast_of_lt hxlt, ZMod.val_natCast_of_lt hylt] at hv
    omega
  have hcard (j : ℕ) : (P j).card = (B j).card := by
    apply Finset.card_image_iff.mpr
    exact hinj j
  have hP : ∀ j : ℕ, (P j).Nonempty := by
    intro j
    obtain ⟨x, hx⟩ := hBnonempty j
    exact ⟨embedBlock j x, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
  have hPdensity : ∀ j : ℕ, δ ≤ (P j).card / (M j : ℝ) := by
    intro j
    rw [hcard]
    exact hdensity j
  have hpair : ∀ j n : ℕ, n < j + 1 →
      ∀ k : ZMod (M j), k ∈ P j → k + (n : ZMod (M j)) ∈ P j → n ∈ D := by
    intro j n hn k hk hkn
    rw [Finset.mem_image] at hk hkn
    obtain ⟨x, hxB, rfl⟩ := hk
    obtain ⟨y, hyB, hEq⟩ := hkn
    have hxlt := hBbound j x hxB
    have hylt := hBbound j y hyB
    have hleftlt : j + 1 + x + n < M j := by
      simp only [M]
      omega
    have hyembedlt : j + 1 + y < M j := by
      simp only [M]
      omega
    have hcast : ((j + 1 + x + n : ℕ) : ZMod (M j)) =
        ((j + 1 + y : ℕ) : ZMod (M j)) := by
      simpa [embedBlock, Nat.cast_add] using hEq.symm
    have hv := congrArg ZMod.val hcast
    rw [ZMod.val_natCast_of_lt hleftlt,
      ZMod.val_natCast_of_lt hyembedlt] at hv
    apply hdiff j x y n hxB hyB
    omega
  exact exists_spectral_probability_of_cyclic_indicators P D δ hδ hP hPdensity hpair

/-- Shifted finite-embedding version for ordinary finite blocks. -/
theorem exists_spectral_probability_of_dense_blocks_finitely_embedded
    (B : ℕ → Finset ℕ) (q : ℕ → ℕ) (S : Set ℕ) (δ : ℝ)
    (hBbound : ∀ j x : ℕ, x ∈ B j → x < j + 1)
    (hBnonempty : ∀ j : ℕ, (B j).Nonempty)
    (hdensity : ∀ j : ℕ, δ ≤ (B j).card / (M j : ℝ))
    (hdiff : ∀ j x y n : ℕ,
      x ∈ B j → y ∈ B j → y = x + n → n + q j ∈ S) :
    ∃ μ : ProbabilityMeasure Circle,
      δ ≤ (μ : Measure Circle).real {(1 : Circle)} ∧
      ∀ F : Finset ℕ,
        (∀ n ∈ F, 0 < (∫ z : Circle, (z : ℂ) ^ n ∂(μ : Measure Circle)).re) →
        ∃ r : ℕ, ∀ n ∈ F, n + r ∈ S := by
  let P : ∀ j : ℕ, Finset (ZMod (M j)) := fun j =>
    (B j).image (embedBlock j)
  have hinj (j : ℕ) : Set.InjOn (embedBlock j) (B j : Set ℕ) := by
    intro x hx y hy hxy
    have hxlt : j + 1 + x < M j := by
      have := hBbound j x hx
      simp only [M]
      omega
    have hylt : j + 1 + y < M j := by
      have := hBbound j y hy
      simp only [M]
      omega
    have hv := congrArg ZMod.val hxy
    change ((j + 1 + x : ℕ) : ZMod (M j)).val =
      ((j + 1 + y : ℕ) : ZMod (M j)).val at hv
    rw [ZMod.val_natCast_of_lt hxlt, ZMod.val_natCast_of_lt hylt] at hv
    omega
  have hcard (j : ℕ) : (P j).card = (B j).card := by
    apply Finset.card_image_iff.mpr
    exact hinj j
  have hP : ∀ j : ℕ, (P j).Nonempty := by
    intro j
    obtain ⟨x, hx⟩ := hBnonempty j
    exact ⟨embedBlock j x, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
  have hPdensity : ∀ j : ℕ, δ ≤ (P j).card / (M j : ℝ) := by
    intro j
    rw [hcard]
    exact hdensity j
  have hpair : ∀ j n : ℕ, n < j + 1 →
      ∀ k : ZMod (M j), k ∈ P j → k + (n : ZMod (M j)) ∈ P j →
        n + q j ∈ S := by
    intro j n hn k hk hkn
    rw [Finset.mem_image] at hk hkn
    obtain ⟨x, hxB, rfl⟩ := hk
    obtain ⟨y, hyB, hEq⟩ := hkn
    have hxlt := hBbound j x hxB
    have hylt := hBbound j y hyB
    have hleftlt : j + 1 + x + n < M j := by
      simp only [M]
      omega
    have hyembedlt : j + 1 + y < M j := by
      simp only [M]
      omega
    have hcast : ((j + 1 + x + n : ℕ) : ZMod (M j)) =
        ((j + 1 + y : ℕ) : ZMod (M j)) := by
      simpa [embedBlock, Nat.cast_add] using hEq.symm
    have hv := congrArg ZMod.val hcast
    rw [ZMod.val_natCast_of_lt hleftlt,
      ZMod.val_natCast_of_lt hyembedlt] at hv
    apply hdiff j x y n hxB hyB
    omega
  exact exists_spectral_probability_of_cyclic_indicators_finitely_embedded
    P q S δ hP hPdensity hpair

end

end Erdos254.FiniteBlockSpectral
