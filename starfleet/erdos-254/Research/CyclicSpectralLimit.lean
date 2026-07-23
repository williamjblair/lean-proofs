import Mathlib
import Research.FiniteCyclicSpectral

namespace Erdos254.CyclicSpectralLimit

open Filter Topology MeasureTheory
open scoped BigOperators ComplexConjugate
open Erdos254.FiniteCyclicSpectral

noncomputable section

local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩
local instance (j : ℕ) : NeZero (3 * (j + 1)) := ⟨by omega⟩

abbrev M (j : ℕ) : ℕ := 3 * (j + 1)

def correlation (Φ : ∀ j : ℕ, ZMod (M j) → ℂ) (j n : ℕ) : ℂ :=
  (energy (Φ j))⁻¹ • ∑ k : ZMod (M j),
    starRingEnd ℂ (Φ j k) * Φ j (k + (n : ZMod (M j)))

/-- Compactness upgrades exact finite cyclic spectral measures to a genuine
circle spectral measure. Positivity detected by all sufficiently long cyclic
models is inherited by the limiting Fourier coefficients. -/
theorem exists_limit_spectral_probability
    (Φ : ∀ j : ℕ, ZMod (M j) → ℂ)
    (D : Set ℕ) (δ : ℝ) (hδ : 0 < δ)
    (hE : ∀ j : ℕ, 0 < energy (Φ j))
    (hatom : ∀ j : ℕ,
      δ ≤ ‖∑ k : ZMod (M j), Φ j k‖ ^ 2 / denom (Φ j))
    (hcorr_nonneg : ∀ j n : ℕ, 0 ≤ (correlation Φ j n).re)
    (hdetect : ∀ j n : ℕ, n < j + 1 → 0 < (correlation Φ j n).re → n ∈ D) :
    ∃ μ : ProbabilityMeasure Circle,
      δ ≤ (μ : Measure Circle).real {(1 : Circle)} ∧
      ∀ n : ℕ, 0 < (∫ z : Circle, (z : ℂ) ^ n ∂(μ : Measure Circle)).re → n ∈ D := by
  choose ν hνcoeff hνatom using fun j =>
    exists_cyclic_spectral_probability (Φ j) (hE j)
  obtain ⟨p, hp⟩ := Ultrafilter.exists_le (atTop : Filter ℕ)
  let μ : ProbabilityMeasure Circle := Ultrafilter.extend ν p
  have hlim : Tendsto ν (p : Filter ℕ) (𝓝 μ) := by
    exact ultrafilter_extend_eq_iff.mp rfl
  have hatomENN : ∀ j : ℕ,
      ENNReal.ofReal δ ≤ (ν j : Measure Circle) {(1 : Circle)} := by
    intro j
    rw [← ofReal_measureReal]
    apply ENNReal.ofReal_le_ofReal
    rw [hνatom j]
    exact hatom j
  have hport := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto
    hlim (isClosed_singleton : IsClosed ({(1 : Circle)} : Set Circle))
  have hbounded : IsBoundedUnder (· ≤ ·) (p : Filter ℕ)
      (fun j => (ν j : Measure Circle) {(1 : Circle)}) := by
    apply isBoundedUnder_of_eventually_le (a := 1)
    exact Filter.Eventually.of_forall fun j => by
      calc
        (ν j : Measure Circle) {(1 : Circle)} ≤
            (ν j : Measure Circle) Set.univ := measure_mono (by simp)
        _ = 1 := measure_univ
  have hlower : ENNReal.ofReal δ ≤
      (p : Filter ℕ).limsup (fun j => (ν j : Measure Circle) {(1 : Circle)}) := by
    apply Filter.le_limsup_of_frequently_le (hu_le := hbounded)
    exact (Filter.Eventually.of_forall hatomENN).frequently
  have hμatomENN : ENNReal.ofReal δ ≤ (μ : Measure Circle) {(1 : Circle)} :=
    hlower.trans hport
  have hμatom : δ ≤ (μ : Measure Circle).real {(1 : Circle)} := by
    rw [measureReal_def]
    exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp hμatomENN
  refine ⟨μ, hμatom, ?_⟩
  intro n hnpos
  let f : ContinuousMap Circle ℂ := ⟨fun z => (z : ℂ) ^ n, by fun_prop⟩
  let fb : BoundedContinuousFunction Circle ℂ := BoundedContinuousFunction.mkOfCompact f
  have hint : Tendsto
      (fun j => ∫ z : Circle, (z : ℂ) ^ n ∂(ν j : Measure Circle))
      (p : Filter ℕ)
      (𝓝 (∫ z : Circle, (z : ℂ) ^ n ∂(μ : Measure Circle))) := by
    have hall := (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp hlim
    simpa [fb, f] using hall fb
  have hcorr_lim : Tendsto (fun j => correlation Φ j n) (p : Filter ℕ)
      (𝓝 (∫ z : Circle, (z : ℂ) ^ n ∂(μ : Measure Circle))) := by
    apply hint.congr'
    exact Filter.Eventually.of_forall (fun j => hνcoeff j n)
  have hrelim := (Complex.continuous_re.tendsto _).comp hcorr_lim
  have hpos_event : ∀ᶠ j : ℕ in (p : Filter ℕ), 0 < (correlation Φ j n).re :=
    (tendsto_order.1 hrelim).1 0 hnpos
  have hlong : ∀ᶠ j : ℕ in (p : Filter ℕ), n < j + 1 := by
    apply hp
    exact eventually_atTop.2 ⟨n, by omega⟩
  have hboth := hpos_event.and hlong
  obtain ⟨j, hjpos, hjlong⟩ := hboth.exists
  exact hdetect j n hjlong hjpos

/-- Shifted finite-embedding variant: if every positive short cyclic correlation
translates by `q j` into `S`, then the positivity set of one limiting spectral
measure is finitely embeddable in `S`. -/
theorem exists_limit_spectral_probability_finitely_embedded
    (Φ : ∀ j : ℕ, ZMod (M j) → ℂ)
    (q : ℕ → ℕ) (S : Set ℕ) (δ : ℝ)
    (hE : ∀ j : ℕ, 0 < energy (Φ j))
    (hatom : ∀ j : ℕ,
      δ ≤ ‖∑ k : ZMod (M j), Φ j k‖ ^ 2 / denom (Φ j))
    (hdetect : ∀ j n : ℕ, n < j + 1 →
      0 < (correlation Φ j n).re → n + q j ∈ S) :
    ∃ μ : ProbabilityMeasure Circle,
      δ ≤ (μ : Measure Circle).real {(1 : Circle)} ∧
      ∀ F : Finset ℕ,
        (∀ n ∈ F, 0 < (∫ z : Circle, (z : ℂ) ^ n ∂(μ : Measure Circle)).re) →
        ∃ r : ℕ, ∀ n ∈ F, n + r ∈ S := by
  choose ν hνcoeff hνatom using fun j =>
    exists_cyclic_spectral_probability (Φ j) (hE j)
  obtain ⟨p, hp⟩ := Ultrafilter.exists_le (atTop : Filter ℕ)
  let μ : ProbabilityMeasure Circle := Ultrafilter.extend ν p
  have hlim : Tendsto ν (p : Filter ℕ) (𝓝 μ) :=
    ultrafilter_extend_eq_iff.mp rfl
  have hatomENN : ∀ j : ℕ,
      ENNReal.ofReal δ ≤ (ν j : Measure Circle) {(1 : Circle)} := by
    intro j
    rw [← ofReal_measureReal]
    apply ENNReal.ofReal_le_ofReal
    rw [hνatom j]
    exact hatom j
  have hport := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto
    hlim (isClosed_singleton : IsClosed ({(1 : Circle)} : Set Circle))
  have hbounded : IsBoundedUnder (· ≤ ·) (p : Filter ℕ)
      (fun j => (ν j : Measure Circle) {(1 : Circle)}) := by
    apply isBoundedUnder_of_eventually_le (a := 1)
    exact Filter.Eventually.of_forall fun j => by
      calc
        (ν j : Measure Circle) {(1 : Circle)} ≤
            (ν j : Measure Circle) Set.univ := measure_mono (by simp)
        _ = 1 := measure_univ
  have hlower : ENNReal.ofReal δ ≤
      (p : Filter ℕ).limsup (fun j => (ν j : Measure Circle) {(1 : Circle)}) := by
    apply Filter.le_limsup_of_frequently_le (hu_le := hbounded)
    exact (Filter.Eventually.of_forall hatomENN).frequently
  have hμatomENN : ENNReal.ofReal δ ≤ (μ : Measure Circle) {(1 : Circle)} :=
    hlower.trans hport
  have hμatom : δ ≤ (μ : Measure Circle).real {(1 : Circle)} := by
    rw [measureReal_def]
    exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp hμatomENN
  have hcoefflim (n : ℕ) : Tendsto (fun j => correlation Φ j n) (p : Filter ℕ)
      (𝓝 (∫ z : Circle, (z : ℂ) ^ n ∂(μ : Measure Circle))) := by
    let f : ContinuousMap Circle ℂ := ⟨fun z => (z : ℂ) ^ n, by fun_prop⟩
    let fb : BoundedContinuousFunction Circle ℂ := BoundedContinuousFunction.mkOfCompact f
    have hall := (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp hlim
    have hint : Tendsto
        (fun j => ∫ z : Circle, (z : ℂ) ^ n ∂(ν j : Measure Circle))
        (p : Filter ℕ)
        (𝓝 (∫ z : Circle, (z : ℂ) ^ n ∂(μ : Measure Circle))) := by
      simpa [fb, f] using hall fb
    apply hint.congr'
    exact Filter.Eventually.of_forall (fun j => hνcoeff j n)
  refine ⟨μ, hμatom, ?_⟩
  intro F hF
  have hpos : ∀ᶠ j : ℕ in (p : Filter ℕ),
      ∀ n ∈ F, 0 < (correlation Φ j n).re := by
    rw [Finset.eventually_all]
    intro n hn
    have hrelim := (Complex.continuous_re.tendsto _).comp (hcoefflim n)
    exact (tendsto_order.1 hrelim).1 0 (hF n hn)
  let R : ℕ := ∑ n ∈ F, n
  have hlong : ∀ᶠ j : ℕ in (p : Filter ℕ), R < j + 1 := by
    apply hp
    exact eventually_atTop.2 ⟨R, by omega⟩
  obtain ⟨j, hjpos, hjlong⟩ := (hpos.and hlong).exists
  refine ⟨q j, ?_⟩
  intro n hn
  apply hdetect j n
  · have hnR : n ≤ R := by
      dsimp [R]
      exact Finset.single_le_sum (s := F) (f := fun m : ℕ => m)
        (fun _ _ => Nat.zero_le _) hn
    omega
  · exact hjpos n hn

end

end Erdos254.CyclicSpectralLimit
