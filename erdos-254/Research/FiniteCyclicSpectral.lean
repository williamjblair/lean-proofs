import Mathlib
import Research.ZModParseval

namespace Erdos254.FiniteCyclicSpectral

open MeasureTheory Finset AddChar
open scoped BigOperators ComplexConjugate
open ZMod
open Erdos254.ZModParseval

noncomputable section

local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩

variable {N : ℕ} [NeZero N]

def energy (Φ : ZMod N → ℂ) : ℝ := ∑ j : ZMod N, ‖Φ j‖ ^ 2

def denom (Φ : ZMod N → ℂ) : ℝ := (N : ℝ) * energy Φ

private def spectralWeight (Φ : ZMod N → ℂ) (k : ZMod N) : ℝ :=
  ‖𝓕 Φ k‖ ^ 2 / denom Φ

private lemma sum_spectralWeight (Φ : ZMod N → ℂ) (hE : 0 < energy Φ) :
    ∑ k : ZMod N, spectralWeight Φ k = 1 := by
  rw [show (∑ k : ZMod N, spectralWeight Φ k) =
      (∑ k : ZMod N, ‖𝓕 Φ k‖ ^ 2) / denom Φ by
    simp [spectralWeight, sum_div]]
  rw [sum_norm_sq_dft]
  simp only [denom]
  change ((N : ℝ) * energy Φ) / ((N : ℝ) * energy Φ) = 1
  exact div_self (mul_ne_zero (by exact_mod_cast (NeZero.ne N)) hE.ne')

private def spectralPMF (Φ : ZMod N → ℂ) (hE : 0 < energy Φ) : PMF (ZMod N) :=
  PMF.ofFintype (fun k => ENNReal.ofReal (spectralWeight Φ k)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by
      unfold spectralWeight denom energy
      positivity)]
    rw [sum_spectralWeight Φ hE, ENNReal.ofReal_one])

private lemma spectralPMF_toReal (Φ : ZMod N → ℂ) (hE : 0 < energy Φ)
    (k : ZMod N) :
    ((spectralPMF Φ hE k).toReal) = spectralWeight Φ k := by
  rw [spectralPMF, PMF.ofFintype_apply, ENNReal.toReal_ofReal]
  unfold spectralWeight denom energy
  positivity

private def sourceProbability (Φ : ZMod N → ℂ) (hE : 0 < energy Φ) :
    ProbabilityMeasure (ZMod N) :=
  ⟨(spectralPMF Φ hE).toMeasure, inferInstance⟩

private def spectralProbability (Φ : ZMod N → ℂ) (hE : 0 < energy Φ) :
    ProbabilityMeasure Circle := by
  letI : MeasurableSpace (ZMod N) := ⊤
  exact (sourceProbability Φ hE).map
    (measurable_of_countable (ZMod.toCircle : ZMod N → Circle)).aemeasurable

/-- A nonzero finite cyclic signal has a circle-valued probability spectral
measure. Its Fourier coefficients are normalized cyclic autocorrelations, and
its atom at `1` is the normalized square of the signal sum. -/
theorem exists_cyclic_spectral_probability
    (Φ : ZMod N → ℂ) (hE : 0 < energy Φ) :
    ∃ ν : ProbabilityMeasure Circle,
      (∀ n : ℕ,
        (∫ z : Circle, (z : ℂ) ^ n ∂(ν : Measure Circle)) =
          (energy Φ)⁻¹ • ∑ j : ZMod N,
            starRingEnd ℂ (Φ j) * Φ (j + (n : ZMod N))) ∧
      (ν : Measure Circle).real {(1 : Circle)} =
        ‖∑ j : ZMod N, Φ j‖ ^ 2 / denom Φ := by
  letI : MeasurableSpace (ZMod N) := ⊤
  let p := spectralPMF Φ hE
  let ν₀ := sourceProbability Φ hE
  let ν := spectralProbability Φ hE
  refine ⟨ν, ?_, ?_⟩
  · intro n
    have hpow (k : ZMod N) : ((ZMod.toCircle k : Circle) : ℂ) ^ n =
        stdAddChar (k * (n : ZMod N)) := by
      change (stdAddChar k) ^ n = _
      rw [← stdAddChar.map_nsmul_eq_pow]
      congr 1
      simp [nsmul_eq_mul, mul_comm]
    have hmap : (ν : Measure Circle) =
        Measure.map (ZMod.toCircle : ZMod N → Circle) (p.toMeasure) := rfl
    rw [hmap, integral_map
      (measurable_of_countable (ZMod.toCircle : ZMod N → Circle)).aemeasurable
      (by fun_prop), PMF.integral_eq_sum]
    simp_rw [hpow]
    dsimp only [p]
    simp_rw [spectralPMF_toReal Φ hE]
    have hnorm (k : ZMod N) :
        (((‖𝓕 Φ k‖ ^ 2 : ℝ) : ℂ)) =
          starRingEnd ℂ (𝓕 Φ k) * 𝓕 Φ k := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
      ring
    have hnum :
        (∑ k : ZMod N, spectralWeight Φ k •
          stdAddChar (k * (n : ZMod N))) =
        (∑ k : ZMod N,
          (starRingEnd ℂ (𝓕 Φ k) * 𝓕 Φ k) *
            stdAddChar (k * (n : ZMod N))) / ((denom Φ : ℝ) : ℂ) := by
      rw [div_eq_mul_inv, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      rw [spectralWeight, Complex.real_smul, Complex.ofReal_div, hnorm]
      ring
    rw [hnum, dft_energy_character]
    rw [Complex.real_smul]
    unfold denom
    push_cast
    field_simp [show (N : ℂ) ≠ 0 by exact_mod_cast (NeZero.ne N), hE.ne']
  · have hmap : (ν : Measure Circle) =
        Measure.map (ZMod.toCircle : ZMod N → Circle) (p.toMeasure) := rfl
    rw [measureReal_def, hmap, Measure.map_apply_of_aemeasurable
      (measurable_of_countable (ZMod.toCircle : ZMod N → Circle)).aemeasurable
      (MeasurableSet.singleton 1)]
    have hpre : (ZMod.toCircle : ZMod N → Circle) ⁻¹' {(1 : Circle)} = {0} := by
      ext k
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro hk
        apply ZMod.injective_toCircle
        simpa using hk
      · rintro rfl
        simp
    rw [hpre, PMF.toMeasure_apply_singleton p 0 (MeasurableSet.singleton 0)]
    rw [spectralPMF_toReal Φ hE]
    simp only [spectralWeight, ZMod.dft_apply_zero]

end

end Erdos254.FiniteCyclicSpectral
