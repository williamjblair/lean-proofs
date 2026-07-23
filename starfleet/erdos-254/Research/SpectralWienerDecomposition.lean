import Mathlib
import Research.AtomicDecomposition
import Research.AtomlessWiener

namespace Erdos254.SpectralWienerDecomposition

open Filter Topology MeasureTheory
open scoped BigOperators
open Erdos254.AtomicDecomposition

noncomputable section

local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩

/-- The pure-point Fourier part of a finite circle measure. -/
def atomicCoeff (μ : Measure Circle) (n : ℕ) : ℂ :=
  ∑' z : atomSet μ, μ.real {(z : Circle)} • ((z : Circle) : ℂ) ^ n

/-- The Fourier coefficient of the atomless remainder. -/
def continuousCoeff (μ : Measure Circle) (n : ℕ) : ℂ :=
  ∫ z : Circle, (z : ℂ) ^ n ∂(continuousPart μ)

private lemma integrable_pow (μ : Measure Circle) [IsFiniteMeasure μ] (n : ℕ) :
    Integrable (fun z : Circle => (z : ℂ) ^ n) μ := by
  apply Integrable.of_bound (by fun_prop) 1
  exact Filter.Eventually.of_forall (by intro z; simp)

lemma coeff_eq_atomic_add_continuous
    (μ : Measure Circle) [IsFiniteMeasure μ] (n : ℕ) :
    (∫ z : Circle, (z : ℂ) ^ n ∂μ) = atomicCoeff μ n + continuousCoeff μ n := by
  simpa [atomicCoeff, continuousCoeff] using
    integral_eq_atomic_add_continuous μ (fun z : Circle => (z : ℂ) ^ n)
      (integrable_pow μ n)

lemma tendsto_cesaro_sq_re_continuousCoeff
    (μ : Measure Circle) [IsFiniteMeasure μ] :
    Tendsto
      (fun N : ℕ => (N : ℝ)⁻¹ *
        ∑ n ∈ Finset.range N, (continuousCoeff μ n).re ^ 2)
      atTop (𝓝 0) := by
  have htop := Erdos254.AtomlessWiener.tendsto_cesaro_sq_fourier_atomless
    (continuousPart μ)
  apply Filter.Tendsto.squeeze tendsto_const_nhds htop
  · intro N
    positivity
  · intro N
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum
    intro n hn
    change (continuousCoeff μ n).re ^ 2 ≤ ‖continuousCoeff μ n‖ ^ 2
    rw [sq_le_sq]
    simpa only [abs_of_nonneg (norm_nonneg _)] using
      Complex.abs_re_le_norm (continuousCoeff μ n)

lemma summable_atomic_terms (μ : Measure Circle) [IsFiniteMeasure μ] (n : ℕ) :
    Summable (fun z : atomSet μ =>
      μ.real {(z : Circle)} • ((z : Circle) : ℂ) ^ n) := by
  apply Summable.of_norm
  simpa [norm_smul, Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg] using
    summable_atom_weights μ

lemma atomicCoeff_zero_re (μ : Measure Circle) [IsFiniteMeasure μ] :
    (atomicCoeff μ 0).re = ∑' z : atomSet μ, μ.real {(z : Circle)} := by
  unfold atomicCoeff
  simp only [pow_zero, Complex.real_smul, mul_one]
  change Complex.reCLM (∑' z : atomSet μ,
    ((μ.real {(z : Circle)} : ℝ) : ℂ)) = _
  have hs : Summable (fun z : atomSet μ =>
      ((μ.real {(z : Circle)} : ℝ) : ℂ)) := by
    simpa only [Complex.ofRealCLM_apply] using
      Complex.ofRealCLM.summable (summable_atom_weights μ)
  rw [Complex.reCLM.map_tsum hs]
  simp

lemma singleton_one_mass_le_atomicCoeff_zero
    (μ : Measure Circle) [IsFiniteMeasure μ] :
    μ.real {(1 : Circle)} ≤ (atomicCoeff μ 0).re := by
  rw [atomicCoeff_zero_re]
  by_cases h1 : μ {(1 : Circle)} = 0
  · rw [measureReal_def, h1, ENNReal.toReal_zero]
    exact tsum_nonneg (fun _ => measureReal_nonneg)
  · let z1 : atomSet μ := ⟨1, h1⟩
    exact (summable_atom_weights μ).le_tsum z1
      (fun _ _ => measureReal_nonneg)

/-- The atomic Fourier series is uniformly approximable in the time variable
by one finite set of atoms. -/
theorem exists_finite_atomic_approximation
    (μ : Measure Circle) [IsFiniteMeasure μ]
    (ε : ℝ) (hε : 0 < ε) :
    ∃ F : Finset (atomSet μ), ∀ n : ℕ,
      ‖atomicCoeff μ n -
        ∑ z ∈ F, μ.real {(z : Circle)} • ((z : Circle) : ℂ) ^ n‖ < ε := by
  let w : atomSet μ → ℝ := fun z => μ.real {(z : Circle)}
  have hw : Summable w := summable_atom_weights μ
  have ht := tendsto_tsum_compl_atTop_zero w
  have hevent := (tendsto_order.1 ht).2 ε hε
  obtain ⟨F₀, hF₀⟩ := eventually_atTop.1 hevent
  refine ⟨F₀, ?_⟩
  intro n
  let f : atomSet μ → ℂ := fun z =>
    μ.real {(z : Circle)} • ((z : Circle) : ℂ) ^ n
  have hf : Summable f := summable_atomic_terms μ n
  have hsplit := hf.sum_add_tsum_subtype_compl F₀
  have hatomic : atomicCoeff μ n = ∑' z, f z := by
    unfold atomicCoeff
    congr 1
  have hdiff : atomicCoeff μ n - ∑ z ∈ F₀, f z =
      ∑' z : {z // z ∉ F₀}, f z := by
    rw [hatomic, ← hsplit]
    abel
  rw [show (∑ z ∈ F₀, μ.real {(z : Circle)} •
      ((z : Circle) : ℂ) ^ n) = ∑ z ∈ F₀, f z by rfl, hdiff]
  calc
    ‖∑' z : {z // z ∉ F₀}, f z‖ ≤
        ∑' z : {z // z ∉ F₀}, ‖f z‖ := by
      apply norm_tsum_le_tsum_norm
      exact hf.norm.subtype _
    _ = ∑' z : {z // z ∉ F₀}, w z := by
      apply tsum_congr
      intro z
      simp [f, w, Real.norm_eq_abs,
        abs_of_nonneg measureReal_nonneg]
    _ < ε := hF₀ F₀ le_rfl

end

end Erdos254.SpectralWienerDecomposition
