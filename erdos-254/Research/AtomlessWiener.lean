import Mathlib
import Research.CesaroGeometric

namespace Erdos254.AtomlessWiener

open Filter Topology MeasureTheory
open scoped BigOperators

noncomputable section

local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩

private def kernel (N : ℕ) (p : Circle × Circle) : ℂ :=
  (N : ℝ)⁻¹ • ∑ n ∈ Finset.range N, ((p.1⁻¹ * p.2 : Circle) : ℂ) ^ n

private lemma kernel_continuous (N : ℕ) : Continuous (kernel N) := by
  unfold kernel
  fun_prop

private lemma norm_kernel_le_one (N : ℕ) (p : Circle × Circle) :
    ‖kernel N p‖ ≤ 1 := by
  by_cases hN : N = 0
  · subst N
    simp [kernel]
  have hsum : ‖∑ n ∈ Finset.range N, ((p.1⁻¹ * p.2 : Circle) : ℂ) ^ n‖ ≤ N := by
    calc
      ‖∑ n ∈ Finset.range N, ((p.1⁻¹ * p.2 : Circle) : ℂ) ^ n‖ ≤
          ∑ n ∈ Finset.range N, ‖((p.1⁻¹ * p.2 : Circle) : ℂ) ^ n‖ :=
        norm_sum_le _ _
      _ = N := by simp
  rw [kernel, norm_smul]
  calc
    ‖(N : ℝ)⁻¹‖ * ‖∑ n ∈ Finset.range N,
        ((p.1⁻¹ * p.2 : Circle) : ℂ) ^ n‖ ≤ ‖(N : ℝ)⁻¹‖ * N :=
      mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
    _ = 1 := by
      rw [Real.norm_eq_abs, abs_inv, abs_of_nonneg (by positivity)]
      exact inv_mul_cancel₀ (by exact_mod_cast hN)

private def coeff (μ : Measure Circle) (n : ℕ) : ℂ :=
  ∫ z : Circle, (z : ℂ) ^ n ∂μ

private lemma integral_ratio_pow
    (μ : Measure Circle) [IsFiniteMeasure μ] (n : ℕ) :
    (∫ p : Circle × Circle, (((p.1⁻¹ * p.2 : Circle) : ℂ) ^ n) ∂(μ.prod μ)) =
      starRingEnd ℂ (coeff μ n) * coeff μ n := by
  have hfun : (fun p : Circle × Circle =>
      (((p.1⁻¹ * p.2 : Circle) : ℂ) ^ n)) =
      (fun p => starRingEnd ℂ ((p.1 : ℂ) ^ n) * (p.2 : ℂ) ^ n) := by
    funext p
    change (((p.1 : ℂ)⁻¹ * (p.2 : ℂ)) ^ n) = _
    have hz : (p.1 : ℂ)⁻¹ = starRingEnd ℂ (p.1 : ℂ) :=
      Circle.coe_inv_eq_conj p.1
    rw [hz, mul_pow, map_pow]
  rw [hfun]
  have hp := integral_prod_mul (μ := μ) (ν := μ)
    (fun z : Circle => starRingEnd ℂ ((z : ℂ) ^ n))
    (fun z : Circle => (z : ℂ) ^ n)
  rw [integral_conj] at hp
  exact hp

private lemma integral_kernel_eq
    (μ : Measure Circle) [IsFiniteMeasure μ] (N : ℕ) :
    (∫ p : Circle × Circle, kernel N p ∂(μ.prod μ)) =
      (((N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, ‖coeff μ n‖ ^ 2 : ℝ) : ℂ) := by
  unfold kernel
  rw [integral_smul]
  have hint : ∀ n ∈ Finset.range N,
      Integrable (fun p : Circle × Circle =>
        (((p.1⁻¹ * p.2 : Circle) : ℂ) ^ n)) (μ.prod μ) := by
    intro n hn
    apply Integrable.of_bound (by fun_prop) 1
    exact Filter.Eventually.of_forall (by intro p; simp)
  rw [integral_finsetSum _ hint]
  simp_rw [integral_ratio_pow μ]
  rw [Complex.ofReal_mul, Complex.ofReal_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- For an atomless finite measure on the circle, the integral of the Cesàro
geometric kernel on the square tends to zero. This is the dominated-convergence
core of Wiener's lemma. -/
theorem tendsto_integral_cesaro_kernel_atomless
    (μ : Measure Circle) [IsFiniteMeasure μ] [NoAtoms μ] :
    Tendsto (fun N : ℕ => ∫ p : Circle × Circle, kernel N p ∂(μ.prod μ))
      atTop (𝓝 0) := by
  have hdiag : (μ.prod μ) (Set.diagonal Circle) = 0 := by
    rw [Measure.prod_apply measurableSet_diagonal]
    simp [Set.diagonal]
  have ht := tendsto_integral_of_dominated_convergence
    (μ := μ.prod μ) (F := kernel) (f := fun _ => (0 : ℂ)) (fun _ => (1 : ℝ))
    (fun N => (kernel_continuous N).aestronglyMeasurable)
    (integrable_const 1)
    (fun N => Filter.Eventually.of_forall (norm_kernel_le_one N))
    (by
      have hne : ∀ᵐ p : Circle × Circle ∂(μ.prod μ), p.1 ≠ p.2 := by
        apply ae_iff.mpr
        simpa [Set.diagonal] using hdiag
      filter_upwards [hne] with p hp
      have hq : p.1⁻¹ * p.2 ≠ (1 : Circle) := by
        intro h
        apply hp
        simpa only [inv_mul_eq_one] using h
      simpa [kernel, hq] using
        Erdos254.CesaroGeometric.tendsto_cesaro_powers_circle (p.1⁻¹ * p.2))
  simpa using ht

/-- Atomless Wiener's lemma: the squared moduli of the Fourier coefficients of
an atomless finite circle measure have Cesàro mean zero. -/
theorem tendsto_cesaro_sq_fourier_atomless
    (μ : Measure Circle) [IsFiniteMeasure μ] [NoAtoms μ] :
    Tendsto
      (fun N : ℕ => (N : ℝ)⁻¹ *
        ∑ n ∈ Finset.range N, ‖∫ z : Circle, (z : ℂ) ^ n ∂μ‖ ^ 2)
      atTop (𝓝 0) := by
  have ht := tendsto_integral_cesaro_kernel_atomless μ
  have hc : Tendsto
      (fun N : ℕ => (((N : ℝ)⁻¹ *
        ∑ n ∈ Finset.range N, ‖coeff μ n‖ ^ 2 : ℝ) : ℂ))
      atTop (𝓝 0) := by
    apply ht.congr'
    exact Filter.Eventually.of_forall (integral_kernel_eq μ)
  have hre := (Complex.continuous_re.tendsto 0).comp hc
  change Tendsto
    (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, ‖coeff μ n‖ ^ 2)
    atTop (𝓝 0) at hre
  simpa [coeff] using hre

end

end Erdos254.AtomlessWiener
