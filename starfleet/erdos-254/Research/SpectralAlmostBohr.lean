import Mathlib
import Research.AtomicBohrLower
import Research.CesaroErrorThick

namespace Erdos254.SpectralAlmostBohr

open MeasureTheory
open scoped BigOperators Topology
open Erdos254.AtomicDecomposition Erdos254.SpectralWienerDecomposition
open Erdos254.AtomicBohrLower Erdos254.CesaroErrorThick
open Erdos254.PiecewiseAssembly

noncomputable section

local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩

/-- Spectral Følner principle: if a finite circle measure has positive mass at
the trivial character, then the positivity set of its Fourier coefficients
contains a finite-dimensional Bohr neighborhood intersected with a thick set. -/
theorem spectral_positive_set_contains_piecewise_bohr
    (μ : Measure Circle) [IsFiniteMeasure μ]
    (δ : ℝ) (hδ : 0 < δ) (hδatom : δ ≤ μ.real {(1 : Circle)})
    (S : Set ℕ)
    (hpositive : ∀ n : ℕ, 0 < (∫ z : Circle, (z : ℂ) ^ n ∂μ).re → n ∈ S) :
    ∃ d : ℕ, ∃ a : Fin d → Circle, ∃ U : Set (Fin d → Circle),
      IsOpen U ∧ (fun _ => (1 : Circle)) ∈ U ∧
      ∃ J : Set ℕ, IsThick J ∧
        ∀ n : ℕ, (fun i => a i ^ n) ∈ U → n ∈ J → n ∈ S := by
  obtain ⟨d, a, U, hUopen, hone, hatomic⟩ :=
    exists_finite_circle_bohr_atomic_lower μ δ hδ hδatom
  let r : ℕ → ℝ := fun n => (continuousCoeff μ n).re
  let J : Set ℕ := {n | |r n| < δ / 2}
  have hr : Filter.Tendsto
      (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, (r n) ^ 2)
      Filter.atTop (nhds 0) := by
    simpa [r] using tendsto_cesaro_sq_re_continuousCoeff μ
  have hJ : IsThick J := by
    apply small_error_set_is_thick r hr (δ / 2)
    positivity
  refine ⟨d, a, U, hUopen, hone, J, hJ, ?_⟩
  intro n hnU hnJ
  apply hpositive n
  have ha := hatomic n hnU
  have hrsmall : |r n| < δ / 2 := hnJ
  have hrbelow : -(δ / 2) < r n := neg_lt_of_abs_lt hrsmall
  have hcoeff := coeff_eq_atomic_add_continuous μ n
  have hre := congrArg Complex.re hcoeff
  change (∫ z : Circle, (z : ℂ) ^ n ∂μ).re =
      (atomicCoeff μ n).re + r n at hre
  rw [hre]
  nlinarith

end

end Erdos254.SpectralAlmostBohr
