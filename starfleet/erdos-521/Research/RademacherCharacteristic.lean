import Research.Definitions
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

open scoped BigOperators ComplexConjugate

namespace Erdos521

noncomputable def finiteRademacherLinear {n : ℕ} (u : Fin n → ℝ)
    (x : Fin n → Bool) : ℝ :=
  ∑ i, sign (x i) * u i

lemma sum_bool_cexp_sign (a : ℝ) :
    (∑ b : Bool, Complex.exp (Complex.I * (a * sign b))) =
      2 * (Real.cos a : ℂ) := by
  rw [Fintype.sum_bool]
  rw [show sign true = (1 : ℝ) by simp [sign],
    show sign false = (-1 : ℝ) by simp [sign]]
  push_cast
  rw [show Complex.I * (↑a * (-1 : ℂ)) = (-a : ℂ) * Complex.I by ring,
    show Complex.I * (↑a * (1 : ℂ)) = (a : ℂ) * Complex.I by ring,
    Complex.exp_mul_I, Complex.exp_mul_I]
  rw [Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos]
  ring

/-- Exact characteristic function factorization for a finite Rademacher linear form. -/
lemma sum_cexp_finiteRademacherLinear {n : ℕ} (u : Fin n → ℝ) (t : ℝ) :
    (∑ x : Fin n → Bool,
      Complex.exp (Complex.I * (t * finiteRademacherLinear u x))) =
      (2 : ℂ) ^ n * ∏ i : Fin n, (Real.cos (t * u i) : ℂ) := by
  have hpoint (x : Fin n → Bool) :
      Complex.exp (Complex.I * (t * finiteRademacherLinear u x)) =
        ∏ i : Fin n, Complex.exp (Complex.I * (t * (sign (x i) * u i))) := by
    unfold finiteRademacherLinear
    rw [show Complex.I * (↑t * ↑(∑ i, sign (x i) * u i)) =
        ∑ i : Fin n, Complex.I * (t * (sign (x i) * u i)) by
      push_cast
      calc
        Complex.I * (↑t * ∑ i, ↑(sign (x i)) * ↑(u i)) =
            (Complex.I * t) * ∑ i, ↑(sign (x i)) * ↑(u i) := by ring
        _ = ∑ i, (Complex.I * t) * (↑(sign (x i)) * ↑(u i)) := by
          rw [Finset.mul_sum]
        _ = _ := by
          apply Finset.sum_congr rfl
          intro i hi
          push_cast
          ring]
    exact Complex.exp_sum Finset.univ _
  simp_rw [hpoint]
  calc
    (∑ x : Fin n → Bool,
      ∏ i : Fin n, Complex.exp (Complex.I * (t * (sign (x i) * u i)))) =
        ∏ i : Fin n, ∑ b : Bool,
          Complex.exp (Complex.I * (t * (sign b * u i))) := by
      exact (Fintype.prod_sum
        (fun i : Fin n ↦ fun b : Bool ↦
          Complex.exp (Complex.I * (t * (sign b * u i))))).symm
    _ = ∏ i : Fin n, (2 * (Real.cos (t * u i) : ℂ)) := by
      apply Finset.prod_congr rfl
      intro i hi
      calc
        (∑ b : Bool, Complex.exp (Complex.I * (t * (sign b * u i)))) =
            ∑ b : Bool, Complex.exp (Complex.I * ((t * u i) * sign b)) := by
          apply Finset.sum_congr rfl
          intro b hb
          congr 1
          push_cast
          ring
        _ = _ := by
          have h := sum_bool_cexp_sign (t * u i)
          push_cast at h
          rw [Complex.ofReal_cos]
          push_cast
          exact h
    _ = (2 : ℂ) ^ n * ∏ i : Fin n, (Real.cos (t * u i) : ℂ) := by
      rw [Finset.prod_mul_distrib]
      simp

lemma average_cexp_finiteRademacherLinear {n : ℕ} (u : Fin n → ℝ) (t : ℝ) :
    (∑ x : Fin n → Bool,
      Complex.exp (Complex.I * (t * finiteRademacherLinear u x))) /
        (2 : ℂ) ^ n =
      ∏ i : Fin n, (Real.cos (t * u i) : ℂ) := by
  rw [sum_cexp_finiteRademacherLinear]
  field_simp

/-- Bivariate specialization: the characteristic function of a signed vector sum is a cosine
product in every dual direction. -/
lemma average_cexp_finiteRademacherBivariate {n : ℕ} (u v : Fin n → ℝ) (s t : ℝ) :
    (∑ x : Fin n → Bool,
      Complex.exp (Complex.I *
        (s * finiteRademacherLinear u x + t * finiteRademacherLinear v x))) /
        (2 : ℂ) ^ n =
      ∏ i : Fin n, (Real.cos (s * u i + t * v i) : ℂ) := by
  let w : Fin n → ℝ := fun i ↦ s * u i + t * v i
  have hlin (x : Fin n → Bool) :
      finiteRademacherLinear w x =
        s * finiteRademacherLinear u x + t * finiteRademacherLinear v x := by
    unfold finiteRademacherLinear w
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    apply congrArg₂ (· + ·) <;> apply Finset.sum_congr rfl <;> intro i hi <;> ring
  have h := average_cexp_finiteRademacherLinear w 1
  rw [show (1 : ℝ) = 1 by rfl] at h
  convert h using 1
  · apply congrArg (fun z : ℂ ↦ z / (2 : ℂ) ^ n)
    apply Finset.sum_congr rfl
    intro x hx
    rw [hlin]
    push_cast
    congr 1
    ring
  · apply Finset.prod_congr rfl
    intro i hi
    dsimp [w]
    norm_num

end Erdos521
