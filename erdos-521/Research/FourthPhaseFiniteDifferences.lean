import Research.FourthModularDecay
import Mathlib.Tactic

namespace Erdos521

/-- The old original-coordinate phase as a polynomial sequence in the coefficient lag. -/
noncomputable def fourthOldPolynomialPhase (q : ℕ) (s t : ℝ) : ℝ :=
  s * fourthCoefficientA q + t * fourthCoefficientB q

lemma fourthOldPolynomialPhase_second_difference (q : ℕ) (s t : ℝ) :
    fourthOldPolynomialPhase (q + 2) s t -
        2 * fourthOldPolynomialPhase (q + 1) s t +
      fourthOldPolynomialPhase q s t = s * (q + 3 : ℝ) + t := by
  unfold fourthOldPolynomialPhase
  simp_rw [fourthCoefficientA_formula, fourthCoefficientB_formula]
  push_cast
  ring

lemma fourthOldPolynomialPhase_third_difference (q : ℕ) (s t : ℝ) :
    fourthOldPolynomialPhase (q + 3) s t -
        3 * fourthOldPolynomialPhase (q + 2) s t +
      3 * fourthOldPolynomialPhase (q + 1) s t -
        fourthOldPolynomialPhase q s t = s := by
  unfold fourthOldPolynomialPhase
  simp_rw [fourthCoefficientA_formula, fourthCoefficientB_formula]
  push_cast
  ring

/-- Sharp three-variable Cauchy--Schwarz inequality for second finite differences. -/
lemma second_difference_sq_le (x0 x1 x2 : ℝ) :
    (x2 - 2 * x1 + x0) ^ 2 ≤ 6 * (x0 ^ 2 + x1 ^ 2 + x2 ^ 2) := by
  nlinarith [sq_nonneg (x1 + 2 * x0), sq_nonneg (x2 - x0),
    sq_nonneg (-2 * x2 - x1)]

/-- Sharp four-variable Cauchy--Schwarz inequality for third finite differences. -/
lemma third_difference_sq_le (x0 x1 x2 x3 : ℝ) :
    (x3 - 3 * x2 + 3 * x1 - x0) ^ 2 ≤
      20 * (x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2) := by
  nlinarith [sq_nonneg (-x1 - 3 * x0), sq_nonneg (-x2 + 3 * x0),
    sq_nonneg (-x3 + x0), sq_nonneg (3 * x2 + 3 * x1),
    sq_nonneg (3 * x3 - x1), sq_nonneg (-3 * x3 - x2)]

/-- Three consecutive modular residuals control the centered residue of the linear second
finite-difference phase `s(q+3)+t`. -/
lemma fourthPhase_second_difference_residue_sq_le (q : ℕ) (s t : ℝ)
    (m0 m1 m2 : ℤ) :
    (s * (q + 3 : ℝ) + t -
      ((m2 : ℝ) - 2 * (m1 : ℝ) + (m0 : ℝ)) * Real.pi) ^ 2 ≤
      6 * ((fourthOldPolynomialPhase q s t - (m0 : ℝ) * Real.pi) ^ 2 +
        (fourthOldPolynomialPhase (q + 1) s t - (m1 : ℝ) * Real.pi) ^ 2 +
        (fourthOldPolynomialPhase (q + 2) s t - (m2 : ℝ) * Real.pi) ^ 2) := by
  let r0 := fourthOldPolynomialPhase q s t - (m0 : ℝ) * Real.pi
  let r1 := fourthOldPolynomialPhase (q + 1) s t - (m1 : ℝ) * Real.pi
  let r2 := fourthOldPolynomialPhase (q + 2) s t - (m2 : ℝ) * Real.pi
  have h := second_difference_sq_le r0 r1 r2
  have hphase := fourthOldPolynomialPhase_second_difference q s t
  have hlin : r2 - 2 * r1 + r0 = s * (q + 3 : ℝ) + t -
      ((m2 : ℝ) - 2 * (m1 : ℝ) + (m0 : ℝ)) * Real.pi := by
    dsimp [r0, r1, r2]
    rw [← hphase]
    ring
  rw [← hlin]
  exact h

/-- Four consecutive modular residuals control the centered residue of the constant third
finite-difference phase `s`. -/
lemma fourthPhase_third_difference_residue_sq_le (q : ℕ) (s t : ℝ)
    (m0 m1 m2 m3 : ℤ) :
    (s - ((m3 : ℝ) - 3 * (m2 : ℝ) + 3 * (m1 : ℝ) - (m0 : ℝ)) *
      Real.pi) ^ 2 ≤
      20 * ((fourthOldPolynomialPhase q s t - (m0 : ℝ) * Real.pi) ^ 2 +
        (fourthOldPolynomialPhase (q + 1) s t - (m1 : ℝ) * Real.pi) ^ 2 +
        (fourthOldPolynomialPhase (q + 2) s t - (m2 : ℝ) * Real.pi) ^ 2 +
        (fourthOldPolynomialPhase (q + 3) s t - (m3 : ℝ) * Real.pi) ^ 2) := by
  let r0 := fourthOldPolynomialPhase q s t - (m0 : ℝ) * Real.pi
  let r1 := fourthOldPolynomialPhase (q + 1) s t - (m1 : ℝ) * Real.pi
  let r2 := fourthOldPolynomialPhase (q + 2) s t - (m2 : ℝ) * Real.pi
  let r3 := fourthOldPolynomialPhase (q + 3) s t - (m3 : ℝ) * Real.pi
  have h := third_difference_sq_le r0 r1 r2 r3
  have hphase := fourthOldPolynomialPhase_third_difference q s t
  have hlin : r3 - 3 * r2 + 3 * r1 - r0 =
      s - ((m3 : ℝ) - 3 * (m2 : ℝ) + 3 * (m1 : ℝ) - (m0 : ℝ)) *
        Real.pi := by
    dsimp [r0, r1, r2, r3]
    linear_combination hphase
  rw [← hlin]
  exact h

end Erdos521
