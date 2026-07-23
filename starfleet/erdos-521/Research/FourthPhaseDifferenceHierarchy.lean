import Research.FourthPhaseFiniteDifferences
import Mathlib.Tactic

namespace Erdos521

lemma fourthOldPolynomialPhase_first_difference (q : ℕ) (s t : ℝ) :
    fourthOldPolynomialPhase (q + 1) s t - fourthOldPolynomialPhase q s t =
      s * fourthCoefficientB q + t * (q + 3 : ℝ) := by
  unfold fourthOldPolynomialPhase
  rw [fourthCoefficientA_formula, fourthCoefficientA_formula,
    fourthCoefficientB_formula, fourthCoefficientB_formula]
  push_cast
  ring

lemma first_difference_sq_le (x0 x1 : ℝ) :
    (x1 - x0) ^ 2 ≤ 2 * (x0 ^ 2 + x1 ^ 2) := by
  nlinarith [sq_nonneg (x0 + x1)]

/-- Two consecutive modular phase residuals control the residue of the quadratic first
finite-difference phase. -/
lemma fourthPhase_first_difference_residue_sq_le (q : ℕ) (s t : ℝ)
    (m0 m1 : ℤ) :
    (s * fourthCoefficientB q + t * (q + 3 : ℝ) -
      ((m1 : ℝ) - (m0 : ℝ)) * Real.pi) ^ 2 ≤
      2 * ((fourthOldPolynomialPhase q s t - (m0 : ℝ) * Real.pi) ^ 2 +
        (fourthOldPolynomialPhase (q + 1) s t - (m1 : ℝ) * Real.pi) ^ 2) := by
  let r0 := fourthOldPolynomialPhase q s t - (m0 : ℝ) * Real.pi
  let r1 := fourthOldPolynomialPhase (q + 1) s t - (m1 : ℝ) * Real.pi
  have h := first_difference_sq_le r0 r1
  have hphase := fourthOldPolynomialPhase_first_difference q s t
  have hlin : r1 - r0 = s * fourthCoefficientB q + t * (q + 3 : ℝ) -
      ((m1 : ℝ) - (m0 : ℝ)) * Real.pi := by
    dsimp [r0, r1]
    rw [← hphase]
    ring
  rw [← hlin]
  exact h

lemma fourthOriginalPhase_some_eq_old (k : ℕ) (s t : ℝ) (q : Fin (k + 1)) :
    fourthOriginalPhase k s t (some q) = fourthOldPolynomialPhase q s t := rfl

end Erdos521
