/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.K5.P44.P44NoncommonData
import ErdosProblems.Erdos686.K5.P44.P44Elimination0Rows
import ErdosProblems.Erdos686.K5.P44.P44Elimination1Rows
import ErdosProblems.Erdos686.K5.P44.P44BezoutKernel

namespace Erdos686
namespace Erdos686Variant

/-! Kernel-checked non-common-zero certificate. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem k5P44CurveDense_toSparse :
    denseBivariateToSparse k5P44CurveDense = k5CurveTerms := by
  decide +kernel

theorem k5P44Section0Dense_toSparse :
    denseBivariateToSparse k5P44Section0Dense =
      k5P44Section0 := by
  decide +kernel

theorem k5P44Resultant0_eval_eq_zero
    {x y : ℤ}
    (hsection :
      denseBivariateEval k5P44Section0Dense x y = 0)
    (hcurve :
      denseBivariateEval k5P44CurveDense x y = 0) :
    denseIntEval k5P44Resultant0 x = 0 := by
  have hresultantDense :=
    denseBivariate_elimination_eval_zero
      k5P44EliminationIdentity0 hsection hcurve
  simpa [denseBivariateEval] using hresultantDense

theorem k5P44Section0Dense_eval_eq_sparse
    (n d : ℕ) :
    denseBivariateEval k5P44Section0Dense
        (n : ℤ) ((n + d : ℕ) : ℤ) =
      sparseBivariateEval k5P44Section0 n (n + d) := by
  calc
    denseBivariateEval k5P44Section0Dense
        (n : ℤ) ((n + d : ℕ) : ℤ) =
        sparseBivariateEval
          (denseBivariateToSparse k5P44Section0Dense)
          n (n + d) :=
      (denseBivariateToSparse_eval _ _ _).symm
    _ = sparseBivariateEval k5P44Section0 n (n + d) := by
      rw [k5P44Section0Dense_toSparse]

theorem k5P44Section1Dense_toSparse :
    denseBivariateToSparse k5P44Section1Dense =
      k5P44Section1 := by
  decide +kernel

theorem k5P44Resultant1_eval_eq_zero
    {x y : ℤ}
    (hsection :
      denseBivariateEval k5P44Section1Dense x y = 0)
    (hcurve :
      denseBivariateEval k5P44CurveDense x y = 0) :
    denseIntEval k5P44Resultant1 x = 0 := by
  have hresultantDense :=
    denseBivariate_elimination_eval_zero
      k5P44EliminationIdentity1 hsection hcurve
  simpa [denseBivariateEval] using hresultantDense

theorem k5P44Section1Dense_eval_eq_sparse
    (n d : ℕ) :
    denseBivariateEval k5P44Section1Dense
        (n : ℤ) ((n + d : ℕ) : ℤ) =
      sparseBivariateEval k5P44Section1 n (n + d) := by
  calc
    denseBivariateEval k5P44Section1Dense
        (n : ℤ) ((n + d : ℕ) : ℤ) =
        sparseBivariateEval
          (denseBivariateToSparse k5P44Section1Dense)
          n (n + d) :=
      (denseBivariateToSparse_eval _ _ _).symm
    _ = sparseBivariateEval k5P44Section1 n (n + d) := by
      rw [k5P44Section1Dense_toSparse]

theorem k5P44Expected_scaled_eval_eq_zero
    {x : ℤ}
    (hresultant0 : denseIntEval k5P44Resultant0 x = 0)
    (hresultant1 : denseIntEval k5P44Resultant1 x = 0) :
    denseIntEval
      (denseIntScale k5P44BezoutScale k5P44Expected) x = 0 :=
  denseInt_bezout_eval_zero
    k5P44ResultantBezoutIdentity hresultant0 hresultant1

theorem k5P44CurveDense_eval_eq_sparse
    (n d : ℕ) :
    denseBivariateEval k5P44CurveDense
        (n : ℤ) ((n + d : ℕ) : ℤ) =
      sparseBivariateEval k5CurveTerms n (n + d) := by
  calc
    denseBivariateEval k5P44CurveDense
        (n : ℤ) ((n + d : ℕ) : ℤ) =
        sparseBivariateEval
          (denseBivariateToSparse k5P44CurveDense) n (n + d) :=
      (denseBivariateToSparse_eval _ _ _).symm
    _ = sparseBivariateEval k5CurveTerms n (n + d) := by
      rw [k5P44CurveDense_toSparse]

theorem k5P44Expected_eval_pos
    (n : ℕ) :
    0 < denseIntEval k5P44Expected (n : ℤ) := by
  unfold k5P44Expected
  rw [denseIntMul_eval, denseIntPow_eval,
    denseIntMul_eval, denseIntPow_eval,
    denseIntMul_eval, denseIntPow_eval,
    denseIntMul_eval, denseIntPow_eval,
    denseIntPow_eval]
  norm_num [denseIntEval]
  positivity

theorem k5P44Expected_scaled_eval_ne_zero
    (n : ℕ) :
    denseIntEval
        (denseIntScale k5P44BezoutScale k5P44Expected)
        (n : ℤ) ≠ 0 := by
  rw [denseIntScale_eval]
  exact mul_ne_zero
    (by norm_num [k5P44BezoutScale])
    (ne_of_gt (k5P44Expected_eval_pos n))

end Erdos686Variant
end Erdos686
