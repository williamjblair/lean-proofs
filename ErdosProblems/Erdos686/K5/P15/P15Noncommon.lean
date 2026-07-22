/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.K5.P15.P15NoncommonData
import ErdosProblems.Erdos686.K5.P15.P15Elimination0Rows
import ErdosProblems.Erdos686.K5.P15.P15Elimination1Rows
import ErdosProblems.Erdos686.K5.P15.P15BezoutKernel

namespace Erdos686
namespace Erdos686Variant

/-! Kernel-checked non-common-zero certificate. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem k5P15CurveDense_toSparse :
    denseBivariateToSparse k5P15CurveDense = k5CurveTerms := by
  decide +kernel

theorem k5P15Section0Dense_toSparse :
    denseBivariateToSparse k5P15Section0Dense =
      k5P15Section0 := by
  decide +kernel

theorem k5P15Resultant0_eval_eq_zero
    {x y : ℤ}
    (hsection :
      denseBivariateEval k5P15Section0Dense x y = 0)
    (hcurve :
      denseBivariateEval k5P15CurveDense x y = 0) :
    denseIntEval k5P15Resultant0 x = 0 := by
  have hresultantDense :=
    denseBivariate_elimination_eval_zero
      k5P15EliminationIdentity0 hsection hcurve
  simpa [denseBivariateEval] using hresultantDense

theorem k5P15Section0Dense_eval_eq_sparse
    (n d : ℕ) :
    denseBivariateEval k5P15Section0Dense
        (n : ℤ) ((n + d : ℕ) : ℤ) =
      sparseBivariateEval k5P15Section0 n (n + d) := by
  calc
    denseBivariateEval k5P15Section0Dense
        (n : ℤ) ((n + d : ℕ) : ℤ) =
        sparseBivariateEval
          (denseBivariateToSparse k5P15Section0Dense)
          n (n + d) :=
      (denseBivariateToSparse_eval _ _ _).symm
    _ = sparseBivariateEval k5P15Section0 n (n + d) := by
      rw [k5P15Section0Dense_toSparse]

theorem k5P15Section1Dense_toSparse :
    denseBivariateToSparse k5P15Section1Dense =
      k5P15Section1 := by
  decide +kernel

theorem k5P15Resultant1_eval_eq_zero
    {x y : ℤ}
    (hsection :
      denseBivariateEval k5P15Section1Dense x y = 0)
    (hcurve :
      denseBivariateEval k5P15CurveDense x y = 0) :
    denseIntEval k5P15Resultant1 x = 0 := by
  have hresultantDense :=
    denseBivariate_elimination_eval_zero
      k5P15EliminationIdentity1 hsection hcurve
  simpa [denseBivariateEval] using hresultantDense

theorem k5P15Section1Dense_eval_eq_sparse
    (n d : ℕ) :
    denseBivariateEval k5P15Section1Dense
        (n : ℤ) ((n + d : ℕ) : ℤ) =
      sparseBivariateEval k5P15Section1 n (n + d) := by
  calc
    denseBivariateEval k5P15Section1Dense
        (n : ℤ) ((n + d : ℕ) : ℤ) =
        sparseBivariateEval
          (denseBivariateToSparse k5P15Section1Dense)
          n (n + d) :=
      (denseBivariateToSparse_eval _ _ _).symm
    _ = sparseBivariateEval k5P15Section1 n (n + d) := by
      rw [k5P15Section1Dense_toSparse]

theorem k5P15Expected_scaled_eval_eq_zero
    {x : ℤ}
    (hresultant0 : denseIntEval k5P15Resultant0 x = 0)
    (hresultant1 : denseIntEval k5P15Resultant1 x = 0) :
    denseIntEval
      (denseIntScale k5P15BezoutScale k5P15Expected) x = 0 :=
  denseInt_bezout_eval_zero
    k5P15ResultantBezoutIdentity hresultant0 hresultant1

theorem k5P15CurveDense_eval_eq_sparse
    (n d : ℕ) :
    denseBivariateEval k5P15CurveDense
        (n : ℤ) ((n + d : ℕ) : ℤ) =
      sparseBivariateEval k5CurveTerms n (n + d) := by
  calc
    denseBivariateEval k5P15CurveDense
        (n : ℤ) ((n + d : ℕ) : ℤ) =
        sparseBivariateEval
          (denseBivariateToSparse k5P15CurveDense) n (n + d) :=
      (denseBivariateToSparse_eval _ _ _).symm
    _ = sparseBivariateEval k5CurveTerms n (n + d) := by
      rw [k5P15CurveDense_toSparse]

theorem k5P15Expected_eval_pos
    (n : ℕ) :
    0 < denseIntEval k5P15Expected (n : ℤ) := by
  unfold k5P15Expected
  rw [denseIntMul_eval, denseIntPow_eval,
    denseIntMul_eval, denseIntPow_eval,
    denseIntMul_eval, denseIntPow_eval,
    denseIntMul_eval, denseIntPow_eval,
    denseIntPow_eval]
  norm_num [denseIntEval]
  positivity

theorem k5P15Expected_scaled_eval_ne_zero
    (n : ℕ) :
    denseIntEval
        (denseIntScale k5P15BezoutScale k5P15Expected)
        (n : ℤ) ≠ 0 := by
  rw [denseIntScale_eval]
  exact mul_ne_zero
    (by norm_num [k5P15BezoutScale])
    (ne_of_gt (k5P15Expected_eval_pos n))

end Erdos686Variant
end Erdos686
