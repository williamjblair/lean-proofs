/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686K5P33NoncommonData
import ErdosProblems.Erdos686K5P33Elimination0Rows
import ErdosProblems.Erdos686K5P33Elimination1Rows
import ErdosProblems.Erdos686K5P33Elimination2Rows
import ErdosProblems.Erdos686K5P33Elimination3Rows
import ErdosProblems.Erdos686K5P33Elimination4Rows
import ErdosProblems.Erdos686K5P33BezoutKernel

namespace Erdos686
namespace Erdos686Variant

/-! Kernel-checked five-section non-common-zero certificate. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem k5P33CurveDense_toSparse :
    denseBivariateToSparse k5P33CurveDense = k5CurveTerms := by
  decide +kernel

theorem k5P33Section0Dense_toSparse :
    denseBivariateToSparse k5P33Section0Dense =
      k5P33Section0 := by
  decide +kernel

theorem k5P33Resultant0_eval_eq_zero
    {x y : ℤ}
    (hsection :
      denseBivariateEval k5P33Section0Dense x y = 0)
    (hcurve : denseBivariateEval k5P33CurveDense x y = 0) :
    denseIntEval k5P33Resultant0 x = 0 := by
  have hresultantDense :=
    denseBivariate_elimination_eval_zero
      k5P33EliminationIdentity0 hsection hcurve
  simpa [denseBivariateEval] using hresultantDense

theorem k5P33Section0Dense_eval_eq_sparse
    (n d : ℕ) :
    denseBivariateEval k5P33Section0Dense
        (n : ℤ) ((n + d : ℕ) : ℤ) =
      sparseBivariateEval k5P33Section0 n (n + d) := by
  calc
    denseBivariateEval k5P33Section0Dense
        (n : ℤ) ((n + d : ℕ) : ℤ) =
        sparseBivariateEval
          (denseBivariateToSparse k5P33Section0Dense)
          n (n + d) :=
      (denseBivariateToSparse_eval _ _ _).symm
    _ = sparseBivariateEval k5P33Section0 n (n + d) := by
      rw [k5P33Section0Dense_toSparse]

theorem k5P33Section1Dense_toSparse :
    denseBivariateToSparse k5P33Section1Dense =
      k5P33Section1 := by
  decide +kernel

theorem k5P33Resultant1_eval_eq_zero
    {x y : ℤ}
    (hsection :
      denseBivariateEval k5P33Section1Dense x y = 0)
    (hcurve : denseBivariateEval k5P33CurveDense x y = 0) :
    denseIntEval k5P33Resultant1 x = 0 := by
  have hresultantDense :=
    denseBivariate_elimination_eval_zero
      k5P33EliminationIdentity1 hsection hcurve
  simpa [denseBivariateEval] using hresultantDense

theorem k5P33Section1Dense_eval_eq_sparse
    (n d : ℕ) :
    denseBivariateEval k5P33Section1Dense
        (n : ℤ) ((n + d : ℕ) : ℤ) =
      sparseBivariateEval k5P33Section1 n (n + d) := by
  calc
    denseBivariateEval k5P33Section1Dense
        (n : ℤ) ((n + d : ℕ) : ℤ) =
        sparseBivariateEval
          (denseBivariateToSparse k5P33Section1Dense)
          n (n + d) :=
      (denseBivariateToSparse_eval _ _ _).symm
    _ = sparseBivariateEval k5P33Section1 n (n + d) := by
      rw [k5P33Section1Dense_toSparse]

theorem k5P33Section2Dense_toSparse :
    denseBivariateToSparse k5P33Section2Dense =
      k5P33Section2 := by
  decide +kernel

theorem k5P33Resultant2_eval_eq_zero
    {x y : ℤ}
    (hsection :
      denseBivariateEval k5P33Section2Dense x y = 0)
    (hcurve : denseBivariateEval k5P33CurveDense x y = 0) :
    denseIntEval k5P33Resultant2 x = 0 := by
  have hresultantDense :=
    denseBivariate_elimination_eval_zero
      k5P33EliminationIdentity2 hsection hcurve
  simpa [denseBivariateEval] using hresultantDense

theorem k5P33Section2Dense_eval_eq_sparse
    (n d : ℕ) :
    denseBivariateEval k5P33Section2Dense
        (n : ℤ) ((n + d : ℕ) : ℤ) =
      sparseBivariateEval k5P33Section2 n (n + d) := by
  calc
    denseBivariateEval k5P33Section2Dense
        (n : ℤ) ((n + d : ℕ) : ℤ) =
        sparseBivariateEval
          (denseBivariateToSparse k5P33Section2Dense)
          n (n + d) :=
      (denseBivariateToSparse_eval _ _ _).symm
    _ = sparseBivariateEval k5P33Section2 n (n + d) := by
      rw [k5P33Section2Dense_toSparse]

theorem k5P33Section3Dense_toSparse :
    denseBivariateToSparse k5P33Section3Dense =
      k5P33Section3 := by
  decide +kernel

theorem k5P33Resultant3_eval_eq_zero
    {x y : ℤ}
    (hsection :
      denseBivariateEval k5P33Section3Dense x y = 0)
    (hcurve : denseBivariateEval k5P33CurveDense x y = 0) :
    denseIntEval k5P33Resultant3 x = 0 := by
  have hresultantDense :=
    denseBivariate_elimination_eval_zero
      k5P33EliminationIdentity3 hsection hcurve
  simpa [denseBivariateEval] using hresultantDense

theorem k5P33Section3Dense_eval_eq_sparse
    (n d : ℕ) :
    denseBivariateEval k5P33Section3Dense
        (n : ℤ) ((n + d : ℕ) : ℤ) =
      sparseBivariateEval k5P33Section3 n (n + d) := by
  calc
    denseBivariateEval k5P33Section3Dense
        (n : ℤ) ((n + d : ℕ) : ℤ) =
        sparseBivariateEval
          (denseBivariateToSparse k5P33Section3Dense)
          n (n + d) :=
      (denseBivariateToSparse_eval _ _ _).symm
    _ = sparseBivariateEval k5P33Section3 n (n + d) := by
      rw [k5P33Section3Dense_toSparse]

theorem k5P33Section4Dense_toSparse :
    denseBivariateToSparse k5P33Section4Dense =
      k5P33Section4 := by
  decide +kernel

theorem k5P33Resultant4_eval_eq_zero
    {x y : ℤ}
    (hsection :
      denseBivariateEval k5P33Section4Dense x y = 0)
    (hcurve : denseBivariateEval k5P33CurveDense x y = 0) :
    denseIntEval k5P33Resultant4 x = 0 := by
  have hresultantDense :=
    denseBivariate_elimination_eval_zero
      k5P33EliminationIdentity4 hsection hcurve
  simpa [denseBivariateEval] using hresultantDense

theorem k5P33Section4Dense_eval_eq_sparse
    (n d : ℕ) :
    denseBivariateEval k5P33Section4Dense
        (n : ℤ) ((n + d : ℕ) : ℤ) =
      sparseBivariateEval k5P33Section4 n (n + d) := by
  calc
    denseBivariateEval k5P33Section4Dense
        (n : ℤ) ((n + d : ℕ) : ℤ) =
        sparseBivariateEval
          (denseBivariateToSparse k5P33Section4Dense)
          n (n + d) :=
      (denseBivariateToSparse_eval _ _ _).symm
    _ = sparseBivariateEval k5P33Section4 n (n + d) := by
      rw [k5P33Section4Dense_toSparse]

theorem k5P33Expected_scaled_eval_eq_zero
    {x : ℤ}
    (hresultant0 : denseIntEval k5P33Resultant0 x = 0)
    (hresultant1 : denseIntEval k5P33Resultant1 x = 0)
    (hresultant2 : denseIntEval k5P33Resultant2 x = 0)
    (hresultant3 : denseIntEval k5P33Resultant3 x = 0)
    (hresultant4 : denseIntEval k5P33Resultant4 x = 0) :
    denseIntEval
      (denseIntScale k5P33BezoutScale k5P33Expected) x = 0 := by
  have hid :=
    denseInt_identity_eval k5P33ResultantBezoutIdentity x
  simp only [denseIntAdd_eval, denseIntMul_eval,
    hresultant0, hresultant1, hresultant2, hresultant3,
    hresultant4, mul_zero, zero_mul, add_zero, zero_add] at hid
  exact hid.symm

theorem k5P33CurveDense_eval_eq_sparse
    (n d : ℕ) :
    denseBivariateEval k5P33CurveDense
        (n : ℤ) ((n + d : ℕ) : ℤ) =
      sparseBivariateEval k5CurveTerms n (n + d) := by
  calc
    denseBivariateEval k5P33CurveDense
        (n : ℤ) ((n + d : ℕ) : ℤ) =
        sparseBivariateEval
          (denseBivariateToSparse k5P33CurveDense) n (n + d) :=
      (denseBivariateToSparse_eval _ _ _).symm
    _ = sparseBivariateEval k5CurveTerms n (n + d) := by
      rw [k5P33CurveDense_toSparse]

theorem k5P33Expected_eval_pos
    (n : ℕ) :
    0 < denseIntEval k5P33Expected (n : ℤ) := by
  unfold k5P33Expected
  rw [denseIntMul_eval, denseIntPow_eval,
    denseIntMul_eval, denseIntPow_eval,
    denseIntMul_eval, denseIntPow_eval,
    denseIntMul_eval, denseIntPow_eval,
    denseIntPow_eval]
  norm_num [denseIntEval]
  positivity

theorem k5P33Expected_scaled_eval_ne_zero
    (n : ℕ) :
    denseIntEval
        (denseIntScale k5P33BezoutScale k5P33Expected)
        (n : ℤ) ≠ 0 := by
  rw [denseIntScale_eval]
  exact mul_ne_zero
    (by norm_num [k5P33BezoutScale])
    (ne_of_gt (k5P33Expected_eval_pos n))

end Erdos686Variant
end Erdos686
