/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686K5P42Noncommon

namespace Erdos686
namespace Erdos686Variant

/-! Completed puncture (4,2) endpoint. -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P42_sections_not_both_zero
    {n d : ℕ}
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n) :
    sparseBivariateEval k5P42Section0 n (n + d) ≠ 0 ∨
      sparseBivariateEval k5P42Section1 n (n + d) ≠ 0 := by
  by_contra h
  push Not at h
  have hsection0 :
      denseBivariateEval
        k5P42Section0Dense (n : ℤ) ((n + d : ℕ) : ℤ) = 0 := by
    rw [k5P42Section0Dense_eval_eq_sparse]
    exact h.1
  have hsection1 :
      denseBivariateEval
        k5P42Section1Dense (n : ℤ) ((n + d : ℕ) : ℤ) = 0 := by
    rw [k5P42Section1Dense_eval_eq_sparse]
    exact h.2
  have hcurve :
      denseBivariateEval
        k5P42CurveDense (n : ℤ) ((n + d : ℕ) : ℤ) = 0 := by
    rw [k5P42CurveDense_eval_eq_sparse]
    exact k5CurveTerms_eval_eq_zero heq
  have hresultant0 :
      denseIntEval k5P42Resultant0 (n : ℤ) = 0 :=
    k5P42Resultant0_eval_eq_zero hsection0 hcurve
  have hresultant1 :
      denseIntEval k5P42Resultant1 (n : ℤ) = 0 :=
    k5P42Resultant1_eval_eq_zero hsection1 hcurve
  have htarget :=
    k5P42Expected_scaled_eval_eq_zero hresultant0 hresultant1
  exact k5P42Expected_scaled_eval_ne_zero n htarget

theorem exists_k5P42PunctureJetWitness
    {n d t : ℕ}
    (data : CanonicalOwnerData 5 n d t)
    (hfour : 4 ∣ n + d + t)
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n) :
    Nonempty (K5PunctureJetWitness data 4 2) := by
  rcases k5P42_sections_not_both_zero heq with
      hsection | hsection
  · exact ⟨{
      value :=
        (sparseBivariateEval k5P42Section0 n (n + d)).natAbs
      value_pos := Int.natAbs_pos.mpr hsection
      local_dvd :=
        k5P42Section0_local_dvd data hfour heq
      value_bound :=
        k5_section_natAbs_bound heq
          k5P42Section0_degreeAtMost k5P42Section0_l1_le
    }⟩
  · exact ⟨{
      value :=
        (sparseBivariateEval k5P42Section1 n (n + d)).natAbs
      value_pos := Int.natAbs_pos.mpr hsection
      local_dvd :=
        k5P42Section1_local_dvd data hfour heq
      value_bound :=
        k5_section_natAbs_bound heq
          k5P42Section1_degreeAtMost k5P42Section1_l1_le
    }⟩

end Erdos686Variant
end Erdos686
