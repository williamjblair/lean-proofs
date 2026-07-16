/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686K5P33Noncommon

namespace Erdos686
namespace Erdos686Variant

/-! Completed central puncture endpoint. -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P33_sections_not_all_zero
    {n d : ℕ}
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n) :
    sparseBivariateEval k5P33Section0 n (n + d) ≠ 0 ∨
      sparseBivariateEval k5P33Section1 n (n + d) ≠ 0 ∨
      sparseBivariateEval k5P33Section2 n (n + d) ≠ 0 ∨
      sparseBivariateEval k5P33Section3 n (n + d) ≠ 0 ∨
      sparseBivariateEval k5P33Section4 n (n + d) ≠ 0 := by
  by_contra h
  push Not at h
  have hsection0 :
      denseBivariateEval k5P33Section0Dense
          (n : ℤ) ((n + d : ℕ) : ℤ) = 0 := by
    rw [k5P33Section0Dense_eval_eq_sparse]
    exact h.1
  have hsection1 :
      denseBivariateEval k5P33Section1Dense
          (n : ℤ) ((n + d : ℕ) : ℤ) = 0 := by
    rw [k5P33Section1Dense_eval_eq_sparse]
    exact h.2.1
  have hsection2 :
      denseBivariateEval k5P33Section2Dense
          (n : ℤ) ((n + d : ℕ) : ℤ) = 0 := by
    rw [k5P33Section2Dense_eval_eq_sparse]
    exact h.2.2.1
  have hsection3 :
      denseBivariateEval k5P33Section3Dense
          (n : ℤ) ((n + d : ℕ) : ℤ) = 0 := by
    rw [k5P33Section3Dense_eval_eq_sparse]
    exact h.2.2.2.1
  have hsection4 :
      denseBivariateEval k5P33Section4Dense
          (n : ℤ) ((n + d : ℕ) : ℤ) = 0 := by
    rw [k5P33Section4Dense_eval_eq_sparse]
    exact h.2.2.2.2
  have hcurve :
      denseBivariateEval k5P33CurveDense
          (n : ℤ) ((n + d : ℕ) : ℤ) = 0 := by
    rw [k5P33CurveDense_eval_eq_sparse]
    exact k5CurveTerms_eval_eq_zero heq
  have hresultant0 :
      denseIntEval k5P33Resultant0 (n : ℤ) = 0 :=
    k5P33Resultant0_eval_eq_zero hsection0 hcurve
  have hresultant1 :
      denseIntEval k5P33Resultant1 (n : ℤ) = 0 :=
    k5P33Resultant1_eval_eq_zero hsection1 hcurve
  have hresultant2 :
      denseIntEval k5P33Resultant2 (n : ℤ) = 0 :=
    k5P33Resultant2_eval_eq_zero hsection2 hcurve
  have hresultant3 :
      denseIntEval k5P33Resultant3 (n : ℤ) = 0 :=
    k5P33Resultant3_eval_eq_zero hsection3 hcurve
  have hresultant4 :
      denseIntEval k5P33Resultant4 (n : ℤ) = 0 :=
    k5P33Resultant4_eval_eq_zero hsection4 hcurve
  have htarget :=
    k5P33Expected_scaled_eval_eq_zero hresultant0 hresultant1 hresultant2 hresultant3 hresultant4
  exact k5P33Expected_scaled_eval_ne_zero n htarget

theorem exists_k5P33PunctureJetWitness
    {n d t : ℕ}
    (data : CanonicalOwnerData 5 n d t)
    (hfour : 4 ∣ n + d + t)
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n) :
    Nonempty (K5PunctureJetWitness data 3 3) := by
  rcases k5P33_sections_not_all_zero heq with
      hsection | hsection | hsection | hsection | hsection
  · exact ⟨{
      value :=
        (sparseBivariateEval k5P33Section0
          n (n + d)).natAbs
      value_pos := Int.natAbs_pos.mpr hsection
      local_dvd :=
        k5P33Section0_local_dvd data hfour heq
      value_bound :=
        k5_section_natAbs_bound heq
          k5P33Section0_degreeAtMost
          k5P33Section0_l1_le
    }⟩
  · exact ⟨{
      value :=
        (sparseBivariateEval k5P33Section1
          n (n + d)).natAbs
      value_pos := Int.natAbs_pos.mpr hsection
      local_dvd :=
        k5P33Section1_local_dvd data hfour heq
      value_bound :=
        k5_section_natAbs_bound heq
          k5P33Section1_degreeAtMost
          k5P33Section1_l1_le
    }⟩
  · exact ⟨{
      value :=
        (sparseBivariateEval k5P33Section2
          n (n + d)).natAbs
      value_pos := Int.natAbs_pos.mpr hsection
      local_dvd :=
        k5P33Section2_local_dvd data hfour heq
      value_bound :=
        k5_section_natAbs_bound heq
          k5P33Section2_degreeAtMost
          k5P33Section2_l1_le
    }⟩
  · exact ⟨{
      value :=
        (sparseBivariateEval k5P33Section3
          n (n + d)).natAbs
      value_pos := Int.natAbs_pos.mpr hsection
      local_dvd :=
        k5P33Section3_local_dvd data hfour heq
      value_bound :=
        k5_section_natAbs_bound heq
          k5P33Section3_degreeAtMost
          k5P33Section3_l1_le
    }⟩
  · exact ⟨{
      value :=
        (sparseBivariateEval k5P33Section4
          n (n + d)).natAbs
      value_pos := Int.natAbs_pos.mpr hsection
      local_dvd :=
        k5P33Section4_local_dvd data hfour heq
      value_bound :=
        k5_section_natAbs_bound heq
          k5P33Section4_degreeAtMost
          k5P33Section4_l1_le
    }⟩

end Erdos686Variant
end Erdos686
