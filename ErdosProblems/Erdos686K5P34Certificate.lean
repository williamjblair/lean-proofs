/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686K5P34CertificateData
import ErdosProblems.Erdos686K5P34S0J1I1Rows
import ErdosProblems.Erdos686K5P34S0J1I2Rows
import ErdosProblems.Erdos686K5P34S0J1I3Rows
import ErdosProblems.Erdos686K5P34S0J1I4Rows
import ErdosProblems.Erdos686K5P34S0J1I5Rows
import ErdosProblems.Erdos686K5P34S0J2I1Rows
import ErdosProblems.Erdos686K5P34S0J2I2Rows
import ErdosProblems.Erdos686K5P34S0J2I3Rows
import ErdosProblems.Erdos686K5P34S0J2I4Rows
import ErdosProblems.Erdos686K5P34S0J2I5Rows
import ErdosProblems.Erdos686K5P34S0J3I1Rows
import ErdosProblems.Erdos686K5P34S0J3I2Rows
import ErdosProblems.Erdos686K5P34S0J3I3Rows
import ErdosProblems.Erdos686K5P34S0J3I5Rows
import ErdosProblems.Erdos686K5P34S0J4I1Rows
import ErdosProblems.Erdos686K5P34S0J4I2Rows
import ErdosProblems.Erdos686K5P34S0J4I3Rows
import ErdosProblems.Erdos686K5P34S0J4I4Rows
import ErdosProblems.Erdos686K5P34S0J4I5Rows
import ErdosProblems.Erdos686K5P34S0J5I1Rows
import ErdosProblems.Erdos686K5P34S0J5I2Rows
import ErdosProblems.Erdos686K5P34S0J5I3Rows
import ErdosProblems.Erdos686K5P34S0J5I4Rows
import ErdosProblems.Erdos686K5P34S0J5I5Rows
import ErdosProblems.Erdos686K5P34S1J1I1Rows
import ErdosProblems.Erdos686K5P34S1J1I2Rows
import ErdosProblems.Erdos686K5P34S1J1I3Rows
import ErdosProblems.Erdos686K5P34S1J1I4Rows
import ErdosProblems.Erdos686K5P34S1J1I5Rows
import ErdosProblems.Erdos686K5P34S1J2I1Rows
import ErdosProblems.Erdos686K5P34S1J2I2Rows
import ErdosProblems.Erdos686K5P34S1J2I3Rows
import ErdosProblems.Erdos686K5P34S1J2I4Rows
import ErdosProblems.Erdos686K5P34S1J2I5Rows
import ErdosProblems.Erdos686K5P34S1J3I1Rows
import ErdosProblems.Erdos686K5P34S1J3I2Rows
import ErdosProblems.Erdos686K5P34S1J3I3Rows
import ErdosProblems.Erdos686K5P34S1J3I5Rows
import ErdosProblems.Erdos686K5P34S1J4I1Rows
import ErdosProblems.Erdos686K5P34S1J4I2Rows
import ErdosProblems.Erdos686K5P34S1J4I3Rows
import ErdosProblems.Erdos686K5P34S1J4I4Rows
import ErdosProblems.Erdos686K5P34S1J4I5Rows
import ErdosProblems.Erdos686K5P34S1J5I1Rows
import ErdosProblems.Erdos686K5P34S1J5I2Rows
import ErdosProblems.Erdos686K5P34S1J5I3Rows
import ErdosProblems.Erdos686K5P34S1J5I4Rows
import ErdosProblems.Erdos686K5P34S1J5I5Rows

namespace Erdos686
namespace Erdos686Variant

/-! Kernel-checked row assembly for the k=5 puncture (3,4). -/

theorem k5P34Section0_degreeAtMost :
    sparseBivariateDegreeAtMost 84 k5P34Section0 :=
  sparseDegreeAtMost_of_decidable (by
    unfold sparseDecidableDegreeAtMost
    decide +kernel)

theorem k5P34Section0_l1_le :
    sparseBivariateL1Norm k5P34Section0 ≤
      k5PunctureCoefficientNorm := by
  decide +kernel

theorem k5P34Section0_local_dvd
    {n d t : ℕ}
    (data : CanonicalOwnerData 5 n d t)
    (hfour : 4 ∣ n + d + t)
    (heq : blockProduct 5 (n + d) =
      4 * blockProduct 5 n) :
    ∀ j ∈ Finset.Icc 1 5, ∀ i ∈ Finset.Icc 1 5,
      (j, i) ≠ (3, 4) →
        canonicalOwnerCell data j i ^ 17 ∣
          (sparseBivariateEval k5P34Section0
            n (n + d)).natAbs := by
  intro j hj i hi hne
  have hx := canonicalOwnerCell_dvd_lower
    data (j := j) (i := i)
  have hy : canonicalOwnerCell data j i ∣
      n + d + i :=
    dvd_trans
      (canonicalOwnerCell_dvd_upper
        data (j := j) (i := i))
      (upperTermAfterFour_dvd_original hfour)
  rcases Finset.mem_Icc.mp hj with ⟨hjlow, hjhigh⟩
  rcases Finset.mem_Icc.mp hi with ⟨hilow, hihigh⟩
  interval_cases j <;> interval_cases i
  · exact
      k5_direct_rows_certificate_pow_dvd_section_natAbs
        heq hx hy k5P34Section0_taylorRows_J1_I1
  · exact
      k5_direct_rows_certificate_pow_dvd_section_natAbs
        heq hx hy k5P34Section0_taylorRows_J1_I2
  · exact
      k5_direct_rows_certificate_pow_dvd_section_natAbs
        heq hx hy k5P34Section0_taylorRows_J1_I3
  · exact
      k5_direct_rows_certificate_pow_dvd_section_natAbs
        heq hx hy k5P34Section0_taylorRows_J1_I4
  · exact
      k5_direct_rows_certificate_pow_dvd_section_natAbs
        heq hx hy k5P34Section0_taylorRows_J1_I5
  · exact
      k5_direct_rows_certificate_pow_dvd_section_natAbs
        heq hx hy k5P34Section0_taylorRows_J2_I1
  · exact
      k5_direct_rows_certificate_pow_dvd_section_natAbs
        heq hx hy k5P34Section0_taylorRows_J2_I2
  · exact
      k5_direct_rows_certificate_pow_dvd_section_natAbs
        heq hx hy k5P34Section0_taylorRows_J2_I3
  · exact
      k5_direct_rows_certificate_pow_dvd_section_natAbs
        heq hx hy k5P34Section0_taylorRows_J2_I4
  · exact
      k5_direct_rows_certificate_pow_dvd_section_natAbs
        heq hx hy k5P34Section0_taylorRows_J2_I5
  · exact
      k5_direct_rows_certificate_pow_dvd_section_natAbs
        heq hx hy k5P34Section0_taylorRows_J3_I1
  · exact
      k5_direct_rows_certificate_pow_dvd_section_natAbs
        heq hx hy k5P34Section0_taylorRows_J3_I2
  · exact
      k5_direct_rows_certificate_pow_dvd_section_natAbs
        heq hx hy k5P34Section0_taylorRows_J3_I3
  · exact (hne rfl).elim
  · exact
      k5_direct_rows_certificate_pow_dvd_section_natAbs
        heq hx hy k5P34Section0_taylorRows_J3_I5
  · exact
      k5_direct_rows_certificate_pow_dvd_section_natAbs
        heq hx hy k5P34Section0_taylorRows_J4_I1
  · exact
      k5_direct_rows_certificate_pow_dvd_section_natAbs
        heq hx hy k5P34Section0_taylorRows_J4_I2
  · exact
      k5_direct_rows_certificate_pow_dvd_section_natAbs
        heq hx hy k5P34Section0_taylorRows_J4_I3
  · exact
      k5_direct_rows_certificate_pow_dvd_section_natAbs
        heq hx hy k5P34Section0_taylorRows_J4_I4
  · exact
      k5_direct_rows_certificate_pow_dvd_section_natAbs
        heq hx hy k5P34Section0_taylorRows_J4_I5
  · exact
      k5_direct_rows_certificate_pow_dvd_section_natAbs
        heq hx hy k5P34Section0_taylorRows_J5_I1
  · exact
      k5_direct_rows_certificate_pow_dvd_section_natAbs
        heq hx hy k5P34Section0_taylorRows_J5_I2
  · exact
      k5_direct_rows_certificate_pow_dvd_section_natAbs
        heq hx hy k5P34Section0_taylorRows_J5_I3
  · exact
      k5_direct_rows_certificate_pow_dvd_section_natAbs
        heq hx hy k5P34Section0_taylorRows_J5_I4
  · exact
      k5_direct_rows_certificate_pow_dvd_section_natAbs
        heq hx hy k5P34Section0_taylorRows_J5_I5

theorem k5P34Section1_degreeAtMost :
    sparseBivariateDegreeAtMost 84 k5P34Section1 :=
  sparseDegreeAtMost_of_decidable (by
    unfold sparseDecidableDegreeAtMost
    decide +kernel)

theorem k5P34Section1_l1_le :
    sparseBivariateL1Norm k5P34Section1 ≤
      k5PunctureCoefficientNorm := by
  decide +kernel

theorem k5P34Section1_local_dvd
    {n d t : ℕ}
    (data : CanonicalOwnerData 5 n d t)
    (hfour : 4 ∣ n + d + t)
    (heq : blockProduct 5 (n + d) =
      4 * blockProduct 5 n) :
    ∀ j ∈ Finset.Icc 1 5, ∀ i ∈ Finset.Icc 1 5,
      (j, i) ≠ (3, 4) →
        canonicalOwnerCell data j i ^ 17 ∣
          (sparseBivariateEval k5P34Section1
            n (n + d)).natAbs := by
  intro j hj i hi hne
  have hx := canonicalOwnerCell_dvd_lower
    data (j := j) (i := i)
  have hy : canonicalOwnerCell data j i ∣
      n + d + i :=
    dvd_trans
      (canonicalOwnerCell_dvd_upper
        data (j := j) (i := i))
      (upperTermAfterFour_dvd_original hfour)
  rcases Finset.mem_Icc.mp hj with ⟨hjlow, hjhigh⟩
  rcases Finset.mem_Icc.mp hi with ⟨hilow, hihigh⟩
  interval_cases j <;> interval_cases i
  · exact
      k5_direct_rows_certificate_pow_dvd_section_natAbs
        heq hx hy k5P34Section1_taylorRows_J1_I1
  · exact
      k5_direct_rows_certificate_pow_dvd_section_natAbs
        heq hx hy k5P34Section1_taylorRows_J1_I2
  · exact
      k5_direct_rows_certificate_pow_dvd_section_natAbs
        heq hx hy k5P34Section1_taylorRows_J1_I3
  · exact
      k5_direct_rows_certificate_pow_dvd_section_natAbs
        heq hx hy k5P34Section1_taylorRows_J1_I4
  · exact
      k5_direct_rows_certificate_pow_dvd_section_natAbs
        heq hx hy k5P34Section1_taylorRows_J1_I5
  · exact
      k5_direct_rows_certificate_pow_dvd_section_natAbs
        heq hx hy k5P34Section1_taylorRows_J2_I1
  · exact
      k5_direct_rows_certificate_pow_dvd_section_natAbs
        heq hx hy k5P34Section1_taylorRows_J2_I2
  · exact
      k5_direct_rows_certificate_pow_dvd_section_natAbs
        heq hx hy k5P34Section1_taylorRows_J2_I3
  · exact
      k5_direct_rows_certificate_pow_dvd_section_natAbs
        heq hx hy k5P34Section1_taylorRows_J2_I4
  · exact
      k5_direct_rows_certificate_pow_dvd_section_natAbs
        heq hx hy k5P34Section1_taylorRows_J2_I5
  · exact
      k5_direct_rows_certificate_pow_dvd_section_natAbs
        heq hx hy k5P34Section1_taylorRows_J3_I1
  · exact
      k5_direct_rows_certificate_pow_dvd_section_natAbs
        heq hx hy k5P34Section1_taylorRows_J3_I2
  · exact
      k5_direct_rows_certificate_pow_dvd_section_natAbs
        heq hx hy k5P34Section1_taylorRows_J3_I3
  · exact (hne rfl).elim
  · exact
      k5_direct_rows_certificate_pow_dvd_section_natAbs
        heq hx hy k5P34Section1_taylorRows_J3_I5
  · exact
      k5_direct_rows_certificate_pow_dvd_section_natAbs
        heq hx hy k5P34Section1_taylorRows_J4_I1
  · exact
      k5_direct_rows_certificate_pow_dvd_section_natAbs
        heq hx hy k5P34Section1_taylorRows_J4_I2
  · exact
      k5_direct_rows_certificate_pow_dvd_section_natAbs
        heq hx hy k5P34Section1_taylorRows_J4_I3
  · exact
      k5_direct_rows_certificate_pow_dvd_section_natAbs
        heq hx hy k5P34Section1_taylorRows_J4_I4
  · exact
      k5_direct_rows_certificate_pow_dvd_section_natAbs
        heq hx hy k5P34Section1_taylorRows_J4_I5
  · exact
      k5_direct_rows_certificate_pow_dvd_section_natAbs
        heq hx hy k5P34Section1_taylorRows_J5_I1
  · exact
      k5_direct_rows_certificate_pow_dvd_section_natAbs
        heq hx hy k5P34Section1_taylorRows_J5_I2
  · exact
      k5_direct_rows_certificate_pow_dvd_section_natAbs
        heq hx hy k5P34Section1_taylorRows_J5_I3
  · exact
      k5_direct_rows_certificate_pow_dvd_section_natAbs
        heq hx hy k5P34Section1_taylorRows_J5_I4
  · exact
      k5_direct_rows_certificate_pow_dvd_section_natAbs
        heq hx hy k5P34Section1_taylorRows_J5_I5

end Erdos686Variant
end Erdos686
