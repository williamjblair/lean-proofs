/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686K5P33CertificateData

namespace Erdos686
namespace Erdos686Variant

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P33Section3_taylorRow0_J3_I1 :
    sparseLocalTaylorRowCheck 17 0
      k5P33Section3 k5P33Section3QJ3I1 k5CurveTerms
        (-3) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P33Section3_taylorRow1_J3_I1 :
    sparseLocalTaylorRowCheck 17 1
      k5P33Section3 k5P33Section3QJ3I1 k5CurveTerms
        (-3) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P33Section3_taylorRow2_J3_I1 :
    sparseLocalTaylorRowCheck 17 2
      k5P33Section3 k5P33Section3QJ3I1 k5CurveTerms
        (-3) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P33Section3_taylorRow3_J3_I1 :
    sparseLocalTaylorRowCheck 17 3
      k5P33Section3 k5P33Section3QJ3I1 k5CurveTerms
        (-3) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P33Section3_taylorRow4_J3_I1 :
    sparseLocalTaylorRowCheck 17 4
      k5P33Section3 k5P33Section3QJ3I1 k5CurveTerms
        (-3) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P33Section3_taylorRow5_J3_I1 :
    sparseLocalTaylorRowCheck 17 5
      k5P33Section3 k5P33Section3QJ3I1 k5CurveTerms
        (-3) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P33Section3_taylorRow6_J3_I1 :
    sparseLocalTaylorRowCheck 17 6
      k5P33Section3 k5P33Section3QJ3I1 k5CurveTerms
        (-3) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P33Section3_taylorRow7_J3_I1 :
    sparseLocalTaylorRowCheck 17 7
      k5P33Section3 k5P33Section3QJ3I1 k5CurveTerms
        (-3) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P33Section3_taylorRow8_J3_I1 :
    sparseLocalTaylorRowCheck 17 8
      k5P33Section3 k5P33Section3QJ3I1 k5CurveTerms
        (-3) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P33Section3_taylorRow9_J3_I1 :
    sparseLocalTaylorRowCheck 17 9
      k5P33Section3 k5P33Section3QJ3I1 k5CurveTerms
        (-3) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P33Section3_taylorRow10_J3_I1 :
    sparseLocalTaylorRowCheck 17 10
      k5P33Section3 k5P33Section3QJ3I1 k5CurveTerms
        (-3) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P33Section3_taylorRow11_J3_I1 :
    sparseLocalTaylorRowCheck 17 11
      k5P33Section3 k5P33Section3QJ3I1 k5CurveTerms
        (-3) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P33Section3_taylorRow12_J3_I1 :
    sparseLocalTaylorRowCheck 17 12
      k5P33Section3 k5P33Section3QJ3I1 k5CurveTerms
        (-3) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P33Section3_taylorRow13_J3_I1 :
    sparseLocalTaylorRowCheck 17 13
      k5P33Section3 k5P33Section3QJ3I1 k5CurveTerms
        (-3) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P33Section3_taylorRow14_J3_I1 :
    sparseLocalTaylorRowCheck 17 14
      k5P33Section3 k5P33Section3QJ3I1 k5CurveTerms
        (-3) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P33Section3_taylorRow15_J3_I1 :
    sparseLocalTaylorRowCheck 17 15
      k5P33Section3 k5P33Section3QJ3I1 k5CurveTerms
        (-3) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P33Section3_taylorRow16_J3_I1 :
    sparseLocalTaylorRowCheck 17 16
      k5P33Section3 k5P33Section3QJ3I1 k5CurveTerms
        (-3) (-1) = true := by
  decide +kernel

theorem k5P33Section3_taylorRows_J3_I1 :
    SparseLocalTaylorRowsCertificate 17
      k5P33Section3 k5P33Section3QJ3I1 k5CurveTerms
        (-3) (-1) := by
  intro a ha
  interval_cases a
  · exact k5P33Section3_taylorRow0_J3_I1
  · exact k5P33Section3_taylorRow1_J3_I1
  · exact k5P33Section3_taylorRow2_J3_I1
  · exact k5P33Section3_taylorRow3_J3_I1
  · exact k5P33Section3_taylorRow4_J3_I1
  · exact k5P33Section3_taylorRow5_J3_I1
  · exact k5P33Section3_taylorRow6_J3_I1
  · exact k5P33Section3_taylorRow7_J3_I1
  · exact k5P33Section3_taylorRow8_J3_I1
  · exact k5P33Section3_taylorRow9_J3_I1
  · exact k5P33Section3_taylorRow10_J3_I1
  · exact k5P33Section3_taylorRow11_J3_I1
  · exact k5P33Section3_taylorRow12_J3_I1
  · exact k5P33Section3_taylorRow13_J3_I1
  · exact k5P33Section3_taylorRow14_J3_I1
  · exact k5P33Section3_taylorRow15_J3_I1
  · exact k5P33Section3_taylorRow16_J3_I1

end Erdos686Variant
end Erdos686
