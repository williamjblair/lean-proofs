/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.K5.P42.P42CertificateData

namespace Erdos686
namespace Erdos686Variant

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P42Section1_taylorRow0_J1_I5 :
    sparseLocalTaylorRowCheck 17 0
      k5P42Section1 k5P42Section1QJ1I5 k5CurveTerms
        (-1) (-5) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P42Section1_taylorRow1_J1_I5 :
    sparseLocalTaylorRowCheck 17 1
      k5P42Section1 k5P42Section1QJ1I5 k5CurveTerms
        (-1) (-5) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P42Section1_taylorRow2_J1_I5 :
    sparseLocalTaylorRowCheck 17 2
      k5P42Section1 k5P42Section1QJ1I5 k5CurveTerms
        (-1) (-5) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P42Section1_taylorRow3_J1_I5 :
    sparseLocalTaylorRowCheck 17 3
      k5P42Section1 k5P42Section1QJ1I5 k5CurveTerms
        (-1) (-5) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P42Section1_taylorRow4_J1_I5 :
    sparseLocalTaylorRowCheck 17 4
      k5P42Section1 k5P42Section1QJ1I5 k5CurveTerms
        (-1) (-5) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P42Section1_taylorRow5_J1_I5 :
    sparseLocalTaylorRowCheck 17 5
      k5P42Section1 k5P42Section1QJ1I5 k5CurveTerms
        (-1) (-5) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P42Section1_taylorRow6_J1_I5 :
    sparseLocalTaylorRowCheck 17 6
      k5P42Section1 k5P42Section1QJ1I5 k5CurveTerms
        (-1) (-5) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P42Section1_taylorRow7_J1_I5 :
    sparseLocalTaylorRowCheck 17 7
      k5P42Section1 k5P42Section1QJ1I5 k5CurveTerms
        (-1) (-5) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P42Section1_taylorRow8_J1_I5 :
    sparseLocalTaylorRowCheck 17 8
      k5P42Section1 k5P42Section1QJ1I5 k5CurveTerms
        (-1) (-5) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P42Section1_taylorRow9_J1_I5 :
    sparseLocalTaylorRowCheck 17 9
      k5P42Section1 k5P42Section1QJ1I5 k5CurveTerms
        (-1) (-5) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P42Section1_taylorRow10_J1_I5 :
    sparseLocalTaylorRowCheck 17 10
      k5P42Section1 k5P42Section1QJ1I5 k5CurveTerms
        (-1) (-5) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P42Section1_taylorRow11_J1_I5 :
    sparseLocalTaylorRowCheck 17 11
      k5P42Section1 k5P42Section1QJ1I5 k5CurveTerms
        (-1) (-5) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P42Section1_taylorRow12_J1_I5 :
    sparseLocalTaylorRowCheck 17 12
      k5P42Section1 k5P42Section1QJ1I5 k5CurveTerms
        (-1) (-5) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P42Section1_taylorRow13_J1_I5 :
    sparseLocalTaylorRowCheck 17 13
      k5P42Section1 k5P42Section1QJ1I5 k5CurveTerms
        (-1) (-5) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P42Section1_taylorRow14_J1_I5 :
    sparseLocalTaylorRowCheck 17 14
      k5P42Section1 k5P42Section1QJ1I5 k5CurveTerms
        (-1) (-5) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P42Section1_taylorRow15_J1_I5 :
    sparseLocalTaylorRowCheck 17 15
      k5P42Section1 k5P42Section1QJ1I5 k5CurveTerms
        (-1) (-5) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P42Section1_taylorRow16_J1_I5 :
    sparseLocalTaylorRowCheck 17 16
      k5P42Section1 k5P42Section1QJ1I5 k5CurveTerms
        (-1) (-5) = true := by
  decide +kernel

theorem k5P42Section1_taylorRows_J1_I5 :
    SparseLocalTaylorRowsCertificate 17
      k5P42Section1 k5P42Section1QJ1I5 k5CurveTerms
        (-1) (-5) := by
  intro a ha
  interval_cases a
  · exact k5P42Section1_taylorRow0_J1_I5
  · exact k5P42Section1_taylorRow1_J1_I5
  · exact k5P42Section1_taylorRow2_J1_I5
  · exact k5P42Section1_taylorRow3_J1_I5
  · exact k5P42Section1_taylorRow4_J1_I5
  · exact k5P42Section1_taylorRow5_J1_I5
  · exact k5P42Section1_taylorRow6_J1_I5
  · exact k5P42Section1_taylorRow7_J1_I5
  · exact k5P42Section1_taylorRow8_J1_I5
  · exact k5P42Section1_taylorRow9_J1_I5
  · exact k5P42Section1_taylorRow10_J1_I5
  · exact k5P42Section1_taylorRow11_J1_I5
  · exact k5P42Section1_taylorRow12_J1_I5
  · exact k5P42Section1_taylorRow13_J1_I5
  · exact k5P42Section1_taylorRow14_J1_I5
  · exact k5P42Section1_taylorRow15_J1_I5
  · exact k5P42Section1_taylorRow16_J1_I5

end Erdos686Variant
end Erdos686
