/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.K5.P33.P33CertificateData

namespace Erdos686
namespace Erdos686Variant

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P33Section2_taylorRow0_J5_I2 :
    sparseLocalTaylorRowCheck 17 0
      k5P33Section2 k5P33Section2QJ5I2 k5CurveTerms
        (-5) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P33Section2_taylorRow1_J5_I2 :
    sparseLocalTaylorRowCheck 17 1
      k5P33Section2 k5P33Section2QJ5I2 k5CurveTerms
        (-5) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P33Section2_taylorRow2_J5_I2 :
    sparseLocalTaylorRowCheck 17 2
      k5P33Section2 k5P33Section2QJ5I2 k5CurveTerms
        (-5) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P33Section2_taylorRow3_J5_I2 :
    sparseLocalTaylorRowCheck 17 3
      k5P33Section2 k5P33Section2QJ5I2 k5CurveTerms
        (-5) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P33Section2_taylorRow4_J5_I2 :
    sparseLocalTaylorRowCheck 17 4
      k5P33Section2 k5P33Section2QJ5I2 k5CurveTerms
        (-5) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P33Section2_taylorRow5_J5_I2 :
    sparseLocalTaylorRowCheck 17 5
      k5P33Section2 k5P33Section2QJ5I2 k5CurveTerms
        (-5) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P33Section2_taylorRow6_J5_I2 :
    sparseLocalTaylorRowCheck 17 6
      k5P33Section2 k5P33Section2QJ5I2 k5CurveTerms
        (-5) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P33Section2_taylorRow7_J5_I2 :
    sparseLocalTaylorRowCheck 17 7
      k5P33Section2 k5P33Section2QJ5I2 k5CurveTerms
        (-5) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P33Section2_taylorRow8_J5_I2 :
    sparseLocalTaylorRowCheck 17 8
      k5P33Section2 k5P33Section2QJ5I2 k5CurveTerms
        (-5) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P33Section2_taylorRow9_J5_I2 :
    sparseLocalTaylorRowCheck 17 9
      k5P33Section2 k5P33Section2QJ5I2 k5CurveTerms
        (-5) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P33Section2_taylorRow10_J5_I2 :
    sparseLocalTaylorRowCheck 17 10
      k5P33Section2 k5P33Section2QJ5I2 k5CurveTerms
        (-5) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P33Section2_taylorRow11_J5_I2 :
    sparseLocalTaylorRowCheck 17 11
      k5P33Section2 k5P33Section2QJ5I2 k5CurveTerms
        (-5) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P33Section2_taylorRow12_J5_I2 :
    sparseLocalTaylorRowCheck 17 12
      k5P33Section2 k5P33Section2QJ5I2 k5CurveTerms
        (-5) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P33Section2_taylorRow13_J5_I2 :
    sparseLocalTaylorRowCheck 17 13
      k5P33Section2 k5P33Section2QJ5I2 k5CurveTerms
        (-5) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P33Section2_taylorRow14_J5_I2 :
    sparseLocalTaylorRowCheck 17 14
      k5P33Section2 k5P33Section2QJ5I2 k5CurveTerms
        (-5) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P33Section2_taylorRow15_J5_I2 :
    sparseLocalTaylorRowCheck 17 15
      k5P33Section2 k5P33Section2QJ5I2 k5CurveTerms
        (-5) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P33Section2_taylorRow16_J5_I2 :
    sparseLocalTaylorRowCheck 17 16
      k5P33Section2 k5P33Section2QJ5I2 k5CurveTerms
        (-5) (-2) = true := by
  decide +kernel

theorem k5P33Section2_taylorRows_J5_I2 :
    SparseLocalTaylorRowsCertificate 17
      k5P33Section2 k5P33Section2QJ5I2 k5CurveTerms
        (-5) (-2) := by
  intro a ha
  interval_cases a
  · exact k5P33Section2_taylorRow0_J5_I2
  · exact k5P33Section2_taylorRow1_J5_I2
  · exact k5P33Section2_taylorRow2_J5_I2
  · exact k5P33Section2_taylorRow3_J5_I2
  · exact k5P33Section2_taylorRow4_J5_I2
  · exact k5P33Section2_taylorRow5_J5_I2
  · exact k5P33Section2_taylorRow6_J5_I2
  · exact k5P33Section2_taylorRow7_J5_I2
  · exact k5P33Section2_taylorRow8_J5_I2
  · exact k5P33Section2_taylorRow9_J5_I2
  · exact k5P33Section2_taylorRow10_J5_I2
  · exact k5P33Section2_taylorRow11_J5_I2
  · exact k5P33Section2_taylorRow12_J5_I2
  · exact k5P33Section2_taylorRow13_J5_I2
  · exact k5P33Section2_taylorRow14_J5_I2
  · exact k5P33Section2_taylorRow15_J5_I2
  · exact k5P33Section2_taylorRow16_J5_I2

end Erdos686Variant
end Erdos686
