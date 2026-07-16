/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686K5P33CertificateData

namespace Erdos686
namespace Erdos686Variant

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P33Section0_taylorRow0_J1_I2 :
    sparseLocalTaylorRowCheck 17 0
      k5P33Section0 k5P33Section0QJ1I2 k5CurveTerms
        (-1) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P33Section0_taylorRow1_J1_I2 :
    sparseLocalTaylorRowCheck 17 1
      k5P33Section0 k5P33Section0QJ1I2 k5CurveTerms
        (-1) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P33Section0_taylorRow2_J1_I2 :
    sparseLocalTaylorRowCheck 17 2
      k5P33Section0 k5P33Section0QJ1I2 k5CurveTerms
        (-1) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P33Section0_taylorRow3_J1_I2 :
    sparseLocalTaylorRowCheck 17 3
      k5P33Section0 k5P33Section0QJ1I2 k5CurveTerms
        (-1) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P33Section0_taylorRow4_J1_I2 :
    sparseLocalTaylorRowCheck 17 4
      k5P33Section0 k5P33Section0QJ1I2 k5CurveTerms
        (-1) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P33Section0_taylorRow5_J1_I2 :
    sparseLocalTaylorRowCheck 17 5
      k5P33Section0 k5P33Section0QJ1I2 k5CurveTerms
        (-1) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P33Section0_taylorRow6_J1_I2 :
    sparseLocalTaylorRowCheck 17 6
      k5P33Section0 k5P33Section0QJ1I2 k5CurveTerms
        (-1) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P33Section0_taylorRow7_J1_I2 :
    sparseLocalTaylorRowCheck 17 7
      k5P33Section0 k5P33Section0QJ1I2 k5CurveTerms
        (-1) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P33Section0_taylorRow8_J1_I2 :
    sparseLocalTaylorRowCheck 17 8
      k5P33Section0 k5P33Section0QJ1I2 k5CurveTerms
        (-1) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P33Section0_taylorRow9_J1_I2 :
    sparseLocalTaylorRowCheck 17 9
      k5P33Section0 k5P33Section0QJ1I2 k5CurveTerms
        (-1) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P33Section0_taylorRow10_J1_I2 :
    sparseLocalTaylorRowCheck 17 10
      k5P33Section0 k5P33Section0QJ1I2 k5CurveTerms
        (-1) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P33Section0_taylorRow11_J1_I2 :
    sparseLocalTaylorRowCheck 17 11
      k5P33Section0 k5P33Section0QJ1I2 k5CurveTerms
        (-1) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P33Section0_taylorRow12_J1_I2 :
    sparseLocalTaylorRowCheck 17 12
      k5P33Section0 k5P33Section0QJ1I2 k5CurveTerms
        (-1) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P33Section0_taylorRow13_J1_I2 :
    sparseLocalTaylorRowCheck 17 13
      k5P33Section0 k5P33Section0QJ1I2 k5CurveTerms
        (-1) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P33Section0_taylorRow14_J1_I2 :
    sparseLocalTaylorRowCheck 17 14
      k5P33Section0 k5P33Section0QJ1I2 k5CurveTerms
        (-1) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P33Section0_taylorRow15_J1_I2 :
    sparseLocalTaylorRowCheck 17 15
      k5P33Section0 k5P33Section0QJ1I2 k5CurveTerms
        (-1) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P33Section0_taylorRow16_J1_I2 :
    sparseLocalTaylorRowCheck 17 16
      k5P33Section0 k5P33Section0QJ1I2 k5CurveTerms
        (-1) (-2) = true := by
  decide +kernel

theorem k5P33Section0_taylorRows_J1_I2 :
    SparseLocalTaylorRowsCertificate 17
      k5P33Section0 k5P33Section0QJ1I2 k5CurveTerms
        (-1) (-2) := by
  intro a ha
  interval_cases a
  · exact k5P33Section0_taylorRow0_J1_I2
  · exact k5P33Section0_taylorRow1_J1_I2
  · exact k5P33Section0_taylorRow2_J1_I2
  · exact k5P33Section0_taylorRow3_J1_I2
  · exact k5P33Section0_taylorRow4_J1_I2
  · exact k5P33Section0_taylorRow5_J1_I2
  · exact k5P33Section0_taylorRow6_J1_I2
  · exact k5P33Section0_taylorRow7_J1_I2
  · exact k5P33Section0_taylorRow8_J1_I2
  · exact k5P33Section0_taylorRow9_J1_I2
  · exact k5P33Section0_taylorRow10_J1_I2
  · exact k5P33Section0_taylorRow11_J1_I2
  · exact k5P33Section0_taylorRow12_J1_I2
  · exact k5P33Section0_taylorRow13_J1_I2
  · exact k5P33Section0_taylorRow14_J1_I2
  · exact k5P33Section0_taylorRow15_J1_I2
  · exact k5P33Section0_taylorRow16_J1_I2

end Erdos686Variant
end Erdos686
