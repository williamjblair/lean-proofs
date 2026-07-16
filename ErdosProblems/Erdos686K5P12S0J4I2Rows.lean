/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686K5P12CertificateData

namespace Erdos686
namespace Erdos686Variant

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P12Section0_taylorRow0_J4_I2 :
    sparseLocalTaylorRowCheck 17 0
      k5P12Section0 k5P12Section0QJ4I2 k5CurveTerms
        (-4) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P12Section0_taylorRow1_J4_I2 :
    sparseLocalTaylorRowCheck 17 1
      k5P12Section0 k5P12Section0QJ4I2 k5CurveTerms
        (-4) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P12Section0_taylorRow2_J4_I2 :
    sparseLocalTaylorRowCheck 17 2
      k5P12Section0 k5P12Section0QJ4I2 k5CurveTerms
        (-4) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P12Section0_taylorRow3_J4_I2 :
    sparseLocalTaylorRowCheck 17 3
      k5P12Section0 k5P12Section0QJ4I2 k5CurveTerms
        (-4) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P12Section0_taylorRow4_J4_I2 :
    sparseLocalTaylorRowCheck 17 4
      k5P12Section0 k5P12Section0QJ4I2 k5CurveTerms
        (-4) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P12Section0_taylorRow5_J4_I2 :
    sparseLocalTaylorRowCheck 17 5
      k5P12Section0 k5P12Section0QJ4I2 k5CurveTerms
        (-4) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P12Section0_taylorRow6_J4_I2 :
    sparseLocalTaylorRowCheck 17 6
      k5P12Section0 k5P12Section0QJ4I2 k5CurveTerms
        (-4) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P12Section0_taylorRow7_J4_I2 :
    sparseLocalTaylorRowCheck 17 7
      k5P12Section0 k5P12Section0QJ4I2 k5CurveTerms
        (-4) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P12Section0_taylorRow8_J4_I2 :
    sparseLocalTaylorRowCheck 17 8
      k5P12Section0 k5P12Section0QJ4I2 k5CurveTerms
        (-4) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P12Section0_taylorRow9_J4_I2 :
    sparseLocalTaylorRowCheck 17 9
      k5P12Section0 k5P12Section0QJ4I2 k5CurveTerms
        (-4) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P12Section0_taylorRow10_J4_I2 :
    sparseLocalTaylorRowCheck 17 10
      k5P12Section0 k5P12Section0QJ4I2 k5CurveTerms
        (-4) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P12Section0_taylorRow11_J4_I2 :
    sparseLocalTaylorRowCheck 17 11
      k5P12Section0 k5P12Section0QJ4I2 k5CurveTerms
        (-4) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P12Section0_taylorRow12_J4_I2 :
    sparseLocalTaylorRowCheck 17 12
      k5P12Section0 k5P12Section0QJ4I2 k5CurveTerms
        (-4) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P12Section0_taylorRow13_J4_I2 :
    sparseLocalTaylorRowCheck 17 13
      k5P12Section0 k5P12Section0QJ4I2 k5CurveTerms
        (-4) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P12Section0_taylorRow14_J4_I2 :
    sparseLocalTaylorRowCheck 17 14
      k5P12Section0 k5P12Section0QJ4I2 k5CurveTerms
        (-4) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P12Section0_taylorRow15_J4_I2 :
    sparseLocalTaylorRowCheck 17 15
      k5P12Section0 k5P12Section0QJ4I2 k5CurveTerms
        (-4) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P12Section0_taylorRow16_J4_I2 :
    sparseLocalTaylorRowCheck 17 16
      k5P12Section0 k5P12Section0QJ4I2 k5CurveTerms
        (-4) (-2) = true := by
  decide +kernel

theorem k5P12Section0_taylorRows_J4_I2 :
    SparseLocalTaylorRowsCertificate 17
      k5P12Section0 k5P12Section0QJ4I2 k5CurveTerms
        (-4) (-2) := by
  intro a ha
  interval_cases a
  · exact k5P12Section0_taylorRow0_J4_I2
  · exact k5P12Section0_taylorRow1_J4_I2
  · exact k5P12Section0_taylorRow2_J4_I2
  · exact k5P12Section0_taylorRow3_J4_I2
  · exact k5P12Section0_taylorRow4_J4_I2
  · exact k5P12Section0_taylorRow5_J4_I2
  · exact k5P12Section0_taylorRow6_J4_I2
  · exact k5P12Section0_taylorRow7_J4_I2
  · exact k5P12Section0_taylorRow8_J4_I2
  · exact k5P12Section0_taylorRow9_J4_I2
  · exact k5P12Section0_taylorRow10_J4_I2
  · exact k5P12Section0_taylorRow11_J4_I2
  · exact k5P12Section0_taylorRow12_J4_I2
  · exact k5P12Section0_taylorRow13_J4_I2
  · exact k5P12Section0_taylorRow14_J4_I2
  · exact k5P12Section0_taylorRow15_J4_I2
  · exact k5P12Section0_taylorRow16_J4_I2

end Erdos686Variant
end Erdos686
