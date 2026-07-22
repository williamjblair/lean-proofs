/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.K5.P11.P11CertificateData

namespace Erdos686
namespace Erdos686Variant

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P11Section1_taylorRow0_J4_I3 :
    sparseLocalTaylorRowCheck 17 0
      k5P11Section1 k5P11Section1QJ4I3 k5CurveTerms
        (-4) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P11Section1_taylorRow1_J4_I3 :
    sparseLocalTaylorRowCheck 17 1
      k5P11Section1 k5P11Section1QJ4I3 k5CurveTerms
        (-4) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P11Section1_taylorRow2_J4_I3 :
    sparseLocalTaylorRowCheck 17 2
      k5P11Section1 k5P11Section1QJ4I3 k5CurveTerms
        (-4) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P11Section1_taylorRow3_J4_I3 :
    sparseLocalTaylorRowCheck 17 3
      k5P11Section1 k5P11Section1QJ4I3 k5CurveTerms
        (-4) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P11Section1_taylorRow4_J4_I3 :
    sparseLocalTaylorRowCheck 17 4
      k5P11Section1 k5P11Section1QJ4I3 k5CurveTerms
        (-4) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P11Section1_taylorRow5_J4_I3 :
    sparseLocalTaylorRowCheck 17 5
      k5P11Section1 k5P11Section1QJ4I3 k5CurveTerms
        (-4) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P11Section1_taylorRow6_J4_I3 :
    sparseLocalTaylorRowCheck 17 6
      k5P11Section1 k5P11Section1QJ4I3 k5CurveTerms
        (-4) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P11Section1_taylorRow7_J4_I3 :
    sparseLocalTaylorRowCheck 17 7
      k5P11Section1 k5P11Section1QJ4I3 k5CurveTerms
        (-4) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P11Section1_taylorRow8_J4_I3 :
    sparseLocalTaylorRowCheck 17 8
      k5P11Section1 k5P11Section1QJ4I3 k5CurveTerms
        (-4) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P11Section1_taylorRow9_J4_I3 :
    sparseLocalTaylorRowCheck 17 9
      k5P11Section1 k5P11Section1QJ4I3 k5CurveTerms
        (-4) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P11Section1_taylorRow10_J4_I3 :
    sparseLocalTaylorRowCheck 17 10
      k5P11Section1 k5P11Section1QJ4I3 k5CurveTerms
        (-4) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P11Section1_taylorRow11_J4_I3 :
    sparseLocalTaylorRowCheck 17 11
      k5P11Section1 k5P11Section1QJ4I3 k5CurveTerms
        (-4) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P11Section1_taylorRow12_J4_I3 :
    sparseLocalTaylorRowCheck 17 12
      k5P11Section1 k5P11Section1QJ4I3 k5CurveTerms
        (-4) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P11Section1_taylorRow13_J4_I3 :
    sparseLocalTaylorRowCheck 17 13
      k5P11Section1 k5P11Section1QJ4I3 k5CurveTerms
        (-4) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P11Section1_taylorRow14_J4_I3 :
    sparseLocalTaylorRowCheck 17 14
      k5P11Section1 k5P11Section1QJ4I3 k5CurveTerms
        (-4) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P11Section1_taylorRow15_J4_I3 :
    sparseLocalTaylorRowCheck 17 15
      k5P11Section1 k5P11Section1QJ4I3 k5CurveTerms
        (-4) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P11Section1_taylorRow16_J4_I3 :
    sparseLocalTaylorRowCheck 17 16
      k5P11Section1 k5P11Section1QJ4I3 k5CurveTerms
        (-4) (-3) = true := by
  decide +kernel

theorem k5P11Section1_taylorRows_J4_I3 :
    SparseLocalTaylorRowsCertificate 17
      k5P11Section1 k5P11Section1QJ4I3 k5CurveTerms
        (-4) (-3) := by
  intro a ha
  interval_cases a
  · exact k5P11Section1_taylorRow0_J4_I3
  · exact k5P11Section1_taylorRow1_J4_I3
  · exact k5P11Section1_taylorRow2_J4_I3
  · exact k5P11Section1_taylorRow3_J4_I3
  · exact k5P11Section1_taylorRow4_J4_I3
  · exact k5P11Section1_taylorRow5_J4_I3
  · exact k5P11Section1_taylorRow6_J4_I3
  · exact k5P11Section1_taylorRow7_J4_I3
  · exact k5P11Section1_taylorRow8_J4_I3
  · exact k5P11Section1_taylorRow9_J4_I3
  · exact k5P11Section1_taylorRow10_J4_I3
  · exact k5P11Section1_taylorRow11_J4_I3
  · exact k5P11Section1_taylorRow12_J4_I3
  · exact k5P11Section1_taylorRow13_J4_I3
  · exact k5P11Section1_taylorRow14_J4_I3
  · exact k5P11Section1_taylorRow15_J4_I3
  · exact k5P11Section1_taylorRow16_J4_I3

end Erdos686Variant
end Erdos686
