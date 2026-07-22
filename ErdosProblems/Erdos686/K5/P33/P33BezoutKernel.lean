/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.K5.P33.P33NoncommonData

namespace Erdos686
namespace Erdos686Variant

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P33ResultantBezoutIdentity :
    denseIntIsZero
      (denseIntSub
        (denseIntAdd (denseIntMul k5P33ResultantCofactor0 k5P33Resultant0) (denseIntAdd (denseIntMul k5P33ResultantCofactor1 k5P33Resultant1) (denseIntAdd (denseIntMul k5P33ResultantCofactor2 k5P33Resultant2) (denseIntAdd (denseIntMul k5P33ResultantCofactor3 k5P33Resultant3) ((denseIntMul k5P33ResultantCofactor4 k5P33Resultant4))))))
        (denseIntScale k5P33BezoutScale
          k5P33Expected)) := by
  unfold denseIntIsZero
  decide +kernel

end Erdos686Variant
end Erdos686
