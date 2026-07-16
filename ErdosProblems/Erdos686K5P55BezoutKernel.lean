/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686K5P55NoncommonData

namespace Erdos686
namespace Erdos686Variant

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P55ResultantBezoutIdentity :
    denseIntIsZero
      (denseIntSub
        (denseIntAdd
          (denseIntMul k5P55ResultantCofactor0
            k5P55Resultant0)
          (denseIntMul k5P55ResultantCofactor1
            k5P55Resultant1))
        (denseIntScale k5P55BezoutScale
          k5P55Expected)) := by
  unfold denseIntIsZero
  decide +kernel

end Erdos686Variant
end Erdos686
