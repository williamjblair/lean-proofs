/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686K5P14NoncommonData

namespace Erdos686
namespace Erdos686Variant

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P14ResultantBezoutIdentity :
    denseIntIsZero
      (denseIntSub
        (denseIntAdd
          (denseIntMul k5P14ResultantCofactor0
            k5P14Resultant0)
          (denseIntMul k5P14ResultantCofactor1
            k5P14Resultant1))
        (denseIntScale k5P14BezoutScale
          k5P14Expected)) := by
  unfold denseIntIsZero
  decide +kernel

end Erdos686Variant
end Erdos686
