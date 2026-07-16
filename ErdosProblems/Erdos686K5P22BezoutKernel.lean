/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686K5P22NoncommonData

namespace Erdos686
namespace Erdos686Variant

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P22ResultantBezoutIdentity :
    denseIntIsZero
      (denseIntSub
        (denseIntAdd
          (denseIntMul k5P22ResultantCofactor0
            k5P22Resultant0)
          (denseIntMul k5P22ResultantCofactor1
            k5P22Resultant1))
        (denseIntScale k5P22BezoutScale
          k5P22Expected)) := by
  unfold denseIntIsZero
  decide +kernel

end Erdos686Variant
end Erdos686
