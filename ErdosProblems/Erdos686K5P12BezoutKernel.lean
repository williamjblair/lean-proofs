/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686K5P12NoncommonData

namespace Erdos686
namespace Erdos686Variant

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P12ResultantBezoutIdentity :
    denseIntIsZero
      (denseIntSub
        (denseIntAdd
          (denseIntMul k5P12ResultantCofactor0
            k5P12Resultant0)
          (denseIntMul k5P12ResultantCofactor1
            k5P12Resultant1))
        (denseIntScale k5P12BezoutScale
          k5P12Expected)) := by
  unfold denseIntIsZero
  decide +kernel

end Erdos686Variant
end Erdos686
