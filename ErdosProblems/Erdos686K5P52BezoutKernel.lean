/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686K5P52NoncommonData

namespace Erdos686
namespace Erdos686Variant

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P52ResultantBezoutIdentity :
    denseIntIsZero
      (denseIntSub
        (denseIntAdd
          (denseIntMul k5P52ResultantCofactor0
            k5P52Resultant0)
          (denseIntMul k5P52ResultantCofactor1
            k5P52Resultant1))
        (denseIntScale k5P52BezoutScale
          k5P52Expected)) := by
  unfold denseIntIsZero
  decide +kernel

end Erdos686Variant
end Erdos686
