/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.K5.P22.P22NoncommonData

namespace Erdos686
namespace Erdos686Variant

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P22EliminationDifference1_row8 :
    denseIntIsZero (k5P22EliminationDifference1.getD 8 []) := by
  unfold denseIntIsZero
  decide +kernel

end Erdos686Variant
end Erdos686
