/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686K5P42NoncommonData

namespace Erdos686
namespace Erdos686Variant

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P42EliminationDifference1_row2 :
    denseIntIsZero (k5P42EliminationDifference1.getD 2 []) := by
  unfold denseIntIsZero
  decide +kernel

end Erdos686Variant
end Erdos686
