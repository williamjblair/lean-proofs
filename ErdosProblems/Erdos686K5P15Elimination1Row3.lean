/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686K5P15NoncommonData

namespace Erdos686
namespace Erdos686Variant

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P15EliminationDifference1_row3 :
    denseIntIsZero (k5P15EliminationDifference1.getD 3 []) := by
  unfold denseIntIsZero
  decide +kernel

end Erdos686Variant
end Erdos686
