/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686K5P33NoncommonData

namespace Erdos686
namespace Erdos686Variant

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P33EliminationDifference4_row1 :
    denseIntIsZero (k5P33EliminationDifference4.getD 1 []) := by
  unfold denseIntIsZero
  decide +kernel

end Erdos686Variant
end Erdos686
