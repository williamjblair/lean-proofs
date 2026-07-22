/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.K5.P33.P33NoncommonData

namespace Erdos686
namespace Erdos686Variant

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P33EliminationDifference2_row3 :
    denseIntIsZero (k5P33EliminationDifference2.getD 3 []) := by
  unfold denseIntIsZero
  decide +kernel

end Erdos686Variant
end Erdos686
