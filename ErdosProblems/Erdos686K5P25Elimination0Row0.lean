/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686K5P25NoncommonData

namespace Erdos686
namespace Erdos686Variant

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P25EliminationDifference0_row0 :
    denseIntIsZero (k5P25EliminationDifference0.getD 0 []) := by
  unfold denseIntIsZero
  decide +kernel

end Erdos686Variant
end Erdos686
