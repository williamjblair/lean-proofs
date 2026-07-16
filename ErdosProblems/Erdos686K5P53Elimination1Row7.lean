/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686K5P53NoncommonData

namespace Erdos686
namespace Erdos686Variant

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P53EliminationDifference1_row7 :
    denseIntIsZero (k5P53EliminationDifference1.getD 7 []) := by
  unfold denseIntIsZero
  decide +kernel

end Erdos686Variant
end Erdos686
