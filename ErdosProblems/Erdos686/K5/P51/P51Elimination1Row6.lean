/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.K5.P51.P51NoncommonData

namespace Erdos686
namespace Erdos686Variant

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5P51EliminationDifference1_row6 :
    denseIntIsZero (k5P51EliminationDifference1.getD 6 []) := by
  unfold denseIntIsZero
  decide +kernel

end Erdos686Variant
end Erdos686
