import ErdosProblems.Erdos686.Core.CFTailBandCheck11

namespace Erdos686
namespace Erdos686Variant

set_option maxRecDepth 500000 in
set_option maxHeartbeats 0 in
-- The generated finite tree requires more than the default reduction budget.
theorem k13FareyCert1000_check :
    fareyCheck 4 72 1 11 1774 (9 * 10 ^ 1000) k13EqRefuted 1 1 8 7
      CFTail1000.k13FareyCert = true := by
  decide +kernel

#print axioms k13FareyCert1000_check

end Erdos686Variant
end Erdos686
