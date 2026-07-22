import ErdosProblems.Erdos686.Core.CFTailBandCheck13

namespace Erdos686
namespace Erdos686Variant

set_option maxRecDepth 500000 in
set_option maxHeartbeats 0 in
-- The generated finite tree requires more than the default reduction budget.
theorem k15FareyCert1000_check :
    fareyCheck 4 97 1 13 2217 (11 * 10 ^ 1000) k15EqRefuted 1 1 11 10
      CFTail1000.k15FareyCert = true := by
  decide +kernel

#print axioms k15FareyCert1000_check

end Erdos686Variant
end Erdos686
