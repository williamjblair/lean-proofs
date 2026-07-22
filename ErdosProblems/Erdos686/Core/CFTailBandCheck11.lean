import ErdosProblems.Erdos686.Core.CFTailBandCheck9

namespace Erdos686
namespace Erdos686Variant

set_option maxRecDepth 500000 in
set_option maxHeartbeats 0 in
-- The generated finite tree requires more than the default reduction budget.
theorem k11FareyCert1000_check :
    fareyCheck 4 50 1 9 1552 (8 * 10 ^ 1000) k11EqRefuted 1 1 8 7
      CFTail1000.k11FareyCert = true := by
  decide +kernel

#print axioms k11FareyCert1000_check

end Erdos686Variant
end Erdos686
