import ErdosProblems.Erdos686CFTailBandCheck5

namespace Erdos686
namespace Erdos686Variant

set_option maxRecDepth 500000 in
set_option maxHeartbeats 0 in
-- The generated finite tree requires more than the default reduction budget.
theorem k7FareyCert1000_check :
    fareyCheck 4 93 5 5 887 (5 * 10 ^ 1000) k7EqRefuted 1 1 5 4
      CFTail1000.k7FareyCert = true := by
  decide +kernel

#print axioms k7FareyCert1000_check

end Erdos686Variant
end Erdos686
