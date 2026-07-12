import ErdosProblems.Erdos686CFTailBandCheck7

namespace Erdos686
namespace Erdos686Variant

set_option maxRecDepth 500000 in
set_option maxHeartbeats 0 in
-- The generated finite tree requires more than the default reduction budget.
theorem k9FareyCert1000_check :
    fareyCheck 4 162 5 7 1109 (7 * 10 ^ 1000) k9EqRefuted 1 1 6 5
      CFTail1000.k9FareyCert = true := by
  decide +kernel

#print axioms k9FareyCert1000_check

end Erdos686Variant
end Erdos686
