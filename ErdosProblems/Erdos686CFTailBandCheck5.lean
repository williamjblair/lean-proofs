import ErdosProblems.Erdos686CFTailBandCert

namespace Erdos686
namespace Erdos686Variant

set_option maxRecDepth 500000 in
set_option maxHeartbeats 0 in
-- The generated finite tree requires more than the default reduction budget.
theorem k5FareyCert1000_check :
    fareyCheck 4 44 5 3 665 (4 * 10 ^ 1000) k5EqRefuted 1 1 4 3
      CFTail1000.k5FareyCert = true := by
  decide +kernel

#print axioms k5FareyCert1000_check

end Erdos686Variant
end Erdos686
