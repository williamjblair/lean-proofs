import ErdosProblems.Erdos686EvenK18CandidateDefs
namespace Erdos686.Erdos686Variant

set_option maxHeartbeats 100000000 in
-- Balanced ordinary-kernel scan of q in [92160, 94208).
set_option maxRecDepth 1000000 in
theorem even18_candidate_cover_scan_45 :
    even18ScanPow even18QCoveredBool 92160 11 = true := by decide

end Erdos686.Erdos686Variant
