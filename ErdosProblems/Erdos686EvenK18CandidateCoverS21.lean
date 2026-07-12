import ErdosProblems.Erdos686EvenK18CandidateDefs
namespace Erdos686.Erdos686Variant

set_option maxHeartbeats 100000000 in
-- Balanced ordinary-kernel scan of q in [43008, 45056).
set_option maxRecDepth 1000000 in
theorem even18_candidate_cover_scan_21 :
    even18ScanPow even18QCoveredBool 43008 11 = true := by decide

end Erdos686.Erdos686Variant
