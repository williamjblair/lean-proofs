import ErdosProblems.Erdos686.EvenK.K18.CandidateDefs
namespace Erdos686.Erdos686Variant

set_option maxHeartbeats 100000000 in
-- Balanced ordinary-kernel scan of q in [98304, 100352).
set_option maxRecDepth 1000000 in
theorem even18_candidate_cover_scan_48 :
    even18ScanPow even18QCoveredBool 98304 11 = true := by decide

end Erdos686.Erdos686Variant
