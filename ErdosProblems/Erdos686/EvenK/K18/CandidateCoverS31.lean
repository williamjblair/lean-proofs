import ErdosProblems.Erdos686.EvenK.K18.CandidateDefs
namespace Erdos686.Erdos686Variant

set_option maxHeartbeats 100000000 in
-- Balanced ordinary-kernel scan of q in [63488, 65536).
set_option maxRecDepth 1000000 in
theorem even18_candidate_cover_scan_31 :
    even18ScanPow even18QCoveredBool 63488 11 = true := by decide

end Erdos686.Erdos686Variant
