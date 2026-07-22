import ErdosProblems.Erdos686.EvenK.K28.CandidateCoverS4
namespace Erdos686.Erdos686Variant

set_option maxHeartbeats 200000000 in
set_option maxRecDepth 1000000 in
theorem even28_candidate_cover_scan_5 :
    even28ScanPow even28QCoveredBool 10240 11 = true := by decide

end Erdos686.Erdos686Variant
