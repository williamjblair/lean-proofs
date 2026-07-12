import ErdosProblems.Erdos686EvenK28CandidateCoverS9
namespace Erdos686.Erdos686Variant

set_option maxHeartbeats 200000000 in
set_option maxRecDepth 1000000 in
theorem even28_candidate_cover_scan_10 :
    even28ScanPow even28QCoveredBool 20480 11 = true := by decide

end Erdos686.Erdos686Variant
