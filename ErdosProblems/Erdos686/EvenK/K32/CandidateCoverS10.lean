import ErdosProblems.Erdos686.EvenK.K32.CandidateCoverS9
namespace Erdos686.Erdos686Variant

set_option maxHeartbeats 200000000 in
set_option maxRecDepth 1000000 in
theorem even32_candidate_cover_scan_10 :
    even32ScanPow even32QCoveredBool 20480 11 = true := by decide

end Erdos686.Erdos686Variant
