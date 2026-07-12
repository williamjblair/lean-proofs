import ErdosProblems.Erdos686EvenK32CandidateCoverS1
namespace Erdos686.Erdos686Variant

set_option maxHeartbeats 200000000 in
set_option maxRecDepth 1000000 in
theorem even32_candidate_cover_scan_2 :
    even32ScanPow even32QCoveredBool 4096 11 = true := by decide

end Erdos686.Erdos686Variant
