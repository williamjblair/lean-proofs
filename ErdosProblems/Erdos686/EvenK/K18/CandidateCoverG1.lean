import ErdosProblems.Erdos686.EvenK.K18.CandidateCoverS11
import ErdosProblems.Erdos686.EvenK.K18.CandidateCoverS12
import ErdosProblems.Erdos686.EvenK.K18.CandidateCoverS13
import ErdosProblems.Erdos686.EvenK.K18.CandidateCoverS14
import ErdosProblems.Erdos686.EvenK.K18.CandidateCoverS15
import ErdosProblems.Erdos686.EvenK.K18.CandidateCoverS16
import ErdosProblems.Erdos686.EvenK.K18.CandidateCoverS17
import ErdosProblems.Erdos686.EvenK.K18.CandidateCoverS18
import ErdosProblems.Erdos686.EvenK.K18.CandidateCoverS19
import ErdosProblems.Erdos686.EvenK.K18.CandidateCoverS20
import ErdosProblems.Erdos686.EvenK.K18.CandidateCoverS21
namespace Erdos686.Erdos686Variant

theorem even18_q_cover_group_1 (q : ℕ)
    (hlo : 22528 ≤ q) (hhi : q < 45056) : even18QCovered q := by
  by_cases h11 : q < 24576
  · exact even18ScanPow_get even18_candidate_cover_scan_11 (by omega) h11
  by_cases h12 : q < 26624
  · exact even18ScanPow_get even18_candidate_cover_scan_12 (by omega) h12
  by_cases h13 : q < 28672
  · exact even18ScanPow_get even18_candidate_cover_scan_13 (by omega) h13
  by_cases h14 : q < 30720
  · exact even18ScanPow_get even18_candidate_cover_scan_14 (by omega) h14
  by_cases h15 : q < 32768
  · exact even18ScanPow_get even18_candidate_cover_scan_15 (by omega) h15
  by_cases h16 : q < 34816
  · exact even18ScanPow_get even18_candidate_cover_scan_16 (by omega) h16
  by_cases h17 : q < 36864
  · exact even18ScanPow_get even18_candidate_cover_scan_17 (by omega) h17
  by_cases h18 : q < 38912
  · exact even18ScanPow_get even18_candidate_cover_scan_18 (by omega) h18
  by_cases h19 : q < 40960
  · exact even18ScanPow_get even18_candidate_cover_scan_19 (by omega) h19
  by_cases h20 : q < 43008
  · exact even18ScanPow_get even18_candidate_cover_scan_20 (by omega) h20
  · exact even18ScanPow_get even18_candidate_cover_scan_21 (by omega) hhi

end Erdos686.Erdos686Variant
