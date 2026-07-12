import ErdosProblems.Erdos686EvenK18CandidateCoverS0
import ErdosProblems.Erdos686EvenK18CandidateCoverS1
import ErdosProblems.Erdos686EvenK18CandidateCoverS2
import ErdosProblems.Erdos686EvenK18CandidateCoverS3
import ErdosProblems.Erdos686EvenK18CandidateCoverS4
import ErdosProblems.Erdos686EvenK18CandidateCoverS5
import ErdosProblems.Erdos686EvenK18CandidateCoverS6
import ErdosProblems.Erdos686EvenK18CandidateCoverS7
import ErdosProblems.Erdos686EvenK18CandidateCoverS8
import ErdosProblems.Erdos686EvenK18CandidateCoverS9
import ErdosProblems.Erdos686EvenK18CandidateCoverS10
namespace Erdos686.Erdos686Variant

theorem even18_q_cover_group_0 (q : ℕ)
    (hlo : 0 ≤ q) (hhi : q < 22528) : even18QCovered q := by
  by_cases h0 : q < 2048
  · exact even18ScanPow_get even18_candidate_cover_scan_0 (by omega) h0
  by_cases h1 : q < 4096
  · exact even18ScanPow_get even18_candidate_cover_scan_1 (by omega) h1
  by_cases h2 : q < 6144
  · exact even18ScanPow_get even18_candidate_cover_scan_2 (by omega) h2
  by_cases h3 : q < 8192
  · exact even18ScanPow_get even18_candidate_cover_scan_3 (by omega) h3
  by_cases h4 : q < 10240
  · exact even18ScanPow_get even18_candidate_cover_scan_4 (by omega) h4
  by_cases h5 : q < 12288
  · exact even18ScanPow_get even18_candidate_cover_scan_5 (by omega) h5
  by_cases h6 : q < 14336
  · exact even18ScanPow_get even18_candidate_cover_scan_6 (by omega) h6
  by_cases h7 : q < 16384
  · exact even18ScanPow_get even18_candidate_cover_scan_7 (by omega) h7
  by_cases h8 : q < 18432
  · exact even18ScanPow_get even18_candidate_cover_scan_8 (by omega) h8
  by_cases h9 : q < 20480
  · exact even18ScanPow_get even18_candidate_cover_scan_9 (by omega) h9
  · exact even18ScanPow_get even18_candidate_cover_scan_10 (by omega) hhi

end Erdos686.Erdos686Variant
