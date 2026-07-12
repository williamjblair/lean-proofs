import ErdosProblems.Erdos686EvenK18CandidateCoverS22
import ErdosProblems.Erdos686EvenK18CandidateCoverS23
import ErdosProblems.Erdos686EvenK18CandidateCoverS24
import ErdosProblems.Erdos686EvenK18CandidateCoverS25
import ErdosProblems.Erdos686EvenK18CandidateCoverS26
import ErdosProblems.Erdos686EvenK18CandidateCoverS27
import ErdosProblems.Erdos686EvenK18CandidateCoverS28
import ErdosProblems.Erdos686EvenK18CandidateCoverS29
import ErdosProblems.Erdos686EvenK18CandidateCoverS30
import ErdosProblems.Erdos686EvenK18CandidateCoverS31
import ErdosProblems.Erdos686EvenK18CandidateCoverS32
namespace Erdos686.Erdos686Variant

theorem even18_q_cover_group_2 (q : ℕ)
    (hlo : 45056 ≤ q) (hhi : q < 67584) : even18QCovered q := by
  by_cases h22 : q < 47104
  · exact even18ScanPow_get even18_candidate_cover_scan_22 (by omega) h22
  by_cases h23 : q < 49152
  · exact even18ScanPow_get even18_candidate_cover_scan_23 (by omega) h23
  by_cases h24 : q < 51200
  · exact even18ScanPow_get even18_candidate_cover_scan_24 (by omega) h24
  by_cases h25 : q < 53248
  · exact even18ScanPow_get even18_candidate_cover_scan_25 (by omega) h25
  by_cases h26 : q < 55296
  · exact even18ScanPow_get even18_candidate_cover_scan_26 (by omega) h26
  by_cases h27 : q < 57344
  · exact even18ScanPow_get even18_candidate_cover_scan_27 (by omega) h27
  by_cases h28 : q < 59392
  · exact even18ScanPow_get even18_candidate_cover_scan_28 (by omega) h28
  by_cases h29 : q < 61440
  · exact even18ScanPow_get even18_candidate_cover_scan_29 (by omega) h29
  by_cases h30 : q < 63488
  · exact even18ScanPow_get even18_candidate_cover_scan_30 (by omega) h30
  by_cases h31 : q < 65536
  · exact even18ScanPow_get even18_candidate_cover_scan_31 (by omega) h31
  · exact even18ScanPow_get even18_candidate_cover_scan_32 (by omega) hhi

end Erdos686.Erdos686Variant
