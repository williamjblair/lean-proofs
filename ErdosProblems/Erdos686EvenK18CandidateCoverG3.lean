import ErdosProblems.Erdos686EvenK18CandidateCoverS33
import ErdosProblems.Erdos686EvenK18CandidateCoverS34
import ErdosProblems.Erdos686EvenK18CandidateCoverS35
import ErdosProblems.Erdos686EvenK18CandidateCoverS36
import ErdosProblems.Erdos686EvenK18CandidateCoverS37
import ErdosProblems.Erdos686EvenK18CandidateCoverS38
import ErdosProblems.Erdos686EvenK18CandidateCoverS39
import ErdosProblems.Erdos686EvenK18CandidateCoverS40
import ErdosProblems.Erdos686EvenK18CandidateCoverS41
import ErdosProblems.Erdos686EvenK18CandidateCoverS42
import ErdosProblems.Erdos686EvenK18CandidateCoverS43
namespace Erdos686.Erdos686Variant

theorem even18_q_cover_group_3 (q : ℕ)
    (hlo : 67584 ≤ q) (hhi : q < 90112) : even18QCovered q := by
  by_cases h33 : q < 69632
  · exact even18ScanPow_get even18_candidate_cover_scan_33 (by omega) h33
  by_cases h34 : q < 71680
  · exact even18ScanPow_get even18_candidate_cover_scan_34 (by omega) h34
  by_cases h35 : q < 73728
  · exact even18ScanPow_get even18_candidate_cover_scan_35 (by omega) h35
  by_cases h36 : q < 75776
  · exact even18ScanPow_get even18_candidate_cover_scan_36 (by omega) h36
  by_cases h37 : q < 77824
  · exact even18ScanPow_get even18_candidate_cover_scan_37 (by omega) h37
  by_cases h38 : q < 79872
  · exact even18ScanPow_get even18_candidate_cover_scan_38 (by omega) h38
  by_cases h39 : q < 81920
  · exact even18ScanPow_get even18_candidate_cover_scan_39 (by omega) h39
  by_cases h40 : q < 83968
  · exact even18ScanPow_get even18_candidate_cover_scan_40 (by omega) h40
  by_cases h41 : q < 86016
  · exact even18ScanPow_get even18_candidate_cover_scan_41 (by omega) h41
  by_cases h42 : q < 88064
  · exact even18ScanPow_get even18_candidate_cover_scan_42 (by omega) h42
  · exact even18ScanPow_get even18_candidate_cover_scan_43 (by omega) hhi

end Erdos686.Erdos686Variant
