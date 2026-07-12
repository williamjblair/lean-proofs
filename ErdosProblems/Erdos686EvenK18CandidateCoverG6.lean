import ErdosProblems.Erdos686EvenK18CandidateCoverS66
import ErdosProblems.Erdos686EvenK18CandidateCoverS67
import ErdosProblems.Erdos686EvenK18CandidateCoverS68
import ErdosProblems.Erdos686EvenK18CandidateCoverS69
import ErdosProblems.Erdos686EvenK18CandidateCoverS70
import ErdosProblems.Erdos686EvenK18CandidateCoverS71
import ErdosProblems.Erdos686EvenK18CandidateCoverS72
import ErdosProblems.Erdos686EvenK18CandidateCoverS73
import ErdosProblems.Erdos686EvenK18CandidateCoverS74
import ErdosProblems.Erdos686EvenK18CandidateCoverS75
import ErdosProblems.Erdos686EvenK18CandidateCoverS76
namespace Erdos686.Erdos686Variant

theorem even18_q_cover_group_6 (q : ℕ)
    (hlo : 135168 ≤ q) (hhi : q < 157696) : even18QCovered q := by
  by_cases h66 : q < 137216
  · exact even18ScanPow_get even18_candidate_cover_scan_66 (by omega) h66
  by_cases h67 : q < 139264
  · exact even18ScanPow_get even18_candidate_cover_scan_67 (by omega) h67
  by_cases h68 : q < 141312
  · exact even18ScanPow_get even18_candidate_cover_scan_68 (by omega) h68
  by_cases h69 : q < 143360
  · exact even18ScanPow_get even18_candidate_cover_scan_69 (by omega) h69
  by_cases h70 : q < 145408
  · exact even18ScanPow_get even18_candidate_cover_scan_70 (by omega) h70
  by_cases h71 : q < 147456
  · exact even18ScanPow_get even18_candidate_cover_scan_71 (by omega) h71
  by_cases h72 : q < 149504
  · exact even18ScanPow_get even18_candidate_cover_scan_72 (by omega) h72
  by_cases h73 : q < 151552
  · exact even18ScanPow_get even18_candidate_cover_scan_73 (by omega) h73
  by_cases h74 : q < 153600
  · exact even18ScanPow_get even18_candidate_cover_scan_74 (by omega) h74
  by_cases h75 : q < 155648
  · exact even18ScanPow_get even18_candidate_cover_scan_75 (by omega) h75
  · exact even18ScanPow_get even18_candidate_cover_scan_76 (by omega) hhi

end Erdos686.Erdos686Variant
