import ErdosProblems.Erdos686.EvenK.K18.CandidateCoverS44
import ErdosProblems.Erdos686.EvenK.K18.CandidateCoverS45
import ErdosProblems.Erdos686.EvenK.K18.CandidateCoverS46
import ErdosProblems.Erdos686.EvenK.K18.CandidateCoverS47
import ErdosProblems.Erdos686.EvenK.K18.CandidateCoverS48
import ErdosProblems.Erdos686.EvenK.K18.CandidateCoverS49
import ErdosProblems.Erdos686.EvenK.K18.CandidateCoverS50
import ErdosProblems.Erdos686.EvenK.K18.CandidateCoverS51
import ErdosProblems.Erdos686.EvenK.K18.CandidateCoverS52
import ErdosProblems.Erdos686.EvenK.K18.CandidateCoverS53
import ErdosProblems.Erdos686.EvenK.K18.CandidateCoverS54
namespace Erdos686.Erdos686Variant

theorem even18_q_cover_group_4 (q : ℕ)
    (hlo : 90112 ≤ q) (hhi : q < 112640) : even18QCovered q := by
  by_cases h44 : q < 92160
  · exact even18ScanPow_get even18_candidate_cover_scan_44 (by omega) h44
  by_cases h45 : q < 94208
  · exact even18ScanPow_get even18_candidate_cover_scan_45 (by omega) h45
  by_cases h46 : q < 96256
  · exact even18ScanPow_get even18_candidate_cover_scan_46 (by omega) h46
  by_cases h47 : q < 98304
  · exact even18ScanPow_get even18_candidate_cover_scan_47 (by omega) h47
  by_cases h48 : q < 100352
  · exact even18ScanPow_get even18_candidate_cover_scan_48 (by omega) h48
  by_cases h49 : q < 102400
  · exact even18ScanPow_get even18_candidate_cover_scan_49 (by omega) h49
  by_cases h50 : q < 104448
  · exact even18ScanPow_get even18_candidate_cover_scan_50 (by omega) h50
  by_cases h51 : q < 106496
  · exact even18ScanPow_get even18_candidate_cover_scan_51 (by omega) h51
  by_cases h52 : q < 108544
  · exact even18ScanPow_get even18_candidate_cover_scan_52 (by omega) h52
  by_cases h53 : q < 110592
  · exact even18ScanPow_get even18_candidate_cover_scan_53 (by omega) h53
  · exact even18ScanPow_get even18_candidate_cover_scan_54 (by omega) hhi

end Erdos686.Erdos686Variant
