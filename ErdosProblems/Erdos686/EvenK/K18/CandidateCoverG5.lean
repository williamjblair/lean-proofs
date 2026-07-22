import ErdosProblems.Erdos686.EvenK.K18.CandidateCoverS55
import ErdosProblems.Erdos686.EvenK.K18.CandidateCoverS56
import ErdosProblems.Erdos686.EvenK.K18.CandidateCoverS57
import ErdosProblems.Erdos686.EvenK.K18.CandidateCoverS58
import ErdosProblems.Erdos686.EvenK.K18.CandidateCoverS59
import ErdosProblems.Erdos686.EvenK.K18.CandidateCoverS60
import ErdosProblems.Erdos686.EvenK.K18.CandidateCoverS61
import ErdosProblems.Erdos686.EvenK.K18.CandidateCoverS62
import ErdosProblems.Erdos686.EvenK.K18.CandidateCoverS63
import ErdosProblems.Erdos686.EvenK.K18.CandidateCoverS64
import ErdosProblems.Erdos686.EvenK.K18.CandidateCoverS65
namespace Erdos686.Erdos686Variant

theorem even18_q_cover_group_5 (q : ℕ)
    (hlo : 112640 ≤ q) (hhi : q < 135168) : even18QCovered q := by
  by_cases h55 : q < 114688
  · exact even18ScanPow_get even18_candidate_cover_scan_55 (by omega) h55
  by_cases h56 : q < 116736
  · exact even18ScanPow_get even18_candidate_cover_scan_56 (by omega) h56
  by_cases h57 : q < 118784
  · exact even18ScanPow_get even18_candidate_cover_scan_57 (by omega) h57
  by_cases h58 : q < 120832
  · exact even18ScanPow_get even18_candidate_cover_scan_58 (by omega) h58
  by_cases h59 : q < 122880
  · exact even18ScanPow_get even18_candidate_cover_scan_59 (by omega) h59
  by_cases h60 : q < 124928
  · exact even18ScanPow_get even18_candidate_cover_scan_60 (by omega) h60
  by_cases h61 : q < 126976
  · exact even18ScanPow_get even18_candidate_cover_scan_61 (by omega) h61
  by_cases h62 : q < 129024
  · exact even18ScanPow_get even18_candidate_cover_scan_62 (by omega) h62
  by_cases h63 : q < 131072
  · exact even18ScanPow_get even18_candidate_cover_scan_63 (by omega) h63
  by_cases h64 : q < 133120
  · exact even18ScanPow_get even18_candidate_cover_scan_64 (by omega) h64
  · exact even18ScanPow_get even18_candidate_cover_scan_65 (by omega) hhi

end Erdos686.Erdos686Variant
