import ErdosProblems.Erdos686EvenK28CandidateCoverS17
namespace Erdos686.Erdos686Variant

theorem even28_q_cover (q : ℕ) (hq : q < 36206) : even28QCovered q := by
  by_cases h0 : q < 2048
  · exact even28ScanPow_get even28_candidate_cover_scan_0 (by omega) h0
  by_cases h1 : q < 4096
  · exact even28ScanPow_get even28_candidate_cover_scan_1 (by omega) h1
  by_cases h2 : q < 6144
  · exact even28ScanPow_get even28_candidate_cover_scan_2 (by omega) h2
  by_cases h3 : q < 8192
  · exact even28ScanPow_get even28_candidate_cover_scan_3 (by omega) h3
  by_cases h4 : q < 10240
  · exact even28ScanPow_get even28_candidate_cover_scan_4 (by omega) h4
  by_cases h5 : q < 12288
  · exact even28ScanPow_get even28_candidate_cover_scan_5 (by omega) h5
  by_cases h6 : q < 14336
  · exact even28ScanPow_get even28_candidate_cover_scan_6 (by omega) h6
  by_cases h7 : q < 16384
  · exact even28ScanPow_get even28_candidate_cover_scan_7 (by omega) h7
  by_cases h8 : q < 18432
  · exact even28ScanPow_get even28_candidate_cover_scan_8 (by omega) h8
  by_cases h9 : q < 20480
  · exact even28ScanPow_get even28_candidate_cover_scan_9 (by omega) h9
  by_cases h10 : q < 22528
  · exact even28ScanPow_get even28_candidate_cover_scan_10 (by omega) h10
  by_cases h11 : q < 24576
  · exact even28ScanPow_get even28_candidate_cover_scan_11 (by omega) h11
  by_cases h12 : q < 26624
  · exact even28ScanPow_get even28_candidate_cover_scan_12 (by omega) h12
  by_cases h13 : q < 28672
  · exact even28ScanPow_get even28_candidate_cover_scan_13 (by omega) h13
  by_cases h14 : q < 30720
  · exact even28ScanPow_get even28_candidate_cover_scan_14 (by omega) h14
  by_cases h15 : q < 32768
  · exact even28ScanPow_get even28_candidate_cover_scan_15 (by omega) h15
  by_cases h16 : q < 34816
  · exact even28ScanPow_get even28_candidate_cover_scan_16 (by omega) h16
  · exact even28ScanPow_get even28_candidate_cover_scan_17 (by omega) (by omega)
end Erdos686.Erdos686Variant
