import ErdosProblems.Erdos686.EvenK.K18.CandidateLogic
import ErdosProblems.Erdos686.EvenK.K18.CandidateCoverG0
import ErdosProblems.Erdos686.EvenK.K18.CandidateCoverG1
import ErdosProblems.Erdos686.EvenK.K18.CandidateCoverG2
import ErdosProblems.Erdos686.EvenK.K18.CandidateCoverG3
import ErdosProblems.Erdos686.EvenK.K18.CandidateCoverG4
import ErdosProblems.Erdos686.EvenK.K18.CandidateCoverG5
import ErdosProblems.Erdos686.EvenK.K18.CandidateCoverG6
namespace Erdos686.Erdos686Variant

/-- Hierarchical ordinary-kernel cover of every possible quotient q. -/
theorem even18_q_cover (q : ℕ) (hq : q < 157420) : even18QCovered q := by
  by_cases h0 : q < 22528
  · exact even18_q_cover_group_0 q (by omega) h0
  by_cases h1 : q < 45056
  · exact even18_q_cover_group_1 q (by omega) h1
  by_cases h2 : q < 67584
  · exact even18_q_cover_group_2 q (by omega) h2
  by_cases h3 : q < 90112
  · exact even18_q_cover_group_3 q (by omega) h3
  by_cases h4 : q < 112640
  · exact even18_q_cover_group_4 q (by omega) h4
  by_cases h5 : q < 135168
  · exact even18_q_cover_group_5 q (by omega) h5
  · exact even18_q_cover_group_6 q (by omega) (by omega)

/-- No positive candidate in the strict large-gap trap satisfies every
prime-field residue condition. -/
theorem even18_candidate_cover (t : ℕ) (htpos : 1 ≤ t)
    (htbound : t ≤ 2990976) : even18CandidateAllowed t = false :=
  even18_candidate_cover_of_qcover even18_q_cover t htpos htbound

end Erdos686.Erdos686Variant
