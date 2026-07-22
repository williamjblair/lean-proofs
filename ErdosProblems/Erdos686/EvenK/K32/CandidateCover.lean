import ErdosProblems.Erdos686.EvenK.K32.CandidateLogic
namespace Erdos686.Erdos686Variant

theorem even32_candidate_cover (t : ℕ) (htpos : 1 ≤ t)
    (htbound : t ≤ 431188) : even32CandidateAllowed t = false :=
  even32_candidate_cover_of_qcover even32_q_cover t htpos htbound

end Erdos686.Erdos686Variant
