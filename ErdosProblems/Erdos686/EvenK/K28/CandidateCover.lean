import ErdosProblems.Erdos686.EvenK.K28.CandidateLogic
namespace Erdos686.Erdos686Variant

theorem even28_candidate_cover (t : ℕ) (htpos : 1 ≤ t)
    (htbound : t ≤ 1049958) : even28CandidateAllowed t = false :=
  even28_candidate_cover_of_qcover even28_q_cover t htpos htbound

end Erdos686.Erdos686Variant
