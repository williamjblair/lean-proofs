/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.K5.P11.P11Endpoint
import ErdosProblems.Erdos686.K5.P12.P12Endpoint
import ErdosProblems.Erdos686.K5.P13.P13Endpoint
import ErdosProblems.Erdos686.K5.P14.P14Endpoint
import ErdosProblems.Erdos686.K5.P15.P15Endpoint
import ErdosProblems.Erdos686.K5.P21.P21Endpoint
import ErdosProblems.Erdos686.K5.P22.P22Endpoint
import ErdosProblems.Erdos686.K5.P23.P23Endpoint
import ErdosProblems.Erdos686.K5.P24.P24Endpoint
import ErdosProblems.Erdos686.K5.P25.P25Endpoint
import ErdosProblems.Erdos686.K5.P31.P31Endpoint
import ErdosProblems.Erdos686.K5.P32.P32Endpoint
import ErdosProblems.Erdos686.K5.P33.P33Endpoint
import ErdosProblems.Erdos686.K5.P34.P34Endpoint
import ErdosProblems.Erdos686.K5.P35.P35Endpoint
import ErdosProblems.Erdos686.K5.P41.P41Endpoint
import ErdosProblems.Erdos686.K5.P42.P42Endpoint
import ErdosProblems.Erdos686.K5.P43.P43Endpoint
import ErdosProblems.Erdos686.K5.P44.P44Endpoint
import ErdosProblems.Erdos686.K5.P45.P45Endpoint
import ErdosProblems.Erdos686.K5.P51.P51Endpoint
import ErdosProblems.Erdos686.K5.P52.P52Endpoint
import ErdosProblems.Erdos686.K5.P53.P53Endpoint
import ErdosProblems.Erdos686.K5.P54.P54Endpoint
import ErdosProblems.Erdos686.K5.P55.P55Endpoint

/-!
# Erdős 686: all k=5 proper-support puncture witnesses
-/

namespace Erdos686
namespace Erdos686Variant

theorem exists_k5_punctureJetWitness
    {n d t j i : ℕ}
    (data : CanonicalOwnerData 5 n d t)
    (hfour : 4 ∣ n + d + t)
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n)
    (hj : j ∈ Finset.Icc 1 5)
    (hi : i ∈ Finset.Icc 1 5) :
    Nonempty (K5PunctureJetWitness data j i) := by
  rcases Finset.mem_Icc.mp hj with ⟨hjlow, hjhigh⟩
  rcases Finset.mem_Icc.mp hi with ⟨hilow, hihigh⟩
  interval_cases j <;> interval_cases i
  · exact exists_k5P11PunctureJetWitness data hfour heq
  · exact exists_k5P12PunctureJetWitness data hfour heq
  · exact exists_k5P13PunctureJetWitness data hfour heq
  · exact exists_k5P14PunctureJetWitness data hfour heq
  · exact exists_k5P15PunctureJetWitness data hfour heq
  · exact exists_k5P21PunctureJetWitness data hfour heq
  · exact exists_k5P22PunctureJetWitness data hfour heq
  · exact exists_k5P23PunctureJetWitness data hfour heq
  · exact exists_k5P24PunctureJetWitness data hfour heq
  · exact exists_k5P25PunctureJetWitness data hfour heq
  · exact exists_k5P31PunctureJetWitness data hfour heq
  · exact exists_k5P32PunctureJetWitness data hfour heq
  · exact exists_k5P33PunctureJetWitness data hfour heq
  · exact exists_k5P34PunctureJetWitness data hfour heq
  · exact exists_k5P35PunctureJetWitness data hfour heq
  · exact exists_k5P41PunctureJetWitness data hfour heq
  · exact exists_k5P42PunctureJetWitness data hfour heq
  · exact exists_k5P43PunctureJetWitness data hfour heq
  · exact exists_k5P44PunctureJetWitness data hfour heq
  · exact exists_k5P45PunctureJetWitness data hfour heq
  · exact exists_k5P51PunctureJetWitness data hfour heq
  · exact exists_k5P52PunctureJetWitness data hfour heq
  · exact exists_k5P53PunctureJetWitness data hfour heq
  · exact exists_k5P54PunctureJetWitness data hfour heq
  · exact exists_k5P55PunctureJetWitness data hfour heq

theorem no_k5_tail_solution_of_proper_support
    {n d t : ℕ}
    (data : CanonicalOwnerData 5 n d t)
    (hfour : 4 ∣ n + d + t)
    (htail : 10 ^ 1000 ≤ d)
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n)
    (hproper :
      ∃ j₀, j₀ ∈ Finset.Icc 1 5 ∧
        ∃ i₀, i₀ ∈ Finset.Icc 1 5 ∧
          canonicalOwnerCell data j₀ i₀ = 1) :
    False :=
  no_k5_tail_solution_of_proper_canonical_support
    data htail heq hproper
      (fun j hj i hi _ =>
        exists_k5_punctureJetWitness data hfour heq hj hi)

end Erdos686Variant
end Erdos686
