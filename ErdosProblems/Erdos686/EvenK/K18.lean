/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.EvenK.K18.Core
import ErdosProblems.Erdos686.EvenK.K18.PrimeConditions
import ErdosProblems.Erdos686.EvenK.K18.CandidateCover

/-!
# Erdős 686: unconditional assembly of the even row `k=18`

The algebraic and archimedean reduction is in `Erdos686EvenK18Core`.
This module discharges its two finite interfaces with the sharded
ordinary-kernel prime-field tables and candidate cover.
-/

namespace Erdos686
namespace Erdos686Variant

/-- The row `k=18` has no quotient-four gap solution once `d≥18`. -/
theorem no_gap_solution_four_even_eighteen {n d : ℕ} (hd : 18 ≤ d) :
    blockProduct 18 (n + d) ≠ 4 * blockProduct 18 n :=
  no_gap_solution_four_even_eighteen_of_cert
    (fun hS hm => even18_candidate_allowed_of_centers hS hm)
    even18_candidate_cover hd

#print axioms no_gap_solution_four_even_eighteen

end Erdos686Variant
end Erdos686
