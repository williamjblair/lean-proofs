/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.K5.P23.P23Elimination0Row0
import ErdosProblems.Erdos686.K5.P23.P23Elimination0Row1
import ErdosProblems.Erdos686.K5.P23.P23Elimination0Row2
import ErdosProblems.Erdos686.K5.P23.P23Elimination0Row3
import ErdosProblems.Erdos686.K5.P23.P23Elimination0Row4
import ErdosProblems.Erdos686.K5.P23.P23Elimination0Row5
import ErdosProblems.Erdos686.K5.P23.P23Elimination0Row6
import ErdosProblems.Erdos686.K5.P23.P23Elimination0Row7
import ErdosProblems.Erdos686.K5.P23.P23Elimination0Row8

namespace Erdos686
namespace Erdos686Variant

theorem k5P23EliminationDifference0_length :
    k5P23EliminationDifference0.length = 9 := by
  decide +kernel

theorem k5P23EliminationDifference0_rows :
    DenseBivariateRowsCertificate k5P23EliminationDifference0 := by
  intro rowIndex hindex
  rw [k5P23EliminationDifference0_length] at hindex
  interval_cases rowIndex
  · exact k5P23EliminationDifference0_row0
  · exact k5P23EliminationDifference0_row1
  · exact k5P23EliminationDifference0_row2
  · exact k5P23EliminationDifference0_row3
  · exact k5P23EliminationDifference0_row4
  · exact k5P23EliminationDifference0_row5
  · exact k5P23EliminationDifference0_row6
  · exact k5P23EliminationDifference0_row7
  · exact k5P23EliminationDifference0_row8

theorem k5P23EliminationIdentity0 :
    denseBivariateIsZero
      (denseBivariateSub
        (denseBivariateAdd
          (denseBivariateMul k5P23SectionCofactor0
            k5P23Section0Dense)
          (denseBivariateMul k5P23CurveCofactor0
            k5P23CurveDense))
        [k5P23Resultant0]) := by
  change denseBivariateIsZero k5P23EliminationDifference0
  exact denseBivariateIsZero_of_rows k5P23EliminationDifference0_rows

end Erdos686Variant
end Erdos686
