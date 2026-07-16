/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686K5P33Elimination2Row0
import ErdosProblems.Erdos686K5P33Elimination2Row1
import ErdosProblems.Erdos686K5P33Elimination2Row2
import ErdosProblems.Erdos686K5P33Elimination2Row3
import ErdosProblems.Erdos686K5P33Elimination2Row4
import ErdosProblems.Erdos686K5P33Elimination2Row5
import ErdosProblems.Erdos686K5P33Elimination2Row6
import ErdosProblems.Erdos686K5P33Elimination2Row7
import ErdosProblems.Erdos686K5P33Elimination2Row8

namespace Erdos686
namespace Erdos686Variant

theorem k5P33EliminationDifference2_length :
    k5P33EliminationDifference2.length = 9 := by
  decide +kernel

theorem k5P33EliminationDifference2_rows :
    DenseBivariateRowsCertificate k5P33EliminationDifference2 := by
  intro rowIndex hindex
  rw [k5P33EliminationDifference2_length] at hindex
  interval_cases rowIndex
  · exact k5P33EliminationDifference2_row0
  · exact k5P33EliminationDifference2_row1
  · exact k5P33EliminationDifference2_row2
  · exact k5P33EliminationDifference2_row3
  · exact k5P33EliminationDifference2_row4
  · exact k5P33EliminationDifference2_row5
  · exact k5P33EliminationDifference2_row6
  · exact k5P33EliminationDifference2_row7
  · exact k5P33EliminationDifference2_row8

theorem k5P33EliminationIdentity2 :
    denseBivariateIsZero
      (denseBivariateSub
        (denseBivariateAdd
          (denseBivariateMul k5P33SectionCofactor2
            k5P33Section2Dense)
          (denseBivariateMul k5P33CurveCofactor2
            k5P33CurveDense))
        [k5P33Resultant2]) := by
  change denseBivariateIsZero k5P33EliminationDifference2
  exact denseBivariateIsZero_of_rows k5P33EliminationDifference2_rows

end Erdos686Variant
end Erdos686
