/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686K5P33Elimination3Row0
import ErdosProblems.Erdos686K5P33Elimination3Row1
import ErdosProblems.Erdos686K5P33Elimination3Row2
import ErdosProblems.Erdos686K5P33Elimination3Row3
import ErdosProblems.Erdos686K5P33Elimination3Row4
import ErdosProblems.Erdos686K5P33Elimination3Row5
import ErdosProblems.Erdos686K5P33Elimination3Row6
import ErdosProblems.Erdos686K5P33Elimination3Row7
import ErdosProblems.Erdos686K5P33Elimination3Row8

namespace Erdos686
namespace Erdos686Variant

theorem k5P33EliminationDifference3_length :
    k5P33EliminationDifference3.length = 9 := by
  decide +kernel

theorem k5P33EliminationDifference3_rows :
    DenseBivariateRowsCertificate k5P33EliminationDifference3 := by
  intro rowIndex hindex
  rw [k5P33EliminationDifference3_length] at hindex
  interval_cases rowIndex
  · exact k5P33EliminationDifference3_row0
  · exact k5P33EliminationDifference3_row1
  · exact k5P33EliminationDifference3_row2
  · exact k5P33EliminationDifference3_row3
  · exact k5P33EliminationDifference3_row4
  · exact k5P33EliminationDifference3_row5
  · exact k5P33EliminationDifference3_row6
  · exact k5P33EliminationDifference3_row7
  · exact k5P33EliminationDifference3_row8

theorem k5P33EliminationIdentity3 :
    denseBivariateIsZero
      (denseBivariateSub
        (denseBivariateAdd
          (denseBivariateMul k5P33SectionCofactor3
            k5P33Section3Dense)
          (denseBivariateMul k5P33CurveCofactor3
            k5P33CurveDense))
        [k5P33Resultant3]) := by
  change denseBivariateIsZero k5P33EliminationDifference3
  exact denseBivariateIsZero_of_rows k5P33EliminationDifference3_rows

end Erdos686Variant
end Erdos686
