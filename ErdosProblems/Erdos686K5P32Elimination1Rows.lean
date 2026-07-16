/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686K5P32Elimination1Row0
import ErdosProblems.Erdos686K5P32Elimination1Row1
import ErdosProblems.Erdos686K5P32Elimination1Row2
import ErdosProblems.Erdos686K5P32Elimination1Row3
import ErdosProblems.Erdos686K5P32Elimination1Row4
import ErdosProblems.Erdos686K5P32Elimination1Row5
import ErdosProblems.Erdos686K5P32Elimination1Row6
import ErdosProblems.Erdos686K5P32Elimination1Row7
import ErdosProblems.Erdos686K5P32Elimination1Row8

namespace Erdos686
namespace Erdos686Variant

theorem k5P32EliminationDifference1_length :
    k5P32EliminationDifference1.length = 9 := by
  decide +kernel

theorem k5P32EliminationDifference1_rows :
    DenseBivariateRowsCertificate k5P32EliminationDifference1 := by
  intro rowIndex hindex
  rw [k5P32EliminationDifference1_length] at hindex
  interval_cases rowIndex
  · exact k5P32EliminationDifference1_row0
  · exact k5P32EliminationDifference1_row1
  · exact k5P32EliminationDifference1_row2
  · exact k5P32EliminationDifference1_row3
  · exact k5P32EliminationDifference1_row4
  · exact k5P32EliminationDifference1_row5
  · exact k5P32EliminationDifference1_row6
  · exact k5P32EliminationDifference1_row7
  · exact k5P32EliminationDifference1_row8

theorem k5P32EliminationIdentity1 :
    denseBivariateIsZero
      (denseBivariateSub
        (denseBivariateAdd
          (denseBivariateMul k5P32SectionCofactor1
            k5P32Section1Dense)
          (denseBivariateMul k5P32CurveCofactor1
            k5P32CurveDense))
        [k5P32Resultant1]) := by
  change denseBivariateIsZero k5P32EliminationDifference1
  exact denseBivariateIsZero_of_rows k5P32EliminationDifference1_rows

end Erdos686Variant
end Erdos686
