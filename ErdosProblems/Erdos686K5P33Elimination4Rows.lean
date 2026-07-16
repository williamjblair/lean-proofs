/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686K5P33Elimination4Row0
import ErdosProblems.Erdos686K5P33Elimination4Row1
import ErdosProblems.Erdos686K5P33Elimination4Row2
import ErdosProblems.Erdos686K5P33Elimination4Row3
import ErdosProblems.Erdos686K5P33Elimination4Row4
import ErdosProblems.Erdos686K5P33Elimination4Row5
import ErdosProblems.Erdos686K5P33Elimination4Row6
import ErdosProblems.Erdos686K5P33Elimination4Row7
import ErdosProblems.Erdos686K5P33Elimination4Row8

namespace Erdos686
namespace Erdos686Variant

theorem k5P33EliminationDifference4_length :
    k5P33EliminationDifference4.length = 9 := by
  decide +kernel

theorem k5P33EliminationDifference4_rows :
    DenseBivariateRowsCertificate k5P33EliminationDifference4 := by
  intro rowIndex hindex
  rw [k5P33EliminationDifference4_length] at hindex
  interval_cases rowIndex
  · exact k5P33EliminationDifference4_row0
  · exact k5P33EliminationDifference4_row1
  · exact k5P33EliminationDifference4_row2
  · exact k5P33EliminationDifference4_row3
  · exact k5P33EliminationDifference4_row4
  · exact k5P33EliminationDifference4_row5
  · exact k5P33EliminationDifference4_row6
  · exact k5P33EliminationDifference4_row7
  · exact k5P33EliminationDifference4_row8

theorem k5P33EliminationIdentity4 :
    denseBivariateIsZero
      (denseBivariateSub
        (denseBivariateAdd
          (denseBivariateMul k5P33SectionCofactor4
            k5P33Section4Dense)
          (denseBivariateMul k5P33CurveCofactor4
            k5P33CurveDense))
        [k5P33Resultant4]) := by
  change denseBivariateIsZero k5P33EliminationDifference4
  exact denseBivariateIsZero_of_rows k5P33EliminationDifference4_rows

end Erdos686Variant
end Erdos686
