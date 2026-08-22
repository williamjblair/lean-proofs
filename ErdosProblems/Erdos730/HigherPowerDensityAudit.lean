/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/
import ErdosProblems.Erdos730.HigherPowerDensity

open Filter Topology

namespace Erdos730.HigherPowerDensityAudit

theorem audit_geometric_sum :
    Tendsto (fun X ↦ ∑' i : HigherPowerIndex, higherPowerEnvelope X i)
      Filter.atTop (nhds 0) :=
  tendsto_tsum_higherPowerEnvelope_zero

theorem audit_terminal_payments :
    Tendsto (fun X : ℕ ↦
      ((higherPrimePowerPairs (higherPowerBranchHeight * X)).card : ℝ) /
        (X : ℝ)) Filter.atTop (nhds 0) :=
  tendsto_higherPrimePowerPairs_scaled_card_div

#print axioms audit_geometric_sum
#print axioms audit_terminal_payments

end Erdos730.HigherPowerDensityAudit
