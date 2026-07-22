/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos730.DensityAssembly

namespace Erdos730.DensityAssemblyAudit

open Filter FullDensityCore DensityAssembly

noncomputable section

local instance : DecidablePred GoodParameter :=
  fun _ ↦ Classical.propDecidable _

theorem audit_final_density_join
    (hbad : limsup badDensity atTop ≤
      4 * densityBudgetSeries + (2 / 3) * Real.log 2) :
    FullDensity.HasCandidatePositiveDensity GoodParameter :=
  hasCandidatePositiveDensity_of_limsup_bad_le hbad

#print axioms audit_final_density_join

end

end Erdos730.DensityAssemblyAudit
