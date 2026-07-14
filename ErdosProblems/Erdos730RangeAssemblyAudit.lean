/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos730RangeAssembly

/-!
# Hostile audit surface for the Erdős 730 four-range assembly

The statements below expose both the exact finite union bound and every
analytic hypothesis needed by the final topology step.  In particular, no
generic positive-density or bad-density assumption is hidden in this file.
-/

open Filter
open scoped Topology

namespace Erdos730.RangeAssemblyAudit

open Erdos730 Erdos730.DensityAssembly Erdos730.FullDensityCore
  Erdos730.RangeAssembly Erdos730.TransitionDensity

noncomputable section

local instance : DecidablePred GoodParameter :=
  fun _ ↦ Classical.propDecidable _

theorem finite_four_range_ledger
    (X : ℕ) (hcut : Nat.sqrt X ≤ transitionTopCut X) :
    badDensity X ≤ normalizedFourRangeCount X :=
  badDensity_le_normalizedFourRangeCount X hcut

theorem exact_remaining_range_surface
    (hhigher : Tendsto normalizedHigherPowerWitnessCount atTop (𝓝 0))
    (hsmallBdd :
      IsBoundedUnder (· ≤ ·) atTop normalizedSmallPrimeWitnessCount)
    (hsmall : limsup normalizedSmallPrimeWitnessCount atTop ≤
      4 * densityBudgetSeries)
    (htopBdd :
      IsBoundedUnder (· ≤ ·) atTop normalizedTopPrimeWitnessCount)
    (htop : limsup normalizedTopPrimeWitnessCount atTop ≤
      (2 / 3) * Real.log 2) :
    FullDensity.HasCandidatePositiveDensity GoodParameter :=
  hasCandidatePositiveDensity_of_range_estimates
    hhigher hsmallBdd hsmall htopBdd htop

#print axioms finite_four_range_ledger
#print axioms exact_remaining_range_surface

end

end Erdos730.RangeAssemblyAudit
