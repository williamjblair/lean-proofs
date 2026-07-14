/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos730SmallPrimeEvents

/-!
# Kernel audit for the concrete Erdős 730 small-prime event bridge

This surface exposes the dependency chain from the branch root progression,
through the fixed-depth quadratic Fourier count and the uniform depth tail,
to the final four-branch small-prime limsup estimate.
-/

open Filter
open scoped Topology

namespace Erdos730.SmallPrimeEventsAudit

open Erdos730
open Erdos730.FixedDepthDensity Erdos730.RangeAssembly
open Erdos730.SmallPrimeDepth Erdos730.SmallPrimeEvents

theorem audit_global_smallPrime_limsup :
    limsup normalizedSmallPrimeWitnessCount atTop ≤
      4 * densityBudgetSeries :=
  limsup_normalizedSmallPrimeWitnessCount_le

#print axioms card_filter_range_cast_le_completeBlocks_add_terminal
#print axioms prime_not_dvd_fixedDepthNaturalBeta
#print axioms padicBranchMap_eq_fixedDepthQuadratic
#print axioms localSmallPrimeFiber_card_cast_le_fixedDepthRaw
#print axioms localSmallPrimeFiber_normalized_le_fixedDepth
#print axioms eventually_normalizedSmallPrimeDepthWitnessCount_le_majorant
#print axioms normalizedSmallPrimeDepthWitnessCount_isBoundedUnder
#print axioms limsup_normalizedSmallPrimeDepthWitnessCount_le
#print axioms limsup_normalizedSmallPrimeDepthTailWitnessCount_le
#print axioms normalizedSmallPrimeWitnessCount_isBoundedUnder
#print axioms audit_global_smallPrime_limsup

end Erdos730.SmallPrimeEventsAudit
