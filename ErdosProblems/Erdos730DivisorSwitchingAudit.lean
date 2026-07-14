/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos730DivisorSwitching

/-!
# Erdős 730 top-range divisor switching: kernel audit

The audit checks the actual local digit classifications, exact finite switch,
unconditional PNT-AP/Abel bridge, eventual cutoff, and final RangeAssembly
boundedness and limsup theorem.
-/

open Filter
open scoped Topology

namespace Erdos730.DivisorSwitching

#print axioms P_top_local_classification
#print axioms Q_top_local_impossible
#print axioms R_top_local_classification
#print axioms S_top_local_impossible

#print axioms topWitnesses_card_le_allowed_sums
#print axioms reciprocalPrimeAPSumReal_eq_count_div_add_integral
#print axioms eventually_reciprocalPrimeAPTopBand_le
#print axioms eventually_topCutoffHypothesis

#print axioms normalizedTopPrimeWitnessCount_isBoundedUnder
#print axioms limsup_normalizedTopPrimeWitnessCount_le

end Erdos730.DivisorSwitching
