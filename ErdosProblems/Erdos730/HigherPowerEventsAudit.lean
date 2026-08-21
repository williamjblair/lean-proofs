/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos730.HigherPowerEvents

/-!
# Kernel audit for the concrete Erdős 730 higher-power event bridge

This surface exposes the exact dependency chain from the root congruence and
equation (16), through the depth-zero-safe finite block count and terminal
root payment, to the global witness ledger and its unconditional limit.
-/

open Filter Topology

namespace Erdos730.HigherPowerEventsAudit

open Erdos730 Erdos730.HigherPowerEvents

theorem audit_requested_limit :
    Tendsto Erdos730.RangeAssembly.normalizedHigherPowerWitnessCount
      atTop (nhds 0) :=
  tendsto_normalizedHigherPowerWitnessCount_zero

#print axioms branchTestValue_root_progression
#print axioms branchTestValue_eq_padicBranchMap
#print axioms localHigherPowerFiber_card_le_block
#print axioms localHigherPowerFiber_card_le_one_of_lt
#print axioms localHigherPowerFiber_normalized_le_pair_payment
#print axioms localHigherPowerWitnesses_card_le_keys
#print axioms normalizedHigherPowerWitnessCount_le_majorant
#print axioms audit_requested_limit

end Erdos730.HigherPowerEventsAudit
