/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos730HigherPowerDecay

/-!
# Audit for the Erdős 730 fixed-prime-power depth decay

The finite checks pin the first higher exponent and the depth-zero boundary;
the final commands expose the kernel dependency surface.
-/

namespace Erdos730

example : higherPowerDepth 5 2 24 = 0 := by
  norm_num [higherPowerDepth, Nat.log]

example : higherPowerDepth 5 2 125 = 1 := by
  norm_num [higherPowerDepth, Nat.log]

#print axioms tendsto_higherPowerDepth_atTop
#print axioms tendsto_pow_higherPowerDepth_zero
#print axioms higherPowerRho_lt_one
#print axioms tendsto_higherPower_normalizedTerm_zero

end Erdos730
