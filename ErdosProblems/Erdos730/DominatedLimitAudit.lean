/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos730.DominatedLimit

/-!
# Audit for the Erdős 730 dominated-limit layer

The examples check the shifted exponent boundary (`k = 0`, hence `a = 2`)
and the zero denominator convention in the finite box ratio.  The final
commands expose all kernel dependencies of the substantive public theorems.
-/

namespace Erdos730

/-- At the first shifted exponent the majorant is exactly `2 / p^2`. -/
example (p : Nat.Primes) :
    higherPowerMajorant (p, 0) = 2 / (p : ℝ) ^ 2 := by
  simpa using higherPowerMajorant_eq (p, 0)

/-- The normalized box bound is well-defined at `Z = 0` and equals zero. -/
example :
    (((Nat.sqrt 0 + cubeRootFloor 0 * Nat.log 2 0 : ℕ) : ℝ) / (0 : ℝ)) = 0 := by
  norm_num [cubeRootFloor]

#print axioms higherPowerMajorant_eq
#print axioms higherPowerMajorant_summable
#print axioms tendsto_tsum_higherPower_of_dominated
#print axioms tendsto_iterated_tsum_higherPower_of_dominated
#print axioms tendsto_rpow_third_mul_logb_div_atTop
#print axioms cubeRootFloor_cast_le_rpow
#print axioms tendsto_higherPrimePower_boxBound_div
#print axioms tendsto_higherPrimePowerPairs_card_div

end Erdos730
