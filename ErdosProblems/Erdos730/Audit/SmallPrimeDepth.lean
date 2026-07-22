/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos730.SmallPrimeDepth

/-! Independent audit surface for the exact small-prime depth partition. -/

namespace Erdos730.SmallPrimeDepthAudit

open Erdos730 Erdos730.BranchEvents Erdos730.RangeAssembly
  Erdos730.SmallPrimeDepth

example : smallPrimeDepth 5 125 = 2 := by
  norm_num [smallPrimeDepth, Nat.log]

theorem boundary_power_band
    {p X : ℕ} (hp : p.Prime) (hX : 0 < X)
    (hpSmall : p ≤ Nat.sqrt X) :
    1 ≤ smallPrimeDepth p X ∧
      p ^ (smallPrimeDepth p X + 1) ≤ X ∧
      X < p ^ (smallPrimeDepth p X + 2) :=
  smallPrimeDepth_spec hp hX hpSmall

theorem exposed_normalized_partition (X R : ℕ) :
    normalizedSmallPrimeWitnessCount X ≤
      (∑ r ∈ Finset.range R, normalizedSmallPrimeDepthWitnessCount r X) +
        normalizedSmallPrimeDepthTailWitnessCount R X :=
  normalizedSmallPrimeWitnessCount_le_depth_sum_add_tail X R

#print axioms boundary_power_band
#print axioms exposed_normalized_partition

end Erdos730.SmallPrimeDepthAudit
