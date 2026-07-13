/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos730HigherPowerCount

/-!
# Audit for the Erdős 730 finite higher-power count

This module checks the two boundary surfaces most likely to hide an indexing
error: an all-allowed interval modulo one, and the p-adic block theorem at
depth zero.  The final commands expose the kernel axiom dependencies.
-/

namespace Erdos730

/-- Modulo one, an all-allowed predicate counts every offset. -/
example (start N : ℕ) :
    intervalResidueCount 1 start N (fun _ ↦ True) = N := by
  simp [intervalResidueCount]

/-- The complete/padded block theorem specializes without an `r ≥ 1`
side condition. -/
example {p start N H : ℕ} (hp : p.Prime)
    (q u v : ZMod (p ^ 0)) {b : ZMod (p ^ 0)} (hb : IsUnit b)
    (A : Finset (ZMod (p ^ 0))) (hA : A.card = H ^ 0) :
    padicBranchAllowedCount p 0 start N q u b v A ≤
      (N / p ^ 0 + 1) * H ^ 0 :=
  padicBranchAllowedCount_le hp q u v hb A hA

#print axioms intervalResidueCount_le
#print axioms interval_bijective_preimage_count_le
#print axioms padicBranchAllowedCount_le
#print axioms padicBranchAllowedCount_le_of_length
#print axioms cubeRootFloor_pow_le
#print axioms mem_higherPrimePowerPairs_iff
#print axioms higherPrimePowerPairs_subset_boxes
#print axioms higherPrimePowerPairs_card_le

end Erdos730
