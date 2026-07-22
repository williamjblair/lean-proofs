/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.Core.CFTailBand
import ErdosProblems.Erdos686.Core.FinalReduction

/-!
# Erdős 686: terminal reduction after the `10^1000` tail certificate

The kernel-checked finite band moves the six odd-tail hypothesis from
`10^120` to `10^1000`.  This module states the exact remaining hypothesis and
reconnects it to the existing terminal reduction.  It does not assert the
remaining infinite tail.
-/

namespace Erdos686
namespace Erdos686Variant

/-- Exact odd-tail hypothesis remaining after the new finite certificate. -/
def OddThueTail1000Hypothesis : Prop :=
  ∀ k, k ∈ ({5, 7, 9, 11, 13, 15} : Finset ℕ) →
    NoLargeGapSolutionFour k (10 ^ 1000)

/-- The `10^1000` tails plus the certified intervening band imply the former
`10^120` tail interface used by the terminal theorem. -/
theorem oddThueTailHypothesis_of_tail1000
    (htail1000 : OddThueTail1000Hypothesis) :
    OddThueTailHypothesis := by
  intro k hk n d hd120
  by_cases hd1000 : d < 10 ^ 1000
  · exact no_odd_target_gap_solution_below_e1000 hk hd120 hd1000
  · exact htail1000 k hk n d (Nat.le_of_not_gt hd1000)

/-- Updated terminal reduction with the exact newly remaining odd tails. -/
theorem erdos686_false_of_tail1000_and_smooth
    (htails : OddThueTail1000Hypothesis)
    (hsmooth : LargeKSmoothHypothesis) :
    ¬ ∀ N : ℕ, 2 ≤ N → ∃ k n m : ℕ,
      2 ≤ k ∧ m ≥ n + k ∧
      (N : ℚ) =
        (∏ i ∈ Finset.Icc 1 k, (((m + i : ℕ) : ℚ))) /
          (∏ i ∈ Finset.Icc 1 k, (((n + i : ℕ) : ℚ))) := by
  exact erdos686_false_of_thue_tails_and_smooth
    (oddThueTailHypothesis_of_tail1000 htails) hsmooth

#print axioms oddThueTailHypothesis_of_tail1000
#print axioms erdos686_false_of_tail1000_and_smooth

end Erdos686Variant
end Erdos686
