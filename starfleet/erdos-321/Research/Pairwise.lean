import Research.Basic

namespace Erdos321

/-- The tempting pairwise surrogate used in OEIS A384927: the sum of the
reciprocals of no two distinct members is itself a unit fraction. -/
def PairwiseUnitSumFree (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ¬(a + b ∣ a * b)

/-- A 16-element counterexample at `N=21` to the sufficiency of the pairwise
surrogate. -/
def pairwiseCounterexample : Finset ℕ :=
  {1, 2, 3, 4, 7, 8, 9, 10, 11, 13, 14, 16, 17, 19, 20, 21}

theorem pairwiseCounterexample_card : pairwiseCounterexample.card = 16 := by
  native_decide

theorem pairwiseCounterexample_subset : pairwiseCounterexample ⊆ Finset.Icc 1 21 := by
  native_decide

theorem pairwiseCounterexample_passes :
    PairwiseUnitSumFree pairwiseCounterexample := by
  norm_num [PairwiseUnitSumFree, pairwiseCounterexample]

/-- Despite passing every two-denominator test, the concrete set is invalid
because `1 + 1/21 = 1/2 + 1/3 + 1/7 + 1/14`. -/
theorem pairwiseCounterexample_not_valid : ¬ Valid pairwiseCounterexample := by
  intro hValid
  have hLeft : ({1, 21} : Finset ℕ) ∈ pairwiseCounterexample.powerset := by
    native_decide
  have hRight : ({2, 3, 7, 14} : Finset ℕ) ∈ pairwiseCounterexample.powerset := by
    native_decide
  have hEq : reciprocalSubsetSum {1, 21} =
      reciprocalSubsetSum {2, 3, 7, 14} := by
    norm_num [reciprocalSubsetSum]
  have hSets : ({1, 21} : Finset ℕ) = {2, 3, 7, 14} :=
    hValid {1, 21} hLeft {2, 3, 7, 14} hRight hEq
  have : (1 : ℕ) ∈ ({2, 3, 7, 14} : Finset ℕ) := by
    rw [← hSets]
    simp
  norm_num at this

end Erdos321
