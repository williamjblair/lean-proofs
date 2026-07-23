import Mathlib

namespace Erdos489

open Classical Filter
open scoped Topology BigOperators

/-- Positive natural numbers divisible by no member of `A`. -/
def sievedSet (A : Set ℕ) : Set ℕ :=
  {n : ℕ | 0 < n ∧ ∀ a ∈ A, ¬ a ∣ n}

/-- The sum of squared successive gaps whose left endpoint is below `x`. -/
noncomputable def gapSumSq (A : Set ℕ) (x : ℕ) : ℝ :=
  let B := sievedSet A
  let b := Nat.nth (· ∈ B)
  ∑ i ∈ Finset.range (Nat.count (· ∈ B) x),
    ((b (i + 1) : ℝ) - (b i : ℝ)) ^ 2

end Erdos489
