import Mathlib

/-!
# Erdős Problem 254: canonical formal statement

This file contains only the definitions and the proposition to be proved.  The
independent verification gate in `check_answer/verify.sh` requires this file to
be byte-for-byte identical to `check_answer/Statement.lean`.
-/

namespace Erdos254

open Filter
open scoped BigOperators

noncomputable section

/-- Distance from a real number to the nearest integer.  Since
`Int.fract x ∈ [0,1)`, the two candidates are the floor and the next integer. -/
def nearestIntegerDistance (x : ℝ) : ℝ :=
  min (Int.fract x) (1 - Int.fract x)

/-- Number of members of `A` in the integer interval `[1,x]`. -/
def countingFunction (A : Set ℕ) (x : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 x).filter (fun n => n ∈ A)).card

/-- The cardinality difference in the first hypothesis. -/
def dyadicIncrement (A : Set ℕ) (x : ℕ) : ℕ :=
  countingFunction A (2 * x) - countingFunction A x

/-- Partial sums, in the natural order, of the nonnegative series appearing in
Problem 254. -/
def phasePartialSum (A : Set ℕ) (θ : ℝ) (N : ℕ) : ℝ := by
  classical
  exact ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n ∈ A),
    nearestIntegerDistance (θ * (n : ℝ))

/-- Every sufficiently large natural number is a sum of distinct members of
`A`; distinctness is encoded by the use of a `Finset`. -/
def IsComplete (A : Set ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ m : ℕ, N₀ ≤ m →
    ∃ s : Finset ℕ, (↑s : Set ℕ) ⊆ A ∧ ∑ n ∈ s, n = m

/-- Faithful formalization of Erdős Problem 254. -/
def Statement : Prop :=
  ∀ A : Set ℕ,
    Tendsto (dyadicIncrement A) (atTop : Filter ℕ) atTop →
    (∀ θ : ℝ, θ ∈ Set.Ioo 0 1 →
      Tendsto (phasePartialSum A θ) atTop atTop) →
    IsComplete A

end

end Erdos254
