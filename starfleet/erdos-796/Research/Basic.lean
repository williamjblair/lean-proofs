import Mathlib

/-!
# Erdős Problem 796: formal statement

This file fixes an exact finite definition of `g_k(n)` and the asymptotic
proposition asked in the problem.  It deliberately contains no claimed proof.
A solution must prove either `Erdos796.Statement` or its negation, without new
axioms or placeholders.
-/

namespace Erdos796

/-- The number of unordered representations `m = a₁ a₂` by two *distinct*
elements of `A`.  Requiring `a₁ < a₂` chooses exactly one ordering. -/
def repCount (A : Finset ℕ) (m : ℕ) : ℕ :=
  ((A ×ˢ A).filter fun a => a.1 < a.2 ∧ a.1 * a.2 = m).card

/-- `A` has fewer than `k` permitted representations of every natural number. -/
def HasRepBound (k : ℕ) (A : Finset ℕ) : Prop :=
  ∀ m : ℕ, repCount A m < k

/-- The exact extremal function in the problem.  `powerset (Icc 1 n)` is the
finite collection of all subsets of `{1, …, n}`, and `sup card` takes the
largest cardinality among the admissible subsets. -/
noncomputable def g (k n : ℕ) : ℕ := by
  classical
  exact (((Finset.Icc 1 n).powerset.filter (HasRepBound k)).sup fun A => A.card)

/-- The residual after subtracting the displayed leading term, normalized by
`n / log n`.  Its limit is the proposed second-order constant. -/
noncomputable def normalizedError (n : ℕ) : ℝ :=
  ((g 3 n : ℝ) - (n : ℝ) * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)) /
    ((n : ℝ) / Real.log (n : ℝ))

/-- A faithful formalization of the affirmative answer to Erdős Problem 796. -/
def Statement : Prop :=
  ∃ c : ℝ, Filter.Tendsto normalizedError Filter.atTop (nhds c)

#check Statement

end Erdos796
