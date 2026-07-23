import Mathlib

/-!
# Erdős Problem 450: a precise uniform-in-`x` formulation

The 1980 source asks how large `y = y(ε,n)` must be so that the number of
integers in `(x,x+y)` having a divisor in `(n,2n)` is at most `ε y`.  The
source does not write a quantifier on `x`; this file pins down the natural
uniform interpretation `∀ x : ℕ`.  The definitions are intentionally exact:
both intervals are open and the right side is the real number `ε * y`.

Because the published problem is an interrogative rather than a proposition,
`IsSufficientScale Y` is the proposition to prove for any proposed quantitative
answer `Y`.  Lower-bound/optimality claims should be stated separately in terms
of `UniformlySparse`.
-/

namespace Erdos450

/-- `m` has a positive natural-number divisor strictly between `n` and `2n`. -/
def HasMediumDivisor (n m : ℕ) : Prop :=
  ∃ d : ℕ, n < d ∧ d < 2 * n ∧ d ∣ m

/-- The integers strictly between `x` and `x+y` that have a divisor in
`(n,2n)`. -/
noncomputable def badIntegers (n x y : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ioo x (x + y)).filter (HasMediumDivisor n)

/-- The exact number of such integers in the open interval `(x,x+y)`. -/
noncomputable def localCount (n x y : ℕ) : ℕ :=
  (badIntegers n x y).card

/-- The requested inequality for one length `y`, uniformly over every
nonnegative integral translate `x`. -/
def UniformlySparse (ε : ℝ) (n y : ℕ) : Prop :=
  ∀ x : ℕ, (localCount n x y : ℝ) ≤ ε * (y : ℝ)

/-- The uniform specification unfolds to the source's exact cardinality
inequality.  This small theorem is the machine-checkable pin for the verifier. -/
theorem uniformlySparse_iff (ε : ℝ) (n y : ℕ) :
    UniformlySparse ε n y ↔
      ∀ x : ℕ, ((badIntegers n x y).card : ℝ) ≤ ε * (y : ℝ) := by
  rfl

/-- A function `Y(ε,n)` is a sufficient asymptotic scale if, for every fixed
positive `ε`, all sufficiently large `n` and every integral length
`y ≥ Y(ε,n)` satisfy the requested estimate uniformly in `x`.

This formalizes the conventional meaning of "how large must `y` be" as a
sufficient threshold.  A sharp answer additionally needs a matching theorem
showing that smaller scales fail. -/
def IsSufficientScale (Y : ℝ → ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ y : ℕ, Y ε n ≤ y → UniformlySparse ε n y

/-- The exact-length version, retained because the original wording can also be
read as asking only for one selected length rather than every larger length. -/
def IsSelectedLengthAnswer (Y : ℝ → ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → UniformlySparse ε n (Y ε n)

end Erdos450
