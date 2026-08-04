import Mathlib

/-!
# Erdős Problem 123 — definitions

The webpage literally writes `a,b,c ≥ 1`, but that version is false at
`(a,b,c)=(1,1,1)`. `IntendedStatement` pins down the nondegenerate open
question, with all three bases greater than one, as in the Formal Conjectures
formalization. `LiteralStatement` is retained so that the wording discrepancy
cannot be used to claim a spurious solution of the intended problem.
-/

namespace Erdos123

/-- The positive integers representable as `a^k b^l c^m` with natural exponents. -/
def Smooth3 (a b c : ℕ) : Set ℕ :=
  {x | ∃ k l m : ℕ, x = a ^ k * b ^ l * c ^ m}

/-- No two distinct members of `s` are comparable in the divisibility order. -/
def IsPrimitive (s : Finset ℕ) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → x ≠ y → ¬x ∣ y

/-- One target has a primitive representation using terms of `A`. -/
def IsRepresentable (A : Set ℕ) (n : ℕ) : Prop :=
  ∃ s : Finset ℕ, (∀ x ∈ s, x ∈ A) ∧ IsPrimitive s ∧ s.sum id = n

/-- Every sufficiently large natural number is the sum of a finite primitive
set of distinct members of `A`. Distinctness is built into `Finset`. -/
def IsDComplete (A : Set ℕ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ s : Finset ℕ,
      (∀ x ∈ s, x ∈ A) ∧ IsPrimitive s ∧ s.sum id = n

/-- Pairwise coprimality of three bases. -/
def PairwiseCoprime3 (a b c : ℕ) : Prop :=
  Nat.Coprime a b ∧ Nat.Coprime a c ∧ Nat.Coprime b c

/-- The displayed webpage statement read literally, including degenerate bases. -/
def LiteralStatement : Prop :=
  ∀ a b c : ℕ, 1 ≤ a → 1 ≤ b → 1 ≤ c → PairwiseCoprime3 a b c →
    IsDComplete (Smooth3 a b c)

/-- The intended nondegenerate Erdős Problem 123. -/
def IntendedStatement : Prop :=
  ∀ a b c : ℕ, 1 < a → 1 < b → 1 < c → PairwiseCoprime3 a b c →
    IsDComplete (Smooth3 a b c)

end Erdos123
