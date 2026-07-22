/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686

/-!
# Erdős 686, k=5: cancellation of the nine-factor window divisor

The complete `G=12` allocation makes the lower five-block divide a
nine-factor diagonal window.  At equation level this does not add an
independent restriction: polynomial division by the monic five-block
equation shows that the same divisibility follows from the equation alone.

The exact quotient has degree four in the gap.  This module records both the
polynomial identity and the resulting unconditional (profile-free) window
divisor, so later arguments do not mistake the aggregate allocation for a
new modular constraint.
-/

namespace Erdos686
namespace Erdos686Variant

/-- The signed nine-factor diagonal window. -/
def k5SignedDiagonalWindow (d : ℕ) : ℤ :=
  ((d : ℤ) - 4) * ((d : ℤ) - 3) * ((d : ℤ) - 2) *
    ((d : ℤ) - 1) * (d : ℤ) * ((d : ℤ) + 1) *
    ((d : ℤ) + 2) * ((d : ℤ) + 3) * ((d : ℤ) + 4)

/-- Degree-four quotient left after reducing the diagonal window by the
degree-five block equation. -/
def k5DiagonalWindowQuotient (n d : ℕ) : ℤ :=
  210 * (n : ℤ) ^ 4 + 2520 * (n : ℤ) ^ 3 +
    10410 * (n : ℤ) ^ 2 + 17100 * (n : ℤ) + 9072 -
  (122 * (d : ℤ) ^ 4 +
    440 * (d : ℤ) ^ 3 * (n : ℤ) + 1320 * (d : ℤ) ^ 3 +
    480 * (d : ℤ) ^ 2 * (n : ℤ) ^ 2 +
    2880 * (d : ℤ) ^ 2 * (n : ℤ) + 3970 * (d : ℤ) ^ 2 +
    455 * (d : ℤ) * (n : ℤ) ^ 3 +
    4095 * (d : ℤ) * (n : ℤ) ^ 2 +
    11090 * (d : ℤ) * (n : ℤ) + 8700 * (d : ℤ))

/-- Cofactor in the polynomial division of the degree-nine window by the
monic degree-five equation in `d`. -/
def k5DiagonalWindowEquationCofactor (n d : ℕ) : ℤ :=
  (d : ℤ) ^ 4 - 5 * (d : ℤ) ^ 3 * (n : ℤ) -
    15 * (d : ℤ) ^ 3 + 15 * (d : ℤ) ^ 2 * (n : ℤ) ^ 2 +
    90 * (d : ℤ) ^ 2 * (n : ℤ) + 110 * (d : ℤ) ^ 2 -
    35 * (d : ℤ) * (n : ℤ) ^ 3 -
    315 * (d : ℤ) * (n : ℤ) ^ 2 -
    830 * (d : ℤ) * (n : ℤ) - 600 * (d : ℤ) +
    70 * (n : ℤ) ^ 4 + 840 * (n : ℤ) ^ 3 +
    3470 * (n : ℤ) ^ 2 + 5700 * (n : ℤ) + 3024

/-- Exact polynomial division identity.  No owner data or residual profile
enters this statement. -/
theorem k5_signed_diagonal_window_polynomial_identity (n d : ℕ) :
    k5SignedDiagonalWindow d =
      (blockProduct 5 n : ℤ) * k5DiagonalWindowQuotient n d +
      k5DiagonalWindowEquationCofactor n d *
        ((blockProduct 5 (n + d) : ℤ) - 4 * (blockProduct 5 n : ℤ)) := by
  norm_num [k5SignedDiagonalWindow, k5DiagonalWindowQuotient,
    k5DiagonalWindowEquationCofactor, blockProduct,
    Finset.prod_Icc_succ_top]
  ring

/-- On the five-block equation, the nine-factor window is exactly the lower
block times the displayed quartic quotient. -/
theorem k5_signed_diagonal_window_eq_block_mul_quartic
    {n d : ℕ}
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n) :
    k5SignedDiagonalWindow d =
      (blockProduct 5 n : ℤ) * k5DiagonalWindowQuotient n d := by
  rw [k5_signed_diagonal_window_polynomial_identity n d]
  have heqZ : (blockProduct 5 (n + d) : ℤ) =
      4 * (blockProduct 5 n : ℤ) := by
    exact_mod_cast heq
  rw [heqZ]
  ring

/-- Natural-number form of the diagonal window. -/
def k5DiagonalWindowNat (d : ℕ) : ℕ :=
  (d - 4) * (d - 3) * (d - 2) * (d - 1) * d *
    (d + 1) * (d + 2) * (d + 3) * (d + 4)

/-- The complete lower block divides the nine-factor diagonal window under
the five-block equation alone.  Thus the aggregate `G=12` divisor (even
without its factor `3`) is algebraically redundant. -/
theorem k5_block_dvd_diagonal_window_of_equation
    {n d : ℕ} (hd : 5 ≤ d)
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n) :
    blockProduct 5 n ∣ k5DiagonalWindowNat d := by
  have hid := k5_signed_diagonal_window_eq_block_mul_quartic heq
  have hwindow : (k5DiagonalWindowNat d : ℤ) = k5SignedDiagonalWindow d := by
    simp only [k5DiagonalWindowNat, k5SignedDiagonalWindow, Nat.cast_mul,
      Nat.cast_add, Nat.cast_ofNat]
    rw [Nat.cast_sub (by omega : 4 ≤ d), Nat.cast_sub (by omega : 3 ≤ d),
      Nat.cast_sub (by omega : 2 ≤ d), Nat.cast_sub (by omega : 1 ≤ d)]
    norm_num
  have hdivZ : (blockProduct 5 n : ℤ) ∣ (k5DiagonalWindowNat d : ℤ) := by
    refine ⟨k5DiagonalWindowQuotient n d, ?_⟩
    rw [hwindow, hid]
  exact_mod_cast hdivZ

#print axioms k5_signed_diagonal_window_polynomial_identity
#print axioms k5_signed_diagonal_window_eq_block_mul_quartic
#print axioms k5_block_dvd_diagonal_window_of_equation

end Erdos686Variant
end Erdos686
