/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.Core.PadicLift

/-!
# Erdős 686: exact normalized owner identity

This module records the exact multiplicative identity behind the normalized
cell-local jet expansions.  It explains why Taylor corrections obtained from
one owner cell remain a row term minus a column term at every order.

The result is deliberately scoped to the local normalized route.  It does not
apply to the global punctured-grid interpolation certificates.
-/

namespace Erdos686
namespace Erdos686Variant

open scoped BigOperators

/-- The shifted quotient
`Q_h(Z)=prod_{r != h} (Z+r-h)`, in natural-number form.  At `Z=n+h`
there is no truncated subtraction and it is the block cofactor obtained by
removing `n+h`. -/
def shiftedLocalQuotientNat (k h Z : ℕ) : ℕ :=
  ((Finset.Icc 1 k).erase h).prod fun r => Z + r - h

lemma shiftedLocalQuotientNat_at_block_term
    {k h n : ℕ} :
    shiftedLocalQuotientNat k h (n + h) =
      localBlockCofactorNat k h n := by
  unfold shiftedLocalQuotientNat localBlockCofactorNat
  apply Finset.prod_congr rfl
  intro r hr
  have hr' : r ∈ Finset.Icc 1 k := (Finset.mem_erase.mp hr).2
  have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr').1
  omega

/-- Exact owner-cell normalization.  If the lower and upper terms at a cell
share a positive owner `A`, cancelling that owner from the block equation
leaves a separated lower-cofactor / upper-cofactor identity.

This is the algebraic source of the all-order coboundary phenomenon for
cell-local normalized `p`-adic logarithms. -/
theorem owner_shiftedLocalQuotient_coboundary
    {k n d i j A R C : ℕ}
    (hi : i ∈ Finset.Icc 1 k)
    (hj : j ∈ Finset.Icc 1 k)
    (hA : 0 < A)
    (hlower : n + j = A * R)
    (hupper : n + d + i = A * C)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    C * shiftedLocalQuotientNat k i (n + d + i) =
      4 * R * shiftedLocalQuotientNat k j (n + j) := by
  rw [shiftedLocalQuotientNat_at_block_term,
    shiftedLocalQuotientNat_at_block_term]
  have hupperFactor :=
    blockProduct_eq_factor_mul_localBlockCofactorNat
      (k := k) (i := i) (n := n + d) hi
  have hlowerFactor :=
    blockProduct_eq_factor_mul_localBlockCofactorNat
      (k := k) (i := j) (n := n) hj
  have hscaled :
      A * (C * localBlockCofactorNat k i (n + d)) =
        A * (4 * R * localBlockCofactorNat k j n) := by
    calc
      A * (C * localBlockCofactorNat k i (n + d))
          = blockProduct k (n + d) := by
              rw [hupperFactor, hupper]
              ring
      _ = 4 * blockProduct k n := heq
      _ = A * (4 * R * localBlockCofactorNat k j n) := by
              rw [hlowerFactor, hlower]
              ring
  exact Nat.eq_of_mul_eq_mul_left hA hscaled

/-- Ratio form of the same identity over `ℚ`.  The right side is explicitly
a lower local quotient divided by an upper local quotient. -/
theorem owner_shiftedLocalQuotient_ratio
    {k n d i j A R C : ℕ}
    (hi : i ∈ Finset.Icc 1 k)
    (hj : j ∈ Finset.Icc 1 k)
    (hA : 0 < A)
    (hR : 0 < R)
    (hlower : n + j = A * R)
    (hupper : n + d + i = A * C)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    (C : ℚ) / (4 * R) =
      (shiftedLocalQuotientNat k j (n + j) : ℚ) /
        shiftedLocalQuotientNat k i (n + d + i) := by
  have hidentity := owner_shiftedLocalQuotient_coboundary
    hi hj hA hlower hupper heq
  have hupperCofactorPos :
      0 < shiftedLocalQuotientNat k i (n + d + i) := by
    rw [shiftedLocalQuotientNat_at_block_term]
    unfold localBlockCofactorNat
    exact Finset.prod_pos fun r hr => by
      have hr1 : 1 ≤ r :=
        (Finset.mem_Icc.mp (Finset.mem_of_mem_erase hr)).1
      omega
  have hleftDen : (4 * (R : ℚ)) ≠ 0 := by positivity
  have hrightDen :
      (shiftedLocalQuotientNat k i (n + d + i) : ℚ) ≠ 0 := by
    exact_mod_cast hupperCofactorPos.ne'
  rw [div_eq_div_iff hleftDen hrightDen]
  calc
    (C : ℚ) * shiftedLocalQuotientNat k i (n + d + i)
        = (4 * R * shiftedLocalQuotientNat k j (n + j) : ℕ) := by
            exact_mod_cast hidentity
    _ = (shiftedLocalQuotientNat k j (n + j) : ℚ) * (4 * R) := by
          push_cast
          ring

#print axioms owner_shiftedLocalQuotient_coboundary
#print axioms owner_shiftedLocalQuotient_ratio

end Erdos686Variant
end Erdos686
