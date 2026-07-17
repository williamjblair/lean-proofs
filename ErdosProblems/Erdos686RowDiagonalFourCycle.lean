/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686TwoRegularCycleMonodromy

/-!
# Erdős 686: row-diagonal four-cycle secant factorization

The first non-tautological cross-owner invariant in a row/signed-diagonal
two-regular component occurs on a four-cycle.  Write its row terms as

`x₁=P₁₁ P₁₂ r₁`, `x₂=P₂₁ P₂₂ r₂`

and its signed-diagonal terms as

`y₁=P₁₁ P₂₁ q₁`, `y₂=P₁₂ P₂₂ q₂`.

The opposite secant `Δρ*x₁-Δj*y₁` is then exactly the crossing
product `P₁₁ P₂₂` times a difference containing the squares of the
other two owners.  In the zero branch, canonical pairwise coprimality and the
small-prime row cofactors force those owner squares into the opposite
diagonal cofactors.  This is stronger than the raw two-owner secant divisor.
-/

namespace Erdos686
namespace Erdos686Variant

/-- Canonical bridge for the zero-branch hypotheses: every nontrivial large
owner cell is coprime to every lower-row cofactor. -/
theorem canonicalLargeOwnerCell_coprime_rowCofactor
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    {e : ℕ × ℕ} (he : e ∈ canonicalLargeOwnerSupport data)
    {j : ℕ} (hj : j ∈ Finset.Icc 1 k) :
    (canonicalLargeOwnerCell data e.1 e.2).Coprime
      (canonicalLargeOwnerRowCofactor data j) := by
  have hcell : canonicalLargeOwnerCell data e.1 e.2 ∣
      kLargePart k (blockProduct k n) := by
    rw [← canonicalLargeOwnerSupport_product_eq_kLargePart data]
    exact Finset.dvd_prod_of_mem
      (fun f => canonicalLargeOwnerCell data f.1 f.2) he
  have hrow := canonicalLargeOwnerRowCofactor_coprime_mass data hj
  exact (Nat.Coprime.coprime_dvd_right hcell hrow).symm

/-- Square-weighted quotient in the row-diagonal four-cycle secant. -/
def rowDiagonalFourCycleQuotient
    (P₁₂ P₂₁ r₁ r₂ q₁ q₂ : ℤ) : ℤ :=
  P₁₂ ^ 2 * r₁ * q₂ - P₂₁ ^ 2 * r₂ * q₁

/-- Exact comparison between the row product and signed-diagonal product on
a four-cycle. -/
theorem rowDiagonal_fourCycle_secant_factorization
    {P₁₁ P₁₂ P₂₁ P₂₂ r₁ r₂ q₁ q₂
      x₁ x₂ y₁ y₂ Δj Δρ : ℤ}
    (hx₁ : x₁ = P₁₁ * P₁₂ * r₁)
    (hx₂ : x₂ = P₂₁ * P₂₂ * r₂)
    (hy₁ : y₁ = P₁₁ * P₂₁ * q₁)
    (hy₂ : y₂ = P₁₂ * P₂₂ * q₂)
    (hxStep : x₂ = x₁ + Δj)
    (hyStep : y₂ = y₁ + Δρ) :
    Δρ * x₁ - Δj * y₁ =
      P₁₁ * P₂₂ *
        rowDiagonalFourCycleQuotient P₁₂ P₂₁ r₁ r₂ q₁ q₂ := by
  have hsecant : Δρ * x₁ - Δj * y₁ = x₁ * y₂ - x₂ * y₁ := by
    rw [hxStep, hyStep]
    ring
  rw [hsecant, hx₁, hx₂, hy₁, hy₂]
  unfold rowDiagonalFourCycleQuotient
  ring

/-- The crossing owner product divides the opposite secant, with the exact
four-cycle quotient exposed. -/
theorem rowDiagonal_fourCycle_crossingProduct_dvd_secant
    {P₁₁ P₁₂ P₂₁ P₂₂ r₁ r₂ q₁ q₂
      x₁ x₂ y₁ y₂ Δj Δρ : ℤ}
    (hx₁ : x₁ = P₁₁ * P₁₂ * r₁)
    (hx₂ : x₂ = P₂₁ * P₂₂ * r₂)
    (hy₁ : y₁ = P₁₁ * P₂₁ * q₁)
    (hy₂ : y₂ = P₁₂ * P₂₂ * q₂)
    (hxStep : x₂ = x₁ + Δj)
    (hyStep : y₂ = y₁ + Δρ) :
    P₁₁ * P₂₂ ∣ Δρ * x₁ - Δj * y₁ := by
  refine ⟨rowDiagonalFourCycleQuotient P₁₂ P₂₁ r₁ r₂ q₁ q₂, ?_⟩
  exact (rowDiagonal_fourCycle_secant_factorization
    hx₁ hx₂ hy₁ hy₂ hxStep hyStep)

/-- Nonzero branch: the crossing owner product is bounded by the absolute
opposite secant. -/
theorem rowDiagonal_fourCycle_crossingProduct_le_secant_natAbs
    {P₁₁ P₁₂ P₂₁ P₂₂ r₁ r₂ q₁ q₂ : ℕ}
    {x₁ x₂ y₁ y₂ Δj Δρ : ℤ}
    (hx₁ : x₁ = (P₁₁ : ℤ) * P₁₂ * r₁)
    (hx₂ : x₂ = (P₂₁ : ℤ) * P₂₂ * r₂)
    (hy₁ : y₁ = (P₁₁ : ℤ) * P₂₁ * q₁)
    (hy₂ : y₂ = (P₁₂ : ℤ) * P₂₂ * q₂)
    (hxStep : x₂ = x₁ + Δj)
    (hyStep : y₂ = y₁ + Δρ)
    (hsecant : Δρ * x₁ - Δj * y₁ ≠ 0) :
    P₁₁ * P₂₂ ≤ (Δρ * x₁ - Δj * y₁).natAbs := by
  apply Nat.le_of_dvd (Int.natAbs_pos.mpr hsecant)
  have hdvd := rowDiagonal_fourCycle_crossingProduct_dvd_secant
    hx₁ hx₂ hy₁ hy₂ hxStep hyStep
  have habs := Int.natAbs_dvd_natAbs.mpr hdvd
  simpa [Int.natAbs_mul] using habs

/-- Arithmetic zero-branch kernel.  Equality of the square-weighted products
forces `P₁₂²` into the opposite diagonal cofactor once the row cofactor and
the other owner are coprime to `P₁₂`. -/
theorem fourCycle_zero_quotient_forces_left_square_dvd_diagonalCofactor
    {P₁₂ P₂₁ r₁ r₂ q₁ q₂ : ℕ}
    (howners : P₁₂.Coprime P₂₁)
    (hrow : P₁₂.Coprime r₂)
    (hzero : P₁₂ ^ 2 * r₁ * q₂ = P₂₁ ^ 2 * r₂ * q₁) :
    P₁₂ ^ 2 ∣ q₁ := by
  have hdvd : P₁₂ ^ 2 ∣ (P₂₁ ^ 2 * r₂) * q₁ := by
    rw [← hzero]
    exact ⟨r₁ * q₂, by ring⟩
  have hcop : (P₁₂ ^ 2).Coprime (P₂₁ ^ 2 * r₂) :=
    (howners.pow 2 2).mul_right (hrow.pow_left 2)
  exact hcop.dvd_of_dvd_mul_left hdvd

/-- Symmetric zero-branch kernel for the other diagonal cofactor. -/
theorem fourCycle_zero_quotient_forces_right_square_dvd_diagonalCofactor
    {P₁₂ P₂₁ r₁ r₂ q₁ q₂ : ℕ}
    (howners : P₁₂.Coprime P₂₁)
    (hrow : P₂₁.Coprime r₁)
    (hzero : P₁₂ ^ 2 * r₁ * q₂ = P₂₁ ^ 2 * r₂ * q₁) :
    P₂₁ ^ 2 ∣ q₂ := by
  have hdvd : P₂₁ ^ 2 ∣ (P₁₂ ^ 2 * r₁) * q₂ := by
    rw [hzero]
    exact ⟨r₂ * q₁, by ring⟩
  have hcop : (P₂₁ ^ 2).Coprime (P₁₂ ^ 2 * r₁) :=
    (howners.symm.pow 2 2).mul_right (hrow.pow_left 2)
  exact hcop.dvd_of_dvd_mul_left hdvd

/-- Complete zero-branch consequence: both opposite owner squares divide the
opposite diagonal cofactors, hence their product square divides `q₁*q₂`. -/
theorem fourCycle_zero_quotient_forces_crossSquare_dvd_diagonalProduct
    {P₁₂ P₂₁ r₁ r₂ q₁ q₂ : ℕ}
    (howners : P₁₂.Coprime P₂₁)
    (hrowLeft : P₁₂.Coprime r₂)
    (hrowRight : P₂₁.Coprime r₁)
    (hzero : P₁₂ ^ 2 * r₁ * q₂ = P₂₁ ^ 2 * r₂ * q₁) :
    (P₁₂ * P₂₁) ^ 2 ∣ q₁ * q₂ := by
  have hleft := fourCycle_zero_quotient_forces_left_square_dvd_diagonalCofactor
    howners hrowLeft hzero
  have hright := fourCycle_zero_quotient_forces_right_square_dvd_diagonalCofactor
    howners hrowRight hzero
  simpa [mul_pow] using Nat.mul_dvd_mul hleft hright

/-- Zero-branch crowding in the first signed-diagonal term: besides its two
ordinary owners it must contain the square of the opposite crossing owner. -/
theorem fourCycle_zero_quotient_forces_left_diagonal_crowding
    {P₁₁ P₁₂ P₂₁ r₁ r₂ q₁ q₂ y₁ : ℕ}
    (howners : P₁₂.Coprime P₂₁)
    (hrow : P₁₂.Coprime r₂)
    (hzero : P₁₂ ^ 2 * r₁ * q₂ = P₂₁ ^ 2 * r₂ * q₁)
    (hy₁ : y₁ = P₁₁ * P₂₁ * q₁) :
    P₁₁ * P₂₁ * P₁₂ ^ 2 ∣ y₁ := by
  obtain ⟨u, hu⟩ :=
    fourCycle_zero_quotient_forces_left_square_dvd_diagonalCofactor
      howners hrow hzero
  refine ⟨u, ?_⟩
  rw [hy₁, hu]
  ring

/-- Symmetric zero-branch crowding in the second signed-diagonal term. -/
theorem fourCycle_zero_quotient_forces_right_diagonal_crowding
    {P₁₂ P₂₁ P₂₂ r₁ r₂ q₁ q₂ y₂ : ℕ}
    (howners : P₁₂.Coprime P₂₁)
    (hrow : P₂₁.Coprime r₁)
    (hzero : P₁₂ ^ 2 * r₁ * q₂ = P₂₁ ^ 2 * r₂ * q₁)
    (hy₂ : y₂ = P₁₂ * P₂₂ * q₂) :
    P₁₂ * P₂₂ * P₂₁ ^ 2 ∣ y₂ := by
  obtain ⟨u, hu⟩ :=
    fourCycle_zero_quotient_forces_right_square_dvd_diagonalCofactor
      howners hrow hzero
  refine ⟨u, ?_⟩
  rw [hy₂, hu]
  ring

/-- Product form of the zero-branch crowding.  The two diagonal terms must
contain the ordinary four-owner mass times the square of the two off-crossing
owners. -/
theorem fourCycle_zero_quotient_forces_ownerMass_mul_crossSquare_dvd_diagonalProduct
    {P₁₁ P₁₂ P₂₁ P₂₂ r₁ r₂ q₁ q₂ y₁ y₂ : ℕ}
    (howners : P₁₂.Coprime P₂₁)
    (hrowLeft : P₁₂.Coprime r₂)
    (hrowRight : P₂₁.Coprime r₁)
    (hzero : P₁₂ ^ 2 * r₁ * q₂ = P₂₁ ^ 2 * r₂ * q₁)
    (hy₁ : y₁ = P₁₁ * P₂₁ * q₁)
    (hy₂ : y₂ = P₁₂ * P₂₂ * q₂) :
    (P₁₁ * P₁₂ * P₂₁ * P₂₂) * (P₁₂ * P₂₁) ^ 2 ∣
      y₁ * y₂ := by
  have hleft := fourCycle_zero_quotient_forces_left_diagonal_crowding
    howners hrowLeft hzero hy₁
  have hright := fourCycle_zero_quotient_forces_right_diagonal_crowding
    howners hrowRight hzero hy₂
  convert Nat.mul_dvd_mul hleft hright using 1
  ring

/-- Exact four-cycle dichotomy.  A nonzero square-weighted quotient bounds one
crossing owner product by the opposite secant.  A zero quotient forces the
extra crossing-owner square into the product of the two signed-diagonal
terms. -/
theorem rowDiagonal_fourCycle_secant_or_ownerSquare_crowding
    {P₁₁ P₁₂ P₂₁ P₂₂ r₁ r₂ q₁ q₂
      x₁ x₂ y₁ y₂ : ℕ} {DeltaJ DeltaRho : ℤ}
    (hP₁₁ : 0 < P₁₁)
    (hP₂₂ : 0 < P₂₂)
    (howners : P₁₂.Coprime P₂₁)
    (hrowLeft : P₁₂.Coprime r₂)
    (hrowRight : P₂₁.Coprime r₁)
    (hx₁ : x₁ = P₁₁ * P₁₂ * r₁)
    (hx₂ : x₂ = P₂₁ * P₂₂ * r₂)
    (hy₁ : y₁ = P₁₁ * P₂₁ * q₁)
    (hy₂ : y₂ = P₁₂ * P₂₂ * q₂)
    (hxStep : (x₂ : ℤ) = x₁ + DeltaJ)
    (hyStep : (y₂ : ℤ) = y₁ + DeltaRho) :
    P₁₁ * P₂₂ <=
        (DeltaRho * (x₁ : ℤ) - DeltaJ * (y₁ : ℤ)).natAbs ∨
      (P₁₁ * P₁₂ * P₂₁ * P₂₂) * (P₁₂ * P₂₁) ^ 2 ∣
        y₁ * y₂ := by
  by_cases hzero : P₁₂ ^ 2 * r₁ * q₂ = P₂₁ ^ 2 * r₂ * q₁
  . exact Or.inr
      (fourCycle_zero_quotient_forces_ownerMass_mul_crossSquare_dvd_diagonalProduct
        howners hrowLeft hrowRight hzero hy₁ hy₂)
  . left
    have hx₁z : (x₁ : ℤ) = (P₁₁ : ℤ) * P₁₂ * r₁ := by
      exact_mod_cast hx₁
    have hx₂z : (x₂ : ℤ) = (P₂₁ : ℤ) * P₂₂ * r₂ := by
      exact_mod_cast hx₂
    have hy₁z : (y₁ : ℤ) = (P₁₁ : ℤ) * P₂₁ * q₁ := by
      exact_mod_cast hy₁
    have hy₂z : (y₂ : ℤ) = (P₁₂ : ℤ) * P₂₂ * q₂ := by
      exact_mod_cast hy₂
    have hquot :
        rowDiagonalFourCycleQuotient
          (P₁₂ : ℤ) P₂₁ r₁ r₂ q₁ q₂ ≠ 0 := by
      intro hq
      apply hzero
      unfold rowDiagonalFourCycleQuotient at hq
      have heq :
          (P₁₂ : ℤ) ^ 2 * r₁ * q₂ =
            (P₂₁ : ℤ) ^ 2 * r₂ * q₁ := sub_eq_zero.mp hq
      exact_mod_cast heq
    have hsecant :
        DeltaRho * (x₁ : ℤ) - DeltaJ * (y₁ : ℤ) ≠ 0 := by
      rw [rowDiagonal_fourCycle_secant_factorization
        hx₁z hx₂z hy₁z hy₂z hxStep hyStep]
      exact mul_ne_zero
        (mul_ne_zero (Int.ofNat_ne_zero.mpr (Nat.ne_of_gt hP₁₁))
          (Int.ofNat_ne_zero.mpr (Nat.ne_of_gt hP₂₂))) hquot
    exact rowDiagonal_fourCycle_crossingProduct_le_secant_natAbs
      hx₁z hx₂z hy₁z hy₂z hxStep hyStep hsecant

#print axioms rowDiagonal_fourCycle_secant_factorization
#print axioms canonicalLargeOwnerCell_coprime_rowCofactor
#print axioms rowDiagonal_fourCycle_crossingProduct_dvd_secant
#print axioms rowDiagonal_fourCycle_crossingProduct_le_secant_natAbs
#print axioms fourCycle_zero_quotient_forces_left_square_dvd_diagonalCofactor
#print axioms fourCycle_zero_quotient_forces_right_square_dvd_diagonalCofactor
#print axioms fourCycle_zero_quotient_forces_crossSquare_dvd_diagonalProduct
#print axioms fourCycle_zero_quotient_forces_left_diagonal_crowding
#print axioms fourCycle_zero_quotient_forces_right_diagonal_crowding
#print axioms fourCycle_zero_quotient_forces_ownerMass_mul_crossSquare_dvd_diagonalProduct
#print axioms rowDiagonal_fourCycle_secant_or_ownerSquare_crowding

end Erdos686Variant
end Erdos686
