/- leanprover/lean4:v4.29.1 mathlib v4.29.1 -/
import ErdosProblems.Erdos686.Core.RowDiagonalSixCycle

/-!
# Erdős 686: canonical-owner specialization of the six-cycle invariant

This file instantiates the abstract six-cycle secant-or-crowding theorem on
six actual cells of the canonical large-owner support.  Exact two-cell row
and signed-diagonal fibres supply the row and diagonal cofactors; canonical
pairwise coprimality and the small/large-prime split discharge every abstract
coprimality hypothesis.
-/

namespace Erdos686
namespace Erdos686Variant

/-- Cofactor left after deleting the complete canonical large-owner product
from one signed-diagonal term. -/
def canonicalLargeOwnerDiagonalCofactor
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t) (h : ℕ) : ℕ :=
  (d + h - (k - 1)) / canonicalLargeOwnerDiagonalAggregate data h

/-- Exact signed-diagonal analogue of the canonical lower-row
factorization. -/
theorem canonicalLargeOwner_diagonal_term_factorization
    {k n d t h : ℕ} (data : CanonicalOwnerData k n d t)
    (hk : 1 ≤ k) (hd : k ≤ d) (hfour : 4 ∣ n + d + t) :
    d + h - (k - 1) =
      canonicalLargeOwnerDiagonalCofactor data h *
        canonicalLargeOwnerDiagonalAggregate data h := by
  exact (Nat.div_mul_cancel
    (canonicalLargeOwnerDiagonalSupport_product_dvd_centeredTerm
      data hk hd hfour)).symm

private theorem canonical_row_pair_factorization
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    {a b : ℕ × ℕ} (hab : a ≠ b)
    (hfibre : canonicalLargeOwnerRowSupport data b.1 = {a, b}) :
    n + b.1 =
      canonicalLargeOwnerCell data a.1 a.2 *
        canonicalLargeOwnerCell data b.1 b.2 *
          canonicalLargeOwnerRowCofactor data b.1 := by
  have hfactor := canonicalLargeOwner_lower_term_factorization data (j := b.1)
  unfold canonicalLargeOwnerRowAggregate at hfactor
  rw [hfibre] at hfactor
  simp only [Finset.prod_insert, Finset.mem_singleton, hab,
    not_false_eq_true, Finset.prod_singleton] at hfactor
  calc
    n + b.1 = canonicalLargeOwnerRowCofactor data b.1 *
        (canonicalLargeOwnerCell data a.1 a.2 *
          canonicalLargeOwnerCell data b.1 b.2) := hfactor
    _ = canonicalLargeOwnerCell data a.1 a.2 *
        canonicalLargeOwnerCell data b.1 b.2 *
          canonicalLargeOwnerRowCofactor data b.1 := by ring

private theorem canonical_diagonal_pair_factorization
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    {a b : ℕ × ℕ} (hab : a ≠ b)
    (hk : 1 ≤ k) (hd : k ≤ d) (hfour : 4 ∣ n + d + t)
    (hb : b ∈ canonicalLargeOwnerSupport data)
    (hfibre : canonicalLargeOwnerDiagonalSupport data
      (canonicalOwnerDiagonalIndex k b) = {b, a}) :
    d + b.2 - b.1 =
      canonicalLargeOwnerCell data b.1 b.2 *
        canonicalLargeOwnerCell data a.1 a.2 *
          canonicalLargeOwnerDiagonalCofactor data
            (canonicalOwnerDiagonalIndex k b) := by
  have hbSquare := (canonicalLargeOwnerSupport_spec data hfour).1 b hb
  have hfactor := canonicalLargeOwner_diagonal_term_factorization
    data (h := canonicalOwnerDiagonalIndex k b) hk hd hfour
  unfold canonicalLargeOwnerDiagonalAggregate at hfactor
  rw [hfibre] at hfactor
  simp only [Finset.prod_insert, Finset.mem_singleton, hab.symm,
    not_false_eq_true, Finset.prod_singleton] at hfactor
  rw [centeredDiffTerm_eq_shiftedDifference hk hd hbSquare] at hfactor
  calc
    d + b.2 - b.1 =
        canonicalLargeOwnerDiagonalCofactor data
            (canonicalOwnerDiagonalIndex k b) *
          (canonicalLargeOwnerCell data b.1 b.2 *
            canonicalLargeOwnerCell data a.1 a.2) := hfactor
    _ = canonicalLargeOwnerCell data b.1 b.2 *
        canonicalLargeOwnerCell data a.1 a.2 *
          canonicalLargeOwnerDiagonalCofactor data
            (canonicalOwnerDiagonalIndex k b) := by ring

private theorem canonical_ownerSquare_coprime_twoOwners_mul_rowCofactor
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    {e left right : ℕ × ℕ} {j : ℕ}
    (he : e ∈ canonicalLargeOwnerSupport data)
    (hel : e ≠ left) (her : e ≠ right)
    (hj : j ∈ Finset.Icc 1 k) :
    (canonicalLargeOwnerCell data e.1 e.2 ^ 2).Coprime
      (canonicalLargeOwnerCell data left.1 left.2 *
        canonicalLargeOwnerCell data right.1 right.2 *
          canonicalLargeOwnerRowCofactor data j) := by
  have hEL := canonicalLargeOwnerCells_pairwise_coprime data hel
  have hER := canonicalLargeOwnerCells_pairwise_coprime data her
  have hEC := canonicalLargeOwnerCell_coprime_rowCofactor data he hj
  exact ((hEL.mul_right hER).mul_right hEC).pow_left 2

private theorem canonical_twoOwners_coprime_ownerSquare_mul_rowCofactor
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    {left right e : ℕ × ℕ} {j : ℕ}
    (hleft : left ∈ canonicalLargeOwnerSupport data)
    (hright : right ∈ canonicalLargeOwnerSupport data)
    (hle : left ≠ e) (hre : right ≠ e)
    (hj : j ∈ Finset.Icc 1 k) :
    (canonicalLargeOwnerCell data left.1 left.2 *
      canonicalLargeOwnerCell data right.1 right.2).Coprime
        (canonicalLargeOwnerCell data e.1 e.2 ^ 2 *
          canonicalLargeOwnerRowCofactor data j) := by
  have hLE := canonicalLargeOwnerCells_pairwise_coprime data hle
  have hRE := canonicalLargeOwnerCells_pairwise_coprime data hre
  have hLC := canonicalLargeOwnerCell_coprime_rowCofactor data hleft hj
  have hRC := canonicalLargeOwnerCell_coprime_rowCofactor data hright hj
  have howners :
      (canonicalLargeOwnerCell data left.1 left.2 *
        canonicalLargeOwnerCell data right.1 right.2).Coprime
          (canonicalLargeOwnerCell data e.1 e.2 ^ 2) :=
    ((hLE.pow_right 2).symm.mul_right (hRE.pow_right 2).symm).symm
  have hcofactor :
      (canonicalLargeOwnerCell data left.1 left.2 *
        canonicalLargeOwnerCell data right.1 right.2).Coprime
          (canonicalLargeOwnerRowCofactor data j) :=
    (hLC.symm.mul_right hRC.symm).symm
  exact howners.mul_right hcofactor

/-- Equation-facing canonical specialization of the six-cycle dichotomy.
The six cells form three exact two-owner rows and three exact two-owner
signed diagonals. -/
theorem canonicalLargeOwnerSixCycle_secant_or_crowding
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    (hd : k ≤ d) (hfour : 4 ∣ n + d + t)
    {a₁ b₁ a₂ b₂ a₃ b₃ : ℕ × ℕ}
    (ha₁ : a₁ ∈ canonicalLargeOwnerSupport data)
    (hb₁ : b₁ ∈ canonicalLargeOwnerSupport data)
    (ha₂ : a₂ ∈ canonicalLargeOwnerSupport data)
    (hb₂ : b₂ ∈ canonicalLargeOwnerSupport data)
    (ha₃ : a₃ ∈ canonicalLargeOwnerSupport data)
    (hb₃ : b₃ ∈ canonicalLargeOwnerSupport data)
    (ha₁b₁ : a₁ ≠ b₁) (hb₁a₂ : b₁ ≠ a₂)
    (ha₂b₂ : a₂ ≠ b₂) (hb₂a₃ : b₂ ≠ a₃)
    (ha₃b₃ : a₃ ≠ b₃) (hb₃a₁ : b₃ ≠ a₁)
    (ha₁a₂ : a₁ ≠ a₂) (ha₁a₃ : a₁ ≠ a₃)
    (ha₂a₃ : a₂ ≠ a₃)
    (hrow₁ : canonicalLargeOwnerRowSupport data b₁.1 = {a₁, b₁})
    (hrow₂ : canonicalLargeOwnerRowSupport data b₂.1 = {a₂, b₂})
    (hrow₃ : canonicalLargeOwnerRowSupport data b₃.1 = {a₃, b₃})
    (hdiag₁ : canonicalLargeOwnerDiagonalSupport data
      (canonicalOwnerDiagonalIndex k b₁) = {b₁, a₂})
    (hdiag₂ : canonicalLargeOwnerDiagonalSupport data
      (canonicalOwnerDiagonalIndex k b₂) = {b₂, a₃})
    (hdiag₃ : canonicalLargeOwnerDiagonalSupport data
      (canonicalOwnerDiagonalIndex k b₃) = {b₃, a₁}) :
    let A₁ := canonicalLargeOwnerCell data a₁.1 a₁.2
    let A₂ := canonicalLargeOwnerCell data a₂.1 a₂.2
    let A₃ := canonicalLargeOwnerCell data a₃.1 a₃.2
    let B₁ := canonicalLargeOwnerCell data b₁.1 b₁.2
    let B₂ := canonicalLargeOwnerCell data b₂.1 b₂.2
    let B₃ := canonicalLargeOwnerCell data b₃.1 b₃.2
    let Q₁ := canonicalLargeOwnerDiagonalCofactor data
      (canonicalOwnerDiagonalIndex k b₁)
    let Q₂ := canonicalLargeOwnerDiagonalCofactor data
      (canonicalOwnerDiagonalIndex k b₂)
    let Q₃ := canonicalLargeOwnerDiagonalCofactor data
      (canonicalOwnerDiagonalIndex k b₃)
    (B₁ * B₂ * B₃) ^ 2 ≤
        (sixCycleSecantProduct
          (n + b₁.1) (n + b₂.1) (n + b₃.1)
          ((d + b₁.2 - b₁.1 : ℕ) : ℤ)
          ((d + b₂.2 - b₂.1 : ℕ) : ℤ)
          ((d + b₃.2 - b₃.1 : ℕ) : ℤ)).natAbs ∨
      ((A₁ * A₃) * A₂ ^ 2 ∣ Q₁ * Q₂) ∨
      ((A₂ * A₁) * A₃ ^ 2 ∣ Q₂ * Q₃) ∨
      ((A₃ * A₂) * A₁ ^ 2 ∣ Q₃ * Q₁) := by
  dsimp
  have hb₁Square := (canonicalLargeOwnerSupport_spec data hfour).1 b₁ hb₁
  have hb₂Square := (canonicalLargeOwnerSupport_spec data hfour).1 b₂ hb₂
  have hb₃Square := (canonicalLargeOwnerSupport_spec data hfour).1 b₃ hb₃
  have hk : 1 ≤ k := le_trans (Finset.mem_Icc.mp hb₁Square.1).1
    (Finset.mem_Icc.mp hb₁Square.1).2
  have hj₁ := hb₁Square.1
  have hj₂ := hb₂Square.1
  have hj₃ := hb₃Square.1
  have hx₁Nat := canonical_row_pair_factorization data ha₁b₁ hrow₁
  have hx₂Nat := canonical_row_pair_factorization data ha₂b₂ hrow₂
  have hx₃Nat := canonical_row_pair_factorization data ha₃b₃ hrow₃
  have hy₁Nat := canonical_diagonal_pair_factorization data
    (a := a₂) (b := b₁) hb₁a₂.symm hk hd hfour hb₁ hdiag₁
  have hy₂Nat := canonical_diagonal_pair_factorization data
    (a := a₃) (b := b₂) hb₂a₃.symm hk hd hfour hb₂ hdiag₂
  have hy₃Nat := canonical_diagonal_pair_factorization data
    (a := a₁) (b := b₃) hb₃a₁.symm hk hd hfour hb₃ hdiag₃
  have hx₁ : ((n + b₁.1 : ℕ) : ℤ) =
      (canonicalLargeOwnerCell data a₁.1 a₁.2 : ℤ) *
        canonicalLargeOwnerCell data b₁.1 b₁.2 *
          canonicalLargeOwnerRowCofactor data b₁.1 := by exact_mod_cast hx₁Nat
  have hx₂ : ((n + b₂.1 : ℕ) : ℤ) =
      (canonicalLargeOwnerCell data a₂.1 a₂.2 : ℤ) *
        canonicalLargeOwnerCell data b₂.1 b₂.2 *
          canonicalLargeOwnerRowCofactor data b₂.1 := by exact_mod_cast hx₂Nat
  have hx₃ : ((n + b₃.1 : ℕ) : ℤ) =
      (canonicalLargeOwnerCell data a₃.1 a₃.2 : ℤ) *
        canonicalLargeOwnerCell data b₃.1 b₃.2 *
          canonicalLargeOwnerRowCofactor data b₃.1 := by exact_mod_cast hx₃Nat
  have hy₁ : ((d + b₁.2 - b₁.1 : ℕ) : ℤ) =
      (canonicalLargeOwnerCell data b₁.1 b₁.2 : ℤ) *
        canonicalLargeOwnerCell data a₂.1 a₂.2 *
          canonicalLargeOwnerDiagonalCofactor data
            (canonicalOwnerDiagonalIndex k b₁) := by exact_mod_cast hy₁Nat
  have hy₂ : ((d + b₂.2 - b₂.1 : ℕ) : ℤ) =
      (canonicalLargeOwnerCell data b₂.1 b₂.2 : ℤ) *
        canonicalLargeOwnerCell data a₃.1 a₃.2 *
          canonicalLargeOwnerDiagonalCofactor data
            (canonicalOwnerDiagonalIndex k b₂) := by exact_mod_cast hy₂Nat
  have hy₃ : ((d + b₃.2 - b₃.1 : ℕ) : ℤ) =
      (canonicalLargeOwnerCell data b₃.1 b₃.2 : ℤ) *
        canonicalLargeOwnerCell data a₁.1 a₁.2 *
          canonicalLargeOwnerDiagonalCofactor data
            (canonicalOwnerDiagonalIndex k b₃) := by exact_mod_cast hy₃Nat
  have hB₁pos := (canonicalLargeOwnerSupport_spec data hfour).2.1 b₁ hb₁
  have hB₂pos := (canonicalLargeOwnerSupport_spec data hfour).2.1 b₂ hb₂
  have hB₃pos := (canonicalLargeOwnerSupport_spec data hfour).2.1 b₃ hb₃
  apply sixCycle_secant_or_ownerSquare_crowding
    (Nat.zero_lt_one.trans hB₁pos) (Nat.zero_lt_one.trans hB₂pos)
      (Nat.zero_lt_one.trans hB₃pos)
  · exact canonical_ownerSquare_coprime_twoOwners_mul_rowCofactor
      data ha₂ ha₁a₂.symm ha₂a₃ hj₁
  · exact canonical_twoOwners_coprime_ownerSquare_mul_rowCofactor
      data ha₁ ha₃ ha₁a₂ ha₂a₃.symm hj₂
  · exact canonical_ownerSquare_coprime_twoOwners_mul_rowCofactor
      data ha₃ ha₂a₃.symm ha₁a₃.symm hj₂
  · exact canonical_twoOwners_coprime_ownerSquare_mul_rowCofactor
      data ha₂ ha₁ ha₂a₃ ha₁a₃ hj₃
  · exact canonical_ownerSquare_coprime_twoOwners_mul_rowCofactor
      data ha₁ ha₁a₃ ha₁a₂ hj₃
  · exact canonical_twoOwners_coprime_ownerSquare_mul_rowCofactor
      data ha₃ ha₂ ha₁a₃.symm ha₁a₂.symm hj₁
  · exact hx₁
  · exact hx₂
  · exact hx₃
  · exact hy₁
  · exact hy₂
  · exact hy₃

#print axioms canonicalLargeOwner_diagonal_term_factorization
#print axioms canonicalLargeOwnerSixCycle_secant_or_crowding

end Erdos686Variant
end Erdos686
