/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.K5.ProperGlobalTangentCancellation

/-!
# Erdős 686, k=5: opposite secants and exact cofactor identity

The four crossings of two rows and two columns carry two opposite matchings.
Their secant resultants multiply to the difference of the row and column
quadratic products.  After the exact four-crossing gcd is removed, this gives
an equality between the two secant quotients and the coprime row/column
cofactors.  Unlike the bipartite tangent-product identity, this retains the
adjacent row and column equations.
-/

namespace Erdos686
namespace Erdos686Variant

/-- The secant through the `(j₁,i₁)` and `(j₂,i₂)` crossings. -/
def k5OppositeSecantPlus
    (n d j₁ j₂ i₁ i₂ : ℕ) : ℤ :=
  ((j₂ : ℤ) - j₁) * (n + d + i₁ : ℕ) -
    ((i₂ : ℤ) - i₁) * (n + j₁ : ℕ)

/-- The secant through the `(j₁,i₂)` and `(j₂,i₁)` crossings. -/
def k5OppositeSecantMinus
    (n d j₁ j₂ i₁ i₂ : ℕ) : ℤ :=
  ((j₂ : ℤ) - j₁) * (n + d + i₂ : ℕ) +
    ((i₂ : ℤ) - i₁) * (n + j₁ : ℕ)

/-- Universal opposite-secant product identity. -/
theorem opposite_secant_product_identity
    (x₁ x₂ z₁ z₂ r s : ℤ)
    (hx : x₂ = x₁ + r) (hz : z₂ = z₁ + s) :
    (r * z₁ - s * x₁) * (r * z₂ + s * x₁) =
      r ^ 2 * z₁ * z₂ - s ^ 2 * x₁ * x₂ := by
  rw [hx, hz]
  ring

/-- Exact quotient identity after a common crossing product has been removed
from the row and column quadratic products and split between the two opposite
secant matchings. -/
theorem opposite_secant_quotient_cofactor_identity
    (x₁ x₂ z₁ z₂ r s μ₁ μ₂ X a b
      Mplus Mminus Uplus Uminus : ℤ)
    (hX : X ≠ 0)
    (hx : x₂ = x₁ + r) (hz : z₂ = z₁ + s)
    (hrow : x₁ * x₂ = X * a)
    (hcolumn : z₁ * z₂ = μ₁ * μ₂ * X * b)
    (hmatching : Mplus * Mminus = X)
    (hplus : Mplus * Uplus = r * z₁ - s * x₁)
    (hminus : Mminus * Uminus = r * z₂ + s * x₁) :
    Uplus * Uminus = r ^ 2 * μ₁ * μ₂ * b - s ^ 2 * a := by
  apply mul_left_cancel₀ hX
  calc
    X * (Uplus * Uminus) =
        (Mplus * Mminus) * (Uplus * Uminus) := by rw [hmatching]
    _ = (Mplus * Uplus) * (Mminus * Uminus) := by ring
    _ = (r * z₁ - s * x₁) * (r * z₂ + s * x₁) := by
      rw [hplus, hminus]
    _ = r ^ 2 * z₁ * z₂ - s ^ 2 * x₁ * x₂ :=
      opposite_secant_product_identity x₁ x₂ z₁ z₂ r s hx hz
    _ = X * (r ^ 2 * μ₁ * μ₂ * b - s ^ 2 * a) := by
      rw [show r ^ 2 * z₁ * z₂ = r ^ 2 * (z₁ * z₂) by ring,
        show s ^ 2 * x₁ * x₂ = s ^ 2 * (x₁ * x₂) by ring,
        hrow, hcolumn]
      ring

/-- The two opposite products of canonical crossing cells divide their
corresponding explicit secants.  This uses only owner row/column divisibility
and global pairwise coprimality; no residual or high-prime hypothesis enters. -/
theorem canonicalOwner_k5_opposite_crossing_products_dvd_secants
    {n d t j₁ j₂ i₁ i₂ : ℕ}
    (data : CanonicalOwnerData 5 n d t)
    (hjneq : j₁ ≠ j₂) (hfour : 4 ∣ n + d + t) :
    (((canonicalOwnerCell data j₁ i₁ *
        canonicalOwnerCell data j₂ i₂ : ℕ) : ℤ) ∣
      k5OppositeSecantPlus n d j₁ j₂ i₁ i₂) ∧
    (((canonicalOwnerCell data j₁ i₂ *
        canonicalOwnerCell data j₂ i₁ : ℕ) : ℤ) ∣
      k5OppositeSecantMinus n d j₁ j₂ i₁ i₂) := by
  have hcopPlus : Nat.Coprime
      (canonicalOwnerCell data j₁ i₁)
      (canonicalOwnerCell data j₂ i₂) := by
    apply canonicalOwnerCells_pairwise_coprime data
    intro heq
    exact hjneq (congrArg Prod.fst heq)
  have hcopMinus : Nat.Coprime
      (canonicalOwnerCell data j₁ i₂)
      (canonicalOwnerCell data j₂ i₁) := by
    apply canonicalOwnerCells_pairwise_coprime data
    intro heq
    exact hjneq (congrArg Prod.fst heq)
  have hlowerZ (j i : ℕ) : ((canonicalOwnerCell data j i : ℕ) : ℤ) ∣
      ((n + j : ℕ) : ℤ) := by
    exact_mod_cast (canonicalOwnerCell_dvd_lower data (j := j) (i := i))
  have hupperZ (j i : ℕ) : ((canonicalOwnerCell data j i : ℕ) : ℤ) ∣
      ((n + d + i : ℕ) : ℤ) := by
    have hupperNat : canonicalOwnerCell data j i ∣ n + d + i :=
      dvd_trans (canonicalOwnerCell_dvd_upper data (j := j) (i := i))
        (upperTermAfterFour_dvd_original hfour)
    exact_mod_cast hupperNat
  have hplus₁ : ((canonicalOwnerCell data j₁ i₁ : ℕ) : ℤ) ∣
      k5OppositeSecantPlus n d j₁ j₂ i₁ i₂ := by
    apply dvd_sub
    · exact dvd_mul_of_dvd_right
        (hupperZ j₁ i₁)
        ((j₂ : ℤ) - j₁)
    · exact dvd_mul_of_dvd_right
        (hlowerZ j₁ i₁)
        ((i₂ : ℤ) - i₁)
  have hplus₂ : ((canonicalOwnerCell data j₂ i₂ : ℕ) : ℤ) ∣
      k5OppositeSecantPlus n d j₁ j₂ i₁ i₂ := by
    have hidentity :
        k5OppositeSecantPlus n d j₁ j₂ i₁ i₂ =
          ((j₂ : ℤ) - j₁) * (n + d + i₂ : ℕ) -
            ((i₂ : ℤ) - i₁) * (n + j₂ : ℕ) := by
      simp only [k5OppositeSecantPlus]
      push_cast
      ring
    rw [hidentity]
    apply dvd_sub
    · exact dvd_mul_of_dvd_right
        (hupperZ j₂ i₂)
        ((j₂ : ℤ) - j₁)
    · exact dvd_mul_of_dvd_right
        (hlowerZ j₂ i₂)
        ((i₂ : ℤ) - i₁)
  have hminus₁ : ((canonicalOwnerCell data j₁ i₂ : ℕ) : ℤ) ∣
      k5OppositeSecantMinus n d j₁ j₂ i₁ i₂ := by
    apply dvd_add
    · exact dvd_mul_of_dvd_right
        (hupperZ j₁ i₂)
        ((j₂ : ℤ) - j₁)
    · exact dvd_mul_of_dvd_right
        (hlowerZ j₁ i₂)
        ((i₂ : ℤ) - i₁)
  have hminus₂ : ((canonicalOwnerCell data j₂ i₁ : ℕ) : ℤ) ∣
      k5OppositeSecantMinus n d j₁ j₂ i₁ i₂ := by
    have hidentity :
        k5OppositeSecantMinus n d j₁ j₂ i₁ i₂ =
          ((j₂ : ℤ) - j₁) * (n + d + i₁ : ℕ) +
            ((i₂ : ℤ) - i₁) * (n + j₂ : ℕ) := by
      simp only [k5OppositeSecantMinus]
      push_cast
      ring
    rw [hidentity]
    apply dvd_add
    · exact dvd_mul_of_dvd_right
        (hupperZ j₂ i₁)
        ((j₂ : ℤ) - j₁)
    · exact dvd_mul_of_dvd_right
        (hlowerZ j₂ i₁)
        ((i₂ : ℤ) - i₁)
  constructor
  · exact hcopPlus.isCoprime.mul_dvd hplus₁ hplus₂
  · exact hcopMinus.isCoprime.mul_dvd hminus₁ hminus₂

/-- Fully owned proper-global wrapper.  The exact row/column gcd supplies
coprime cofactors `a,b`; the two opposite secant divisors then supply integer
quotients whose product is their explicit linear combination. -/
theorem k5_fullyOwned_opposite_secant_cofactor_identity
    {n d t j₁ j₂ i₁ i₂ : ℕ}
    (data : CanonicalOwnerData 5 n d t)
    (hj₁ : j₁ ∈ Finset.Icc 1 5) (hj₂ : j₂ ∈ Finset.Icc 1 5)
    (hi₁ : i₁ ∈ Finset.Icc 1 5) (hi₂ : i₂ ∈ Finset.Icc 1 5)
    (hjneq : j₁ ≠ j₂) (hineq : i₁ ≠ i₂)
    (hfour : 4 ∣ n + d + t)
    (hj₁one : canonicalLowerResidual data j₁ = 1)
    (hj₂one : canonicalLowerResidual data j₂ = 1)
    (hi₁one : canonicalUpperResidual data i₁ = 1)
    (hi₂one : canonicalUpperResidual data i₂ = 1) :
    let A := (n + j₁) * (n + j₂)
    let B := upperTermAfterFour n d t i₁ * upperTermAfterFour n d t i₂
    let X := canonicalOwnerCell data j₁ i₁ *
      canonicalOwnerCell data j₁ i₂ *
      canonicalOwnerCell data j₂ i₁ *
      canonicalOwnerCell data j₂ i₂
    let Mplus := canonicalOwnerCell data j₁ i₁ *
      canonicalOwnerCell data j₂ i₂
    let Mminus := canonicalOwnerCell data j₁ i₂ *
      canonicalOwnerCell data j₂ i₁
    ∃ a b : ℕ, Nat.Coprime a b ∧ A = X * a ∧ B = X * b ∧
      ∃ Uplus Uminus : ℤ,
        k5OppositeSecantPlus n d j₁ j₂ i₁ i₂ =
            (Mplus : ℤ) * Uplus ∧
          k5OppositeSecantMinus n d j₁ j₂ i₁ i₂ =
            (Mminus : ℤ) * Uminus ∧
          Uplus * Uminus =
            (((j₂ : ℤ) - j₁) ^ 2) *
                (k5UpperFourMultiplier t i₁ : ℤ) *
                (k5UpperFourMultiplier t i₂ : ℤ) * (b : ℤ) -
              (((i₂ : ℤ) - i₁) ^ 2) * (a : ℤ) := by
  dsimp only
  let A : ℕ := (n + j₁) * (n + j₂)
  let B : ℕ := upperTermAfterFour n d t i₁ *
    upperTermAfterFour n d t i₂
  let X : ℕ := canonicalOwnerCell data j₁ i₁ *
    canonicalOwnerCell data j₁ i₂ *
    canonicalOwnerCell data j₂ i₁ *
    canonicalOwnerCell data j₂ i₂
  let Mplus : ℕ := canonicalOwnerCell data j₁ i₁ *
    canonicalOwnerCell data j₂ i₂
  let Mminus : ℕ := canonicalOwnerCell data j₁ i₂ *
    canonicalOwnerCell data j₂ i₁
  let a : ℕ := A / X
  let b : ℕ := B / X
  have hgcd : Nat.gcd A B = X := by
    dsimp [A, B, X]
    exact k5_proper_global_row_column_gcd_eq_crossings data
      hj₁ hj₂ hi₁ hi₂ hjneq hineq
      hj₁one hj₂one hi₁one hi₂one
  have hXpos : 0 < X := by
    dsimp [X]
    have h₁₁ := canonicalOwnerCell_pos data (j := j₁) (i := i₁)
    have h₁₂ := canonicalOwnerCell_pos data (j := j₁) (i := i₂)
    have h₂₁ := canonicalOwnerCell_pos data (j := j₂) (i := i₁)
    have h₂₂ := canonicalOwnerCell_pos data (j := j₂) (i := i₂)
    positivity
  have hXdA : X ∣ A := by rw [← hgcd]; exact Nat.gcd_dvd_left A B
  have hXdB : X ∣ B := by rw [← hgcd]; exact Nat.gcd_dvd_right A B
  have hA : A = X * a := by
    dsimp [a]
    exact (Nat.mul_div_cancel' hXdA).symm
  have hB : B = X * b := by
    dsimp [b]
    exact (Nat.mul_div_cancel' hXdB).symm
  have hcop : Nat.Coprime a b := by
    dsimp [a, b]
    rw [← hgcd]
    exact Nat.coprime_div_gcd_div_gcd (by simpa [hgcd] using hXpos)
  obtain ⟨hplusDvd, hminusDvd⟩ :=
    canonicalOwner_k5_opposite_crossing_products_dvd_secants
      data hjneq hfour
  obtain ⟨Uplus, hUplus⟩ := hplusDvd
  obtain ⟨Uminus, hUminus⟩ := hminusDvd
  have hM : (Mplus : ℤ) * (Mminus : ℤ) = (X : ℤ) := by
    dsimp [Mplus, Mminus, X]
    ring
  have hx : ((n + j₂ : ℕ) : ℤ) =
      (n + j₁ : ℕ) + ((j₂ : ℤ) - j₁) := by
    push_cast
    ring
  have hz : ((n + d + i₂ : ℕ) : ℤ) =
      (n + d + i₁ : ℕ) + ((i₂ : ℤ) - i₁) := by
    push_cast
    ring
  have hrowZ : ((n + j₁ : ℕ) : ℤ) * (n + j₂ : ℕ) =
      (X : ℤ) * (a : ℤ) := by
    dsimp [A] at hA
    exact_mod_cast hA
  have hmul₁ := k5UpperFourMultiplier_mul_upperTermAfterFour
    (n := n) (d := d) (t := t) (i := i₁) hfour
  have hmul₂ := k5UpperFourMultiplier_mul_upperTermAfterFour
    (n := n) (d := d) (t := t) (i := i₂) hfour
  have hcolumnZ :
      ((n + d + i₁ : ℕ) : ℤ) * (n + d + i₂ : ℕ) =
        (k5UpperFourMultiplier t i₁ : ℤ) *
          (k5UpperFourMultiplier t i₂ : ℤ) * (X : ℤ) * (b : ℤ) := by
    have hBcast : (B : ℤ) = (X : ℤ) * (b : ℤ) := by
      exact_mod_cast hB
    dsimp [B] at hBcast
    have hmul₁Z :
        (k5UpperFourMultiplier t i₁ : ℤ) *
            (upperTermAfterFour n d t i₁ : ℤ) = (n + d + i₁ : ℕ) := by
      exact_mod_cast hmul₁
    have hmul₂Z :
        (k5UpperFourMultiplier t i₂ : ℤ) *
            (upperTermAfterFour n d t i₂ : ℤ) = (n + d + i₂ : ℕ) := by
      exact_mod_cast hmul₂
    rw [← hmul₁Z, ← hmul₂Z]
    calc
      (k5UpperFourMultiplier t i₁ : ℤ) *
            (upperTermAfterFour n d t i₁ : ℤ) *
          ((k5UpperFourMultiplier t i₂ : ℤ) *
            (upperTermAfterFour n d t i₂ : ℤ)) =
          (k5UpperFourMultiplier t i₁ : ℤ) *
            (k5UpperFourMultiplier t i₂ : ℤ) *
            ((upperTermAfterFour n d t i₁ : ℤ) *
              (upperTermAfterFour n d t i₂ : ℤ)) := by ring
      _ = (k5UpperFourMultiplier t i₁ : ℤ) *
          (k5UpperFourMultiplier t i₂ : ℤ) * (X : ℤ) * (b : ℤ) := by
        rw [hBcast]
        ring
  have hquot := opposite_secant_quotient_cofactor_identity
    ((n + j₁ : ℕ) : ℤ) ((n + j₂ : ℕ) : ℤ)
    ((n + d + i₁ : ℕ) : ℤ) ((n + d + i₂ : ℕ) : ℤ)
    ((j₂ : ℤ) - j₁) ((i₂ : ℤ) - i₁)
    (k5UpperFourMultiplier t i₁ : ℤ)
    (k5UpperFourMultiplier t i₂ : ℤ)
    (X : ℤ) (a : ℤ) (b : ℤ) (Mplus : ℤ) (Mminus : ℤ)
    Uplus Uminus (by exact_mod_cast hXpos.ne') hx hz hrowZ hcolumnZ hM
    (by simpa [k5OppositeSecantPlus] using hUplus.symm)
    (by simpa [k5OppositeSecantMinus] using hUminus.symm)
  exact ⟨a, b, hcop, by simpa [A, X] using hA,
    by simpa [B, X] using hB, Uplus, Uminus,
    by simpa [Mplus] using hUplus,
    by simpa [Mminus] using hUminus, hquot⟩

#print axioms opposite_secant_product_identity
#print axioms opposite_secant_quotient_cofactor_identity
#print axioms canonicalOwner_k5_opposite_crossing_products_dvd_secants
#print axioms k5_fullyOwned_opposite_secant_cofactor_identity

end Erdos686Variant
end Erdos686
