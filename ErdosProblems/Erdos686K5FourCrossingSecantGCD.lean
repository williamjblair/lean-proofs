/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686K5OppositeSecantTangentGCD

/-!
# Erdős 686, k=5: the four local opposite-secant gcds

The generic opposite-secant/tangent lemma can be applied at each vertex of
the proper-global `2 x 2` crossing grid.  At a vertex, the secant through
that vertex supplies the cancelled tangent congruence.  The other secant is
congruent to `±(j₂-j₁)(i₂-i₁)` modulo the crossing owner.  Consequently the
common part of that owner and the product of the two secant quotients divides
a fixed local coefficient; it is independent of `n` and `d`.

The four divisors below are the exact specialization.  They are an upper
bound, not a lower bound: pairwise coprimality alone does not force a crossing
owner to divide either secant quotient.
-/

namespace Erdos686
namespace Erdos686Variant

private theorem canonicalOwner_fullyOwned_row_cell_complement
    {k n d t j i : ℕ}
    (data : CanonicalOwnerData k n d t)
    (hi : i ∈ Finset.Icc 1 k)
    (hlower : canonicalLowerResidual data j = 1) :
    ∃ R : ℕ,
      Nat.Coprime (canonicalOwnerCell data j i) R ∧
      n + j = canonicalOwnerCell data j i * R := by
  classical
  let S := Finset.Icc 1 k
  let P := canonicalOwnerCell data j i
  let R := ∏ i' ∈ S.erase i, canonicalOwnerCell data j i'
  have hcop : Nat.Coprime P R := by
    dsimp [P, R]
    apply Nat.Coprime.prod_right
    intro i' hi'
    apply canonicalOwnerCells_pairwise_coprime data
    intro heq
    have hii' : i = i' := congrArg Prod.snd heq
    subst i'
    exact (Finset.mem_erase.mp hi').1 rfl
  have hrow : n + j = P * R := by
    calc
      n + j = canonicalOwnerRow data j := by
        rw [canonical_lower_term_factorization data, hlower, one_mul]
      _ = ∏ i' ∈ S, canonicalOwnerCell data j i' := by
        rw [canonicalOwner_row_cell_product data]
      _ = P * R := by
        symm
        exact Finset.mul_prod_erase S
          (fun i' => canonicalOwnerCell data j i') hi
  exact ⟨R, hcop, hrow⟩

private theorem local_crossing_gcd_dvd_of_tangent_identity
    {P xrest : ℕ} {M N U V q r D kappa epsilon : ℤ}
    (hP : P ≠ 0)
    (hcop : Nat.Coprime P xrest)
    (hD : ((P : ℤ) ^ 2) ∣ D)
    (hidentity :
      q * (((P : ℤ) * M) * U) -
          kappa * ((P : ℤ) * (xrest : ℤ)) = r * D)
    (hopposite : (P : ℤ) ∣ N * V - epsilon) :
    Nat.gcd P (U * V).natAbs ∣ (kappa * epsilon).natAbs := by
  apply local_tangent_opposite_secant_gcd_dvd_coefficient
    (C := q) hP hcop
  · rw [hidentity]
    exact dvd_mul_of_dvd_right hD r
  · exact hopposite

/-- At all four vertices of a fully owned proper-global crossing grid, the
gcd of the owner with the product of the two opposite-secant quotients divides
an explicit coefficient depending only on the four indices. -/
theorem k5_proper_global_four_crossing_secant_gcds_dvd_coefficients
    {n d t j₁ j₂ i₁ i₂ : ℕ}
    (data : CanonicalOwnerData 5 n d t)
    (hj₁ : j₁ ∈ Finset.Icc 1 5) (hj₂ : j₂ ∈ Finset.Icc 1 5)
    (hi₁ : i₁ ∈ Finset.Icc 1 5) (hi₂ : i₂ ∈ Finset.Icc 1 5)
    (hjneq : j₁ ≠ j₂)
    (hfour : 4 ∣ n + d + t)
    (hj₁one : canonicalLowerResidual data j₁ = 1)
    (hj₂one : canonicalLowerResidual data j₂ = 1)
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n) :
    let P₁₁ := canonicalOwnerCell data j₁ i₁
    let P₁₂ := canonicalOwnerCell data j₁ i₂
    let P₂₁ := canonicalOwnerCell data j₂ i₁
    let P₂₂ := canonicalOwnerCell data j₂ i₂
    let r : ℤ := (j₂ : ℤ) - j₁
    let s : ℤ := (i₂ : ℤ) - i₁
    let p₁ : ℤ := 4 * localBlockCoefficient 5 j₁
    let p₂ : ℤ := 4 * localBlockCoefficient 5 j₂
    let q₁ : ℤ := localBlockCoefficient 5 i₁
    let q₂ : ℤ := localBlockCoefficient 5 i₂
    ∃ Uplus Uminus : ℤ,
      k5OppositeSecantPlus n d j₁ j₂ i₁ i₂ =
          ((P₁₁ * P₂₂ : ℕ) : ℤ) * Uplus ∧
      k5OppositeSecantMinus n d j₁ j₂ i₁ i₂ =
          ((P₁₂ * P₂₁ : ℕ) : ℤ) * Uminus ∧
      Nat.gcd P₁₁ (Uplus * Uminus).natAbs ∣
        ((r * p₁ - s * q₁) * (r * s)).natAbs ∧
      Nat.gcd P₂₂ (Uplus * Uminus).natAbs ∣
        ((r * p₂ - s * q₂) * (r * s)).natAbs ∧
      Nat.gcd P₁₂ (Uplus * Uminus).natAbs ∣
        ((r * p₁ + s * q₂) * (r * s)).natAbs ∧
      Nat.gcd P₂₁ (Uplus * Uminus).natAbs ∣
        ((r * p₂ + s * q₁) * (r * s)).natAbs := by
  dsimp only
  let P₁₁ := canonicalOwnerCell data j₁ i₁
  let P₁₂ := canonicalOwnerCell data j₁ i₂
  let P₂₁ := canonicalOwnerCell data j₂ i₁
  let P₂₂ := canonicalOwnerCell data j₂ i₂
  let r : ℤ := (j₂ : ℤ) - j₁
  let s : ℤ := (i₂ : ℤ) - i₁
  let p₁ : ℤ := 4 * localBlockCoefficient 5 j₁
  let p₂ : ℤ := 4 * localBlockCoefficient 5 j₂
  let q₁ : ℤ := localBlockCoefficient 5 i₁
  let q₂ : ℤ := localBlockCoefficient 5 i₂
  obtain ⟨hplusDvd, hminusDvd⟩ :=
    canonicalOwner_k5_opposite_crossing_products_dvd_secants
      (i₁ := i₁) (i₂ := i₂) data hjneq hfour
  obtain ⟨Uplus, hplus⟩ := hplusDvd
  obtain ⟨Uminus, hminus⟩ := hminusDvd
  have hplus' :
      k5OppositeSecantPlus n d j₁ j₂ i₁ i₂ =
        (((P₁₁ * P₂₂ : ℕ) : ℤ) * Uplus) := by
    simpa [P₁₁, P₂₂] using hplus
  have hminus' :
      k5OppositeSecantMinus n d j₁ j₂ i₁ i₂ =
        (((P₁₂ * P₂₁ : ℕ) : ℤ) * Uminus) := by
    simpa [P₁₂, P₂₁] using hminus
  have hplusCast :
      (P₁₁ : ℤ) * (P₂₂ : ℤ) * Uplus =
        k5OppositeSecantPlus n d j₁ j₂ i₁ i₂ := by
    calc
      (P₁₁ : ℤ) * (P₂₂ : ℤ) * Uplus =
          ((P₁₁ * P₂₂ : ℕ) : ℤ) * Uplus := by push_cast; ring
      _ = k5OppositeSecantPlus n d j₁ j₂ i₁ i₂ := hplus'.symm
  have hplusCastComm :
      (P₂₂ : ℤ) * (P₁₁ : ℤ) * Uplus =
        k5OppositeSecantPlus n d j₁ j₂ i₁ i₂ := by
    rw [mul_comm (P₂₂ : ℤ) (P₁₁ : ℤ)]
    exact hplusCast
  have hminusCast :
      (P₁₂ : ℤ) * (P₂₁ : ℤ) * Uminus =
        k5OppositeSecantMinus n d j₁ j₂ i₁ i₂ := by
    calc
      (P₁₂ : ℤ) * (P₂₁ : ℤ) * Uminus =
          ((P₁₂ * P₂₁ : ℕ) : ℤ) * Uminus := by push_cast; ring
      _ = k5OppositeSecantMinus n d j₁ j₂ i₁ i₂ := hminus'.symm
  have hminusCastComm :
      (P₂₁ : ℤ) * (P₁₂ : ℤ) * Uminus =
        k5OppositeSecantMinus n d j₁ j₂ i₁ i₂ := by
    rw [mul_comm (P₂₁ : ℤ) (P₁₂ : ℤ)]
    exact hminusCast
  obtain ⟨R₁₁, hcop₁₁, hrow₁₁⟩ :=
    canonicalOwner_fullyOwned_row_cell_complement data hi₁ hj₁one
  obtain ⟨R₁₂, hcop₁₂, hrow₁₂⟩ :=
    canonicalOwner_fullyOwned_row_cell_complement data hi₂ hj₁one
  obtain ⟨R₂₁, hcop₂₁, hrow₂₁⟩ :=
    canonicalOwner_fullyOwned_row_cell_complement data hi₁ hj₂one
  obtain ⟨R₂₂, hcop₂₂, hrow₂₂⟩ :=
    canonicalOwner_fullyOwned_row_cell_complement data hi₂ hj₂one
  have hP₁₁ : P₁₁ ≠ 0 := (canonicalOwnerCell_pos data).ne'
  have hP₁₂ : P₁₂ ≠ 0 := (canonicalOwnerCell_pos data).ne'
  have hP₂₁ : P₂₁ ≠ 0 := (canonicalOwnerCell_pos data).ne'
  have hP₂₂ : P₂₂ ≠ 0 := (canonicalOwnerCell_pos data).ne'
  have hD₁₁ := canonicalOwnerCell_sq_dvd_k5OwnerSquareDefect
    data hj₁ hi₁ hfour heq
  have hD₁₂ := canonicalOwnerCell_sq_dvd_k5OwnerSquareDefect
    data hj₁ hi₂ hfour heq
  have hD₂₁ := canonicalOwnerCell_sq_dvd_k5OwnerSquareDefect
    data hj₂ hi₁ hfour heq
  have hD₂₂ := canonicalOwnerCell_sq_dvd_k5OwnerSquareDefect
    data hj₂ hi₂ hfour heq
  have hx₁₁ : ((n + j₁ : ℕ) : ℤ) = (P₁₁ : ℤ) * (R₁₁ : ℤ) := by
    exact_mod_cast hrow₁₁
  have hx₁₂ : ((n + j₁ : ℕ) : ℤ) = (P₁₂ : ℤ) * (R₁₂ : ℤ) := by
    exact_mod_cast hrow₁₂
  have hx₂₁ : ((n + j₂ : ℕ) : ℤ) = (P₂₁ : ℤ) * (R₂₁ : ℤ) := by
    exact_mod_cast hrow₂₁
  have hx₂₂ : ((n + j₂ : ℕ) : ℤ) = (P₂₂ : ℤ) * (R₂₂ : ℤ) := by
    exact_mod_cast hrow₂₂
  have hdvdLower (j i : ℕ) :
      ((canonicalOwnerCell data j i : ℕ) : ℤ) ∣ ((n + j : ℕ) : ℤ) := by
    exact_mod_cast canonicalOwnerCell_dvd_lower data
  have hdvdUpper (j i : ℕ) :
      ((canonicalOwnerCell data j i : ℕ) : ℤ) ∣ ((n + d + i : ℕ) : ℤ) := by
    exact_mod_cast dvd_trans (canonicalOwnerCell_dvd_upper data)
      (upperTermAfterFour_dvd_original hfour)
  have hop₁₁ : (P₁₁ : ℤ) ∣
      ((P₁₂ * P₂₁ : ℕ) : ℤ) * Uminus - r * s := by
    rw [← hminus']
    have hsum := dvd_add
      (dvd_mul_of_dvd_right (hdvdUpper j₁ i₁) r)
      (dvd_mul_of_dvd_right (hdvdLower j₁ i₁) s)
    convert hsum using 1 <;>
      simp only [k5OppositeSecantMinus, r, s] <;> push_cast <;> ring
  have hop₂₂ : (P₂₂ : ℤ) ∣
      ((P₁₂ * P₂₁ : ℕ) : ℤ) * Uminus - (-(r * s)) := by
    rw [← hminus']
    have hsum := dvd_add
      (dvd_mul_of_dvd_right (hdvdUpper j₂ i₂) r)
      (dvd_mul_of_dvd_right (hdvdLower j₂ i₂) s)
    convert hsum using 1 <;>
      simp only [k5OppositeSecantMinus, r, s] <;> push_cast <;> ring
  have hop₁₂ : (P₁₂ : ℤ) ∣
      ((P₁₁ * P₂₂ : ℕ) : ℤ) * Uplus - (-(r * s)) := by
    rw [← hplus']
    have hsub := dvd_sub
      (dvd_mul_of_dvd_right (hdvdUpper j₁ i₂) r)
      (dvd_mul_of_dvd_right (hdvdLower j₁ i₂) s)
    convert hsub using 1 <;>
      simp only [k5OppositeSecantPlus, r, s] <;> push_cast <;> ring
  have hop₂₁ : (P₂₁ : ℤ) ∣
      ((P₁₁ * P₂₂ : ℕ) : ℤ) * Uplus - r * s := by
    rw [← hplus']
    have hsub := dvd_sub
      (dvd_mul_of_dvd_right (hdvdUpper j₂ i₁) r)
      (dvd_mul_of_dvd_right (hdvdLower j₂ i₁) s)
    convert hsub using 1 <;>
      simp only [k5OppositeSecantPlus, r, s] <;> push_cast <;> ring
  have hid₁₁ :
      q₁ * (((P₁₁ : ℤ) * (P₂₂ : ℤ)) * Uplus) -
          (r * p₁ - s * q₁) * ((P₁₁ : ℤ) * (R₁₁ : ℤ)) =
        r * k5OwnerSquareDefect n d j₁ i₁ := by
    rw [← hx₁₁, hplusCast]
    simp only [k5OppositeSecantPlus, k5OwnerSquareDefect,
      r, s, p₁, q₁]
    push_cast
    ring
  have hid₂₂ :
      q₂ * (((P₂₂ : ℤ) * (P₁₁ : ℤ)) * Uplus) -
          (r * p₂ - s * q₂) * ((P₂₂ : ℤ) * (R₂₂ : ℤ)) =
        r * k5OwnerSquareDefect n d j₂ i₂ := by
    rw [← hx₂₂, hplusCastComm]
    simp only [k5OppositeSecantPlus, k5OwnerSquareDefect,
      r, s, p₂, q₂]
    push_cast
    ring
  have hid₁₂ :
      q₂ * (((P₁₂ : ℤ) * (P₂₁ : ℤ)) * Uminus) -
          (r * p₁ + s * q₂) * ((P₁₂ : ℤ) * (R₁₂ : ℤ)) =
        r * k5OwnerSquareDefect n d j₁ i₂ := by
    rw [← hx₁₂, hminusCast]
    simp only [k5OppositeSecantMinus, k5OwnerSquareDefect,
      r, s, p₁, q₂]
    push_cast
    ring
  have hid₂₁ :
      q₁ * (((P₂₁ : ℤ) * (P₁₂ : ℤ)) * Uminus) -
          (r * p₂ + s * q₁) * ((P₂₁ : ℤ) * (R₂₁ : ℤ)) =
        r * k5OwnerSquareDefect n d j₂ i₁ := by
    rw [← hx₂₁, hminusCastComm]
    simp only [k5OppositeSecantMinus, k5OwnerSquareDefect,
      r, s, p₂, q₁]
    push_cast
    ring
  have hg₁₁ := local_crossing_gcd_dvd_of_tangent_identity
    hP₁₁ hcop₁₁ hD₁₁ hid₁₁ hop₁₁
  have hg₂₂ := local_crossing_gcd_dvd_of_tangent_identity
    hP₂₂ hcop₂₂ hD₂₂ hid₂₂ hop₂₂
  have hg₁₂ := local_crossing_gcd_dvd_of_tangent_identity
    hP₁₂ hcop₁₂ hD₁₂ hid₁₂ hop₁₂
  have hg₂₁ := local_crossing_gcd_dvd_of_tangent_identity
    hP₂₁ hcop₂₁ hD₂₁ hid₂₁ hop₂₁
  refine ⟨Uplus, Uminus, hplus', hminus', ?_, ?_, ?_, ?_⟩
  · simpa [mul_assoc] using hg₁₁
  · simpa [Int.natAbs_neg, mul_assoc] using hg₂₂
  · simpa [Int.natAbs_neg, mul_assoc, mul_left_comm, mul_comm] using hg₁₂
  · simpa [mul_assoc, mul_left_comm, mul_comm] using hg₂₁

/-- Pairwise coprimality identifies the product of the four local gcds with
the gcd of the full crossing product and the secant-quotient product.  Hence
that single gcd divides a completely explicit index-dependent integer. -/
theorem k5_proper_global_crossing_product_secant_gcd_dvd_coefficient_product
    {n d t j₁ j₂ i₁ i₂ : ℕ}
    (data : CanonicalOwnerData 5 n d t)
    (hj₁ : j₁ ∈ Finset.Icc 1 5) (hj₂ : j₂ ∈ Finset.Icc 1 5)
    (hi₁ : i₁ ∈ Finset.Icc 1 5) (hi₂ : i₂ ∈ Finset.Icc 1 5)
    (hjneq : j₁ ≠ j₂) (hineq : i₁ ≠ i₂)
    (hfour : 4 ∣ n + d + t)
    (hj₁one : canonicalLowerResidual data j₁ = 1)
    (hj₂one : canonicalLowerResidual data j₂ = 1)
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n) :
    let P₁₁ := canonicalOwnerCell data j₁ i₁
    let P₁₂ := canonicalOwnerCell data j₁ i₂
    let P₂₁ := canonicalOwnerCell data j₂ i₁
    let P₂₂ := canonicalOwnerCell data j₂ i₂
    let r : ℤ := (j₂ : ℤ) - j₁
    let s : ℤ := (i₂ : ℤ) - i₁
    let p₁ : ℤ := 4 * localBlockCoefficient 5 j₁
    let p₂ : ℤ := 4 * localBlockCoefficient 5 j₂
    let q₁ : ℤ := localBlockCoefficient 5 i₁
    let q₂ : ℤ := localBlockCoefficient 5 i₂
    ∃ Uplus Uminus : ℤ,
      k5OppositeSecantPlus n d j₁ j₂ i₁ i₂ =
          ((P₁₁ * P₂₂ : ℕ) : ℤ) * Uplus ∧
      k5OppositeSecantMinus n d j₁ j₂ i₁ i₂ =
          ((P₁₂ * P₂₁ : ℕ) : ℤ) * Uminus ∧
      Nat.gcd (P₁₁ * P₂₂ * (P₁₂ * P₂₁))
          (Uplus * Uminus).natAbs ∣
        ((r * p₁ - s * q₁) * (r * s)).natAbs *
          ((r * p₂ - s * q₂) * (r * s)).natAbs *
          (((r * p₁ + s * q₂) * (r * s)).natAbs *
            ((r * p₂ + s * q₁) * (r * s)).natAbs) := by
  dsimp only
  let P₁₁ := canonicalOwnerCell data j₁ i₁
  let P₁₂ := canonicalOwnerCell data j₁ i₂
  let P₂₁ := canonicalOwnerCell data j₂ i₁
  let P₂₂ := canonicalOwnerCell data j₂ i₂
  let r : ℤ := (j₂ : ℤ) - j₁
  let s : ℤ := (i₂ : ℤ) - i₁
  let p₁ : ℤ := 4 * localBlockCoefficient 5 j₁
  let p₂ : ℤ := 4 * localBlockCoefficient 5 j₂
  let q₁ : ℤ := localBlockCoefficient 5 i₁
  let q₂ : ℤ := localBlockCoefficient 5 i₂
  obtain ⟨Uplus, Uminus, hplus, hminus, h₁₁, h₂₂, h₁₂, h₂₁⟩ :=
    k5_proper_global_four_crossing_secant_gcds_dvd_coefficients
      data hj₁ hj₂ hi₁ hi₂ hjneq hfour hj₁one hj₂one heq
  let S := (Uplus * Uminus).natAbs
  have hpair (j i j' i' : ℕ)
      (hne : (j, i) ≠ (j', i')) :
      Nat.Coprime (canonicalOwnerCell data j i)
        (canonicalOwnerCell data j' i') :=
    canonicalOwnerCells_pairwise_coprime data hne
  have h₁₁₂₂ : Nat.Coprime P₁₁ P₂₂ := by
    apply hpair
    intro h
    exact hjneq (congrArg Prod.fst h)
  have h₁₂₂₁ : Nat.Coprime P₁₂ P₂₁ := by
    apply hpair
    intro h
    exact hjneq (congrArg Prod.fst h)
  have h₁₁₁₂ : Nat.Coprime P₁₁ P₁₂ := by
    apply hpair
    intro h
    exact hineq (congrArg Prod.snd h)
  have h₁₁₂₁ : Nat.Coprime P₁₁ P₂₁ := by
    apply hpair
    intro h
    exact hjneq (congrArg Prod.fst h)
  have h₂₂₁₂ : Nat.Coprime P₂₂ P₁₂ := by
    apply hpair
    intro h
    exact hjneq ((congrArg Prod.fst h).symm)
  have h₂₂₂₁ : Nat.Coprime P₂₂ P₂₁ := by
    apply hpair
    intro h
    exact hineq ((congrArg Prod.snd h).symm)
  have hblocks : Nat.Coprime (P₁₁ * P₂₂) (P₁₂ * P₂₁) :=
    (h₁₁₁₂.mul_right h₁₁₂₁).mul_left
      (h₂₂₁₂.mul_right h₂₂₂₁)
  have hgcd :
      Nat.gcd (P₁₁ * P₂₂ * (P₁₂ * P₂₁)) S =
        Nat.gcd P₁₁ S * Nat.gcd P₂₂ S *
          (Nat.gcd P₁₂ S * Nat.gcd P₂₁ S) := by
    rw [hblocks.mul_gcd S, h₁₁₂₂.mul_gcd S, h₁₂₂₁.mul_gcd S]
  have hprod := Nat.mul_dvd_mul (Nat.mul_dvd_mul h₁₁ h₂₂)
    (Nat.mul_dvd_mul h₁₂ h₂₁)
  refine ⟨Uplus, Uminus, hplus, hminus, ?_⟩
  rw [hgcd]
  simpa [S, r, s, p₁, p₂, q₁, q₂, P₁₁, P₁₂, P₂₁, P₂₂,
    mul_assoc] using hprod

#print axioms k5_proper_global_four_crossing_secant_gcds_dvd_coefficients
#print axioms k5_proper_global_crossing_product_secant_gcd_dvd_coefficient_product

end Erdos686Variant
end Erdos686
