/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.K5.FourCrossingSecantGCD

/-!
# Erdős 686, k=5: lower divisibility in a zero secant-coefficient branch

The fixed-coefficient four-crossing bound has genuine zero branches.  In a
zero branch the cancelled tangent congruence instead forces the owner, after
removing its coefficient gcd, into the corresponding secant quotient.

The final theorem specializes this to the only `G = 12` residual profile
that defeats selection of a nonzero `2 x 2` coefficient grid.  Its zero is at
the `(4,1)` crossing.  The lower profile also makes `n+4`, and hence that
crossing owner, coprime to `24`, so the complete owner divides the minus
secant quotient and the associated secant gcd.
-/

namespace Erdos686
namespace Erdos686Variant

/-- Exact natural cancellation: if `P | c Q U` and `P` is coprime to `Q`,
then the part of `P` not already present in `c` divides `U`. -/
theorem reduced_modulus_dvd_of_dvd_coefficient_mul_coprime
    {P c Q U : ℕ} (hP : P ≠ 0)
    (hcop : Nat.Coprime P Q) (hdiv : P ∣ c * Q * U) :
    P / Nat.gcd P c ∣ U := by
  have hreorder : P ∣ (c * U) * Q := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hdiv
  have hcU : P ∣ c * U := hcop.dvd_of_dvd_mul_right hreorder
  obtain ⟨k, hk⟩ := hcU
  let g := Nat.gcd P c
  have hgP : g ∣ P := Nat.gcd_dvd_left P c
  have hgc : g ∣ c := Nat.gcd_dvd_right P c
  have hgpos : 0 < g :=
    Nat.gcd_pos_of_pos_left c (Nat.pos_of_ne_zero hP)
  have hcopred : Nat.Coprime (P / g) (c / g) :=
    Nat.coprime_div_gcd_div_gcd hgpos
  have heq : (c / g) * U = (P / g) * k := by
    calc
      (c / g) * U = (c * U) / g := by
        rw [mul_comm c U, Nat.mul_div_assoc U hgc]
        ac_rfl
      _ = (P * k) / g := by rw [hk]
      _ = (P / g) * k := by
        rw [mul_comm P k, Nat.mul_div_assoc k hgP]
        ac_rfl
  apply hcopred.dvd_of_dvd_mul_left
  exact ⟨k, heq⟩

/-- The exact `G=12` residual vectors whose only fully owned grid is rows
`{2,4}` and columns `{1,3}`. -/
def K5G12ZeroResidualProfile
    {n d t : ℕ} (data : CanonicalOwnerData 5 n d t) : Prop :=
  t = 4 ∧
  canonicalLowerResidual data 1 = 2 ∧
  canonicalLowerResidual data 2 = 1 ∧
  canonicalLowerResidual data 3 = 2 ∧
  canonicalLowerResidual data 4 = 1 ∧
  canonicalLowerResidual data 5 = 3 ∧
  canonicalUpperResidual data 1 = 1 ∧
  canonicalUpperResidual data 2 = 2 ∧
  canonicalUpperResidual data 3 = 1 ∧
  canonicalUpperResidual data 4 = 2 ∧
  canonicalUpperResidual data 5 = 3

private theorem k5_G12_zero_profile_n_mod_six
    {n d t : ℕ} {data : CanonicalOwnerData 5 n d t}
    (hprofile : K5G12ZeroResidualProfile data) :
    n % 6 = 1 := by
  have h2 : 2 ∣ n + 1 := by
    have hfac := canonical_lower_term_factorization data (j := 1)
    rw [hprofile.2.1] at hfac
    exact ⟨canonicalOwnerRow data 1, hfac⟩
  have h3 : 3 ∣ n + 5 := by
    have hfac := canonical_lower_term_factorization data (j := 5)
    rw [hprofile.2.2.2.2.2.1] at hfac
    exact ⟨canonicalOwnerRow data 5, hfac⟩
  have hmod2 : (n + 1) % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp h2
  have hmod3 : (n + 5) % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp h3
  rw [Nat.add_mod] at hmod2 hmod3
  have hn6 := Nat.mod_lt n (by norm_num : 0 < 6)
  omega

private theorem k5_G12_zero_profile_lower_four_coprime_twenty_four
    {n d t : ℕ} {data : CanonicalOwnerData 5 n d t}
    (hprofile : K5G12ZeroResidualProfile data) :
    Nat.Coprime (n + 4) 24 := by
  have hn := k5_G12_zero_profile_n_mod_six hprofile
  have hcop6 : Nat.Coprime (n + 4) 6 := by
    apply Nat.coprime_of_mul_modEq_one 5
    change ((n + 4) * 5) % 6 = 1 % 6
    omega
  have hcop216 : Nat.Coprime (n + 4) (6 ^ 3) := hcop6.pow_right 3
  exact Nat.Coprime.coprime_dvd_right
    (by norm_num : 24 ∣ 6 ^ 3) hcop216

/-- In the obstructing `G=12` profile, the zero tangent coefficient at the
`(4,1)` crossing forces the whole crossing owner into `Uminus`.  Therefore it
also divides the gcd of that owner with `Uplus*Uminus`. -/
theorem k5_G12_zero_crossing_owner_dvd_minus_secant_and_gcd
    {n d t : ℕ}
    (data : CanonicalOwnerData 5 n d t)
    (hfour : 4 ∣ n + d + t)
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n)
    (hprofile : K5G12ZeroResidualProfile data) :
    let P₂₁ := canonicalOwnerCell data 4 1
    let P₁₂ := canonicalOwnerCell data 2 3
    ∃ Uplus Uminus : ℤ,
      k5OppositeSecantPlus n d 2 4 1 3 =
          ((canonicalOwnerCell data 2 1 *
            canonicalOwnerCell data 4 3 : ℕ) : ℤ) * Uplus ∧
      k5OppositeSecantMinus n d 2 4 1 3 =
          ((P₁₂ * P₂₁ : ℕ) : ℤ) * Uminus ∧
      P₂₁ / Nat.gcd P₂₁ 24 ∣ Uminus.natAbs ∧
      P₂₁ / Nat.gcd P₂₁ 24 ∣
        Nat.gcd P₂₁ (Uplus * Uminus).natAbs ∧
      Nat.Coprime P₂₁ 24 ∧
      P₂₁ ∣ Uminus.natAbs ∧
      P₂₁ ∣ Nat.gcd P₂₁ (Uplus * Uminus).natAbs := by
  dsimp only
  let P₂₁ := canonicalOwnerCell data 4 1
  let P₁₂ := canonicalOwnerCell data 2 3
  obtain ⟨hplusDvd, hminusDvd⟩ :=
    canonicalOwner_k5_opposite_crossing_products_dvd_secants
      (j₁ := 2) (j₂ := 4) (i₁ := 1) (i₂ := 3)
      data (by norm_num) hfour
  obtain ⟨Uplus, hplus⟩ := hplusDvd
  obtain ⟨Uminus, hminus⟩ := hminusDvd
  have hplus' :
      k5OppositeSecantPlus n d 2 4 1 3 =
        ((canonicalOwnerCell data 2 1 *
          canonicalOwnerCell data 4 3 : ℕ) : ℤ) * Uplus := by
    exact hplus
  have hminus' :
      k5OppositeSecantMinus n d 2 4 1 3 =
        ((P₁₂ * P₂₁ : ℕ) : ℤ) * Uminus := by
    simpa [P₁₂, P₂₁] using hminus
  have hP : P₂₁ ≠ 0 := (canonicalOwnerCell_pos data).ne'
  have hD : ((P₂₁ : ℤ) ^ 2) ∣ k5OwnerSquareDefect n d 4 1 := by
    simpa [P₂₁] using canonicalOwnerCell_sq_dvd_k5OwnerSquareDefect
      data (by norm_num) (by norm_num) hfour heq
  have hminusCast :
      (P₂₁ : ℤ) * (P₁₂ : ℤ) * Uminus =
        k5OppositeSecantMinus n d 2 4 1 3 := by
    calc
      (P₂₁ : ℤ) * (P₁₂ : ℤ) * Uminus =
          ((P₁₂ * P₂₁ : ℕ) : ℤ) * Uminus := by push_cast; ring
      _ = k5OppositeSecantMinus n d 2 4 1 3 := hminus'.symm
  have hidentity :
      (24 : ℤ) * (((P₂₁ : ℤ) * (P₁₂ : ℤ)) * Uminus) =
        2 * k5OwnerSquareDefect n d 4 1 := by
    rw [hminusCast]
    simp only [k5OppositeSecantMinus, k5OwnerSquareDefect]
    rw [localBlockCoefficient_eq_sign_mul_nat (by norm_num : 1 ∈ Finset.Icc 1 5),
      localBlockCoefficient_eq_sign_mul_nat (by norm_num : 4 ∈ Finset.Icc 1 5)]
    norm_num [localBlockCoefficientNat]
    ring
  have hsquare : ((P₂₁ : ℤ) ^ 2) ∣
      (24 : ℤ) * (((P₂₁ : ℤ) * (P₁₂ : ℤ)) * Uminus) := by
    rw [hidentity]
    exact dvd_mul_of_dvd_right hD 2
  have hfirstZ : (P₂₁ : ℤ) ∣
      (24 : ℤ) * (P₁₂ : ℤ) * Uminus := by
    have hcancel := owner_dvd_resultantQuotient_tangent_defect
      (P := (P₂₁ : ℤ)) (b := 24) (Mrest := (P₁₂ : ℤ))
      (U := Uminus) (kappa := 0) (xrest := 0)
      (by exact_mod_cast hP) (by simpa [mul_assoc] using hsquare)
    simpa using hcancel
  have hfirst : P₂₁ ∣ 24 * P₁₂ * Uminus.natAbs := by
    have h := Int.natAbs_dvd_natAbs.mpr hfirstZ
    simpa [Int.natAbs_mul, mul_assoc] using h
  have hcopCross : Nat.Coprime P₂₁ P₁₂ := by
    dsimp [P₂₁, P₁₂]
    apply canonicalOwnerCells_pairwise_coprime data
    norm_num
  have hreduced : P₂₁ / Nat.gcd P₂₁ 24 ∣ Uminus.natAbs :=
    reduced_modulus_dvd_of_dvd_coefficient_mul_coprime
      hP hcopCross hfirst
  have hreducedP : P₂₁ / Nat.gcd P₂₁ 24 ∣ P₂₁ :=
    Nat.div_dvd_of_dvd (Nat.gcd_dvd_left P₂₁ 24)
  have hUminusProduct : Uminus.natAbs ∣ (Uplus * Uminus).natAbs := by
    rw [Int.natAbs_mul]
    exact dvd_mul_left _ _
  have hreducedProduct :
      P₂₁ / Nat.gcd P₂₁ 24 ∣ (Uplus * Uminus).natAbs :=
    hreduced.trans hUminusProduct
  have hreducedGcd : P₂₁ / Nat.gcd P₂₁ 24 ∣
      Nat.gcd P₂₁ (Uplus * Uminus).natAbs :=
    Nat.dvd_gcd hreducedP hreducedProduct
  have hcopTerm :=
    k5_G12_zero_profile_lower_four_coprime_twenty_four hprofile
  have hPdvdTerm : P₂₁ ∣ n + 4 := by
    exact canonicalOwnerCell_dvd_lower data
  have hcop24 : Nat.Coprime P₂₁ 24 := hcopTerm.of_dvd_left hPdvdTerm
  have hgcdOne : Nat.gcd P₂₁ 24 = 1 := hcop24.gcd_eq_one
  have hPdvdU : P₂₁ ∣ Uminus.natAbs := by
    simpa [hgcdOne] using hreduced
  have hPdvdProduct : P₂₁ ∣ (Uplus * Uminus).natAbs :=
    hPdvdU.trans hUminusProduct
  have hPdvdGcd : P₂₁ ∣ Nat.gcd P₂₁ (Uplus * Uminus).natAbs :=
    Nat.dvd_gcd (dvd_refl P₂₁) hPdvdProduct
  exact ⟨Uplus, Uminus, hplus', hminus', hreduced, hreducedGcd,
    hcop24, hPdvdU, hPdvdGcd⟩

#print axioms reduced_modulus_dvd_of_dvd_coefficient_mul_coprime
#print axioms k5_G12_zero_crossing_owner_dvd_minus_secant_and_gcd

end Erdos686Variant
end Erdos686
