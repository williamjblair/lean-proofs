/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.K5.G12SecantComplement

/-!
# Erdős 686, k=5: primitivity of the exceptional secant quotient

Write the exceptional complement sum as `R+C = P Q K`.  The square tangent
at the other crossing `Q` gives a congruence modulo `Q` involving `K` and the
row complement of `Q`.  Independently, the nonzero local opposite-secant
coefficient bounds the common part of `Q` and the secant quotient by `56`.
The tangent congruence forces the common part of `Q` and `K` into the single
exceptional prime `5`.  Thus the complement quotient is primitive away from
characteristic five.  This is not a reformulation of `P Q | R+C`.
-/

namespace Erdos686
namespace Erdos686Variant

private theorem fully_owned_row_cell_coprime_quotient
    {k n d t j i : ℕ}
    (data : CanonicalOwnerData k n d t)
    (hi : i ∈ Finset.Icc 1 k)
    (hlower : canonicalLowerResidual data j = 1) :
    Nat.Coprime (canonicalOwnerCell data j i)
      ((n + j) / canonicalOwnerCell data j i) := by
  classical
  let S := Finset.Icc 1 k
  let P := canonicalOwnerCell data j i
  let T := ∏ i' ∈ S.erase i, canonicalOwnerCell data j i'
  have hcop : Nat.Coprime P T := by
    dsimp [P, T]
    apply Nat.Coprime.prod_right
    intro i' hi'
    apply canonicalOwnerCells_pairwise_coprime data
    intro heq
    have hii' : i = i' := congrArg Prod.snd heq
    subst i'
    exact (Finset.mem_erase.mp hi').1 rfl
  have hrow : n + j = P * T := by
    calc
      n + j = canonicalOwnerRow data j := by
        rw [canonical_lower_term_factorization data, hlower, one_mul]
      _ = ∏ i' ∈ S, canonicalOwnerCell data j i' := by
        rw [canonicalOwner_row_cell_product data]
      _ = P * T := by
        symm
        exact Finset.mul_prod_erase S
          (fun i' => canonicalOwnerCell data j i') hi
  have hPpos : 0 < P := by
    dsimp [P]
    exact canonicalOwnerCell_pos data
  have hquot : (n + j) / P = T := by
    rw [hrow]
    exact Nat.mul_div_cancel_left T hPpos
  simpa [P, hquot] using hcop

/-- In the exceptional profile, the only possible common prime between the
quotient `K` in `R+C=P Q K` and the second crossing owner `Q` is `5`.
The displayed congruence is the independent `Q`-tangent relation. -/
theorem k5_G12_exceptional_complement_quotient_gcd_Q_dvd_five
    {n d t : ℕ}
    (data : CanonicalOwnerData 5 n d t)
    (hfour : 4 ∣ n + d + t)
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n)
    (hprofile : K5G12ZeroResidualProfile data) :
    let P := canonicalOwnerCell data 4 1
    let Q := canonicalOwnerCell data 2 3
    let R := (n + 4) / P
    let C := (n + d + 1) / P
    let K := (R + C) / (P * Q)
    let S := (n + 2) / Q
    let D := (n + d + 3) / Q
    R + C = P * Q * K ∧
      n + 2 = Q * S ∧
      n + d + 3 = Q * D ∧
      S + D = P ^ 2 * K ∧
      Q ∣ P ^ 2 * K + 5 * S ∧
      Nat.Coprime Q S ∧
      Nat.gcd Q K ∣ 5 ∧
      (Nat.Coprime Q K ∨ (5 ∣ Q ∧ 5 ∣ K)) := by
  dsimp only
  let P := canonicalOwnerCell data 4 1
  let Q := canonicalOwnerCell data 2 3
  let R := (n + 4) / P
  let C := (n + d + 1) / P
  let K := (R + C) / (P * Q)
  let S := (n + 2) / Q
  let D := (n + d + 3) / Q
  have hPpos : 0 < P := by
    dsimp [P]
    exact canonicalOwnerCell_pos data
  have hQpos : 0 < Q := by
    dsimp [Q]
    exact canonicalOwnerCell_pos data
  have hPdvdLower : P ∣ n + 4 := by
    dsimp [P]
    exact canonicalOwnerCell_dvd_lower data
  have hPdvdUpper : P ∣ n + d + 1 := by
    dsimp [P]
    have hmodified := canonicalOwnerCell_dvd_upper data (j := 4) (i := 1)
    simpa [upperTermAfterFour, hprofile.1] using hmodified
  have hQdvdLower : Q ∣ n + 2 := by
    dsimp [Q]
    exact canonicalOwnerCell_dvd_lower data
  have hQdvdUpper : Q ∣ n + d + 3 := by
    dsimp [Q]
    have hmodified := canonicalOwnerCell_dvd_upper data (j := 2) (i := 3)
    simpa [upperTermAfterFour, hprofile.1] using hmodified
  have hrowP : n + 4 = P * R := by
    dsimp [R]
    exact (Nat.mul_div_cancel' hPdvdLower).symm
  have hcolumnP : n + d + 1 = P * C := by
    dsimp [C]
    exact (Nat.mul_div_cancel' hPdvdUpper).symm
  have hrowQ : n + 2 = Q * S := by
    dsimp [S]
    exact (Nat.mul_div_cancel' hQdvdLower).symm
  have hcolumnQ : n + d + 3 = Q * D := by
    dsimp [D]
    exact (Nat.mul_div_cancel' hQdvdUpper).symm
  obtain ⟨Uplus, Uminus, -, hminus, -, -, hcopP24, hPdvdU, -⟩ :=
    k5_G12_zero_crossing_owner_dvd_minus_secant_and_gcd
      data hfour heq hprofile
  have hQcop2 : Nat.Coprime Q 2 := by
    have htwoLower : 2 ∣ n + 1 := by
      have hfactor := canonical_lower_term_factorization data (j := 1)
      rw [hprofile.2.1] at hfactor
      exact ⟨canonicalOwnerRow data 1, hfactor⟩
    obtain ⟨z, hz⟩ := htwoLower
    have hodd : Odd (n + 2) := ⟨z, by omega⟩
    exact Nat.Coprime.coprime_dvd_left hQdvdLower
      (Nat.coprime_two_right.mpr hodd)
  have hPcop2 : Nat.Coprime P 2 := by
    exact hcopP24.coprime_dvd_right (by norm_num : 2 ∣ 24)
  have hsumDvd : P * Q ∣ R + C := by
    have hsecant :
        k5OppositeSecantMinus n d 2 4 1 3 =
          ((2 * ((n + 4) + (n + d + 1)) : ℕ) : ℤ) := by
      simp only [k5OppositeSecantMinus]
      push_cast
      ring
    have hminusAbs :
        2 * ((n + 4) + (n + d + 1)) = (Q * P) * Uminus.natAbs := by
      have habs := congrArg Int.natAbs hminus
      rw [hsecant] at habs
      simpa [Q, P, Int.natAbs_mul] using habs
    obtain ⟨W, hW⟩ := hPdvdU
    have hcancelled : 2 * (R + C) = Q * P * W := by
      have hmul : P * (2 * (R + C)) = P * (Q * P * W) := by
        calc
          P * (2 * (R + C)) = 2 * ((n + 4) + (n + d + 1)) := by
            rw [hrowP, hcolumnP]
            ring
          _ = (Q * P) * Uminus.natAbs := hminusAbs
          _ = P * (Q * P * W) := by rw [hW]; ring
      exact Nat.mul_left_cancel hPpos hmul
    have hPQdvdTwice : P * Q ∣ 2 * (R + C) := by
      refine ⟨W, ?_⟩
      rw [hcancelled]
      ring
    exact (hPcop2.mul_left hQcop2).dvd_of_dvd_mul_left hPQdvdTwice
  have hsum : R + C = P * Q * K := by
    dsimp [K]
    exact (Nat.mul_div_cancel' hsumDvd).symm
  have hSD : S + D = P ^ 2 * K := by
    have hmul : Q * (S + D) = Q * (P ^ 2 * K) := by
      calc
        Q * (S + D) = (n + 2) + (n + d + 3) := by
          rw [hrowQ, hcolumnQ]
          ring
        _ = (n + 4) + (n + d + 1) := by omega
        _ = P * (R + C) := by rw [hrowP, hcolumnP]; ring
        _ = Q * (P ^ 2 * K) := by rw [hsum]; ring
    exact Nat.mul_left_cancel hQpos hmul
  have hQcop4 : Nat.Coprime Q 4 := by
    simpa using hQcop2.pow_right 2
  have hQsq : ((Q : ℤ) ^ 2) ∣ k5OwnerSquareDefect n d 2 3 := by
    simpa [Q] using canonicalOwnerCell_sq_dvd_k5OwnerSquareDefect
      data (by norm_num) (by norm_num) hfour heq
  have hdefectIdentity :
      k5OwnerSquareDefect n d 2 3 =
        (4 : ℤ) * ((Q : ℤ) * (D + 6 * S : ℕ)) := by
    simp only [k5OwnerSquareDefect]
    rw [localBlockCoefficient_eq_sign_mul_nat (by norm_num : 3 ∈ Finset.Icc 1 5),
      localBlockCoefficient_eq_sign_mul_nat (by norm_num : 2 ∈ Finset.Icc 1 5)]
    norm_num [localBlockCoefficientNat]
    have hrowQZ : ((n + 2 : ℕ) : ℤ) = (Q : ℤ) * (S : ℤ) := by
      exact_mod_cast hrowQ
    have hcolumnQZ : ((n + d + 3 : ℕ) : ℤ) = (Q : ℤ) * (D : ℤ) := by
      exact_mod_cast hcolumnQ
    push_cast at hrowQZ hcolumnQZ
    rw [hrowQZ, hcolumnQZ]
    ring
  have hQdvdFour : Q ∣ 4 * (D + 6 * S) := by
    have hcancelZ : (Q : ℤ) ∣ (4 : ℤ) * (D + 6 * S : ℕ) := by
      apply owner_dvd_resultantQuotient_tangent_defect
        (P := (Q : ℤ)) (b := 4) (Mrest := 1)
        (U := (D + 6 * S : ℕ)) (kappa := 0) (xrest := 0)
        (by exact_mod_cast hQpos.ne')
      simpa [hdefectIdentity, mul_assoc] using hQsq
    exact_mod_cast hcancelZ
  have hQtangent0 : Q ∣ D + 6 * S :=
    hQcop4.dvd_of_dvd_mul_left hQdvdFour
  have hDidentity : D + 6 * S = P ^ 2 * K + 5 * S := by omega
  have hQtangent : Q ∣ P ^ 2 * K + 5 * S := by
    rw [← hDidentity]
    exact hQtangent0
  have hQcopS : Nat.Coprime Q S := by
    simpa [Q, S] using fully_owned_row_cell_coprime_quotient
      data (j := 2) (i := 3) (by norm_num) hprofile.2.2.1
  let g := Nat.gcd Q K
  have hgQ : g ∣ Q := Nat.gcd_dvd_left Q K
  have hgK : g ∣ K := Nat.gcd_dvd_right Q K
  have hgTangent : g ∣ P ^ 2 * K + 5 * S := hgQ.trans hQtangent
  have hgPK : g ∣ P ^ 2 * K := dvd_mul_of_dvd_right hgK (P ^ 2)
  have hgFiveS : g ∣ 5 * S := by
    exact (Nat.dvd_add_iff_right hgPK).mpr hgTangent
  have hgcopS : Nat.Coprime g S := hQcopS.of_dvd_left hgQ
  have hg5 : g ∣ 5 := hgcopS.dvd_of_dvd_mul_right hgFiveS
  have hdichotomy : Nat.Coprime Q K ∨ (5 ∣ Q ∧ 5 ∣ K) := by
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hg5 with hgEq | hgEq
    · left
      rw [Nat.coprime_iff_gcd_eq_one]
      exact hgEq
    · right
      constructor
      · simpa [g, hgEq] using Nat.gcd_dvd_left Q K
      · simpa [g, hgEq] using Nat.gcd_dvd_right Q K
  exact ⟨hsum, hrowQ, hcolumnQ, hSD, hQtangent, hQcopS, hg5,
    hdichotomy⟩

#print axioms k5_G12_exceptional_complement_quotient_gcd_Q_dvd_five

end Erdos686Variant
end Erdos686
