/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686K5ZeroSecantGCDLower

/-!
# Erdős 686, k=5: the exceptional G=12 secant complement

In the unique `G=12` residual profile whose fully owned `2 x 2` grid has a
zero tangent coefficient, the zero crossing owner occurs in both the exact
minus-secant factorization and its quotient.  Cancelling that owner against
the fully owned row and column equations leaves a new global divisibility:
the product of two crossing owners divides the sum of the complementary row
and column cofactors.  The centered tail window then bounds that product by
strictly less than three times the row complement.
-/

namespace Erdos686
namespace Erdos686Variant

/-- The exceptional zero-secant branch forces an owner product into a sum of
two exact row/column complements.  This is stronger than the preceding
divisibility of the secant quotient: it cancels the common crossing owner and
the factor `2`, and records the strict centered-window bound. -/
theorem k5_G12_zero_crossing_product_dvd_complement_sum
    {n d t : ℕ}
    (data : CanonicalOwnerData 5 n d t)
    (hfour : 4 ∣ n + d + t)
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n)
    (hprofile : K5G12ZeroResidualProfile data)
    (htail : 10 ^ 1000 ≤ d)
    (hdlt : d < n)
    (hcells : ∀ j ∈ Finset.Icc 1 5, ∀ i ∈ Finset.Icc 1 5,
      1 < canonicalOwnerCell data j i) :
    let P := canonicalOwnerCell data 4 1
    let Q := canonicalOwnerCell data 2 3
    let R := (n + 4) / P
    let C := (n + d + 1) / P
    n + 4 = P * R ∧
      n + d + 1 = P * C ∧
      Nat.Coprime (P * Q) 2 ∧
      P * Q ∣ R + C ∧
      Nat.Coprime R C ∧
      Nat.Coprime (P * Q) (R * C) ∧
      P * Q ≤ R + C ∧
      R < C ∧ C < 2 * R ∧
      2 * C < 3 * R ∧
      P * Q < 3 * R ∧
      2 * (P * Q) < 5 * R ∧
      15 ≤ P * Q := by
  dsimp only
  let P := canonicalOwnerCell data 4 1
  let Q := canonicalOwnerCell data 2 3
  let R := (n + 4) / P
  let C := (n + d + 1) / P
  obtain ⟨Uplus, Uminus, -, hminus, -, -, hcopP24, hPdvdU, -⟩ :=
    k5_G12_zero_crossing_owner_dvd_minus_secant_and_gcd
      data hfour heq hprofile
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
  have hrow : n + 4 = P * R := by
    dsimp [R]
    exact (Nat.mul_div_cancel' hPdvdLower).symm
  have hcolumn : n + d + 1 = P * C := by
    dsimp [C]
    exact (Nat.mul_div_cancel' hPdvdUpper).symm
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
    simpa [Q, P, Int.natAbs_mul, mul_assoc] using habs
  obtain ⟨W, hW⟩ := hPdvdU
  have hcancelled : 2 * (R + C) = Q * P * W := by
    have hmul : P * (2 * (R + C)) = P * (Q * P * W) := by
      calc
        P * (2 * (R + C)) = 2 * ((n + 4) + (n + d + 1)) := by
          rw [hrow, hcolumn]
          ring
        _ = (Q * P) * Uminus.natAbs := hminusAbs
        _ = P * (Q * P * W) := by rw [hW]; ring
    exact Nat.mul_left_cancel hPpos hmul
  have hPQdvdTwice : P * Q ∣ 2 * (R + C) := by
    refine ⟨W, ?_⟩
    rw [hcancelled]
    ring
  have htwoLower : 2 ∣ n + 1 := by
    have hfactor := canonical_lower_term_factorization data (j := 1)
    rw [hprofile.2.1] at hfactor
    exact ⟨canonicalOwnerRow data 1, hfactor⟩
  have htermOdd : Odd (n + 2) := by
    obtain ⟨z, hz⟩ := htwoLower
    exact ⟨z, by omega⟩
  have hQdvdLower : Q ∣ n + 2 := by
    dsimp [Q]
    exact canonicalOwnerCell_dvd_lower data
  have hcopQ2 : Nat.Coprime Q 2 := by
    exact Nat.Coprime.coprime_dvd_left hQdvdLower
      (Nat.coprime_two_right.mpr htermOdd)
  have hcopP2 : Nat.Coprime P 2 := by
    exact hcopP24.coprime_dvd_right (by norm_num : 2 ∣ 24)
  have hcopPQ2 : Nat.Coprime (P * Q) 2 := hcopP2.mul_left hcopQ2
  have hPQdvd : P * Q ∣ R + C :=
    hcopPQ2.dvd_of_dvd_mul_left hPQdvdTwice
  have hgcdTerms : Nat.gcd (n + 4) (n + d + 1) = P := by
    have hgcd := canonicalOwner_fullyOwned_gcd_modifiedUpper_eq_cell
      data (j := 4) (i := 1) (by norm_num) (by norm_num)
      hprofile.2.2.2.2.1 hprofile.2.2.2.2.2.2.1
    simpa [upperTermAfterFour, hprofile.1, P] using hgcd
  have hgcdRC : Nat.gcd R C = 1 := by
    rw [hrow, hcolumn, Nat.gcd_mul_left] at hgcdTerms
    apply Nat.mul_left_cancel hPpos
    simpa using hgcdTerms
  have hcopRC : Nat.Coprime R C :=
    Nat.coprime_iff_gcd_eq_one.mpr hgcdRC
  have hcopSumR : Nat.Coprime (R + C) R := by
    simpa using hcopRC.symm
  have hcopSumC : Nat.Coprime (R + C) C := by
    simpa using hcopRC
  have hcopPQR : Nat.Coprime (P * Q) R :=
    Nat.Coprime.of_dvd_left hPQdvd hcopSumR
  have hcopPQC : Nat.Coprime (P * Q) C :=
    Nat.Coprime.of_dvd_left hPQdvd hcopSumC
  have hcopPQRC : Nat.Coprime (P * Q) (R * C) :=
    hcopPQR.mul_right hcopPQC
  have hRpos : 0 < R := by
    by_contra hnot
    have hzero : R = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hzero, mul_zero] at hrow
    omega
  have hsumpos : 0 < R + C := Nat.add_pos_left hRpos C
  have hPQle : P * Q ≤ R + C := Nat.le_of_dvd hsumpos hPQdvd
  have hd5 : 5 ≤ d := by
    have hbase : 5 ≤ 10 ^ 1000 := by
      calc
        5 ≤ 10 ^ 1 := by norm_num
        _ ≤ 10 ^ 1000 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    exact hbase.trans htail
  have hgap : 2 * d < n :=
    twice_gap_lt_n_of_four_solution (by norm_num) hd5 heq
  have htermLower : n + 4 < n + d + 1 := by omega
  have hRC : R < C := by
    rw [hrow, hcolumn] at htermLower
    exact (Nat.mul_lt_mul_left hPpos).mp htermLower
  have htermUpper : n + d + 1 < 2 * (n + 4) := by omega
  have hCtwoR : C < 2 * R := by
    rw [hcolumn, hrow] at htermUpper
    have hrewritten : P * C < P * (2 * R) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using htermUpper
    exact (Nat.mul_lt_mul_left hPpos).mp hrewritten
  have htermThreeHalves : 2 * (n + d + 1) < 3 * (n + 4) := by omega
  have hCthreeHalves : 2 * C < 3 * R := by
    rw [hcolumn, hrow] at htermThreeHalves
    have hrewritten : P * (2 * C) < P * (3 * R) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using htermThreeHalves
    exact (Nat.mul_lt_mul_left hPpos).mp hrewritten
  have hsumUpper : R + C < 3 * R := by omega
  have hproductUpper : P * Q < 3 * R := hPQle.trans_lt hsumUpper
  have htwiceSumUpper : 2 * (R + C) < 5 * R := by omega
  have htwiceProductUpper : 2 * (P * Q) < 5 * R :=
    (Nat.mul_le_mul_left 2 hPQle).trans_lt htwiceSumUpper
  have hPgt : 1 < P := by
    dsimp [P]
    exact hcells 4 (by norm_num) 1 (by norm_num)
  have hQgt : 1 < Q := by
    dsimp [Q]
    exact hcells 2 (by norm_num) 3 (by norm_num)
  have hPfive : 5 ≤ P := by
    have hcopP24' : Nat.Coprime P 24 := by simpa [P] using hcopP24
    by_contra hnot
    have hPle : P ≤ 4 := by omega
    interval_cases P <;> norm_num at hPgt hcopP24'
  have hQthree : 3 ≤ Q := by
    by_contra hnot
    have hQle : Q ≤ 2 := by omega
    interval_cases Q <;> norm_num at hQgt hcopQ2
  have hlowerProduct : 15 ≤ P * Q := by
    calc
      15 = 5 * 3 := by norm_num
      _ ≤ P * Q := Nat.mul_le_mul hPfive hQthree
  exact ⟨hrow, hcolumn, hcopPQ2, hPQdvd, hcopRC, hcopPQRC, hPQle,
    hRC, hCtwoR, hCthreeHalves, hproductUpper, htwiceProductUpper,
    hlowerProduct⟩

#print axioms k5_G12_zero_crossing_product_dvd_complement_sum

end Erdos686Variant
end Erdos686
