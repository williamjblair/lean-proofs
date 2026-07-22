/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.K5.G12PrimitiveQuotient

/-!
# Erdős 686, k=5: the exceptional anti-diagonal inside the quotient

For the exceptional `G=12` profile, the four cells `(4,1)`, `(3,2)`,
`(2,3)`, and `(1,4)` lie on the same anti-diagonal.  The common sum of the
lower and upper terms on this anti-diagonal is also the complement sum used
to define `K`.  Pairwise coprimality therefore puts the two interior
anti-diagonal owners, not merely their prime support, inside `K`.
-/

namespace Erdos686
namespace Erdos686Variant

/-- Product of the eight owners on the two anti-diagonals immediately next
to the exceptional anti-diagonal. -/
def k5G12AdjacentAntiDiagonalOwnerProduct
    {n d t : ℕ} (data : CanonicalOwnerData 5 n d t) : ℕ :=
  canonicalOwnerCell data 1 3 * canonicalOwnerCell data 2 2 *
    canonicalOwnerCell data 3 1 * canonicalOwnerCell data 1 5 *
    canonicalOwnerCell data 2 4 * canonicalOwnerCell data 3 3 *
    canonicalOwnerCell data 4 2 * canonicalOwnerCell data 5 1

/-- The two remaining owners on the exceptional anti-diagonal divide the
exact complement quotient `K`. -/
theorem k5_G12_anti_diagonal_owner_product_dvd_complement_quotient
    {n d t : ℕ}
    (data : CanonicalOwnerData 5 n d t)
    (hfour : 4 ∣ n + d + t)
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n)
    (hprofile : K5G12ZeroResidualProfile data) :
    let P := canonicalOwnerCell data 4 1
    let Q := canonicalOwnerCell data 2 3
    let A := canonicalOwnerCell data 3 2
    let B := canonicalOwnerCell data 1 4
    let R := (n + 4) / P
    let C := (n + d + 1) / P
    let K := (R + C) / (P * Q)
    A * B ∣ K ∧
      Nat.Coprime (A * B) (P * Q) ∧
      (n + 3) + (n + d + 2) = P ^ 2 * Q * K := by
  dsimp only
  let P := canonicalOwnerCell data 4 1
  let Q := canonicalOwnerCell data 2 3
  let A := canonicalOwnerCell data 3 2
  let B := canonicalOwnerCell data 1 4
  let R := (n + 4) / P
  let C := (n + d + 1) / P
  let K := (R + C) / (P * Q)
  have hprimitive :=
    k5_G12_exceptional_complement_quotient_gcd_Q_dvd_five
      data hfour heq hprofile
  have hsum : R + C = P * Q * K := hprimitive.1
  have hPdvdLower : P ∣ n + 4 := by
    dsimp [P]
    exact canonicalOwnerCell_dvd_lower data
  have hPdvdUpper : P ∣ n + d + 1 := by
    dsimp [P]
    have hmodified := canonicalOwnerCell_dvd_upper data (j := 4) (i := 1)
    simpa [upperTermAfterFour, hprofile.1] using hmodified
  have hrowP : n + 4 = P * R := by
    dsimp [R]
    exact (Nat.mul_div_cancel' hPdvdLower).symm
  have hcolumnP : n + d + 1 = P * C := by
    dsimp [C]
    exact (Nat.mul_div_cancel' hPdvdUpper).symm
  have htarget : (n + 3) + (n + d + 2) = P ^ 2 * Q * K := by
    calc
      (n + 3) + (n + d + 2) = (n + 4) + (n + d + 1) := by omega
      _ = P * (R + C) := by rw [hrowP, hcolumnP]; ring
      _ = P ^ 2 * Q * K := by rw [hsum]; ring
  have hAdvdLower : A ∣ n + 3 := by
    dsimp [A]
    exact canonicalOwnerCell_dvd_lower data
  have hAdvdUpper : A ∣ n + d + 2 := by
    dsimp [A]
    exact dvd_trans (canonicalOwnerCell_dvd_upper data)
      (upperTermAfterFour_dvd_original hfour)
  have hAdvdTarget : A ∣ (n + 3) + (n + d + 2) :=
    dvd_add hAdvdLower hAdvdUpper
  have hBdvdLower : B ∣ n + 1 := by
    dsimp [B]
    exact canonicalOwnerCell_dvd_lower data
  have hBdvdUpper : B ∣ n + d + 4 := by
    dsimp [B]
    exact dvd_trans (canonicalOwnerCell_dvd_upper data)
      (upperTermAfterFour_dvd_original hfour)
  have hBdvdTarget : B ∣ (n + 3) + (n + d + 2) := by
    have hsumB : B ∣ (n + 1) + (n + d + 4) :=
      dvd_add hBdvdLower hBdvdUpper
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hsumB
  have hpair (j i j' i' : ℕ)
      (hne : (j, i) ≠ (j', i')) :
      Nat.Coprime (canonicalOwnerCell data j i)
        (canonicalOwnerCell data j' i') :=
    canonicalOwnerCells_pairwise_coprime data hne
  have hAB : Nat.Coprime A B := by
    dsimp [A, B]
    apply hpair
    norm_num
  have hAP : Nat.Coprime A P := by
    dsimp [A, P]
    apply hpair
    norm_num
  have hAQ : Nat.Coprime A Q := by
    dsimp [A, Q]
    apply hpair
    norm_num
  have hBP : Nat.Coprime B P := by
    dsimp [B, P]
    apply hpair
    norm_num
  have hBQ : Nat.Coprime B Q := by
    dsimp [B, Q]
    apply hpair
    norm_num
  have hABP : Nat.Coprime (A * B) P := hAP.mul_left hBP
  have hABQ : Nat.Coprime (A * B) Q := hAQ.mul_left hBQ
  have hABPQ : Nat.Coprime (A * B) (P * Q) :=
    hABP.mul_right hABQ
  have hABFactor : Nat.Coprime (A * B) (P ^ 2 * Q) :=
    (hABP.pow_right 2).mul_right hABQ
  have hABdvdTarget : A * B ∣ (n + 3) + (n + d + 2) :=
    hAB.mul_dvd_of_dvd_of_dvd hAdvdTarget hBdvdTarget
  have hABdvdFactor : A * B ∣ (P ^ 2 * Q) * K := by
    simpa [htarget]
      using hABdvdTarget
  have hABdvdK : A * B ∣ K :=
    hABFactor.dvd_of_dvd_mul_left hABdvdFactor
  exact ⟨hABdvdK, hABPQ, htarget⟩

/-- Every owner can meet the complement quotient only through its fixed
anti-diagonal offset.  In particular, the exceptional anti-diagonal is the
only one on which an unrestricted owner factor can enter `K`. -/
theorem k5_G12_owner_gcd_complement_quotient_dvd_antidiagonal_offset
    {n d t j i : ℕ}
    (data : CanonicalOwnerData 5 n d t)
    (hfour : 4 ∣ n + d + t)
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n)
    (hprofile : K5G12ZeroResidualProfile data) :
    let P := canonicalOwnerCell data 4 1
    let Q := canonicalOwnerCell data 2 3
    let R := (n + 4) / P
    let C := (n + d + 1) / P
    let K := (R + C) / (P * Q)
    Nat.gcd (canonicalOwnerCell data j i) K ∣
      Int.natAbs ((j : ℤ) + (i : ℤ) - 5) := by
  dsimp only
  let P := canonicalOwnerCell data 4 1
  let Q := canonicalOwnerCell data 2 3
  let R := (n + 4) / P
  let C := (n + d + 1) / P
  let K := (R + C) / (P * Q)
  let E := canonicalOwnerCell data j i
  let g := Nat.gcd E K
  have hprimitive :=
    k5_G12_exceptional_complement_quotient_gcd_Q_dvd_five
      data hfour heq hprofile
  have hsum : R + C = P * Q * K := hprimitive.1
  have hPdvdLower : P ∣ n + 4 := by
    dsimp [P]
    exact canonicalOwnerCell_dvd_lower data
  have hPdvdUpper : P ∣ n + d + 1 := by
    dsimp [P]
    have hmodified := canonicalOwnerCell_dvd_upper data (j := 4) (i := 1)
    simpa [upperTermAfterFour, hprofile.1] using hmodified
  have hrowP : n + 4 = P * R := by
    dsimp [R]
    exact (Nat.mul_div_cancel' hPdvdLower).symm
  have hcolumnP : n + d + 1 = P * C := by
    dsimp [C]
    exact (Nat.mul_div_cancel' hPdvdUpper).symm
  have htarget : (n + 3) + (n + d + 2) = P ^ 2 * Q * K := by
    calc
      (n + 3) + (n + d + 2) = (n + 4) + (n + d + 1) := by omega
      _ = P * (R + C) := by rw [hrowP, hcolumnP]; ring
      _ = P ^ 2 * Q * K := by rw [hsum]; ring
  have hEdvdLower : E ∣ n + j := by
    dsimp [E]
    exact canonicalOwnerCell_dvd_lower data
  have hEdvdUpper : E ∣ n + d + i := by
    dsimp [E]
    exact dvd_trans (canonicalOwnerCell_dvd_upper data)
      (upperTermAfterFour_dvd_original hfour)
  have hgdvdSum : g ∣ (n + j) + (n + d + i) :=
    (Nat.gcd_dvd_left E K).trans (dvd_add hEdvdLower hEdvdUpper)
  have hKdTarget : K ∣ (n + 3) + (n + d + 2) := by
    refine ⟨P ^ 2 * Q, ?_⟩
    rw [htarget]
    ring
  have hgdvdTarget : g ∣ (n + 3) + (n + d + 2) :=
    (Nat.gcd_dvd_right E K).trans hKdTarget
  have hgdvdSumZ : (g : ℤ) ∣
      (((n + j) + (n + d + i) : ℕ) : ℤ) := by
    exact_mod_cast hgdvdSum
  have hgdvdTargetZ : (g : ℤ) ∣
      (((n + 3) + (n + d + 2) : ℕ) : ℤ) := by
    exact_mod_cast hgdvdTarget
  have hgdvdOffsetZ : (g : ℤ) ∣ (j : ℤ) + (i : ℤ) - 5 := by
    have hsub := dvd_sub hgdvdSumZ hgdvdTargetZ
    convert hsub using 1
    push_cast
    ring
  have habs := Int.natAbs_dvd_natAbs.mpr hgdvdOffsetZ
  simpa [E, g] using habs

/-- The eight owners on anti-diagonals `j+i=4` and `j+i=6` are jointly
coprime to `K`.  This is the maximal adjacent-diagonal exclusion supplied by
the exact complement sum. -/
theorem k5_G12_adjacent_antidiagonal_owner_product_coprime_complement_quotient
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
    Nat.Coprime (k5G12AdjacentAntiDiagonalOwnerProduct data) K := by
  dsimp only
  let P := canonicalOwnerCell data 4 1
  let Q := canonicalOwnerCell data 2 3
  let R := (n + 4) / P
  let C := (n + d + 1) / P
  let K := (R + C) / (P * Q)
  have hcell (j i : ℕ)
      (hoffset : Int.natAbs ((j : ℤ) + (i : ℤ) - 5) = 1) :
      Nat.Coprime (canonicalOwnerCell data j i) K := by
    rw [Nat.coprime_iff_gcd_eq_one]
    apply Nat.eq_one_of_dvd_one
    rw [← hoffset]
    exact k5_G12_owner_gcd_complement_quotient_dvd_antidiagonal_offset
      data hfour heq hprofile
  have h13 := hcell 1 3 (by norm_num)
  have h22 := hcell 2 2 (by norm_num)
  have h31 := hcell 3 1 (by norm_num)
  have h15 := hcell 1 5 (by norm_num)
  have h24 := hcell 2 4 (by norm_num)
  have h33 := hcell 3 3 (by norm_num)
  have h42 := hcell 4 2 (by norm_num)
  have h51 := hcell 5 1 (by norm_num)
  have h₂ := h13.mul_left h22
  have h₃ := h₂.mul_left h31
  have h₄ := h₃.mul_left h15
  have h₅ := h₄.mul_left h24
  have h₆ := h₅.mul_left h33
  have h₇ := h₆.mul_left h42
  have hall := h₇.mul_left h51
  simpa [k5G12AdjacentAntiDiagonalOwnerProduct, mul_assoc] using hall

/-- In the live tail, the maximal forced owner divisor also satisfies the
exact complement upper bound.  Thus any later contradiction can compare the
two interior anti-diagonal owners directly with the four-factor row
complement `R`. -/
theorem k5_G12_forced_antidiagonal_owner_product_upper
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
    let A := canonicalOwnerCell data 3 2
    let B := canonicalOwnerCell data 1 4
    let R := (n + 4) / P
    let C := (n + d + 1) / P
    let K := (R + C) / (P * Q)
    A * B ∣ K ∧ 2 * (P * Q) * (A * B) < 5 * R := by
  dsimp only
  let P := canonicalOwnerCell data 4 1
  let Q := canonicalOwnerCell data 2 3
  let A := canonicalOwnerCell data 3 2
  let B := canonicalOwnerCell data 1 4
  let R := (n + 4) / P
  let C := (n + d + 1) / P
  let K := (R + C) / (P * Q)
  have hforced :=
    k5_G12_anti_diagonal_owner_product_dvd_complement_quotient
      data hfour heq hprofile
  have hABdvd : A * B ∣ K := hforced.1
  have hprimitive :=
    k5_G12_exceptional_complement_quotient_gcd_Q_dvd_five
      data hfour heq hprofile
  have hsum : R + C = P * Q * K := hprimitive.1
  have hcomplement :=
    k5_G12_zero_crossing_product_dvd_complement_sum
      data hfour heq hprofile htail hdlt hcells
  have hRltC : R < C := hcomplement.2.2.2.2.2.2.2.1
  have htwoC : 2 * C < 3 * R :=
    hcomplement.2.2.2.2.2.2.2.2.2.1
  have hKpos : 0 < K := by
    by_contra hnot
    have hKzero : K = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hKzero, mul_zero] at hsum
    omega
  have hABle : A * B ≤ K := Nat.le_of_dvd hKpos hABdvd
  have hforcedLe : 2 * (P * Q) * (A * B) ≤ 2 * (P * Q) * K :=
    Nat.mul_le_mul_left (2 * (P * Q)) hABle
  have hsumUpper : 2 * (R + C) < 5 * R := by omega
  have hKUpper : 2 * (P * Q) * K < 5 * R := by
    calc
      2 * (P * Q) * K = 2 * (R + C) := by rw [hsum]; ring
      _ < 5 * R := hsumUpper
  exact ⟨hABdvd, hforcedLe.trans_lt hKUpper⟩

#print axioms k5_G12_anti_diagonal_owner_product_dvd_complement_quotient
#print axioms k5_G12_owner_gcd_complement_quotient_dvd_antidiagonal_offset
#print axioms k5_G12_adjacent_antidiagonal_owner_product_coprime_complement_quotient
#print axioms k5_G12_forced_antidiagonal_owner_product_upper

end Erdos686Variant
end Erdos686
