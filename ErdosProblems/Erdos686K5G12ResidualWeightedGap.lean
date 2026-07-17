/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686K5G12DiagonalOwners

/-!
# Erdős 686, k=5: an independent residual-weighted gap quotient

The residual-two rows `1,3` and residual-two columns `2,4` give normalized
row and column terms.  Their differences place the complete shifted diagonal
`(1,2),(2,3),(3,4),(4,5)` inside `(d+1)/2`.  This quotient is independent of
the complement-sum quotient `K`.
-/

namespace Erdos686
namespace Erdos686Variant

open scoped BigOperators

private theorem canonicalOwnerCell_dvd_ownerRow
    {n d t j i : ℕ} (data : CanonicalOwnerData 5 n d t)
    (hi : i ∈ Finset.Icc 1 5) :
    canonicalOwnerCell data j i ∣ canonicalOwnerRow data j := by
  rw [← canonicalOwner_row_cell_product data]
  exact Finset.dvd_prod_of_mem (fun i' => canonicalOwnerCell data j i') hi

private theorem canonicalOwnerCell_dvd_ownerColumn
    {n d t j i : ℕ} (data : CanonicalOwnerData 5 n d t)
    (hj : j ∈ Finset.Icc 1 5) :
    canonicalOwnerCell data j i ∣ canonicalOwnerColumn data i := by
  rw [← canonicalOwner_column_cell_product data]
  exact Finset.dvd_prod_of_mem (fun j' => canonicalOwnerCell data j' i) hj

/-- The complete `i-j=1` owner diagonal divides the half-gap.  The theorem
also records the exact residual-weighted quotient equation. -/
theorem k5_G12_residual_weighted_gap_diagonal_product_dvd_half_gap
    {n d t : ℕ}
    (data : CanonicalOwnerData 5 n d t)
    (hfour : 4 ∣ n + d + t)
    (hd : 5 ≤ d)
    (hprofile : K5G12ZeroResidualProfile data) :
    let X := canonicalOwnerCell data 1 2
    let Q := canonicalOwnerCell data 2 3
    let Y := canonicalOwnerCell data 3 4
    let Z := canonicalOwnerCell data 4 5
    let M := X * Q * Y * Z
    let H := ((d + 1) / 2) / M
    M ∣ (d + 1) / 2 ∧ (d + 1) / 2 = M * H := by
  dsimp only
  rcases hprofile with
    ⟨rfl, hl1, hl2, hl3, hl4, hl5, hu1, hu2, hu3, hu4, hu5⟩
  let X := canonicalOwnerCell data 1 2
  let Q := canonicalOwnerCell data 2 3
  let Y := canonicalOwnerCell data 3 4
  let Z := canonicalOwnerCell data 4 5
  let M := X * Q * Y * Z
  let H := ((d + 1) / 2) / M
  let L1 := canonicalOwnerRow data 1
  let L3 := canonicalOwnerRow data 3
  let U2 := canonicalOwnerColumn data 2
  let U4 := canonicalOwnerColumn data 4
  have hL1 : n + 1 = 2 * L1 := by
    simpa [L1, hl1] using canonical_lower_term_factorization data (j := 1)
  have hL3 : n + 3 = 2 * L3 := by
    simpa [L3, hl3] using canonical_lower_term_factorization data (j := 3)
  have hU2 : n + d + 2 = 2 * U2 := by
    simpa [U2, hu2] using canonical_upper_term_factorization data hfour (i := 2)
  have hU4 : n + d + 4 = 8 * U4 := by
    simpa [U4, hu4] using canonical_upper_term_factorization data hfour (i := 4)
  have hhalf1 : (d + 1) / 2 = U2 - L1 := by
    have heven : d + 1 = 2 * (U2 - L1) := by omega
    rw [heven]
    exact Nat.mul_div_right _ (by norm_num)
  have hhalf3 : (d + 1) / 2 = 4 * U4 - L3 := by
    have heven : d + 1 = 2 * (4 * U4 - L3) := by omega
    rw [heven]
    exact Nat.mul_div_right _ (by norm_num)
  have hXdL : X ∣ L1 := by
    dsimp [X, L1]
    exact canonicalOwnerCell_dvd_ownerRow data (by norm_num)
  have hXdU : X ∣ U2 := by
    dsimp [X, U2]
    exact canonicalOwnerCell_dvd_ownerColumn data (by norm_num)
  have hX : X ∣ (d + 1) / 2 := by
    rw [hhalf1]
    exact Nat.dvd_sub hXdU hXdL
  have hYdL : Y ∣ L3 := by
    dsimp [Y, L3]
    exact canonicalOwnerCell_dvd_ownerRow data (by norm_num)
  have hYdU : Y ∣ U4 := by
    dsimp [Y, U4]
    exact canonicalOwnerCell_dvd_ownerColumn data (by norm_num)
  have hY : Y ∣ (d + 1) / 2 := by
    rw [hhalf3]
    exact Nat.dvd_sub (dvd_mul_of_dvd_right hYdU 4) hYdL
  have hhalfDouble : d + 1 = 2 * ((d + 1) / 2) := by
    rw [hhalf1]
    omega
  have hQdvdGap : Q ∣ d + 1 := by
    dsimp [Q]
    simpa using canonicalOwnerCell_dvd_shiftedDifference data
      hd (by norm_num) (by norm_num) hfour
  have hZdvdGap : Z ∣ d + 1 := by
    dsimp [Z]
    simpa using canonicalOwnerCell_dvd_shiftedDifference data
      hd (by norm_num) (by norm_num) hfour
  have hnodd : Odd (n + 2) := by
    refine ⟨L1, ?_⟩
    omega
  have hQdvdOdd : Q ∣ n + 2 := by
    dsimp [Q]
    exact canonicalOwnerCell_dvd_lower data
  have hQcop2 : Nat.Coprime Q 2 :=
    Nat.Coprime.coprime_dvd_left hQdvdOdd
      (Nat.coprime_two_right.mpr hnodd)
  have hn4odd : Odd (n + 4) := by
    refine ⟨L1 + 1, ?_⟩
    omega
  have hZdvdOdd : Z ∣ n + 4 := by
    dsimp [Z]
    exact canonicalOwnerCell_dvd_lower data
  have hZcop2 : Nat.Coprime Z 2 :=
    Nat.Coprime.coprime_dvd_left hZdvdOdd
      (Nat.coprime_two_right.mpr hn4odd)
  have hQ : Q ∣ (d + 1) / 2 := by
    rw [hhalfDouble] at hQdvdGap
    exact hQcop2.dvd_of_dvd_mul_left hQdvdGap
  have hZ : Z ∣ (d + 1) / 2 := by
    rw [hhalfDouble] at hZdvdGap
    exact hZcop2.dvd_of_dvd_mul_left hZdvdGap
  have hpair (j i j' i' : ℕ) (hne : (j, i) ≠ (j', i')) :
      Nat.Coprime (canonicalOwnerCell data j i)
        (canonicalOwnerCell data j' i') :=
    canonicalOwnerCells_pairwise_coprime data hne
  have hXQ : Nat.Coprime X Q := by dsimp [X, Q]; apply hpair; norm_num
  have hXY : Nat.Coprime X Y := by dsimp [X, Y]; apply hpair; norm_num
  have hXZ : Nat.Coprime X Z := by dsimp [X, Z]; apply hpair; norm_num
  have hQY : Nat.Coprime Q Y := by dsimp [Q, Y]; apply hpair; norm_num
  have hQZ : Nat.Coprime Q Z := by dsimp [Q, Z]; apply hpair; norm_num
  have hYZ : Nat.Coprime Y Z := by dsimp [Y, Z]; apply hpair; norm_num
  have hXQY : Nat.Coprime (X * Q) Y := hXY.mul_left hQY
  have hXQZ : Nat.Coprime (X * Q) Z := hXZ.mul_left hQZ
  have hXQYZ : Nat.Coprime (X * Q * Y) Z := hXQZ.mul_left hYZ
  have hXQdvd : X * Q ∣ (d + 1) / 2 :=
    hXQ.mul_dvd_of_dvd_of_dvd hX hQ
  have hXQYdvd : X * Q * Y ∣ (d + 1) / 2 :=
    hXQY.mul_dvd_of_dvd_of_dvd hXQdvd hY
  have hM : M ∣ (d + 1) / 2 := by
    dsimp [M]
    exact hXQYZ.mul_dvd_of_dvd_of_dvd hXQYdvd hZ
  have hfactor : (d + 1) / 2 = M * H := by
    dsimp [H]
    exact (Nat.mul_div_cancel' hM).symm
  exact ⟨hM, hfactor⟩

/-- On the opposite shifted diagonal, the three cells not involving the
residual-three row divide the half-gap.  Adding the final `(5,4)` owner gives
the complete four-cell divisor of the full gap. -/
theorem k5_G12_opposite_residual_weighted_gap_products
    {n d t : ℕ}
    (data : CanonicalOwnerData 5 n d t)
    (hfour : 4 ∣ n + d + t)
    (hd : 5 ≤ d)
    (hprofile : K5G12ZeroResidualProfile data) :
    let X := canonicalOwnerCell data 2 1
    let A := canonicalOwnerCell data 3 2
    let Y := canonicalOwnerCell data 4 3
    let Z := canonicalOwnerCell data 5 4
    X * A * Y ∣ (d - 1) / 2 ∧ X * A * Y * Z ∣ d - 1 := by
  dsimp only
  rcases hprofile with
    ⟨rfl, hl1, hl2, hl3, hl4, hl5, hu1, hu2, hu3, hu4, hu5⟩
  let X := canonicalOwnerCell data 2 1
  let A := canonicalOwnerCell data 3 2
  let Y := canonicalOwnerCell data 4 3
  let Z := canonicalOwnerCell data 5 4
  let L3 := canonicalOwnerRow data 3
  let U2 := canonicalOwnerColumn data 2
  have hL1 : n + 1 = 2 * canonicalOwnerRow data 1 := by
    simpa [hl1] using canonical_lower_term_factorization data (j := 1)
  have hL3 : n + 3 = 2 * L3 := by
    simpa [L3, hl3] using canonical_lower_term_factorization data (j := 3)
  have hU2 : n + d + 2 = 2 * U2 := by
    simpa [U2, hu2] using canonical_upper_term_factorization data hfour (i := 2)
  have hhalf : (d - 1) / 2 = U2 - L3 := by
    have heq : d - 1 = 2 * (U2 - L3) := by omega
    rw [heq]
    exact Nat.mul_div_right _ (by norm_num)
  have hAdL : A ∣ L3 := by
    dsimp [A, L3]
    exact canonicalOwnerCell_dvd_ownerRow data (by norm_num)
  have hAdU : A ∣ U2 := by
    dsimp [A, U2]
    exact canonicalOwnerCell_dvd_ownerColumn data (by norm_num)
  have hA : A ∣ (d - 1) / 2 := by
    rw [hhalf]
    exact Nat.dvd_sub hAdU hAdL
  have hdouble : d - 1 = 2 * ((d - 1) / 2) := by
    rw [hhalf]
    omega
  have hnodd : Odd (n + 2) := by
    refine ⟨canonicalOwnerRow data 1, ?_⟩
    omega
  have hn4odd : Odd (n + 4) := by
    refine ⟨canonicalOwnerRow data 1 + 1, ?_⟩
    omega
  have hXdLower : X ∣ n + 2 := by
    dsimp [X]
    exact canonicalOwnerCell_dvd_lower data
  have hYdLower : Y ∣ n + 4 := by
    dsimp [Y]
    exact canonicalOwnerCell_dvd_lower data
  have hXcop2 : Nat.Coprime X 2 :=
    Nat.Coprime.coprime_dvd_left hXdLower
      (Nat.coprime_two_right.mpr hnodd)
  have hYcop2 : Nat.Coprime Y 2 :=
    Nat.Coprime.coprime_dvd_left hYdLower
      (Nat.coprime_two_right.mpr hn4odd)
  have hXdGap : X ∣ d - 1 := by
    dsimp [X]
    simpa using canonicalOwnerCell_dvd_shiftedDifference data hd
      (by norm_num) (by norm_num) hfour
  have hYdGap : Y ∣ d - 1 := by
    dsimp [Y]
    simpa using canonicalOwnerCell_dvd_shiftedDifference data hd
      (by norm_num) (by norm_num) hfour
  have hZdGap : Z ∣ d - 1 := by
    dsimp [Z]
    simpa using canonicalOwnerCell_dvd_shiftedDifference data hd
      (by norm_num) (by norm_num) hfour
  have hX : X ∣ (d - 1) / 2 := by
    rw [hdouble] at hXdGap
    exact hXcop2.dvd_of_dvd_mul_left hXdGap
  have hY : Y ∣ (d - 1) / 2 := by
    rw [hdouble] at hYdGap
    exact hYcop2.dvd_of_dvd_mul_left hYdGap
  have hpair (j i j' i' : ℕ) (hne : (j, i) ≠ (j', i')) :
      Nat.Coprime (canonicalOwnerCell data j i)
        (canonicalOwnerCell data j' i') :=
    canonicalOwnerCells_pairwise_coprime data hne
  have hXA : Nat.Coprime X A := by dsimp [X, A]; apply hpair; norm_num
  have hXY : Nat.Coprime X Y := by dsimp [X, Y]; apply hpair; norm_num
  have hAY : Nat.Coprime A Y := by dsimp [A, Y]; apply hpair; norm_num
  have hXZ : Nat.Coprime X Z := by dsimp [X, Z]; apply hpair; norm_num
  have hAZ : Nat.Coprime A Z := by dsimp [A, Z]; apply hpair; norm_num
  have hYZ : Nat.Coprime Y Z := by dsimp [Y, Z]; apply hpair; norm_num
  have hXAdvd : X * A ∣ (d - 1) / 2 :=
    hXA.mul_dvd_of_dvd_of_dvd hX hA
  have hXAYcop : Nat.Coprime (X * A) Y := hXY.mul_left hAY
  have hXAYdvd : X * A * Y ∣ (d - 1) / 2 :=
    hXAYcop.mul_dvd_of_dvd_of_dvd hXAdvd hY
  have hXAYdGap : X * A * Y ∣ d - 1 := by
    rw [hdouble]
    exact dvd_mul_of_dvd_right hXAYdvd 2
  have hXAYZcop : Nat.Coprime (X * A * Y) Z :=
    (hXZ.mul_left hAZ).mul_left hYZ
  have hfull : X * A * Y * Z ∣ d - 1 :=
    hXAYZcop.mul_dvd_of_dvd_of_dvd hXAYdGap hZdGap
  exact ⟨hXAYdvd, hfull⟩

/-- The short positive offset-three diagonal also divides its normalized
half-gap.  One cell is controlled by the row-one/column-four residual
weights; the other is odd because it lies in the fully owned odd row two. -/
theorem k5_G12_positive_three_diagonal_product_dvd_half_gap
    {n d t : ℕ}
    (data : CanonicalOwnerData 5 n d t)
    (hfour : 4 ∣ n + d + t)
    (hd : 5 ≤ d)
    (hprofile : K5G12ZeroResidualProfile data) :
    canonicalOwnerCell data 1 4 * canonicalOwnerCell data 2 5 ∣
      (d + 3) / 2 := by
  rcases hprofile with
    ⟨rfl, hl1, hl2, hl3, hl4, hl5, hu1, hu2, hu3, hu4, hu5⟩
  let B := canonicalOwnerCell data 1 4
  let Z := canonicalOwnerCell data 2 5
  let L1 := canonicalOwnerRow data 1
  let U4 := canonicalOwnerColumn data 4
  have hL1 : n + 1 = 2 * L1 := by
    simpa [L1, hl1] using canonical_lower_term_factorization data (j := 1)
  have hU4 : n + d + 4 = 8 * U4 := by
    simpa [U4, hu4] using canonical_upper_term_factorization data hfour (i := 4)
  have hhalf : (d + 3) / 2 = 4 * U4 - L1 := by
    have heq : d + 3 = 2 * (4 * U4 - L1) := by omega
    rw [heq]
    exact Nat.mul_div_right _ (by norm_num)
  have hBdL : B ∣ L1 := by
    dsimp [B, L1]
    exact canonicalOwnerCell_dvd_ownerRow data (by norm_num)
  have hBdU : B ∣ U4 := by
    dsimp [B, U4]
    exact canonicalOwnerCell_dvd_ownerColumn data (by norm_num)
  have hB : B ∣ (d + 3) / 2 := by
    rw [hhalf]
    exact Nat.dvd_sub (dvd_mul_of_dvd_right hBdU 4) hBdL
  have hdouble : d + 3 = 2 * ((d + 3) / 2) := by
    rw [hhalf]
    omega
  have hnodd : Odd (n + 2) := by
    refine ⟨L1, ?_⟩
    omega
  have hZdLower : Z ∣ n + 2 := by
    dsimp [Z]
    exact canonicalOwnerCell_dvd_lower data
  have hZcop2 : Nat.Coprime Z 2 :=
    Nat.Coprime.coprime_dvd_left hZdLower
      (Nat.coprime_two_right.mpr hnodd)
  have hZdGap : Z ∣ d + 3 := by
    dsimp [Z]
    simpa using canonicalOwnerCell_dvd_shiftedDifference data hd
      (by norm_num) (by norm_num) hfour
  have hZ : Z ∣ (d + 3) / 2 := by
    rw [hdouble] at hZdGap
    exact hZcop2.dvd_of_dvd_mul_left hZdGap
  have hBZ : Nat.Coprime B Z := by
    dsimp [B, Z]
    apply canonicalOwnerCells_pairwise_coprime data
    norm_num
  exact hBZ.mul_dvd_of_dvd_of_dvd hB hZ

/-- Combining the independent complement and normalized-gap quotients covers
ten distinct owner cells.  The two owners already absorbed by `K` are not
double-counted in the shifted-gap factors. -/
theorem k5_G12_ten_distinct_owner_product_dvd_global_quotient_product
    {n d t : ℕ}
    (data : CanonicalOwnerData 5 n d t)
    (hfour : 4 ∣ n + d + t)
    (hd : 5 ≤ d)
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n)
    (hprofile : K5G12ZeroResidualProfile data) :
    let P := canonicalOwnerCell data 4 1
    let Q := canonicalOwnerCell data 2 3
    let A := canonicalOwnerCell data 3 2
    let B := canonicalOwnerCell data 1 4
    let R := (n + 4) / P
    let C := (n + d + 1) / P
    let K := (R + C) / (P * Q)
    let Dp := canonicalOwnerCell data 1 2 * Q *
      canonicalOwnerCell data 3 4 * canonicalOwnerCell data 4 5
    let Dm := canonicalOwnerCell data 2 1 *
      canonicalOwnerCell data 4 3 * canonicalOwnerCell data 5 4
    let E := canonicalOwnerCell data 2 5
    (A * B) * Dp * Dm * E ∣
      K * ((d + 1) / 2) * (d - 1) * ((d + 3) / 2) := by
  dsimp only
  let P := canonicalOwnerCell data 4 1
  let Q := canonicalOwnerCell data 2 3
  let A := canonicalOwnerCell data 3 2
  let B := canonicalOwnerCell data 1 4
  let R := (n + 4) / P
  let C := (n + d + 1) / P
  let K := (R + C) / (P * Q)
  let Dp := canonicalOwnerCell data 1 2 * Q *
    canonicalOwnerCell data 3 4 * canonicalOwnerCell data 4 5
  let Dm := canonicalOwnerCell data 2 1 *
    canonicalOwnerCell data 4 3 * canonicalOwnerCell data 5 4
  let E := canonicalOwnerCell data 2 5
  have hK :=
    k5_G12_anti_diagonal_owner_product_dvd_complement_quotient
      data hfour heq hprofile
  have hAB : A * B ∣ K := hK.1
  have hp :=
    k5_G12_residual_weighted_gap_diagonal_product_dvd_half_gap
      data hfour hd hprofile
  have hDp : Dp ∣ (d + 1) / 2 := by
    simpa [Dp, Q, mul_assoc] using hp.1
  have hm := k5_G12_opposite_residual_weighted_gap_products
    data hfour hd hprofile
  have hDmFull :
      canonicalOwnerCell data 2 1 * A * canonicalOwnerCell data 4 3 *
        canonicalOwnerCell data 5 4 ∣ d - 1 := by
    simpa [A, mul_assoc] using hm.2
  have hDmSub : Dm ∣
      canonicalOwnerCell data 2 1 * A * canonicalOwnerCell data 4 3 *
        canonicalOwnerCell data 5 4 := by
    refine ⟨A, ?_⟩
    dsimp [Dm]
    ring
  have hDm : Dm ∣ d - 1 := hDmSub.trans hDmFull
  have hthree := k5_G12_positive_three_diagonal_product_dvd_half_gap
    data hfour hd hprofile
  have hEsub : E ∣ B * E := dvd_mul_left E B
  have hE : E ∣ (d + 3) / 2 := by
    exact hEsub.trans (by simpa [B, E] using hthree)
  have h₁ := Nat.mul_dvd_mul hAB hDp
  have h₂ := Nat.mul_dvd_mul h₁ hDm
  have h₃ := Nat.mul_dvd_mul h₂ hE
  simpa [A, B, Dp, Dm, E, K, P, Q, R, C, mul_assoc] using h₃

#print axioms k5_G12_residual_weighted_gap_diagonal_product_dvd_half_gap
#print axioms k5_G12_opposite_residual_weighted_gap_products
#print axioms k5_G12_positive_three_diagonal_product_dvd_half_gap
#print axioms k5_G12_ten_distinct_owner_product_dvd_global_quotient_product

end Erdos686Variant
end Erdos686
