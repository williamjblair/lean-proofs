/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.K5.G12ResidualWeightedGap

/-!
# Erdős 686, k=5: square-tangent control of the uncovered matching

The five cells left by the optimal row/column cover obstruction are the
main diagonal.  Their independent owner-square congruences combine into a
square divisor for the complete matching product, with an explicit global
height bound.
-/

namespace Erdos686
namespace Erdos686Variant

/-- Product of the five canonical owners on the main diagonal. -/
def k5G12DiagonalMatchingOwnerProduct
    {n d t : ℕ} (data : CanonicalOwnerData 5 n d t) : ℕ :=
  canonicalOwnerCell data 1 1 * canonicalOwnerCell data 2 2 *
    canonicalOwnerCell data 3 3 * canonicalOwnerCell data 4 4 *
    canonicalOwnerCell data 5 5

private theorem diagonal_owner_gcd_gap_quotient_dvd_fixed
    {n d t j r : ℕ}
    (data : CanonicalOwnerData 5 n d t)
    (hfour : 4 ∣ n + d + t)
    (hd : 5 ≤ d)
    (hj : j ∈ Finset.Icc 1 5)
    (hr : canonicalLowerResidual data j = r)
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n) :
    let P := canonicalOwnerCell data j j
    Nat.gcd P (d / P) ∣
      3 * (localBlockCoefficient 5 j).natAbs * r := by
  classical
  dsimp only
  let P := canonicalOwnerCell data j j
  let S := Finset.Icc 1 5
  let rest := ∏ i ∈ S.erase j, canonicalOwnerCell data j i
  let a := d / P
  let b := (n + j) / P
  let g := Nat.gcd P a
  have hPpos : 0 < P := by
    dsimp [P]
    exact canonicalOwnerCell_pos data
  have hPd : P ∣ d := by
    dsimp [P]
    simpa using canonicalOwnerCell_dvd_shiftedDifference data hd hj hj hfour
  have hdEq : d = P * a := by
    dsimp [a]
    exact (Nat.mul_div_cancel' hPd).symm
  have hcopPrest : Nat.Coprime P rest := by
    dsimp [P, rest]
    apply Nat.Coprime.prod_right
    intro i hi
    apply canonicalOwnerCells_pairwise_coprime data
    intro heqPair
    have : j = i := congrArg Prod.snd heqPair
    subst i
    exact (Finset.mem_erase.mp hi).1 rfl
  have hownerRow : canonicalOwnerRow data j = P * rest := by
    rw [← canonicalOwner_row_cell_product data]
    symm
    exact Finset.mul_prod_erase S
      (fun i => canonicalOwnerCell data j i) hj
  have hrow : n + j = r * (P * rest) := by
    rw [canonical_lower_term_factorization data, hr, hownerRow]
  have hbEq : b = r * rest := by
    dsimp [b]
    rw [hrow]
    have hreorder : r * (P * rest) = P * (r * rest) := by ring
    rw [hreorder, Nat.mul_div_cancel_left _ hPpos]
  have hsquare := canonicalOwnerCell_sq_dvd_k5OwnerSquareDefect
    data hj hj hfour heq
  have hdefect :
      k5OwnerSquareDefect n d j j =
        (P : ℤ) * (localBlockCoefficient 5 j *
          ((a : ℤ) - 3 * (b : ℤ))) := by
    unfold k5OwnerSquareDefect
    have hdZ : (d : ℤ) = (P : ℤ) * (a : ℤ) := by exact_mod_cast hdEq
    have hrowZ : ((n + j : ℕ) : ℤ) = (P : ℤ) * (b : ℤ) := by
      dsimp [b]
      exact_mod_cast (Nat.mul_div_cancel' (canonicalOwnerCell_dvd_lower data)).symm
    rw [show ((n + d + j : ℕ) : ℤ) = ((n + j : ℕ) : ℤ) + d by
      push_cast; ring, hdZ, hrowZ]
    ring
  change ((P : ℤ) ^ 2) ∣ k5OwnerSquareDefect n d j j at hsquare
  rw [hdefect] at hsquare
  have hPdvdZ : (P : ℤ) ∣ localBlockCoefficient 5 j *
      ((a : ℤ) - 3 * (b : ℤ)) := by
    have hcancel := owner_dvd_resultantQuotient_tangent_defect
      (P := (P : ℤ)) (b := localBlockCoefficient 5 j)
      (Mrest := 1) (U := (a : ℤ) - 3 * (b : ℤ))
      (kappa := 0) (xrest := 0)
      (by exact_mod_cast hPpos.ne')
      (by simpa [mul_assoc, mul_left_comm, mul_comm] using hsquare)
    simpa using hcancel
  have hgP : g ∣ P := Nat.gcd_dvd_left P a
  have hga : g ∣ a := Nat.gcd_dvd_right P a
  have hgMainZ : (g : ℤ) ∣ localBlockCoefficient 5 j *
      ((a : ℤ) - 3 * (b : ℤ)) := by
    exact dvd_trans (by exact_mod_cast hgP) hPdvdZ
  have hgaZ : (g : ℤ) ∣ localBlockCoefficient 5 j * (a : ℤ) := by
    exact dvd_mul_of_dvd_right (by exact_mod_cast hga) _
  have hgThreeBZ : (g : ℤ) ∣
      3 * localBlockCoefficient 5 j * (b : ℤ) := by
    have hsub := dvd_sub hgaZ hgMainZ
    convert hsub using 1
    ring
  have hgThreeB : g ∣
      3 * (localBlockCoefficient 5 j).natAbs * b := by
    have habs := Int.natAbs_dvd_natAbs.mpr hgThreeBZ
    simpa [Int.natAbs_mul, mul_assoc] using habs
  have hgcopRest : Nat.Coprime g rest := hcopPrest.of_dvd_left hgP
  have hgFixedRest : g ∣
      (3 * (localBlockCoefficient 5 j).natAbs * r) * rest := by
    rw [hbEq] at hgThreeB
    simpa [mul_assoc, mul_left_comm, mul_comm] using hgThreeB
  exact hgcopRest.dvd_of_dvd_mul_right hgFixedRest

/-- On the main diagonal all five tangent defects collapse to translates of
the same affine form `d-3n`. -/
theorem k5_G12_diagonal_matching_tangent_product_explicit
    (n d : ℕ) :
    k5OwnerSquareDefect n d 1 1 *
      k5OwnerSquareDefect n d 2 2 *
      k5OwnerSquareDefect n d 3 3 *
      k5OwnerSquareDefect n d 4 4 *
      k5OwnerSquareDefect n d 5 5 =
    82944 *
      (((d : ℤ) - 3 * n - 3) * ((d : ℤ) - 3 * n - 6) *
        ((d : ℤ) - 3 * n - 9) * ((d : ℤ) - 3 * n - 12) *
        ((d : ℤ) - 3 * n - 15)) := by
  have hc1 : localBlockCoefficient 5 1 = 24 := by
    rw [localBlockCoefficient_eq_sign_mul_nat (by norm_num)]
    norm_num [localBlockCoefficientNat]
  have hc2 : localBlockCoefficient 5 2 = -6 := by
    rw [localBlockCoefficient_eq_sign_mul_nat (by norm_num)]
    norm_num [localBlockCoefficientNat]
  have hc3 : localBlockCoefficient 5 3 = 4 := by
    rw [localBlockCoefficient_eq_sign_mul_nat (by norm_num)]
    norm_num [localBlockCoefficientNat]
  have hc4 : localBlockCoefficient 5 4 = -6 := by
    rw [localBlockCoefficient_eq_sign_mul_nat (by norm_num)]
    norm_num [localBlockCoefficientNat]
  have hc5 : localBlockCoefficient 5 5 = 24 := by
    rw [localBlockCoefficient_eq_sign_mul_nat (by norm_num)]
    norm_num [localBlockCoefficientNat]
  simp only [k5OwnerSquareDefect, hc1, hc2, hc3, hc4, hc5]
  push_cast
  ring

/-- Each diagonal owner is almost a unitary divisor of the common gap.  Its
overlap with the complementary gap quotient is bounded by the exact row
residual and tangent coefficient. -/
theorem k5_G12_diagonal_owner_gap_quotient_gcds_fixed
    {n d t : ℕ}
    (data : CanonicalOwnerData 5 n d t)
    (hfour : 4 ∣ n + d + t)
    (hd : 5 ≤ d)
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n)
    (hprofile : K5G12ZeroResidualProfile data) :
    Nat.gcd (canonicalOwnerCell data 1 1)
        (d / canonicalOwnerCell data 1 1) ∣ 144 ∧
      Nat.gcd (canonicalOwnerCell data 2 2)
        (d / canonicalOwnerCell data 2 2) ∣ 18 ∧
      Nat.gcd (canonicalOwnerCell data 3 3)
        (d / canonicalOwnerCell data 3 3) ∣ 24 ∧
      Nat.gcd (canonicalOwnerCell data 4 4)
        (d / canonicalOwnerCell data 4 4) ∣ 18 ∧
      Nat.gcd (canonicalOwnerCell data 5 5)
        (d / canonicalOwnerCell data 5 5) ∣ 216 := by
  rcases hprofile with
    ⟨rfl, hl1, hl2, hl3, hl4, hl5, hu1, hu2, hu3, hu4, hu5⟩
  have h1 := diagonal_owner_gcd_gap_quotient_dvd_fixed
    data hfour hd (j := 1) (r := 2) (by norm_num) hl1 heq
  have h2 := diagonal_owner_gcd_gap_quotient_dvd_fixed
    data hfour hd (j := 2) (r := 1) (by norm_num) hl2 heq
  have h3 := diagonal_owner_gcd_gap_quotient_dvd_fixed
    data hfour hd (j := 3) (r := 2) (by norm_num) hl3 heq
  have h4 := diagonal_owner_gcd_gap_quotient_dvd_fixed
    data hfour hd (j := 4) (r := 1) (by norm_num) hl4 heq
  have h5 := diagonal_owner_gcd_gap_quotient_dvd_fixed
    data hfour hd (j := 5) (r := 3) (by norm_num) hl5 heq
  rw [localBlockCoefficient_eq_sign_mul_nat (by norm_num)] at h1
  rw [localBlockCoefficient_eq_sign_mul_nat (by norm_num)] at h2
  rw [localBlockCoefficient_eq_sign_mul_nat (by norm_num)] at h3
  rw [localBlockCoefficient_eq_sign_mul_nat (by norm_num)] at h4
  rw [localBlockCoefficient_eq_sign_mul_nat (by norm_num)] at h5
  norm_num [localBlockCoefficientNat] at h1 h2 h3 h4 h5
  exact ⟨h1, h2, h3, h4, h5⟩

/-- The five diagonal owners are pairwise coprime divisors of the gap, so
their complete matching product divides the gap. -/
theorem k5_G12_diagonal_matching_owner_product_dvd_gap
    {n d t : ℕ}
    (data : CanonicalOwnerData 5 n d t)
    (hfour : 4 ∣ n + d + t)
    (hd : 5 ≤ d) :
    k5G12DiagonalMatchingOwnerProduct data ∣ d := by
  let P1 := canonicalOwnerCell data 1 1
  let P2 := canonicalOwnerCell data 2 2
  let P3 := canonicalOwnerCell data 3 3
  let P4 := canonicalOwnerCell data 4 4
  let P5 := canonicalOwnerCell data 5 5
  have hpair (j i : ℕ) (hne : j ≠ i) :
      Nat.Coprime (canonicalOwnerCell data j j)
        (canonicalOwnerCell data i i) := by
    apply canonicalOwnerCells_pairwise_coprime data
    intro hp
    exact hne (congrArg Prod.fst hp)
  have h12 : Nat.Coprime P1 P2 := by dsimp [P1, P2]; exact hpair 1 2 (by norm_num)
  have h13 : Nat.Coprime P1 P3 := by dsimp [P1, P3]; exact hpair 1 3 (by norm_num)
  have h14 : Nat.Coprime P1 P4 := by dsimp [P1, P4]; exact hpair 1 4 (by norm_num)
  have h15 : Nat.Coprime P1 P5 := by dsimp [P1, P5]; exact hpair 1 5 (by norm_num)
  have h23 : Nat.Coprime P2 P3 := by dsimp [P2, P3]; exact hpair 2 3 (by norm_num)
  have h24 : Nat.Coprime P2 P4 := by dsimp [P2, P4]; exact hpair 2 4 (by norm_num)
  have h25 : Nat.Coprime P2 P5 := by dsimp [P2, P5]; exact hpair 2 5 (by norm_num)
  have h34 : Nat.Coprime P3 P4 := by dsimp [P3, P4]; exact hpair 3 4 (by norm_num)
  have h35 : Nat.Coprime P3 P5 := by dsimp [P3, P5]; exact hpair 3 5 (by norm_num)
  have h45 : Nat.Coprime P4 P5 := by dsimp [P4, P5]; exact hpair 4 5 (by norm_num)
  have hp1d : P1 ∣ d := by
    dsimp [P1]
    simpa using canonicalOwnerCell_dvd_shiftedDifference data hd
      (by norm_num) (by norm_num) hfour
  have hp2d : P2 ∣ d := by
    dsimp [P2]
    simpa using canonicalOwnerCell_dvd_shiftedDifference data hd
      (by norm_num) (by norm_num) hfour
  have hp3d : P3 ∣ d := by
    dsimp [P3]
    simpa using canonicalOwnerCell_dvd_shiftedDifference data hd
      (by norm_num) (by norm_num) hfour
  have hp4d : P4 ∣ d := by
    dsimp [P4]
    simpa using canonicalOwnerCell_dvd_shiftedDifference data hd
      (by norm_num) (by norm_num) hfour
  have hp5d : P5 ∣ d := by
    dsimp [P5]
    simpa using canonicalOwnerCell_dvd_shiftedDifference data hd
      (by norm_num) (by norm_num) hfour
  have hp12d : P1 * P2 ∣ d := h12.mul_dvd_of_dvd_of_dvd hp1d hp2d
  have hc123 : Nat.Coprime (P1 * P2) P3 := h13.mul_left h23
  have hp123d : P1 * P2 * P3 ∣ d :=
    hc123.mul_dvd_of_dvd_of_dvd hp12d hp3d
  have hc1234 : Nat.Coprime (P1 * P2 * P3) P4 :=
    (h14.mul_left h24).mul_left h34
  have hp1234d : P1 * P2 * P3 * P4 ∣ d :=
    hc1234.mul_dvd_of_dvd_of_dvd hp123d hp4d
  have hc12345 : Nat.Coprime (P1 * P2 * P3 * P4) P5 :=
    ((h15.mul_left h25).mul_left h35).mul_left h45
  dsimp [k5G12DiagonalMatchingOwnerProduct]
  exact hc12345.mul_dvd_of_dvd_of_dvd hp1234d hp5d

/-- The full diagonal matching product is a unitary divisor of `d` away
from a fixed `2,3`-smooth overlap.  Pairwise owner coprimality improves the
product of the five local constants to their lcm `432`. -/
theorem k5_G12_diagonal_matching_gap_quotient_gcd_dvd_432
    {n d t : ℕ}
    (data : CanonicalOwnerData 5 n d t)
    (hfour : 4 ∣ n + d + t)
    (hd : 5 ≤ d)
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n)
    (hprofile : K5G12ZeroResidualProfile data) :
    let M := k5G12DiagonalMatchingOwnerProduct data
    Nat.gcd M (d / M) ∣ 432 := by
  dsimp only
  let P1 := canonicalOwnerCell data 1 1
  let P2 := canonicalOwnerCell data 2 2
  let P3 := canonicalOwnerCell data 3 3
  let P4 := canonicalOwnerCell data 4 4
  let P5 := canonicalOwnerCell data 5 5
  let M := k5G12DiagonalMatchingOwnerProduct data
  let U := d / M
  have hlocal := k5_G12_diagonal_owner_gap_quotient_gcds_fixed
    data hfour hd heq hprofile
  have hpair (j i : ℕ) (hne : j ≠ i) :
      Nat.Coprime (canonicalOwnerCell data j j)
        (canonicalOwnerCell data i i) := by
    apply canonicalOwnerCells_pairwise_coprime data
    intro hp
    exact hne (congrArg Prod.fst hp)
  have h12 : Nat.Coprime P1 P2 := by dsimp [P1, P2]; exact hpair 1 2 (by norm_num)
  have h13 : Nat.Coprime P1 P3 := by dsimp [P1, P3]; exact hpair 1 3 (by norm_num)
  have h14 : Nat.Coprime P1 P4 := by dsimp [P1, P4]; exact hpair 1 4 (by norm_num)
  have h15 : Nat.Coprime P1 P5 := by dsimp [P1, P5]; exact hpair 1 5 (by norm_num)
  have h23 : Nat.Coprime P2 P3 := by dsimp [P2, P3]; exact hpair 2 3 (by norm_num)
  have h24 : Nat.Coprime P2 P4 := by dsimp [P2, P4]; exact hpair 2 4 (by norm_num)
  have h25 : Nat.Coprime P2 P5 := by dsimp [P2, P5]; exact hpair 2 5 (by norm_num)
  have h34 : Nat.Coprime P3 P4 := by dsimp [P3, P4]; exact hpair 3 4 (by norm_num)
  have h35 : Nat.Coprime P3 P5 := by dsimp [P3, P5]; exact hpair 3 5 (by norm_num)
  have h45 : Nat.Coprime P4 P5 := by dsimp [P4, P5]; exact hpair 4 5 (by norm_num)
  have hp1d : P1 ∣ d := by
    dsimp [P1]
    simpa using canonicalOwnerCell_dvd_shiftedDifference data hd
      (by norm_num) (by norm_num) hfour
  have hp2d : P2 ∣ d := by
    dsimp [P2]
    simpa using canonicalOwnerCell_dvd_shiftedDifference data hd
      (by norm_num) (by norm_num) hfour
  have hp3d : P3 ∣ d := by
    dsimp [P3]
    simpa using canonicalOwnerCell_dvd_shiftedDifference data hd
      (by norm_num) (by norm_num) hfour
  have hp4d : P4 ∣ d := by
    dsimp [P4]
    simpa using canonicalOwnerCell_dvd_shiftedDifference data hd
      (by norm_num) (by norm_num) hfour
  have hp5d : P5 ∣ d := by
    dsimp [P5]
    simpa using canonicalOwnerCell_dvd_shiftedDifference data hd
      (by norm_num) (by norm_num) hfour
  have hp12d : P1 * P2 ∣ d := h12.mul_dvd_of_dvd_of_dvd hp1d hp2d
  have hc123 : Nat.Coprime (P1 * P2) P3 := h13.mul_left h23
  have hp123d : P1 * P2 * P3 ∣ d :=
    hc123.mul_dvd_of_dvd_of_dvd hp12d hp3d
  have hc1234 : Nat.Coprime (P1 * P2 * P3) P4 :=
    (h14.mul_left h24).mul_left h34
  have hp1234d : P1 * P2 * P3 * P4 ∣ d :=
    hc1234.mul_dvd_of_dvd_of_dvd hp123d hp4d
  have hc12345 : Nat.Coprime (P1 * P2 * P3 * P4) P5 :=
    ((h15.mul_left h25).mul_left h35).mul_left h45
  have hMd : M ∣ d := by
    dsimp [M, k5G12DiagonalMatchingOwnerProduct]
    exact hc12345.mul_dvd_of_dvd_of_dvd hp1234d hp5d
  have hdEq : d = M * U := by
    dsimp [U]
    exact (Nat.mul_div_cancel' hMd).symm
  have hUdiv (P : ℕ) (hPpos : 0 < P) (hPM : P ∣ M) : U ∣ d / P := by
    obtain ⟨q, hMq⟩ := hPM
    refine ⟨q, ?_⟩
    calc
      d / P = (M * U) / P := by rw [hdEq]
      _ = (P * (q * U)) / P := by rw [hMq]; ring
      _ = q * U := Nat.mul_div_cancel_left _ hPpos
      _ = U * q := by ring
  have hp1M : P1 ∣ M := by
    refine ⟨P2 * P3 * P4 * P5, ?_⟩
    dsimp [M, k5G12DiagonalMatchingOwnerProduct]
    ring
  have hp2M : P2 ∣ M := by
    refine ⟨P1 * P3 * P4 * P5, ?_⟩
    dsimp [M, k5G12DiagonalMatchingOwnerProduct]
    ring
  have hp3M : P3 ∣ M := by
    refine ⟨P1 * P2 * P4 * P5, ?_⟩
    dsimp [M, k5G12DiagonalMatchingOwnerProduct]
    ring
  have hp4M : P4 ∣ M := by
    refine ⟨P1 * P2 * P3 * P5, ?_⟩
    dsimp [M, k5G12DiagonalMatchingOwnerProduct]
    ring
  have hp5M : P5 ∣ M := by
    refine ⟨P1 * P2 * P3 * P4, ?_⟩
    dsimp [M, k5G12DiagonalMatchingOwnerProduct]
    ring
  have hp1pos : 0 < P1 := by dsimp [P1]; exact canonicalOwnerCell_pos data
  have hp2pos : 0 < P2 := by dsimp [P2]; exact canonicalOwnerCell_pos data
  have hp3pos : 0 < P3 := by dsimp [P3]; exact canonicalOwnerCell_pos data
  have hp4pos : 0 < P4 := by dsimp [P4]; exact canonicalOwnerCell_pos data
  have hp5pos : 0 < P5 := by dsimp [P5]; exact canonicalOwnerCell_pos data
  let g1 := Nat.gcd P1 U
  let g2 := Nat.gcd P2 U
  let g3 := Nat.gcd P3 U
  let g4 := Nat.gcd P4 U
  let g5 := Nat.gcd P5 U
  have hg1 : g1 ∣ 432 := by
    apply dvd_trans (Nat.dvd_gcd (Nat.gcd_dvd_left P1 U)
      ((Nat.gcd_dvd_right P1 U).trans (hUdiv P1 hp1pos hp1M)))
    exact hlocal.1.trans (by norm_num)
  have hg2 : g2 ∣ 432 := by
    apply dvd_trans (Nat.dvd_gcd (Nat.gcd_dvd_left P2 U)
      ((Nat.gcd_dvd_right P2 U).trans (hUdiv P2 hp2pos hp2M)))
    exact hlocal.2.1.trans (by norm_num)
  have hg3 : g3 ∣ 432 := by
    apply dvd_trans (Nat.dvd_gcd (Nat.gcd_dvd_left P3 U)
      ((Nat.gcd_dvd_right P3 U).trans (hUdiv P3 hp3pos hp3M)))
    exact hlocal.2.2.1.trans (by norm_num)
  have hg4 : g4 ∣ 432 := by
    apply dvd_trans (Nat.dvd_gcd (Nat.gcd_dvd_left P4 U)
      ((Nat.gcd_dvd_right P4 U).trans (hUdiv P4 hp4pos hp4M)))
    exact hlocal.2.2.2.1.trans (by norm_num)
  have hg5 : g5 ∣ 432 := by
    apply dvd_trans (Nat.dvd_gcd (Nat.gcd_dvd_left P5 U)
      ((Nat.gcd_dvd_right P5 U).trans (hUdiv P5 hp5pos hp5M)))
    exact hlocal.2.2.2.2.trans (by norm_num)
  have hgc12 : Nat.Coprime g1 g2 :=
    (h12.of_dvd_left (Nat.gcd_dvd_left P1 U)).of_dvd_right
      (Nat.gcd_dvd_left P2 U)
  have hgc13 : Nat.Coprime g1 g3 :=
    (h13.of_dvd_left (Nat.gcd_dvd_left P1 U)).of_dvd_right
      (Nat.gcd_dvd_left P3 U)
  have hgc14 : Nat.Coprime g1 g4 :=
    (h14.of_dvd_left (Nat.gcd_dvd_left P1 U)).of_dvd_right
      (Nat.gcd_dvd_left P4 U)
  have hgc15 : Nat.Coprime g1 g5 :=
    (h15.of_dvd_left (Nat.gcd_dvd_left P1 U)).of_dvd_right
      (Nat.gcd_dvd_left P5 U)
  have hgc23 : Nat.Coprime g2 g3 :=
    (h23.of_dvd_left (Nat.gcd_dvd_left P2 U)).of_dvd_right
      (Nat.gcd_dvd_left P3 U)
  have hgc24 : Nat.Coprime g2 g4 :=
    (h24.of_dvd_left (Nat.gcd_dvd_left P2 U)).of_dvd_right
      (Nat.gcd_dvd_left P4 U)
  have hgc25 : Nat.Coprime g2 g5 :=
    (h25.of_dvd_left (Nat.gcd_dvd_left P2 U)).of_dvd_right
      (Nat.gcd_dvd_left P5 U)
  have hgc34 : Nat.Coprime g3 g4 :=
    (h34.of_dvd_left (Nat.gcd_dvd_left P3 U)).of_dvd_right
      (Nat.gcd_dvd_left P4 U)
  have hgc35 : Nat.Coprime g3 g5 :=
    (h35.of_dvd_left (Nat.gcd_dvd_left P3 U)).of_dvd_right
      (Nat.gcd_dvd_left P5 U)
  have hgc45 : Nat.Coprime g4 g5 :=
    (h45.of_dvd_left (Nat.gcd_dvd_left P4 U)).of_dvd_right
      (Nat.gcd_dvd_left P5 U)
  have hg12 : g1 * g2 ∣ 432 := hgc12.mul_dvd_of_dvd_of_dvd hg1 hg2
  have hgc123 : Nat.Coprime (g1 * g2) g3 := hgc13.mul_left hgc23
  have hg123 : g1 * g2 * g3 ∣ 432 :=
    hgc123.mul_dvd_of_dvd_of_dvd hg12 hg3
  have hgc1234 : Nat.Coprime (g1 * g2 * g3) g4 :=
    (hgc14.mul_left hgc24).mul_left hgc34
  have hg1234 : g1 * g2 * g3 * g4 ∣ 432 :=
    hgc1234.mul_dvd_of_dvd_of_dvd hg123 hg4
  have hgc12345 : Nat.Coprime (g1 * g2 * g3 * g4) g5 :=
    ((hgc15.mul_left hgc25).mul_left hgc35).mul_left hgc45
  have hgprod : g1 * g2 * g3 * g4 * g5 ∣ 432 :=
    hgc12345.mul_dvd_of_dvd_of_dvd hg1234 hg5
  have hs12 : Nat.gcd U (P1 * P2) ∣ Nat.gcd U P1 * Nat.gcd U P2 :=
    gcd_mul_dvd_mul_gcd U P1 P2
  have hs123 : Nat.gcd U (P1 * P2 * P3) ∣
      Nat.gcd U P1 * Nat.gcd U P2 * Nat.gcd U P3 := by
    exact (gcd_mul_dvd_mul_gcd U (P1 * P2) P3).trans
      (Nat.mul_dvd_mul hs12 (dvd_refl _))
  have hs1234 : Nat.gcd U (P1 * P2 * P3 * P4) ∣
      Nat.gcd U P1 * Nat.gcd U P2 * Nat.gcd U P3 * Nat.gcd U P4 := by
    exact (gcd_mul_dvd_mul_gcd U (P1 * P2 * P3) P4).trans
      (Nat.mul_dvd_mul hs123 (dvd_refl _))
  have hs12345 : Nat.gcd U (P1 * P2 * P3 * P4 * P5) ∣
      Nat.gcd U P1 * Nat.gcd U P2 * Nat.gcd U P3 * Nat.gcd U P4 * Nat.gcd U P5 := by
    exact (gcd_mul_dvd_mul_gcd U (P1 * P2 * P3 * P4) P5).trans
      (Nat.mul_dvd_mul hs1234 (dvd_refl _))
  have hsplit : Nat.gcd M U ∣ g1 * g2 * g3 * g4 * g5 := by
    simpa [M, k5G12DiagonalMatchingOwnerProduct, g1, g2, g3, g4, g5,
      Nat.gcd_comm, mul_assoc] using hs12345
  exact hsplit.trans hgprod

/-- Exact unitary-overlap decomposition of the gap.  If `M` is the complete
diagonal matching product, `U=d/M`, and `G=gcd(M,U)`, then the only overlap
is the fixed `2,3`-smooth factor `G ∣ 432`; after removing it, the two
quotients are coprime and `d = G^2 (M/G) (U/G)`. -/
theorem k5_G12_diagonal_matching_unitary_overlap_decomposition
    {n d t : ℕ}
    (data : CanonicalOwnerData 5 n d t)
    (hfour : 4 ∣ n + d + t)
    (hd : 5 ≤ d)
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n)
    (hprofile : K5G12ZeroResidualProfile data) :
    let M := k5G12DiagonalMatchingOwnerProduct data
    let U := d / M
    let G := Nat.gcd M U
    G ∣ 432 ∧ Nat.Coprime (M / G) (U / G) ∧
      d = G ^ 2 * (M / G) * (U / G) := by
  dsimp only
  let M := k5G12DiagonalMatchingOwnerProduct data
  let U := d / M
  let G := Nat.gcd M U
  have hMd : M ∣ d := by
    dsimp [M]
    exact k5_G12_diagonal_matching_owner_product_dvd_gap data hfour hd
  have hdEq : d = M * U := by
    dsimp [U]
    exact (Nat.mul_div_cancel' hMd).symm
  have hMpos : 0 < M := by
    dsimp [M, k5G12DiagonalMatchingOwnerProduct]
    exact mul_pos (mul_pos (mul_pos (mul_pos
      (canonicalOwnerCell_pos data) (canonicalOwnerCell_pos data))
      (canonicalOwnerCell_pos data)) (canonicalOwnerCell_pos data))
      (canonicalOwnerCell_pos data)
  have hGpos : 0 < G := by
    dsimp [G]
    exact Nat.gcd_pos_of_pos_left U hMpos
  have hG432 : G ∣ 432 := by
    dsimp [G, M, U]
    exact k5_G12_diagonal_matching_gap_quotient_gcd_dvd_432
      data hfour hd heq hprofile
  have hcop : Nat.Coprime (M / G) (U / G) := by
    dsimp [G]
    exact Nat.coprime_div_gcd_div_gcd hGpos
  have hGM : G * (M / G) = M := Nat.mul_div_cancel' (by
    dsimp [G]
    exact Nat.gcd_dvd_left M U)
  have hGU : G * (U / G) = U := Nat.mul_div_cancel' (by
    dsimp [G]
    exact Nat.gcd_dvd_right M U)
  refine ⟨hG432, hcop, ?_⟩
  calc
    d = M * U := hdEq
    _ = (G * (M / G)) * (G * (U / G)) := by rw [hGM, hGU]
    _ = G ^ 2 * (M / G) * (U / G) := by ring

/-- The square of the complete uncovered matching product divides the
product of its five nonzero tangent defects and is bounded by their exact
uniform heights. -/
theorem k5_G12_diagonal_matching_square_dvd_tangent_product_and_height
    {n d t : ℕ}
    (data : CanonicalOwnerData 5 n d t)
    (hfour : 4 ∣ n + d + t)
    (hd : 5 ≤ d)
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n)
    (_hprofile : K5G12ZeroResidualProfile data) :
    let M := k5G12DiagonalMatchingOwnerProduct data
    let F := k5OwnerSquareDefect n d 1 1 *
      k5OwnerSquareDefect n d 2 2 *
      k5OwnerSquareDefect n d 3 3 *
      k5OwnerSquareDefect n d 4 4 *
      k5OwnerSquareDefect n d 5 5
    ((M : ℤ) ^ 2) ∣ F ∧ M ^ 2 ≤ (240 * n) ^ 5 := by
  dsimp only
  let P1 := canonicalOwnerCell data 1 1
  let P2 := canonicalOwnerCell data 2 2
  let P3 := canonicalOwnerCell data 3 3
  let P4 := canonicalOwnerCell data 4 4
  let P5 := canonicalOwnerCell data 5 5
  let M := k5G12DiagonalMatchingOwnerProduct data
  let D1 := k5OwnerSquareDefect n d 1 1
  let D2 := k5OwnerSquareDefect n d 2 2
  let D3 := k5OwnerSquareDefect n d 3 3
  let D4 := k5OwnerSquareDefect n d 4 4
  let D5 := k5OwnerSquareDefect n d 5 5
  have h1 : ((P1 : ℤ) ^ 2) ∣ D1 := by
    dsimp [P1, D1]
    exact canonicalOwnerCell_sq_dvd_k5OwnerSquareDefect data
      (by norm_num) (by norm_num) hfour heq
  have h2 : ((P2 : ℤ) ^ 2) ∣ D2 := by
    dsimp [P2, D2]
    exact canonicalOwnerCell_sq_dvd_k5OwnerSquareDefect data
      (by norm_num) (by norm_num) hfour heq
  have h3 : ((P3 : ℤ) ^ 2) ∣ D3 := by
    dsimp [P3, D3]
    exact canonicalOwnerCell_sq_dvd_k5OwnerSquareDefect data
      (by norm_num) (by norm_num) hfour heq
  have h4 : ((P4 : ℤ) ^ 2) ∣ D4 := by
    dsimp [P4, D4]
    exact canonicalOwnerCell_sq_dvd_k5OwnerSquareDefect data
      (by norm_num) (by norm_num) hfour heq
  have h5 : ((P5 : ℤ) ^ 2) ∣ D5 := by
    dsimp [P5, D5]
    exact canonicalOwnerCell_sq_dvd_k5OwnerSquareDefect data
      (by norm_num) (by norm_num) hfour heq
  have hdivRaw := Int.mul_dvd_mul (Int.mul_dvd_mul
    (Int.mul_dvd_mul (Int.mul_dvd_mul h1 h2) h3) h4) h5
  have hdiv : ((M : ℤ) ^ 2) ∣ D1 * D2 * D3 * D4 * D5 := by
    simpa [M, k5G12DiagonalMatchingOwnerProduct, P1, P2, P3, P4, P5,
      pow_two, mul_assoc, mul_left_comm, mul_comm] using hdivRaw
  have hb1 : D1.natAbs ≤ 240 * n := by
    dsimp [D1]
    exact k5OwnerSquareDefect_natAbs_le hd (by norm_num) (by norm_num) heq
  have hb2 : D2.natAbs ≤ 240 * n := by
    dsimp [D2]
    exact k5OwnerSquareDefect_natAbs_le hd (by norm_num) (by norm_num) heq
  have hb3 : D3.natAbs ≤ 240 * n := by
    dsimp [D3]
    exact k5OwnerSquareDefect_natAbs_le hd (by norm_num) (by norm_num) heq
  have hb4 : D4.natAbs ≤ 240 * n := by
    dsimp [D4]
    exact k5OwnerSquareDefect_natAbs_le hd (by norm_num) (by norm_num) heq
  have hb5 : D5.natAbs ≤ 240 * n := by
    dsimp [D5]
    exact k5OwnerSquareDefect_natAbs_le hd (by norm_num) (by norm_num) heq
  have hne1 : D1 ≠ 0 := by
    dsimp [D1]
    exact k5OwnerSquareDefect_ne_zero_of_solution hd
      (by norm_num) (by norm_num) heq
  have hne2 : D2 ≠ 0 := by
    dsimp [D2]
    exact k5OwnerSquareDefect_ne_zero_of_solution hd
      (by norm_num) (by norm_num) heq
  have hne3 : D3 ≠ 0 := by
    dsimp [D3]
    exact k5OwnerSquareDefect_ne_zero_of_solution hd
      (by norm_num) (by norm_num) heq
  have hne4 : D4 ≠ 0 := by
    dsimp [D4]
    exact k5OwnerSquareDefect_ne_zero_of_solution hd
      (by norm_num) (by norm_num) heq
  have hne5 : D5 ≠ 0 := by
    dsimp [D5]
    exact k5OwnerSquareDefect_ne_zero_of_solution hd
      (by norm_num) (by norm_num) heq
  have hnatDiv : M ^ 2 ∣ (D1 * D2 * D3 * D4 * D5).natAbs := by
    have habs := Int.natAbs_dvd_natAbs.mpr hdiv
    simpa [Int.natAbs_pow, M] using habs
  have hprodPos : 0 < (D1 * D2 * D3 * D4 * D5).natAbs := by
    exact Int.natAbs_pos.mpr (mul_ne_zero (mul_ne_zero
      (mul_ne_zero (mul_ne_zero hne1 hne2) hne3) hne4) hne5)
  have hMle : M ^ 2 ≤ (D1 * D2 * D3 * D4 * D5).natAbs :=
    Nat.le_of_dvd hprodPos hnatDiv
  have hheight : (D1 * D2 * D3 * D4 * D5).natAbs ≤ (240 * n) ^ 5 := by
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_mul]
    calc
      D1.natAbs * D2.natAbs * D3.natAbs * D4.natAbs * D5.natAbs ≤
          (240 * n) * (240 * n) * (240 * n) * (240 * n) * (240 * n) :=
        Nat.mul_le_mul (Nat.mul_le_mul
          (Nat.mul_le_mul (Nat.mul_le_mul hb1 hb2) hb3) hb4) hb5
      _ = (240 * n) ^ 5 := by ring
  exact ⟨hdiv, hMle.trans hheight⟩

/-- Combined form of the unitary-overlap decomposition and the tangent-product
square divisor.  The unbounded diagonal factor `A=M/G` is coprime to the
complementary factor `B=U/G`, while the tangent product absorbs the full
square `G^2 A^2`; the overlap `G` is a divisor of `432`. -/
theorem k5_G12_diagonal_matching_unitary_overlap_and_tangent_product
    {n d t : ℕ}
    (data : CanonicalOwnerData 5 n d t)
    (hfour : 4 ∣ n + d + t)
    (hd : 5 ≤ d)
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n)
    (hprofile : K5G12ZeroResidualProfile data) :
    let M := k5G12DiagonalMatchingOwnerProduct data
    let U := d / M
    let G := Nat.gcd M U
    let A := M / G
    let B := U / G
    let F := k5OwnerSquareDefect n d 1 1 *
      k5OwnerSquareDefect n d 2 2 *
      k5OwnerSquareDefect n d 3 3 *
      k5OwnerSquareDefect n d 4 4 *
      k5OwnerSquareDefect n d 5 5
    G ∣ 432 ∧ Nat.Coprime A B ∧ d = G ^ 2 * A * B ∧
      (((G : ℤ) ^ 2 * (A : ℤ) ^ 2) ∣ F) ∧
      G ^ 2 * A ^ 2 ≤ (240 * n) ^ 5 := by
  dsimp only
  let M := k5G12DiagonalMatchingOwnerProduct data
  let U := d / M
  let G := Nat.gcd M U
  let A := M / G
  let B := U / G
  let F := k5OwnerSquareDefect n d 1 1 *
    k5OwnerSquareDefect n d 2 2 *
    k5OwnerSquareDefect n d 3 3 *
    k5OwnerSquareDefect n d 4 4 *
    k5OwnerSquareDefect n d 5 5
  have hsplit := k5_G12_diagonal_matching_unitary_overlap_decomposition
    data hfour hd heq hprofile
  have htangent := k5_G12_diagonal_matching_square_dvd_tangent_product_and_height
    data hfour hd heq hprofile
  have hGM : G * A = M := by
    dsimp [G, A]
    exact Nat.mul_div_cancel' (Nat.gcd_dvd_left M U)
  have hpowInt : (M : ℤ) ^ 2 = (G : ℤ) ^ 2 * (A : ℤ) ^ 2 := by
    rw [← hGM]
    push_cast
    ring
  have hpowNat : M ^ 2 = G ^ 2 * A ^ 2 := by
    rw [← hGM]
    ring
  refine ⟨hsplit.1, hsplit.2.1, hsplit.2.2, ?_, ?_⟩
  · rw [← hpowInt]
    exact htangent.1
  · rw [← hpowNat]
    exact htangent.2

#print axioms k5_G12_diagonal_matching_owner_product_dvd_gap
#print axioms k5_G12_diagonal_matching_square_dvd_tangent_product_and_height
#print axioms k5_G12_diagonal_matching_tangent_product_explicit
#print axioms k5_G12_diagonal_owner_gap_quotient_gcds_fixed
#print axioms k5_G12_diagonal_matching_gap_quotient_gcd_dvd_432
#print axioms k5_G12_diagonal_matching_unitary_overlap_decomposition
#print axioms k5_G12_diagonal_matching_unitary_overlap_and_tangent_product

end Erdos686Variant
end Erdos686
