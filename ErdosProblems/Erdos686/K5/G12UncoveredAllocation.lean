/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.K5.G12DiagonalMatchingTangent

/-!
# Erdős 686, k=5: exact allocation of the ten previously uncovered cells

The ten cells outside the already controlled ten-cell gap cover and the
main diagonal occupy only five shifted diagonals.  Pairwise coprimality
therefore packs them into five, rather than ten, linear gap factors.  The
same partition gives an exact factorization of the whole lower block in the
`G=12` profile.  Restoring the two cells previously charged to the
complement quotient then gives a cofactor-free allocation of all twenty-five
owners into nine gap factors.
-/

namespace Erdos686
namespace Erdos686Variant

open scoped BigOperators

/-- The ten cells complementary to the ten-cell quotient cover and the
main-diagonal matching in the exceptional `G=12` profile. -/
def k5G12UncoveredTenOwnerProduct
    {n d t : ℕ} (data : CanonicalOwnerData 5 n d t) : ℕ :=
  canonicalOwnerCell data 1 3 * canonicalOwnerCell data 1 5 *
  canonicalOwnerCell data 2 4 *
  canonicalOwnerCell data 3 1 * canonicalOwnerCell data 3 5 *
  canonicalOwnerCell data 4 1 * canonicalOwnerCell data 4 2 *
  canonicalOwnerCell data 5 1 * canonicalOwnerCell data 5 2 *
  canonicalOwnerCell data 5 3

/-- The ten cells already occurring in the complement and normalized-gap
quotients. -/
def k5G12ControlledTenOwnerProduct
    {n d t : ℕ} (data : CanonicalOwnerData 5 n d t) : ℕ :=
  canonicalOwnerCell data 3 2 * canonicalOwnerCell data 1 4 *
  (canonicalOwnerCell data 1 2 * canonicalOwnerCell data 2 3 *
    canonicalOwnerCell data 3 4 * canonicalOwnerCell data 4 5) *
  (canonicalOwnerCell data 2 1 * canonicalOwnerCell data 4 3 *
    canonicalOwnerCell data 5 4) *
  canonicalOwnerCell data 2 5

/-- The controlled ten-cell product after removing the two exceptional
anti-diagonal owners already forced into `K`. -/
def k5G12ControlledEightOwnerProduct
    {n d t : ℕ} (data : CanonicalOwnerData 5 n d t) : ℕ :=
  (canonicalOwnerCell data 1 2 * canonicalOwnerCell data 2 3 *
    canonicalOwnerCell data 3 4 * canonicalOwnerCell data 4 5) *
  (canonicalOwnerCell data 2 1 * canonicalOwnerCell data 4 3 *
    canonicalOwnerCell data 5 4) *
  canonicalOwnerCell data 2 5

private theorem three_pairwise_owner_product_dvd
    {n d t N : ℕ} {a b c : ℕ × ℕ}
    (data : CanonicalOwnerData 5 n d t)
    (ha : canonicalOwnerCell data a.1 a.2 ∣ N)
    (hb : canonicalOwnerCell data b.1 b.2 ∣ N)
    (hc : canonicalOwnerCell data c.1 c.2 ∣ N)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    canonicalOwnerCell data a.1 a.2 *
        canonicalOwnerCell data b.1 b.2 *
        canonicalOwnerCell data c.1 c.2 ∣ N := by
  have hcopAB := canonicalOwnerCells_pairwise_coprime data hab
  have hcopAC := canonicalOwnerCells_pairwise_coprime data hac
  have hcopBC := canonicalOwnerCells_pairwise_coprime data hbc
  have hAB := hcopAB.mul_dvd_of_dvd_of_dvd ha hb
  exact (hcopAC.mul_left hcopBC).mul_dvd_of_dvd_of_dvd hAB hc

/-- The complete previously-uncovered ten-cell product fits into exactly
five shifted-diagonal factors.  This is an exact finite allocation; no
support enumeration or size estimate is used. -/
theorem k5_G12_uncovered_ten_owner_product_dvd_five_gap_factors
    {n d t : ℕ}
    (data : CanonicalOwnerData 5 n d t)
    (hfour : 4 ∣ n + d + t)
    (hd : 5 ≤ d) :
    k5G12UncoveredTenOwnerProduct data ∣
      (d - 4) * (d - 3) * (d - 2) * (d + 2) * (d + 4) := by
  let P13 := canonicalOwnerCell data 1 3
  let P15 := canonicalOwnerCell data 1 5
  let P24 := canonicalOwnerCell data 2 4
  let P31 := canonicalOwnerCell data 3 1
  let P35 := canonicalOwnerCell data 3 5
  let P41 := canonicalOwnerCell data 4 1
  let P42 := canonicalOwnerCell data 4 2
  let P51 := canonicalOwnerCell data 5 1
  let P52 := canonicalOwnerCell data 5 2
  let P53 := canonicalOwnerCell data 5 3
  have h13 : P13 ∣ d + 2 := by
    dsimp [P13]
    simpa using canonicalOwnerCell_dvd_shiftedDifference data hd
      (by norm_num) (by norm_num) hfour
  have h24 : P24 ∣ d + 2 := by
    dsimp [P24]
    simpa using canonicalOwnerCell_dvd_shiftedDifference data hd
      (by norm_num) (by norm_num) hfour
  have h35 : P35 ∣ d + 2 := by
    dsimp [P35]
    simpa using canonicalOwnerCell_dvd_shiftedDifference data hd
      (by norm_num) (by norm_num) hfour
  have hplus : P13 * P24 * P35 ∣ d + 2 := by
    exact three_pairwise_owner_product_dvd
      (a := (1, 3)) (b := (2, 4)) (c := (3, 5)) data h13 h24 h35
      (by norm_num) (by norm_num) (by norm_num)
  have h31 : P31 ∣ d - 2 := by
    dsimp [P31]
    simpa using canonicalOwnerCell_dvd_shiftedDifference data hd
      (by norm_num) (by norm_num) hfour
  have h42 : P42 ∣ d - 2 := by
    dsimp [P42]
    simpa using canonicalOwnerCell_dvd_shiftedDifference data hd
      (by norm_num) (by norm_num) hfour
  have h53 : P53 ∣ d - 2 := by
    dsimp [P53]
    simpa using canonicalOwnerCell_dvd_shiftedDifference data hd
      (by norm_num) (by norm_num) hfour
  have hminus : P31 * P42 * P53 ∣ d - 2 := by
    exact three_pairwise_owner_product_dvd
      (a := (3, 1)) (b := (4, 2)) (c := (5, 3)) data h31 h42 h53
      (by norm_num) (by norm_num) (by norm_num)
  have h41 : P41 ∣ d - 3 := by
    dsimp [P41]
    simpa using canonicalOwnerCell_dvd_shiftedDifference data hd
      (by norm_num) (by norm_num) hfour
  have h52 : P52 ∣ d - 3 := by
    dsimp [P52]
    simpa using canonicalOwnerCell_dvd_shiftedDifference data hd
      (by norm_num) (by norm_num) hfour
  have hthree : P41 * P52 ∣ d - 3 := by
    exact (canonicalOwnerCells_pairwise_coprime data (by norm_num)).mul_dvd_of_dvd_of_dvd
      h41 h52
  have h51 : P51 ∣ d - 4 := by
    dsimp [P51]
    simpa using canonicalOwnerCell_dvd_shiftedDifference data hd
      (by norm_num) (by norm_num) hfour
  have h15 : P15 ∣ d + 4 := by
    dsimp [P15]
    simpa using canonicalOwnerCell_dvd_shiftedDifference data hd
      (by norm_num) (by norm_num) hfour
  have hproduct := Nat.mul_dvd_mul
    (Nat.mul_dvd_mul (Nat.mul_dvd_mul (Nat.mul_dvd_mul h51 hthree) hminus) hplus) h15
  simpa [k5G12UncoveredTenOwnerProduct, P13, P15, P24, P31, P35,
    P41, P42, P51, P52, P53, mul_assoc, mul_left_comm, mul_comm] using hproduct

/-- The earlier ten-cell cover can also be allocated entirely to its three
shifted-gap factors.  In particular the two exceptional anti-diagonal cells
need not be charged to the unbounded complement quotient `K`: they are the
missing cells in the already banked full offset-minus-one and offset-three
diagonals. -/
theorem k5_G12_controlled_ten_owner_product_dvd_three_gap_factors
    {n d t : ℕ}
    (data : CanonicalOwnerData 5 n d t)
    (hfour : 4 ∣ n + d + t)
    (hd : 5 ≤ d)
    (hprofile : K5G12ZeroResidualProfile data) :
    k5G12ControlledTenOwnerProduct data ∣
      ((d + 1) / 2) * (d - 1) * ((d + 3) / 2) := by
  have hp := k5_G12_residual_weighted_gap_diagonal_product_dvd_half_gap
    data hfour hd hprofile
  have hm := k5_G12_opposite_residual_weighted_gap_products
    data hfour hd hprofile
  have hthree := k5_G12_positive_three_diagonal_product_dvd_half_gap
    data hfour hd hprofile
  have hproduct := Nat.mul_dvd_mul (Nat.mul_dvd_mul hp.1 hm.2) hthree
  simpa [k5G12ControlledTenOwnerProduct,
    mul_assoc, mul_left_comm, mul_comm] using hproduct

/-- The `G=12` profile partitions all twenty-five cells exactly into the
controlled ten-cell cover, the five-cell diagonal matching, and the ten-cell
five-gap allocation. -/
theorem k5_G12_exact_complete_owner_partition
    {n d t : ℕ}
    (data : CanonicalOwnerData 5 n d t)
    (hprofile : K5G12ZeroResidualProfile data) :
    12 * (k5G12ControlledTenOwnerProduct data *
      k5G12DiagonalMatchingOwnerProduct data *
      k5G12UncoveredTenOwnerProduct data) = blockProduct 5 n := by
  have hresprod := canonicalLowerResidual_product_eq_global data
  have hres : canonicalOwnerResidual data = 12 := by
    rw [← hresprod]
    rcases hprofile with
      ⟨-, hl1, hl2, hl3, hl4, hl5, -⟩
    norm_num [Finset.prod_Icc_succ_top, hl1, hl2, hl3, hl4, hl5]
  have hall := canonicalOwnerResidual_mul_allCells data
  rw [hres] at hall
  norm_num [Finset.prod_Icc_succ_top] at hall
  rw [← hall]
  simp only [k5G12ControlledTenOwnerProduct,
    k5G12DiagonalMatchingOwnerProduct, k5G12UncoveredTenOwnerProduct]
  ring

/-- Cancel the two anti-diagonal owners from both the controlled product and
the complement quotient.  The new quotient `J` is the genuine unallocated
part of `K`; the other eight controlled owners fit into the three normalized
gap factors with `J` as their only remaining cofactor. -/
theorem k5_G12_reduced_complement_quotient_controls_eight_owners
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
    let J := K / (A * B)
    K = A * B * J ∧
      k5G12ControlledEightOwnerProduct data ∣
        J * ((d + 1) / 2) * (d - 1) * ((d + 3) / 2) := by
  dsimp only
  let P := canonicalOwnerCell data 4 1
  let Q := canonicalOwnerCell data 2 3
  let A := canonicalOwnerCell data 3 2
  let B := canonicalOwnerCell data 1 4
  let R := (n + 4) / P
  let C := (n + d + 1) / P
  let K := (R + C) / (P * Q)
  let J := K / (A * B)
  have hABraw :=
    k5_G12_anti_diagonal_owner_product_dvd_complement_quotient
      data hfour heq hprofile
  have hAB : A * B ∣ K := by simpa [A, B, K, P, Q, R, C] using hABraw.1
  have hfactor : K = A * B * J := by
    dsimp [J]
    exact (Nat.mul_div_cancel' hAB).symm
  have hcontrolledRaw :=
    k5_G12_ten_distinct_owner_product_dvd_global_quotient_product
      data hfour hd heq hprofile
  have hcontrolled : A * B * k5G12ControlledEightOwnerProduct data ∣
      K * ((d + 1) / 2) * (d - 1) * ((d + 3) / 2) := by
    simpa [A, B, K, P, Q, R, C, k5G12ControlledEightOwnerProduct,
      mul_assoc, mul_left_comm, mul_comm] using hcontrolledRaw
  have hABpos : 0 < A * B := Nat.mul_pos
    (by dsimp [A]; exact canonicalOwnerCell_pos data)
    (by dsimp [B]; exact canonicalOwnerCell_pos data)
  have hcancelled : k5G12ControlledEightOwnerProduct data ∣
      J * ((d + 1) / 2) * (d - 1) * ((d + 3) / 2) := by
    apply (Nat.mul_dvd_mul_iff_left hABpos).mp
    rw [hfactor] at hcontrolled
    simpa [mul_assoc] using hcontrolled
  exact ⟨hfactor, hcancelled⟩

/-- After the exact twenty-five-cell partition, every owner factor is
absorbed by nine linear gap factors except for the single complement
quotient `K`.  Thus `K` is the only unbounded cofactor left by the complete
finite allocation. -/
theorem k5_G12_block_dvd_single_quotient_nine_gap_product
    {n d t : ℕ}
    (data : CanonicalOwnerData 5 n d t)
    (hfour : 4 ∣ n + d + t)
    (hd : 5 ≤ d)
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n)
    (hprofile : K5G12ZeroResidualProfile data) :
    let P := canonicalOwnerCell data 4 1
    let Q := canonicalOwnerCell data 2 3
    let R := (n + 4) / P
    let C := (n + d + 1) / P
    let K := (R + C) / (P * Q)
    blockProduct 5 n ∣
      12 * (K * ((d + 1) / 2) * (d - 1) * ((d + 3) / 2) * d *
        ((d - 4) * (d - 3) * (d - 2) * (d + 2) * (d + 4))) := by
  dsimp only
  let P := canonicalOwnerCell data 4 1
  let Q := canonicalOwnerCell data 2 3
  let R := (n + 4) / P
  let C := (n + d + 1) / P
  let K := (R + C) / (P * Q)
  have hcontrolledRaw :=
    k5_G12_ten_distinct_owner_product_dvd_global_quotient_product
      data hfour hd heq hprofile
  have hcontrolled : k5G12ControlledTenOwnerProduct data ∣
      K * ((d + 1) / 2) * (d - 1) * ((d + 3) / 2) := by
    simpa [k5G12ControlledTenOwnerProduct, P, Q, R, C, K,
      mul_assoc, mul_left_comm, mul_comm] using hcontrolledRaw
  have hmatching : k5G12DiagonalMatchingOwnerProduct data ∣ d :=
    k5_G12_diagonal_matching_owner_product_dvd_gap data hfour hd
  have huncovered :=
    k5_G12_uncovered_ten_owner_product_dvd_five_gap_factors
      data hfour hd
  have hproduct := Nat.mul_dvd_mul
    (Nat.mul_dvd_mul hcontrolled hmatching) huncovered
  have hpartition := k5_G12_exact_complete_owner_partition data hprofile
  rw [← hpartition]
  simpa [mul_assoc] using Nat.mul_dvd_mul_left 12 hproduct

/-- Complete cofactor-free allocation of all twenty-five owners.  The exact
`G=12` block is absorbed by nine linear gap factors (two of them normalized
by the residual weights); no complement quotient remains. -/
theorem k5_G12_block_dvd_nine_gap_product
    {n d t : ℕ}
    (data : CanonicalOwnerData 5 n d t)
    (hfour : 4 ∣ n + d + t)
    (hd : 5 ≤ d)
    (hprofile : K5G12ZeroResidualProfile data) :
    blockProduct 5 n ∣
      12 * (((d + 1) / 2) * (d - 1) * ((d + 3) / 2) * d *
        ((d - 4) * (d - 3) * (d - 2) * (d + 2) * (d + 4))) := by
  have hcontrolled :=
    k5_G12_controlled_ten_owner_product_dvd_three_gap_factors
      data hfour hd hprofile
  have hmatching : k5G12DiagonalMatchingOwnerProduct data ∣ d :=
    k5_G12_diagonal_matching_owner_product_dvd_gap data hfour hd
  have huncovered :=
    k5_G12_uncovered_ten_owner_product_dvd_five_gap_factors
      data hfour hd
  have hproduct := Nat.mul_dvd_mul
    (Nat.mul_dvd_mul hcontrolled hmatching) huncovered
  have hpartition := k5_G12_exact_complete_owner_partition data hprofile
  rw [← hpartition]
  simpa [mul_assoc] using Nat.mul_dvd_mul_left 12 hproduct

/-- Sharp normalized form of the complete allocation.  The two residual
weight cancellations improve the generic coefficient `12` to `3`: the
whole lower block divides three times the nine-term diagonal window. -/
theorem k5_G12_block_dvd_three_mul_diagonal_window
    {n d t : ℕ}
    (data : CanonicalOwnerData 5 n d t)
    (hfour : 4 ∣ n + d + t)
    (hd : 5 ≤ d)
    (hprofile : K5G12ZeroResidualProfile data) :
    blockProduct 5 n ∣
      3 * ((d - 4) * (d - 3) * (d - 2) * (d - 1) * d *
        (d + 1) * (d + 2) * (d + 3) * (d + 4)) := by
  have hdiv := k5_G12_block_dvd_nine_gap_product
    data hfour hd hprofile
  rcases hprofile with
    ⟨rfl, hl1, -, -, -, -, -, hu2, -, -, -⟩
  let L1 := canonicalOwnerRow data 1
  let U2 := canonicalOwnerColumn data 2
  have hL1 : n + 1 = 2 * L1 := by
    simpa [L1, hl1] using canonical_lower_term_factorization data (j := 1)
  have hU2 : n + d + 2 = 2 * U2 := by
    simpa [U2, hu2] using canonical_upper_term_factorization data hfour (i := 2)
  have heven1 : Even (d + 1) := by
    refine ⟨U2 - L1, ?_⟩
    omega
  have heven3 : Even (d + 3) := by
    refine ⟨U2 - L1 + 1, ?_⟩
    omega
  have hdouble1 : 2 * ((d + 1) / 2) = d + 1 :=
    Nat.two_mul_div_two_of_even heven1
  have hdouble3 : 2 * ((d + 3) / 2) = d + 3 :=
    Nat.two_mul_div_two_of_even heven3
  have htargets :
      12 * (((d + 1) / 2) * (d - 1) * ((d + 3) / 2) * d *
        ((d - 4) * (d - 3) * (d - 2) * (d + 2) * (d + 4))) =
      3 * ((d - 4) * (d - 3) * (d - 2) * (d - 1) * d *
        (d + 1) * (d + 2) * (d + 3) * (d + 4)) := by
    calc
      12 * (((d + 1) / 2) * (d - 1) * ((d + 3) / 2) * d *
          ((d - 4) * (d - 3) * (d - 2) * (d + 2) * (d + 4))) =
          3 * (2 * ((d + 1) / 2)) * (2 * ((d + 3) / 2)) *
            ((d - 4) * (d - 3) * (d - 2) * (d - 1) * d *
              (d + 2) * (d + 4)) := by ring
      _ = 3 * ((d - 4) * (d - 3) * (d - 2) * (d - 1) * d *
          (d + 1) * (d + 2) * (d + 3) * (d + 4)) := by
        rw [hdouble1, hdouble3]
        ring
  rw [← htargets]
  exact hdiv

#print axioms k5_G12_uncovered_ten_owner_product_dvd_five_gap_factors
#print axioms k5_G12_controlled_ten_owner_product_dvd_three_gap_factors
#print axioms k5_G12_exact_complete_owner_partition
#print axioms k5_G12_reduced_complement_quotient_controls_eight_owners
#print axioms k5_G12_block_dvd_single_quotient_nine_gap_product
#print axioms k5_G12_block_dvd_nine_gap_product
#print axioms k5_G12_block_dvd_three_mul_diagonal_window

end Erdos686Variant
end Erdos686
