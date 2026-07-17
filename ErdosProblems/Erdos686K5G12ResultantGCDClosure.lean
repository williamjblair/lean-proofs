/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686K5G12CenteredSumResultant
import ErdosProblems.Erdos686TwoOwnerAggregate

/-!
# Erdős 686, k=5: gcd closure of the G=12 centered resultant

The four gap quotients in the centered-sum resultant are not arbitrary.
The two fully owned complement pairs give gcd bounds `2`; the two
residual-two pairs give gcd bounds `24`, after the possible overlap of `J`
with their row-rest owner products is confined to `6`.  Iterated gcd
cancellation then forces the entire remaining complement quotient `J` into
the fixed integer `23040`.
-/

namespace Erdos686
namespace Erdos686Variant

open scoped BigOperators

set_option maxHeartbeats 1000000

private theorem gcd_dvd_two_of_coprime_sum_difference
    {J x y z : ℕ}
    (hxy : Nat.Coprime x y) (hJsum : J ∣ x + y)
    (hxylt : x ≤ y) (hz : z = y - x) :
    Nat.gcd J z ∣ 2 := by
  let g := Nat.gcd J z
  have hgJ : g ∣ J := Nat.gcd_dvd_left J z
  have hgz : g ∣ z := Nat.gcd_dvd_right J z
  have hgsum : g ∣ x + y := hgJ.trans hJsum
  have hgtwox : g ∣ 2 * x := by
    have hsub := Nat.dvd_sub hgsum hgz
    rw [hz] at hsub
    convert hsub using 1 <;> omega
  have hcopsumx : Nat.Coprime (x + y) x := by simpa using hxy.symm
  have hcopgx : Nat.Coprime g x :=
    hcopsumx.of_dvd_left hgsum
  exact hcopgx.dvd_of_dvd_mul_right hgtwox

private theorem gcd_dvd_twenty_four_of_weighted_sum_difference
    {J r c z : ℕ}
    (hJsum : J ∣ 2 * (r + c))
    (hrc : r ≤ c) (hz : z = 2 * (c - r))
    (hrest : Nat.gcd J r ∣ 6) :
    Nat.gcd J z ∣ 24 := by
  let g := Nat.gcd J z
  have hgJ : g ∣ J := Nat.gcd_dvd_left J z
  have hgz : g ∣ z := Nat.gcd_dvd_right J z
  have hgsum : g ∣ 2 * (r + c) := hgJ.trans hJsum
  have hgfourr : g ∣ 4 * r := by
    have hsub := Nat.dvd_sub hgsum hgz
    rw [hz] at hsub
    convert hsub using 1 <;> omega
  have hggcd : Nat.gcd g r ∣ 6 := by
    exact (gcd_dvd_gcd hgJ (dvd_refl r)).trans hrest
  exact dvd_scaled_of_dvd_mul_of_gcd_dvd hgfourr hggcd

/-- Exact gcd bounds for all four quotients occurring in the nonlinear
centered-sum resultant. -/
theorem k5_G12_centered_resultant_quotient_gcd_bounds
    {n d t : ℕ}
    (data : CanonicalOwnerData 5 n d t)
    (hfour : 4 ∣ n + d + t)
    (hd : 5 ≤ d)
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
    let J := K / (A * B)
    Nat.gcd J ((d - 3) / P) ∣ 2 ∧
      Nat.gcd J ((d - 1) / A) ∣ 24 ∧
      Nat.gcd J ((d + 1) / Q) ∣ 2 ∧
      Nat.gcd J ((d + 3) / B) ∣ 24 := by
  classical
  dsimp only
  let P := canonicalOwnerCell data 4 1
  let Q := canonicalOwnerCell data 2 3
  let A := canonicalOwnerCell data 3 2
  let B := canonicalOwnerCell data 1 4
  let R := (n + 4) / P
  let C := (n + d + 1) / P
  let K := (R + C) / (P * Q)
  let J := K / (A * B)
  let p := (d - 3) / P
  let q := (d + 1) / Q
  let a := (d - 1) / A
  let b := (d + 3) / B
  let RA := canonicalOwnerCell data 3 1 * canonicalOwnerCell data 3 3 *
    canonicalOwnerCell data 3 4 * canonicalOwnerCell data 3 5
  let CA := canonicalOwnerCell data 1 2 * canonicalOwnerCell data 2 2 *
    canonicalOwnerCell data 4 2 * canonicalOwnerCell data 5 2
  let RB := canonicalOwnerCell data 1 1 * canonicalOwnerCell data 1 2 *
    canonicalOwnerCell data 1 3 * canonicalOwnerCell data 1 5
  let CB := canonicalOwnerCell data 2 4 * canonicalOwnerCell data 3 4 *
    canonicalOwnerCell data 4 4 * canonicalOwnerCell data 5 4
  have hforced := k5_G12_anti_diagonal_owner_product_dvd_complement_quotient
    data hfour heq hprofile
  have hABdvdK : A * B ∣ K := hforced.1
  have htarget : (n + 3) + (n + d + 2) = P ^ 2 * Q * K := by
    simpa [P, Q, A, B, R, C, K] using hforced.2.2
  have hKeq : K = A * B * J := by
    dsimp [J]
    exact (Nat.mul_div_cancel' hABdvdK).symm
  have hJdvdK : J ∣ K := by
    refine ⟨A * B, ?_⟩
    rw [hKeq]
    ring
  have hprimitive := k5_G12_exceptional_complement_quotient_gcd_Q_dvd_five
    data hfour heq hprofile
  have hsumP : R + C = P * Q * K := hprimitive.1
  have hcomp := k5_G12_zero_crossing_product_dvd_complement_sum
    data hfour heq hprofile htail hdlt hcells
  rcases hcomp with
    ⟨hrowP, hcolP, -, -, hcopRC, -, -, hRltC, -, -, -, -, -⟩
  change n + 4 = P * R at hrowP
  change n + d + 1 = P * C at hcolP
  change R < C at hRltC
  change Nat.Coprime R C at hcopRC
  have hPd : P ∣ d - 3 := by
    dsimp [P]
    simpa using canonicalOwnerCell_dvd_shiftedDifference data hd
      (by norm_num) (by norm_num) hfour
  have hPfactor : d - 3 = P * p := by
    dsimp [p]
    exact (Nat.mul_div_cancel' hPd).symm
  have hpCR : p = C - R := by
    apply Nat.mul_left_cancel (show 0 < P by
      dsimp [P]; exact canonicalOwnerCell_pos data)
    calc
      P * p = d - 3 := hPfactor.symm
      _ = P * C - P * R := by rw [← hrowP, ← hcolP]; omega
      _ = P * (C - R) := (Nat.mul_sub_left_distrib P C R).symm
  have hJsumP : J ∣ R + C := by
    exact hJdvdK.trans ⟨P * Q, by rw [hsumP]; ring⟩
  have hgp : Nat.gcd J p ∣ 2 :=
    gcd_dvd_two_of_coprime_sum_difference hcopRC hJsumP
      (Nat.le_of_lt hRltC) hpCR

  let S := (n + 2) / Q
  let D := (n + d + 3) / Q
  have hrowQ : n + 2 = Q * S := hprimitive.2.1
  have hcolQ : n + d + 3 = Q * D := hprimitive.2.2.1
  have hsumQ : S + D = P ^ 2 * K := hprimitive.2.2.2.1
  have hgcdTermsQ : Nat.gcd (n + 2) (n + d + 3) = Q := by
    have hg := canonicalOwner_fullyOwned_gcd_modifiedUpper_eq_cell
      data (j := 2) (i := 3) (by norm_num) (by norm_num)
      hprofile.2.2.1 hprofile.2.2.2.2.2.2.2.2.1
    simpa [upperTermAfterFour, hprofile.1, Q] using hg
  have hcopSD : Nat.Coprime S D := by
    rw [hrowQ, hcolQ, Nat.gcd_mul_left] at hgcdTermsQ
    apply Nat.mul_left_cancel (show 0 < Q by
      dsimp [Q]; exact canonicalOwnerCell_pos data)
    simpa using hgcdTermsQ
  have hQd : Q ∣ d + 1 := by
    dsimp [Q]
    simpa using canonicalOwnerCell_dvd_shiftedDifference data hd
      (by norm_num) (by norm_num) hfour
  have hQfactor : d + 1 = Q * q := by
    dsimp [q]
    exact (Nat.mul_div_cancel' hQd).symm
  have hSltD : S < D := by
    have hQpos : 0 < Q := by dsimp [Q]; exact canonicalOwnerCell_pos data
    apply (Nat.mul_lt_mul_left hQpos).mp
    rw [← hrowQ, ← hcolQ]
    omega
  have hqDS : q = D - S := by
    apply Nat.mul_left_cancel (show 0 < Q by
      dsimp [Q]; exact canonicalOwnerCell_pos data)
    calc
      Q * q = d + 1 := hQfactor.symm
      _ = Q * D - Q * S := by rw [← hrowQ, ← hcolQ]; omega
      _ = Q * (D - S) := (Nat.mul_sub_left_distrib Q D S).symm
  have hJsumQ : J ∣ S + D := by
    rw [hsumQ]
    exact dvd_mul_of_dvd_right hJdvdK (P ^ 2)
  have hgq : Nat.gcd J q ∣ 2 :=
    gcd_dvd_two_of_coprime_sum_difference hcopSD hJsumQ
      (Nat.le_of_lt hSltD) hqDS

  have hcellOverlap (j i c : ℕ)
      (hoff : Int.natAbs ((j : ℤ) + (i : ℤ) - 5) = c) :
      Nat.gcd J (canonicalOwnerCell data j i) ∣ c := by
    have hJKgcd : Nat.gcd J (canonicalOwnerCell data j i) ∣
        Nat.gcd K (canonicalOwnerCell data j i) :=
      gcd_dvd_gcd hJdvdK (dvd_refl _)
    have hcell := k5_G12_owner_gcd_complement_quotient_dvd_antidiagonal_offset
      data hfour heq hprofile (j := j) (i := i)
    have hcell' : Nat.gcd K (canonicalOwnerCell data j i) ∣ c := by
      rw [Nat.gcd_comm]
      simpa [hoff] using hcell
    exact hJKgcd.trans hcell'
  have hJRA : Nat.gcd J RA ∣ 6 := by
    have h31 := hcellOverlap 3 1 1 (by norm_num)
    have h33 := hcellOverlap 3 3 1 (by norm_num)
    have h34 := hcellOverlap 3 4 2 (by norm_num)
    have h35 := hcellOverlap 3 5 3 (by norm_num)
    have hsplit1 := gcd_mul_dvd_mul_gcd J
      (canonicalOwnerCell data 3 1) (canonicalOwnerCell data 3 3)
    have hsplit2 := gcd_mul_dvd_mul_gcd J
      (canonicalOwnerCell data 3 1 * canonicalOwnerCell data 3 3)
      (canonicalOwnerCell data 3 4)
    have hsplit3 := gcd_mul_dvd_mul_gcd J
      (canonicalOwnerCell data 3 1 * canonicalOwnerCell data 3 3 *
        canonicalOwnerCell data 3 4) (canonicalOwnerCell data 3 5)
    have hprod :
        Nat.gcd J (canonicalOwnerCell data 3 1) *
          Nat.gcd J (canonicalOwnerCell data 3 3) *
          Nat.gcd J (canonicalOwnerCell data 3 4) *
          Nat.gcd J (canonicalOwnerCell data 3 5) ∣ 6 := by
      exact Nat.mul_dvd_mul (Nat.mul_dvd_mul (Nat.mul_dvd_mul h31 h33) h34) h35
    apply dvd_trans (hsplit3.trans (Nat.mul_dvd_mul
      (hsplit2.trans (Nat.mul_dvd_mul hsplit1 (dvd_refl _))) (dvd_refl _)))
    simpa [RA, mul_assoc] using hprod
  have hJRB : Nat.gcd J RB ∣ 6 := by
    have h11 := hcellOverlap 1 1 3 (by norm_num)
    have h12 := hcellOverlap 1 2 2 (by norm_num)
    have h13 := hcellOverlap 1 3 1 (by norm_num)
    have h15 := hcellOverlap 1 5 1 (by norm_num)
    have hsplit1 := gcd_mul_dvd_mul_gcd J
      (canonicalOwnerCell data 1 1) (canonicalOwnerCell data 1 2)
    have hsplit2 := gcd_mul_dvd_mul_gcd J
      (canonicalOwnerCell data 1 1 * canonicalOwnerCell data 1 2)
      (canonicalOwnerCell data 1 3)
    have hsplit3 := gcd_mul_dvd_mul_gcd J
      (canonicalOwnerCell data 1 1 * canonicalOwnerCell data 1 2 *
        canonicalOwnerCell data 1 3) (canonicalOwnerCell data 1 5)
    have hprod :
        Nat.gcd J (canonicalOwnerCell data 1 1) *
          Nat.gcd J (canonicalOwnerCell data 1 2) *
          Nat.gcd J (canonicalOwnerCell data 1 3) *
          Nat.gcd J (canonicalOwnerCell data 1 5) ∣ 6 := by
      exact Nat.mul_dvd_mul (Nat.mul_dvd_mul (Nat.mul_dvd_mul h11 h12) h13) h15
    apply dvd_trans (hsplit3.trans (Nat.mul_dvd_mul
      (hsplit2.trans (Nat.mul_dvd_mul hsplit1 (dvd_refl _))) (dvd_refl _)))
    simpa [RB, mul_assoc] using hprod

  have hrowProdA : canonicalOwnerRow data 3 = A * RA := by
    rw [← canonicalOwner_row_cell_product data]
    norm_num [A, RA, Finset.prod_Icc_succ_top]
    ring
  have hcolProdA : canonicalOwnerColumn data 2 = A * CA := by
    rw [← canonicalOwner_column_cell_product data]
    norm_num [A, CA, Finset.prod_Icc_succ_top]
    ring
  have hrowProdB : canonicalOwnerRow data 1 = B * RB := by
    rw [← canonicalOwner_row_cell_product data]
    norm_num [B, RB, Finset.prod_Icc_succ_top]
    ring
  have hcolProdB : canonicalOwnerColumn data 4 = B * CB := by
    rw [← canonicalOwner_column_cell_product data]
    norm_num [B, CB, Finset.prod_Icc_succ_top]
    ring
  rcases hprofile with
    ⟨rfl, hl1, hl2, hl3, hl4, hl5, hu1, hu2, hu3, hu4, hu5⟩
  have hrowA : n + 3 = 2 * (A * RA) := by
    simpa [hl3, hrowProdA] using canonical_lower_term_factorization data (j := 3)
  have hcolA : n + d + 2 = 2 * (A * CA) := by
    simpa [upperTermAfterFour, hu2, hcolProdA] using
      canonical_upper_term_factorization data hfour (i := 2)
  have hAfactor : d - 1 = A * a := by
    dsimp [a]
    exact (Nat.mul_div_cancel' (by
      dsimp [A]
      simpa using canonicalOwnerCell_dvd_shiftedDifference data hd
        (by norm_num) (by norm_num) hfour)).symm
  have hRAltC : RA ≤ CA := by
    have hApos : 0 < A := by dsimp [A]; exact canonicalOwnerCell_pos data
    have hmul : 2 * (A * RA) < 2 * (A * CA) := by
      rw [← hrowA, ← hcolA]
      omega
    have hmul' : A * RA < A * CA := by
      exact (Nat.mul_lt_mul_left (by norm_num : 0 < 2)).mp hmul
    exact Nat.le_of_lt ((Nat.mul_lt_mul_left hApos).mp hmul')
  have haDiff : a = 2 * (CA - RA) := by
    apply Nat.mul_left_cancel (show 0 < A by
      dsimp [A]; exact canonicalOwnerCell_pos data)
    calc
      A * a = d - 1 := hAfactor.symm
      _ = (n + d + 2) - (n + 3) := by omega
      _ = 2 * (A * CA) - 2 * (A * RA) := by rw [hrowA, hcolA]
      _ = 2 * (A * CA - A * RA) :=
        (Nat.mul_sub_left_distrib 2 (A * CA) (A * RA)).symm
      _ = 2 * (A * (CA - RA)) :=
        congrArg (fun z : ℕ => 2 * z)
          (Nat.mul_sub_left_distrib A CA RA).symm
      _ = A * (2 * (CA - RA)) := by ring
  have hJsumA : J ∣ 2 * (RA + CA) := by
    have ht := htarget
    rw [hrowA, hcolA, hKeq] at ht
    refine ⟨P ^ 2 * Q * B, ?_⟩
    apply Nat.mul_left_cancel (show 0 < A by
      dsimp [A]; exact canonicalOwnerCell_pos data)
    convert ht using 1 <;> ring
  have hga : Nat.gcd J a ∣ 24 :=
    gcd_dvd_twenty_four_of_weighted_sum_difference hJsumA hRAltC haDiff hJRA

  have hrowB : n + 1 = 2 * (B * RB) := by
    simpa [hl1, hrowProdB] using canonical_lower_term_factorization data (j := 1)
  have hcolB : n + d + 4 = 8 * (B * CB) := by
    have hfac := canonical_upper_term_factorization data hfour (i := 4)
    rw [hu4, hcolProdB] at hfac
    simpa [upperTermAfterFour] using congrArg (fun z : ℕ => 4 * z) hfac
  have hBfactor : d + 3 = B * b := by
    dsimp [b]
    exact (Nat.mul_div_cancel' (by
      dsimp [B]
      simpa using canonicalOwnerCell_dvd_shiftedDifference data hd
        (by norm_num) (by norm_num) hfour)).symm
  have hRBle : RB ≤ 4 * CB := by
    have hBpos : 0 < B := by dsimp [B]; exact canonicalOwnerCell_pos data
    have hmul : 2 * (B * RB) < 8 * (B * CB) := by
      rw [← hrowB, ← hcolB]
      omega
    have hmul' : B * RB < B * (4 * CB) := by
      apply (Nat.mul_lt_mul_left (by norm_num : 0 < 2)).mp
      convert hmul using 1 <;> ring
    exact Nat.le_of_lt ((Nat.mul_lt_mul_left hBpos).mp hmul')
  have hbDiff : b = 2 * (4 * CB - RB) := by
    apply Nat.mul_left_cancel (show 0 < B by
      dsimp [B]; exact canonicalOwnerCell_pos data)
    calc
      B * b = d + 3 := hBfactor.symm
      _ = (n + d + 4) - (n + 1) := by omega
      _ = 8 * (B * CB) - 2 * (B * RB) := by rw [hrowB, hcolB]
      _ = 2 * (B * (4 * CB)) - 2 * (B * RB) := by ring
      _ = 2 * (B * (4 * CB) - B * RB) :=
        (Nat.mul_sub_left_distrib 2 (B * (4 * CB)) (B * RB)).symm
      _ = 2 * (B * (4 * CB - RB)) :=
        congrArg (fun z : ℕ => 2 * z)
          (Nat.mul_sub_left_distrib B (4 * CB) RB).symm
      _ = B * (2 * (4 * CB - RB)) := by ring
  have hJsumB : J ∣ 2 * (RB + 4 * CB) := by
    have ht' : (n + 1) + (n + d + 4) = P ^ 2 * Q * K := by
      omega
    rw [hrowB, hcolB, hKeq] at ht'
    refine ⟨P ^ 2 * Q * A, ?_⟩
    apply Nat.mul_left_cancel (show 0 < B by
      dsimp [B]; exact canonicalOwnerCell_pos data)
    convert ht' using 1 <;> ring
  have hgb : Nat.gcd J b ∣ 24 := by
    apply gcd_dvd_twenty_four_of_weighted_sum_difference
      hJsumB hRBle hbDiff hJRB
  exact ⟨hgp, hga, hgq, hgb⟩

/-- The nonlinear resultant and its four gcd bounds force the remaining
unallocated complement quotient into a fixed integer. -/
theorem k5_G12_remaining_complement_quotient_dvd_23040
    {n d t : ℕ}
    (data : CanonicalOwnerData 5 n d t)
    (hfour : 4 ∣ n + d + t)
    (hd : 5 ≤ d)
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
    let J := K / (A * B)
    J ∣ 23040 := by
  dsimp only
  let P := canonicalOwnerCell data 4 1
  let Q := canonicalOwnerCell data 2 3
  let A := canonicalOwnerCell data 3 2
  let B := canonicalOwnerCell data 1 4
  let R := (n + 4) / P
  let C := (n + d + 1) / P
  let K := (R + C) / (P * Q)
  let J := K / (A * B)
  let p := (d - 3) / P
  let q := (d + 1) / Q
  let a := (d - 1) / A
  let b := (d + 3) / B
  have hres := k5_G12_remaining_complement_quotient_dvd_centered_resultant
    data hfour hd heq hprofile
  have hg := k5_G12_centered_resultant_quotient_gcd_bounds
    data hfour hd heq hprofile htail hdlt hcells
  have h1 : J ∣ (5 * p ^ 2 * a * q) * 24 := by
    apply dvd_scaled_of_dvd_mul_of_gcd_dvd
      (m := J) (b := b) (K := 5 * p ^ 2 * a * q)
    · simpa [p, q, a, b, mul_assoc] using hres
    · simpa [p, q, a, b] using hg.2.2.2
  have h2 : J ∣ (5 * p ^ 2 * a * 24) * 2 := by
    apply dvd_scaled_of_dvd_mul_of_gcd_dvd
      (m := J) (b := q) (K := 5 * p ^ 2 * a * 24)
    · simpa [mul_assoc, mul_left_comm, mul_comm] using h1
    · simpa [p, q, a, b] using hg.2.2.1
  have h3 : J ∣ (5 * p ^ 2 * (24 * 2)) * 24 := by
    apply dvd_scaled_of_dvd_mul_of_gcd_dvd
      (m := J) (b := a) (K := 5 * p ^ 2 * (24 * 2))
    · convert h2 using 1 <;> ring
    · simpa [p, q, a, b] using hg.2.1
  have h4 : J ∣ (5 * p * (24 * 2 * 24)) * 2 := by
    apply dvd_scaled_of_dvd_mul_of_gcd_dvd
      (m := J) (b := p) (K := 5 * p * (24 * 2 * 24))
    · convert h3 using 1 <;> ring
    · simpa [p, q, a, b] using hg.1
  have h5 : J ∣ (5 * (24 * 2 * 24) * 2) * 2 := by
    apply dvd_scaled_of_dvd_mul_of_gcd_dvd
      (m := J) (b := p) (K := 5 * (24 * 2 * 24) * 2)
    · convert h4 using 1 <;> ring
    · simpa [p, q, a, b] using hg.1
  norm_num at h5 ⊢
  exact h5

#print axioms k5_G12_centered_resultant_quotient_gcd_bounds
#print axioms k5_G12_remaining_complement_quotient_dvd_23040

end Erdos686Variant
end Erdos686
