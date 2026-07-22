/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.K5.G12UncoveredAllocation

/-!
# Erdős 686, k=5: unitary overlap inside the exceptional anti-diagonal quotient

The two interior owners on the exceptional anti-diagonal divide the exact
complement quotient `K`.  This module combines that global sum equation with
their independent owner-square tangent congruences.  After one owner is
cancelled from `K`, any repeated part of `(3,2)` divides `20`, while any
repeated part of `(1,4)` divides `180`.  Pairwise owner coprimality then gives
the sharp combined fixed overlap `gcd(A*B, K/(A*B)) | 180`.

Unlike the nine-gap window divisor, this conclusion uses the owner-square
congruences and the exact `G=12` row/column residual weights.
-/

namespace Erdos686
namespace Erdos686Variant

open scoped BigOperators

private theorem owner_coprime_row_rest
    {n d t j i : ℕ}
    (data : CanonicalOwnerData 5 n d t)
    (hi : i ∈ Finset.Icc 1 5) :
    Nat.Coprime (canonicalOwnerCell data j i)
      (∏ i' ∈ (Finset.Icc 1 5).erase i, canonicalOwnerCell data j i') := by
  classical
  apply Nat.Coprime.prod_right
  intro i' hi'
  apply canonicalOwnerCells_pairwise_coprime data
  intro heq
  have hii' : i = i' := congrArg Prod.snd heq
  subst i'
  exact (Finset.mem_erase.mp hi').1 rfl

private theorem owner_row_eq_owner_mul_rest
    {n d t j i : ℕ}
    (data : CanonicalOwnerData 5 n d t)
    (hi : i ∈ Finset.Icc 1 5) :
    canonicalOwnerRow data j = canonicalOwnerCell data j i *
      (∏ i' ∈ (Finset.Icc 1 5).erase i, canonicalOwnerCell data j i') := by
  classical
  rw [← canonicalOwner_row_cell_product data]
  symm
  exact Finset.mul_prod_erase (Finset.Icc 1 5)
    (fun i' => canonicalOwnerCell data j i') hi

private theorem owner_column_eq_owner_mul_rest
    {n d t j i : ℕ}
    (data : CanonicalOwnerData 5 n d t)
    (hj : j ∈ Finset.Icc 1 5) :
    canonicalOwnerColumn data i = canonicalOwnerCell data j i *
      (∏ j' ∈ (Finset.Icc 1 5).erase j, canonicalOwnerCell data j' i) := by
  classical
  rw [← canonicalOwner_column_cell_product data]
  symm
  exact Finset.mul_prod_erase (Finset.Icc 1 5)
    (fun j' => canonicalOwnerCell data j' i) hj

/-- Repeated prime-power mass in the two forced anti-diagonal owners is
uniformly bounded.  The final `180` bound is for their complete product. -/
theorem k5_G12_antidiagonal_quotient_unitary_overlap_dvd_180
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
    let KA := K / A
    let KB := K / B
    let J := K / (A * B)
    Nat.gcd A KA ∣ 20 ∧ Nat.gcd B KB ∣ 180 ∧
      Nat.gcd (A * B) J ∣ 180 := by
  classical
  dsimp only
  let P := canonicalOwnerCell data 4 1
  let Q := canonicalOwnerCell data 2 3
  let A := canonicalOwnerCell data 3 2
  let B := canonicalOwnerCell data 1 4
  let R := (n + 4) / P
  let C := (n + d + 1) / P
  let K := (R + C) / (P * Q)
  let KA := K / A
  let KB := K / B
  let J := K / (A * B)
  let RA := ∏ i' ∈ (Finset.Icc 1 5).erase 2,
    canonicalOwnerCell data 3 i'
  let CA := ∏ j' ∈ (Finset.Icc 1 5).erase 3,
    canonicalOwnerCell data j' 2
  let RB := ∏ i' ∈ (Finset.Icc 1 5).erase 4,
    canonicalOwnerCell data 1 i'
  let CB := ∏ j' ∈ (Finset.Icc 1 5).erase 1,
    canonicalOwnerCell data j' 4
  have hforced := k5_G12_anti_diagonal_owner_product_dvd_complement_quotient
    data hfour heq hprofile
  have hABdvdK : A * B ∣ K := hforced.1
  have htarget : (n + 3) + (n + d + 2) = P ^ 2 * Q * K := by
    simpa [P, Q, A, B, R, C, K] using hforced.2.2
  have hApos : 0 < A := by dsimp [A]; exact canonicalOwnerCell_pos data
  have hBpos : 0 < B := by dsimp [B]; exact canonicalOwnerCell_pos data
  have hABpos : 0 < A * B := Nat.mul_pos hApos hBpos
  have hAdvdK : A ∣ K := (dvd_mul_right A B).trans hABdvdK
  have hBdvdK : B ∣ K := (dvd_mul_left B A).trans (by
    simpa [mul_comm] using hABdvdK)
  have hKeqA : K = A * KA := by
    dsimp [KA]
    exact (Nat.mul_div_cancel' hAdvdK).symm
  have hKeqB : K = B * KB := by
    dsimp [KB]
    exact (Nat.mul_div_cancel' hBdvdK).symm
  have hKeqAB : K = A * B * J := by
    dsimp [J]
    exact (Nat.mul_div_cancel' hABdvdK).symm
  have hKAeq : KA = B * J := by
    apply Nat.mul_left_cancel hApos
    rw [← hKeqA, hKeqAB]
    ring
  have hKBeq : KB = A * J := by
    apply Nat.mul_left_cancel hBpos
    rw [← hKeqB, hKeqAB]
    ring
  rcases hprofile with
    ⟨rfl, hl1, hl2, hl3, hl4, hl5, hu1, hu2, hu3, hu4, hu5⟩

  have hrowProdA : canonicalOwnerRow data 3 = A * RA := by
    simpa [A, RA] using owner_row_eq_owner_mul_rest
      data (j := 3) (i := 2) (by norm_num)
  have hcolProdA : canonicalOwnerColumn data 2 = A * CA := by
    simpa [A, CA] using owner_column_eq_owner_mul_rest
      data (j := 3) (i := 2) (by norm_num)
  have hrowA : n + 3 = 2 * (A * RA) := by
    have hfac := canonical_lower_term_factorization data (j := 3)
    rw [hl3, hrowProdA] at hfac
    exact hfac
  have hcolA : n + d + 2 = 2 * (A * CA) := by
    have hfac := canonical_upper_term_factorization data hfour (i := 2)
    rw [hu2, hcolProdA] at hfac
    simpa [upperTermAfterFour] using hfac
  have hnormA : 2 * (RA + CA) = P ^ 2 * Q * KA := by
    apply Nat.mul_left_cancel hApos
    calc
      A * (2 * (RA + CA)) = (n + 3) + (n + d + 2) := by
        rw [hrowA, hcolA]
        ring
      _ = P ^ 2 * Q * K := htarget
      _ = A * (P ^ 2 * Q * KA) := by rw [hKeqA]; ring
  have hcopARA : Nat.Coprime A RA := by
    simpa [A, RA] using owner_coprime_row_rest
      data (j := 3) (i := 2) (by norm_num)
  have hsqA : ((A : ℤ) ^ 2) ∣ k5OwnerSquareDefect n d 3 2 := by
    simpa [A] using canonicalOwnerCell_sq_dvd_k5OwnerSquareDefect
      data (by norm_num) (by norm_num) hfour heq
  have hc2 : localBlockCoefficient 5 2 = -6 := by
    rw [localBlockCoefficient_eq_sign_mul_nat (by norm_num)]
    norm_num [localBlockCoefficientNat]
  have hc3 : localBlockCoefficient 5 3 = 4 := by
    rw [localBlockCoefficient_eq_sign_mul_nat (by norm_num)]
    norm_num [localBlockCoefficientNat]
  have hrowAZ : ((n + 3 : ℕ) : ℤ) =
      (2 : ℤ) * ((A : ℤ) * (RA : ℤ)) := by
    exact_mod_cast hrowA
  have hcolAZ : ((n + d + 2 : ℕ) : ℤ) =
      (2 : ℤ) * ((A : ℤ) * (CA : ℤ)) := by
    exact_mod_cast hcolA
  have hdefA : k5OwnerSquareDefect n d 3 2 =
      (A : ℤ) * (-4 * (3 * (CA : ℤ) + 8 * (RA : ℤ))) := by
    simp only [k5OwnerSquareDefect, hc2, hc3]
    rw [hrowAZ, hcolAZ]
    ring
  have hAdivZ : (A : ℤ) ∣
      -4 * (3 * (CA : ℤ) + 8 * (RA : ℤ)) := by
    rw [hdefA] at hsqA
    refine (mul_dvd_mul_iff_left (a := (A : ℤ))
      (by exact_mod_cast hApos.ne')).mp ?_
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hsqA
  have hAdiv : A ∣ 4 * (3 * CA + 8 * RA) := by
    have habs := Int.natAbs_dvd_natAbs.mpr hAdivZ
    simpa [Int.natAbs_mul] using habs
  let gA := Nat.gcd A KA
  have hgAtan : gA ∣ 4 * (3 * CA + 8 * RA) :=
    (Nat.gcd_dvd_left A KA).trans hAdiv
  have hgAmain : gA ∣ 6 * (P ^ 2 * Q * KA) :=
    by
      dsimp [gA]
      convert dvd_mul_of_dvd_right
        (Nat.gcd_dvd_right A KA) (6 * (P ^ 2 * Q)) using 1 <;> ring
  have htanA : 4 * (3 * CA + 8 * RA) =
      6 * (P ^ 2 * Q * KA) + 20 * RA := by
    rw [← hnormA]
    ring
  rw [htanA] at hgAtan
  have hgA20RA : gA ∣ 20 * RA :=
    (Nat.dvd_add_iff_right hgAmain).mpr hgAtan
  have hcopgARA : Nat.Coprime gA RA :=
    hcopARA.of_dvd_left (Nat.gcd_dvd_left A KA)
  have hgA20 : gA ∣ 20 := hcopgARA.dvd_of_dvd_mul_right hgA20RA

  have hrowProdB : canonicalOwnerRow data 1 = B * RB := by
    simpa [B, RB] using owner_row_eq_owner_mul_rest
      data (j := 1) (i := 4) (by norm_num)
  have hcolProdB : canonicalOwnerColumn data 4 = B * CB := by
    simpa [B, CB] using owner_column_eq_owner_mul_rest
      data (j := 1) (i := 4) (by norm_num)
  have hrowB : n + 1 = 2 * (B * RB) := by
    have hfac := canonical_lower_term_factorization data (j := 1)
    rw [hl1, hrowProdB] at hfac
    exact hfac
  have hcolB : n + d + 4 = 8 * (B * CB) := by
    have hfac := canonical_upper_term_factorization data hfour (i := 4)
    rw [hu4, hcolProdB] at hfac
    simpa [upperTermAfterFour] using congrArg (fun z : ℕ => 4 * z) hfac
  have htargetB : (n + 1) + (n + d + 4) = P ^ 2 * Q * K := by
    omega
  have hnormB : 2 * (RB + 4 * CB) = P ^ 2 * Q * KB := by
    apply Nat.mul_left_cancel hBpos
    calc
      B * (2 * (RB + 4 * CB)) = (n + 1) + (n + d + 4) := by
        rw [hrowB, hcolB]
        ring
      _ = P ^ 2 * Q * K := htargetB
      _ = B * (P ^ 2 * Q * KB) := by rw [hKeqB]; ring
  have hcopBRB : Nat.Coprime B RB := by
    simpa [B, RB] using owner_coprime_row_rest
      data (j := 1) (i := 4) (by norm_num)
  have hsqB : ((B : ℤ) ^ 2) ∣ k5OwnerSquareDefect n d 1 4 := by
    simpa [B] using canonicalOwnerCell_sq_dvd_k5OwnerSquareDefect
      data (by norm_num) (by norm_num) hfour heq
  have hc1 : localBlockCoefficient 5 1 = 24 := by
    rw [localBlockCoefficient_eq_sign_mul_nat (by norm_num)]
    norm_num [localBlockCoefficientNat]
  have hc4 : localBlockCoefficient 5 4 = -6 := by
    rw [localBlockCoefficient_eq_sign_mul_nat (by norm_num)]
    norm_num [localBlockCoefficientNat]
  have hrowBZ : ((n + 1 : ℕ) : ℤ) =
      (2 : ℤ) * ((B : ℤ) * (RB : ℤ)) := by
    exact_mod_cast hrowB
  have hcolBZ : ((n + d + 4 : ℕ) : ℤ) =
      (8 : ℤ) * ((B : ℤ) * (CB : ℤ)) := by
    exact_mod_cast hcolB
  have hdefB : k5OwnerSquareDefect n d 1 4 =
      (B : ℤ) * (-48 * ((CB : ℤ) + 4 * (RB : ℤ))) := by
    simp only [k5OwnerSquareDefect, hc1, hc4]
    rw [hrowBZ, hcolBZ]
    ring
  have hBdivZ : (B : ℤ) ∣
      -48 * ((CB : ℤ) + 4 * (RB : ℤ)) := by
    rw [hdefB] at hsqB
    refine (mul_dvd_mul_iff_left (a := (B : ℤ))
      (by exact_mod_cast hBpos.ne')).mp ?_
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hsqB
  have hBdiv : B ∣ 48 * (CB + 4 * RB) := by
    have habs := Int.natAbs_dvd_natAbs.mpr hBdivZ
    simpa [Int.natAbs_mul] using habs
  let gB := Nat.gcd B KB
  have hgBtan : gB ∣ 48 * (CB + 4 * RB) :=
    (Nat.gcd_dvd_left B KB).trans hBdiv
  have hgBmain : gB ∣ 6 * (P ^ 2 * Q * KB) :=
    by
      dsimp [gB]
      convert dvd_mul_of_dvd_right
        (Nat.gcd_dvd_right B KB) (6 * (P ^ 2 * Q)) using 1 <;> ring
  have htanB : 48 * (CB + 4 * RB) =
      6 * (P ^ 2 * Q * KB) + 180 * RB := by
    rw [← hnormB]
    ring
  rw [htanB] at hgBtan
  have hgB180RB : gB ∣ 180 * RB :=
    (Nat.dvd_add_iff_right hgBmain).mpr hgBtan
  have hcopgBRB : Nat.Coprime gB RB :=
    hcopBRB.of_dvd_left (Nat.gcd_dvd_left B KB)
  have hgB180 : gB ∣ 180 := hcopgBRB.dvd_of_dvd_mul_right hgB180RB

  have hJdvdKA : J ∣ KA := by refine ⟨B, by rw [hKAeq]; ring⟩
  have hJdvdKB : J ∣ KB := by refine ⟨A, by rw [hKBeq]; ring⟩
  let gAJ := Nat.gcd A J
  let gBJ := Nat.gcd B J
  have hgAJgA : gAJ ∣ gA := by
    exact Nat.dvd_gcd (Nat.gcd_dvd_left A J)
      ((Nat.gcd_dvd_right A J).trans hJdvdKA)
  have hgBJgB : gBJ ∣ gB := by
    exact Nat.dvd_gcd (Nat.gcd_dvd_left B J)
      ((Nat.gcd_dvd_right B J).trans hJdvdKB)
  have hgAJ180 : gAJ ∣ 180 := (hgAJgA.trans hgA20).trans (by norm_num)
  have hgBJ180 : gBJ ∣ 180 := hgBJgB.trans hgB180
  have hcopAB : Nat.Coprime A B := by
    dsimp [A, B]
    exact canonicalOwnerCells_pairwise_coprime data (by norm_num)
  have hcopg : Nat.Coprime gAJ gBJ :=
    (hcopAB.of_dvd_left (Nat.gcd_dvd_left A J)).of_dvd_right
      (Nat.gcd_dvd_left B J)
  have hgprod : gAJ * gBJ ∣ 180 :=
    hcopg.mul_dvd_of_dvd_of_dvd hgAJ180 hgBJ180
  have hsplit : Nat.gcd (A * B) J ∣ gAJ * gBJ := by
    dsimp [gAJ, gBJ]
    have h := gcd_mul_dvd_mul_gcd J A B
    calc
      Nat.gcd (A * B) J = Nat.gcd J (A * B) := Nat.gcd_comm _ _
      _ ∣ Nat.gcd J A * Nat.gcd J B := h
      _ = Nat.gcd A J * Nat.gcd B J := by
        rw [Nat.gcd_comm J A, Nat.gcd_comm J B]
  exact ⟨hgA20, hgB180, hsplit.trans hgprod⟩

/-- The presently combined linear constraints still allow arbitrarily large
exact CRT models.  This is a synthetic obstruction theorem: it does not
claim that these numbers arise from canonical owner data or satisfy the
five-block equation.  It shows that the exact complement row/column
equations, both forced anti-diagonal quotient overlaps, and the diagonal
unitary-overlap condition alone cannot yield a finite tail bound.

Here `M=d`, so `gcd(M,d/M)=1`; moreover `M` is coprime to the remaining
anti-diagonal quotient `J`.  Thus even adding the strongest possible CRT
separation between those two free cofactors leaves an unbounded family. -/
theorem k5_G12_linear_aggregate_has_unbounded_CRT_models (s : ℕ) :
    let v := s + 1
    let P := 5
    let Q := 3
    let A := 7
    let B := 11
    let J := 4 + 77 * (81912 * v)
    let K := A * B * J
    let d := 3473 + 94608360 * v
    let n := 9811 + 18164805120 * v
    let M := d
    let R := 1963 + 3632961024 * v
    let C := 2657 + 3651882696 * v
    let S := 3271 + 6054935040 * v
    let D := 4429 + 6086471160 * v
    let RA := 701 + 1297486080 * v
    let CA := 949 + 1304243820 * v
    let RB := 446 + 825672960 * v
    let CB := 151 + 207493335 * v
    s ≤ d ∧ d < n ∧ 40 * d < 13 * n ∧
      (K = A * B * J ∧ Nat.gcd (A * B) (K / (A * B)) = 1) ∧
      (M ∣ d ∧ Nat.gcd M (d / M) = 1 ∧ Nat.gcd M J = 1) ∧
      (n + 4 = P * R ∧ n + d + 1 = P * C ∧ R + C = P * Q * K) ∧
      (n + 2 = Q * S ∧ n + d + 3 = Q * D ∧ S + D = P ^ 2 * K) ∧
      (n + 3 = 2 * (A * RA) ∧ n + d + 2 = 2 * (A * CA)) ∧
      (n + 1 = 2 * (B * RB) ∧ n + d + 4 = 8 * (B * CB)) ∧
      A ∣ (d - 1) / 2 ∧ B ∣ (d + 3) / 2 := by
  dsimp only
  let J := 4 + 77 * (81912 * (s + 1))
  let d := 3473 + 94608360 * (s + 1)
  have h77J : Nat.Coprime 77 J := by
    dsimp [J]
    rw [Nat.coprime_add_mul_left_right]
    norm_num
  have hquot : (7 * 11 * J) / (7 * 11) = J := by
    rw [show 7 * 11 * J = (7 * 11) * J by ring]
    exact Nat.mul_div_cancel_left J (by norm_num)
  have h3413J : Nat.Coprime 3413 J := by
    have hbase : Nat.Coprime 3413
        (4 + 3413 * (1848 * (s + 1))) := by
      rw [Nat.coprime_add_mul_left_right]
      norm_num
    have hjeq : J = 4 + 3413 * (1848 * (s + 1)) := by
      dsimp [J]
      ring
    rw [hjeq]
    exact hbase
  have hdJ : Nat.Coprime d J := by
    have hrel : d = 15 * J + 3413 := by
      dsimp [d, J]
      ring
    rw [hrel]
    exact (Nat.coprime_mul_right_add_left 3413 J 15).mpr h3413J
  have hdpos : 0 < d := by dsimp [d]; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [d]
    omega
  · dsimp [d]
    omega
  · dsimp [d]
    omega
  · constructor
    · rfl
    · rw [hquot]
      exact h77J.gcd_eq_one
  · refine ⟨dvd_refl d, ?_, hdJ.gcd_eq_one⟩
    rw [Nat.div_self (by omega : 0 < 3473 + 94608360 * (s + 1))]
    norm_num
  · constructor
    · ring
    constructor <;> ring
  · constructor
    · ring
    constructor <;> ring
  · constructor <;> ring
  · constructor <;> ring
  · refine ⟨248 + 6757740 * (s + 1), ?_⟩
    rw [show
      (3473 + 94608360 * (s + 1) - 1) =
        2 * (7 * (248 + 6757740 * (s + 1))) by omega]
    simp
  · refine ⟨158 + 4300380 * (s + 1), ?_⟩
    rw [show
      (3473 + 94608360 * (s + 1) + 3) =
        2 * (11 * (158 + 4300380 * (s + 1))) by ring]
    simp

#print axioms k5_G12_antidiagonal_quotient_unitary_overlap_dvd_180
#print axioms k5_G12_linear_aggregate_has_unbounded_CRT_models

end Erdos686Variant
end Erdos686
