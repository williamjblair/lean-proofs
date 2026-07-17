/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686K5G12FixedCofactorWindow

/-!
# Erdős 686, k=5: primitive half-sum/half-difference complement

In the exceptional `G=12` profile, the two complementary cofactors `R,C`
are coprime odd integers.  Their sum is the fixed-cofactor expression
`P*Q*A*B*J`, while their difference is the exterior gap quotient
`(d-3)/P`.  Consequently the sum and difference have gcd exactly two, so
their halves are coprime.

This is an exact primitive reduction of the six-value cofactor branch.  It
does not by itself exclude any of the six values of `J`.
-/

namespace Erdos686
namespace Erdos686Variant

/-- Exact primitive split of the exceptional complement.

Writing

`X = P*Q*A*B`, `p = (d-3)/P`,

the theorem records

`X*J = R+C`, `p=C-R`, `gcd(X*J,p)=2`,

and the corresponding coprime half-sum/half-difference parametrization.
-/
theorem k5_G12_primitive_complement_split
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
    let X := P * Q * (A * B)
    let p := (d - 3) / P
    R + C = X * J ∧
      C = R + p ∧
      Nat.gcd (X * J) p = 2 ∧
      Nat.Coprime ((X * J) / 2) (p / 2) ∧
      2 * R + p = X * J ∧
      2 * C = X * J + p := by
  dsimp only
  let P := canonicalOwnerCell data 4 1
  let Q := canonicalOwnerCell data 2 3
  let A := canonicalOwnerCell data 3 2
  let B := canonicalOwnerCell data 1 4
  let R := (n + 4) / P
  let C := (n + d + 1) / P
  let K := (R + C) / (P * Q)
  let J := K / (A * B)
  let X := P * Q * (A * B)
  let p := (d - 3) / P
  have hfixed := k5_G12_fixed_cofactor_narrow_window
    data hfour hd heq hprofile htail hdlt hcells
  have hsum : R + C = X * J := by
    simpa [P, Q, A, B, R, C, K, J, X] using hfixed.2.1
  have hcomp := k5_G12_zero_crossing_product_dvd_complement_sum
    data hfour heq hprofile htail hdlt hcells
  have hrow : n + 4 = P * R := by
    simpa [P, Q, R, C] using hcomp.1
  have hcolumn : n + d + 1 = P * C := by
    simpa [P, Q, R, C] using hcomp.2.1
  have hcopRC : Nat.Coprime R C := by
    simpa [P, Q, R, C] using hcomp.2.2.2.2.1
  have hRltC : R < C := by
    simpa [P, Q, R, C] using hcomp.2.2.2.2.2.2.2.1
  have hPpos : 0 < P := by
    dsimp [P]
    exact canonicalOwnerCell_pos data
  have hPd : P ∣ d - 3 := by
    dsimp [P]
    simpa using canonicalOwnerCell_dvd_shiftedDifference data hd
      (by norm_num) (by norm_num) hfour
  have hPp : d - 3 = P * p := by
    dsimp [p]
    exact (Nat.mul_div_cancel' hPd).symm
  have hCeq : C = R + p := by
    apply Nat.mul_left_cancel hPpos
    rw [← hcolumn, Nat.mul_add, ← hrow, ← hPp]
    omega
  have htwoN1 : 2 ∣ n + 1 := by
    have hfac := canonical_lower_term_factorization data (j := 1)
    rw [hprofile.2.1] at hfac
    exact ⟨canonicalOwnerRow data 1, hfac⟩
  have hnOdd : Odd n := by
    rw [Nat.odd_iff]
    have hm := Nat.dvd_iff_mod_eq_zero.mp htwoN1
    omega
  have hn4Odd : Odd (n + 4) := by
    rw [Nat.odd_iff] at hnOdd ⊢
    omega
  have hRodd : Odd R := by
    have hprodOdd : Odd (P * R) := by rwa [← hrow]
    exact (Nat.odd_mul.mp hprodOdd).2
  have hpEven : Even p := by
    simpa [P, Q, A, B, R, C, K, J, p] using
      (k5_G12_fixed_cofactor_exterior_two_adic_constraint
        data hfour hd heq hprofile htail hdlt hcells).2.2.2.1
  have hCodd : Odd C := by
    rw [hCeq]
    exact hRodd.add_even hpEven
  have hsumEven : Even (R + C) := hRodd.add_odd hCodd
  have htwoSum : 2 ∣ R + C := even_iff_two_dvd.mp hsumEven
  have htwoP : 2 ∣ p := even_iff_two_dvd.mp hpEven
  let g := Nat.gcd (R + C) p
  have hgsum : g ∣ R + C := Nat.gcd_dvd_left _ _
  have hgp : g ∣ p := Nat.gcd_dvd_right _ _
  have hgtwoR : g ∣ 2 * R := by
    have hsub := Nat.dvd_sub hgsum hgp
    rw [hCeq] at hsub
    have heq : R + (R + p) - p = 2 * R := by omega
    rwa [heq] at hsub
  have hcopSumR : Nat.Coprime (R + C) R := by
    simpa using hcopRC.symm
  have hcopgR : Nat.Coprime g R :=
    hcopSumR.of_dvd_left hgsum
  have hgTwo : g ∣ 2 := hcopgR.dvd_of_dvd_mul_right hgtwoR
  have htwoG : 2 ∣ g := Nat.dvd_gcd htwoSum htwoP
  have hgcd : Nat.gcd (R + C) p = 2 := by
    exact Nat.dvd_antisymm hgTwo htwoG
  have hgcdX : Nat.gcd (X * J) p = 2 := by
    rw [← hsum]
    exact hgcd
  have hcopHalves : Nat.Coprime ((X * J) / 2) (p / 2) := by
    have hgpos : 0 < Nat.gcd (X * J) p := by rw [hgcdX]; norm_num
    simpa [hgcdX] using Nat.coprime_div_gcd_div_gcd hgpos
  have hRsplit : 2 * R + p = X * J := by
    rw [← hsum, hCeq]
    omega
  have hCsplit : 2 * C = X * J + p := by
    rw [← hsum, hCeq]
    omega
  exact ⟨hsum, hCeq, hgcdX, hcopHalves, hRsplit, hCsplit⟩

#print axioms k5_G12_primitive_complement_split

end Erdos686Variant
end Erdos686
