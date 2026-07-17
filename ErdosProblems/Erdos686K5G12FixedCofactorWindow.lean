/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686K5G12ResultantGCDClosure

/-!
# Erdős 686, k=5: a fixed-cofactor window in the G=12 branch

The centered resultant bounds the last quotient `J` by the fixed integer
`23040`.  Combining that genuinely nonlinear input with the exact exceptional
complement sum gives more than a bare divisor statement: the product of the
four anti-diagonal owners lies in a fixed narrow multiplicative window around
the fully owned row complement.  In particular the row term itself is bounded
by a fixed multiple of those four owners.

This is a strict reduction of the live `G=12` branch, but it is not its
closure: the four anti-diagonal owners remain unbounded divisors of four
different gap translates.
-/

namespace Erdos686
namespace Erdos686Variant

private theorem even_right_of_odd_left_even_mul
    {a b : ℕ} (ha : Odd a) (hab : Even (a * b)) : Even b := by
  rcases Nat.even_mul.mp hab with haEven | hbEven
  · rcases ha with ⟨x, hx⟩
    rcases haEven with ⟨y, hy⟩
    omega
  · exact hbEven

private theorem divisor_512_dvd_four_of_not_eight
    {g : ℕ} (hg : g ∣ 512) (h8 : ¬8 ∣ g) : g ∣ 4 := by
  have hgpow : g ∣ 2 ^ 9 := by norm_num at hg ⊢; exact hg
  obtain ⟨k, hk9, rfl⟩ :=
    (Nat.dvd_prime_pow (by norm_num : Nat.Prime 2)).mp hgpow
  have hk3 : ¬3 ≤ k := by
    intro hk
    apply h8
    change 2 ^ 3 ∣ 2 ^ k
    exact Nat.pow_dvd_pow 2 hk
  have hk2 : k ≤ 2 := by omega
  change 2 ^ k ∣ 2 ^ 2
  exact Nat.pow_dvd_pow 2 hk2

/-- Exact fixed-cofactor factorization and its narrow complement window.

Writing `X=P*Q*A*B`, the theorem proves

`R+C=X*J`, `J | 23040`, and `4R < 2XJ < 5R`.

It also records that the complete factor `XJ` is coprime to both complementary
terms and converts the fixed bound on `J` into the useful row bound
`n+4 < 11520 P^2 Q A B`.
-/
theorem k5_G12_fixed_cofactor_narrow_window
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
    K = A * B * J ∧
      R + C = (P * Q * (A * B)) * J ∧
      J ∣ 23040 ∧
      Nat.Coprime (R * C) ((P * Q * (A * B)) * J) ∧
      4 * R < 2 * ((P * Q * (A * B)) * J) ∧
      2 * ((P * Q * (A * B)) * J) < 5 * R ∧
      n + 4 < 11520 * (P ^ 2 * Q * (A * B)) := by
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
  have hforced := k5_G12_anti_diagonal_owner_product_dvd_complement_quotient
    data hfour heq hprofile
  have hABdvdK : A * B ∣ K := hforced.1
  have hKeq : K = A * B * J := by
    dsimp [J]
    exact (Nat.mul_div_cancel' hABdvdK).symm
  have hprimitive := k5_G12_exceptional_complement_quotient_gcd_Q_dvd_five
    data hfour heq hprofile
  have hsum0 : R + C = P * Q * K := hprimitive.1
  have hsum : R + C = X * J := by
    rw [hsum0, hKeq]
    dsimp [X]
    ring
  have hJdvd : J ∣ 23040 := by
    dsimp [J, K, R, C, P, Q, A, B]
    exact k5_G12_remaining_complement_quotient_dvd_23040
      data hfour hd heq hprofile htail hdlt hcells
  have hJle : J ≤ 23040 := Nat.le_of_dvd (by norm_num) hJdvd
  have hcomp := k5_G12_zero_crossing_product_dvd_complement_sum
    data hfour heq hprofile htail hdlt hcells
  have hrow : n + 4 = P * R := hcomp.1
  have hcopRC : Nat.Coprime R C := hcomp.2.2.2.2.1
  have hRltC : R < C := hcomp.2.2.2.2.2.2.2.1
  have htwoC : 2 * C < 3 * R := hcomp.2.2.2.2.2.2.2.2.2.1
  have hsumR : Nat.Coprime (R + C) R := by simpa using hcopRC.symm
  have hsumC : Nat.Coprime (R + C) C := by simpa using hcopRC
  have hRsum : Nat.Coprime R (R + C) := hsumR.symm
  have hCsum : Nat.Coprime C (R + C) := hsumC.symm
  have hcopProdSum : Nat.Coprime (R * C) (R + C) :=
    hRsum.mul_left hCsum
  have hcopProd : Nat.Coprime (R * C) (X * J) := by
    rwa [hsum] at hcopProdSum
  have hlower : 4 * R < 2 * (X * J) := by
    rw [← hsum]
    omega
  have hupper : 2 * (X * J) < 5 * R := by
    rw [← hsum]
    omega
  have hXJle : X * J ≤ X * 23040 := Nat.mul_le_mul_left X hJle
  have hRbound : R < 11520 * X := by
    have : 2 * R < X * J := by
      rw [← hsum]
      omega
    have : 2 * R < X * 23040 := this.trans_le hXJle
    omega
  have hPpos : 0 < P := by
    dsimp [P]
    exact canonicalOwnerCell_pos data
  have hnBound : n + 4 < 11520 * (P ^ 2 * Q * (A * B)) := by
    rw [hrow]
    have hmul := (Nat.mul_lt_mul_left hPpos).mpr hRbound
    dsimp [X] at hmul
    convert hmul using 1
    ring
  exact ⟨hKeq, by simpa [X] using hsum, hJdvd,
    by simpa [X] using hcopProd, by simpa [X] using hlower,
    by simpa [X] using hupper, hnBound⟩

/-- The two exterior gap quotients have exact two-adic behavior in the
high-two part of the fixed-cofactor branch.  Both quotients are always even;
if `4 | J`, then each has gcd exactly `2` with `J`, hence neither can be
divisible by four.  This excludes all synthetic fixed-cofactor models in
which the same extra factor of two is placed in either exterior quotient. -/
theorem k5_G12_fixed_cofactor_exterior_two_adic_constraint
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
    let p := (d - 3) / P
    let q := (d + 1) / Q
    Odd d ∧ Odd P ∧ Odd Q ∧ Even p ∧ Even q ∧
      (4 ∣ J → Nat.gcd J p = 2 ∧ Nat.gcd J q = 2 ∧
        ¬4 ∣ p ∧ ¬4 ∣ q ∧ d % 4 = 1 ∧ n % 4 = 3) := by
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
  have hnEvenSucc : 2 ∣ n + 1 := by
    have hfac := canonical_lower_term_factorization data (j := 1)
    rw [hprofile.2.1] at hfac
    exact ⟨canonicalOwnerRow data 1, hfac⟩
  have hnMod : n % 2 = 1 := by
    have hs := Nat.dvd_iff_mod_eq_zero.mp hnEvenSucc
    omega
  have hnOdd : Odd n := Nat.odd_iff.mpr hnMod
  have hsumEven : 2 ∣ n + d + 4 := by
    exact dvd_trans (by norm_num : 2 ∣ 4) (by simpa [hprofile.1] using hfour)
  have hdMod : d % 2 = 1 := by
    have hs := Nat.dvd_iff_mod_eq_zero.mp hsumEven
    omega
  have hdOdd : Odd d := Nat.odd_iff.mpr hdMod
  have hn4Odd : Odd (n + 4) := by
    rw [Nat.odd_iff]
    omega
  have hn2Odd : Odd (n + 2) := by
    rw [Nat.odd_iff]
    omega
  have hPdvdLower : P ∣ n + 4 := by
    dsimp [P]
    exact canonicalOwnerCell_dvd_lower data
  have hQdvdLower : Q ∣ n + 2 := by
    dsimp [Q]
    exact canonicalOwnerCell_dvd_lower data
  have hPodd : Odd P := Odd.of_dvd_nat hn4Odd hPdvdLower
  have hQodd : Odd Q := Odd.of_dvd_nat hn2Odd hQdvdLower
  have hPd : P ∣ d - 3 := by
    dsimp [P]
    simpa using canonicalOwnerCell_dvd_shiftedDifference data hd
      (by norm_num) (by norm_num) hfour
  have hQd : Q ∣ d + 1 := by
    dsimp [Q]
    simpa using canonicalOwnerCell_dvd_shiftedDifference data hd
      (by norm_num) (by norm_num) hfour
  have hPfactor : d - 3 = P * p := by
    dsimp [p]
    exact (Nat.mul_div_cancel' hPd).symm
  have hQfactor : d + 1 = Q * q := by
    dsimp [q]
    exact (Nat.mul_div_cancel' hQd).symm
  have hd3Even : Even (d - 3) := by
    rw [even_iff_two_dvd, Nat.dvd_iff_mod_eq_zero]
    omega
  have hd1Even : Even (d + 1) := by
    rw [even_iff_two_dvd, Nat.dvd_iff_mod_eq_zero]
    omega
  have hpEven : Even p := by
    apply even_right_of_odd_left_even_mul hPodd
    rwa [← hPfactor]
  have hqEven : Even q := by
    apply even_right_of_odd_left_even_mul hQodd
    rwa [← hQfactor]
  refine ⟨hdOdd, hPodd, hQodd, hpEven, hqEven, ?_⟩
  intro hfourJ
  have hg := k5_G12_centered_resultant_quotient_gcd_bounds
    data hfour hd heq hprofile htail hdlt hcells
  have hgpDvd : Nat.gcd J p ∣ 2 := by simpa [J, K, R, C, P, Q, A, B, p, q] using hg.1
  have hgqDvd : Nat.gcd J q ∣ 2 := by
    simpa [J, K, R, C, P, Q, A, B, p, q] using hg.2.2.1
  have htwoP : 2 ∣ p := even_iff_two_dvd.mp hpEven
  have htwoQ : 2 ∣ q := even_iff_two_dvd.mp hqEven
  have htwoJ : 2 ∣ J := (by norm_num : 2 ∣ 4).trans hfourJ
  have htwoGcdP : 2 ∣ Nat.gcd J p := Nat.dvd_gcd htwoJ htwoP
  have htwoGcdQ : 2 ∣ Nat.gcd J q := Nat.dvd_gcd htwoJ htwoQ
  have hgpEq : Nat.gcd J p = 2 := Nat.dvd_antisymm hgpDvd htwoGcdP
  have hgqEq : Nat.gcd J q = 2 := Nat.dvd_antisymm hgqDvd htwoGcdQ
  have hnotFourP : ¬4 ∣ p := by
    intro hfourP
    have : 4 ∣ Nat.gcd J p := Nat.dvd_gcd hfourJ hfourP
    rw [hgpEq] at this
    norm_num at this
  have hnotFourQ : ¬4 ∣ q := by
    intro hfourQ
    have : 4 ∣ Nat.gcd J q := Nat.dvd_gcd hfourJ hfourQ
    rw [hgqEq] at this
    norm_num at this
  have hpModFour : p % 4 = 2 := by
    have hpModTwo : p % 2 = 0 := Nat.even_iff.mp hpEven
    have hpNotZero : p % 4 ≠ 0 := by
      intro hz
      exact hnotFourP (Nat.dvd_of_mod_eq_zero hz)
    have hcompat := Nat.mod_mod_of_dvd p (by norm_num : 2 ∣ 4)
    have hlt := Nat.mod_lt p (by norm_num : 0 < 4)
    omega
  have hPModFour : P % 4 = 1 ∨ P % 4 = 3 := by
    have hPModTwo : P % 2 = 1 := Nat.odd_iff.mp hPodd
    have hcompat := Nat.mod_mod_of_dvd P (by norm_num : 2 ∣ 4)
    have hlt := Nat.mod_lt P (by norm_num : 0 < 4)
    omega
  have hdSubMod : (d - 3) % 4 = 2 := by
    rw [hPfactor, Nat.mul_mod, hpModFour]
    rcases hPModFour with hP1 | hP3
    · rw [hP1]
    · rw [hP3]
  have hdModFour : d % 4 = 1 := by
    rw [← Nat.sub_add_cancel (by omega : 3 ≤ d), Nat.add_mod, hdSubMod]
  have hnModFour : n % 4 = 3 := by
    have hsumMod : (n + d + 4) % 4 = 0 := by
      exact Nat.dvd_iff_mod_eq_zero.mp (by simpa [hprofile.1] using hfour)
    rw [Nat.add_mod, Nat.add_mod] at hsumMod
    have hnlt := Nat.mod_lt n (by norm_num : 0 < 4)
    omega
  exact ⟨hgpEq, hgqEq, hnotFourP, hnotFourQ, hdModFour, hnModFour⟩

/-- The fixed cofactor never contains eight.  The only nontrivial case is
`4 | J`.  There the exterior quotient constraint gives `d = 1 (mod 4)` and
`n = 3 (mod 4)`.  The exact row-one/column-four equation then shows that the
row complement has exactly one factor of two while the disjoint column
complement is odd.  Its left side consequently has exact two-adic valuation
two, excluding `8 | J`. -/
theorem k5_G12_fixed_cofactor_not_eight
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
    ¬8 ∣ J := by
  dsimp only
  let P := canonicalOwnerCell data 4 1
  let Q := canonicalOwnerCell data 2 3
  let A := canonicalOwnerCell data 3 2
  let B := canonicalOwnerCell data 1 4
  let R := (n + 4) / P
  let C := (n + d + 1) / P
  let K := (R + C) / (P * Q)
  let J := K / (A * B)
  by_cases h4J : 4 ∣ J
  · have htwo := k5_G12_fixed_cofactor_exterior_two_adic_constraint
      data hfour hd heq hprofile htail hdlt hcells
    have hPodd : Odd P := by simpa [P, Q, A, B, R, C, K, J] using htwo.2.1
    have hQodd : Odd Q := by simpa [P, Q, A, B, R, C, K, J] using htwo.2.2.1
    have htwoHigh := htwo.2.2.2.2.2 h4J
    have hd4 : d % 4 = 1 := by
      simpa [P, Q, A, B, R, C, K, J] using htwoHigh.2.2.2.2.1
    have hn4 : n % 4 = 3 := by
      simpa [P, Q, A, B, R, C, K, J] using htwoHigh.2.2.2.2.2
    let E11 := canonicalOwnerCell data 1 1
    let E12 := canonicalOwnerCell data 1 2
    let E13 := canonicalOwnerCell data 1 3
    let E15 := canonicalOwnerCell data 1 5
    let RB := E11 * E12 * E13 * E15
    let CB := canonicalOwnerCell data 2 4 * canonicalOwnerCell data 3 4 *
      canonicalOwnerCell data 4 4 * canonicalOwnerCell data 5 4
    have hforced := k5_G12_anti_diagonal_owner_product_dvd_complement_quotient
      data hfour heq hprofile
    have hABdvdK : A * B ∣ K := hforced.1
    have hKeq : K = A * B * J := by
      dsimp [J]
      exact (Nat.mul_div_cancel' hABdvdK).symm
    have htarget : (n + 1) + (n + d + 4) = P ^ 2 * Q * K := by
      have ht : (n + 3) + (n + d + 2) = P ^ 2 * Q * K := by
        simpa [P, Q, A, B, R, C, K] using hforced.2.2
      omega
    have hrowProd : canonicalOwnerRow data 1 = B * RB := by
      rw [← canonicalOwner_row_cell_product data]
      norm_num [B, RB, E11, E12, E13, E15, Finset.prod_Icc_succ_top]
      ring
    have hcolProd : canonicalOwnerColumn data 4 = B * CB := by
      rw [← canonicalOwner_column_cell_product data]
      norm_num [B, CB, Finset.prod_Icc_succ_top]
      ring
    have hrow : n + 1 = 2 * (B * RB) := by
      simpa [hprofile.2.1, hrowProd] using
        canonical_lower_term_factorization data (j := 1)
    have hcol : n + d + 4 = 8 * (B * CB) := by
      have hfac := canonical_upper_term_factorization data hfour (i := 4)
      rw [hprofile.2.2.2.2.2.2.2.2.2.1, hcolProd] at hfac
      simpa [upperTermAfterFour, hprofile.1] using hfac
    have hBpos : 0 < B := by dsimp [B]; exact canonicalOwnerCell_pos data
    have hnorm : 2 * (RB + 4 * CB) = P ^ 2 * Q * A * J := by
      apply Nat.mul_left_cancel hBpos
      calc
        B * (2 * (RB + 4 * CB)) = (n + 1) + (n + d + 4) := by
          rw [hrow, hcol]
          ring
        _ = P ^ 2 * Q * K := htarget
        _ = B * (P ^ 2 * Q * A * J) := by rw [hKeq]; ring
    have hrowAfac := canonical_lower_term_factorization data (j := 3)
    rw [hprofile.2.2.2.1] at hrowAfac
    have hAdvdRow : A ∣ canonicalOwnerRow data 3 := by
      rw [← canonicalOwner_row_cell_product data]
      refine Finset.dvd_prod_of_mem (fun i => canonicalOwnerCell data 3 i) ?_
      norm_num
    have htwoAdvd : 2 * A ∣ n + 3 := by
      obtain ⟨w, hw⟩ := hAdvdRow
      refine ⟨w, ?_⟩
      rw [hrowAfac, hw]
      ring
    have hAodd : Odd A := by
      rcases Nat.even_or_odd A with hAeven | hAodd
      · have hfourA : 4 ∣ 2 * A := by
          obtain ⟨z, hz⟩ := hAeven
          refine ⟨z, ?_⟩
          rw [hz]
          ring
        have hfourTerm : 4 ∣ n + 3 := hfourA.trans htwoAdvd
        have hm := Nat.dvd_iff_mod_eq_zero.mp hfourTerm
        rw [Nat.add_mod, hn4] at hm
        norm_num at hm
      · exact hAodd
    have hoddCoeff : Odd (P ^ 2 * Q * A) := by
      rw [Nat.odd_mul, Nat.odd_mul]
      exact ⟨⟨hPodd.pow, hQodd⟩, hAodd⟩
    have hpair (j i j' i' : ℕ) (hne : (j, i) ≠ (j', i')) :
        Nat.Coprime (canonicalOwnerCell data j i)
          (canonicalOwnerCell data j' i') :=
      canonicalOwnerCells_pairwise_coprime data hne
    have hBcopRB : Nat.Coprime B RB := by
      have h11 : Nat.Coprime B E11 := by dsimp [B, E11]; exact hpair 1 4 1 1 (by norm_num)
      have h12 : Nat.Coprime B E12 := by dsimp [B, E12]; exact hpair 1 4 1 2 (by norm_num)
      have h13 : Nat.Coprime B E13 := by dsimp [B, E13]; exact hpair 1 4 1 3 (by norm_num)
      have h15 : Nat.Coprime B E15 := by dsimp [B, E15]; exact hpair 1 4 1 5 (by norm_num)
      simpa [RB, mul_assoc] using ((h11.mul_right h12).mul_right h13).mul_right h15
    have hsumEven : Even (RB + 4 * CB) := by
      have hfourLeft : 4 ∣ 2 * (RB + 4 * CB) := by
        rw [hnorm]
        exact dvd_mul_of_dvd_right h4J (P ^ 2 * Q * A)
      obtain ⟨z, hz⟩ := hfourLeft
      refine ⟨z, ?_⟩
      omega
    have hBodd : Odd B := by
      rcases Nat.even_or_odd B with hBeven | hBodd
      · have hcopTwoRB : Nat.Coprime 2 RB :=
          Nat.Coprime.coprime_dvd_left (even_iff_two_dvd.mp hBeven) hBcopRB
        have hRBodd : Odd RB := Nat.coprime_two_left.mp hcopTwoRB
        rcases hRBodd with ⟨x, hx⟩
        rcases hsumEven with ⟨y, hy⟩
        omega
      · exact hBodd
    have hRBeven : Even RB := by
      rcases hsumEven with ⟨z, hz⟩
      refine ⟨z - 2 * CB, ?_⟩
      omega
    have hcellDvd (i : ℕ) (hi : i ∈ Finset.Icc 1 5) :
        canonicalOwnerCell data 1 i ∣ d + i - 1 := by
      exact canonicalOwnerCell_dvd_shiftedDifference data hd (by norm_num) hi hfour
    have hE11odd : Odd E11 := by
      apply Odd.of_dvd_nat (show Odd d by rw [Nat.odd_iff]; omega)
      simpa [E11] using hcellDvd 1 (by norm_num)
    have hE13odd : Odd E13 := by
      apply Odd.of_dvd_nat (show Odd (d + 2) by rw [Nat.odd_iff]; omega)
      simpa [E13] using hcellDvd 3 (by norm_num)
    have hE15odd : Odd E15 := by
      apply Odd.of_dvd_nat (show Odd (d + 4) by rw [Nat.odd_iff]; omega)
      simpa [E15] using hcellDvd 5 (by norm_num)
    have hE12even : Even E12 := by
      have hpre : Even (E11 * E12 * E13) := by
        apply even_right_of_odd_left_even_mul hE15odd
        simpa [RB, mul_assoc, mul_left_comm, mul_comm] using hRBeven
      have hpairEven : Even (E11 * E12) := by
        apply even_right_of_odd_left_even_mul hE13odd
        simpa [mul_assoc, mul_left_comm, mul_comm] using hpre
      exact even_right_of_odd_left_even_mul hE11odd hpairEven
    have hE12dvd : E12 ∣ d + 1 := by
      simpa [E12] using hcellDvd 2 (by norm_num)
    have hnotFourE12 : ¬4 ∣ E12 := by
      intro h4E
      have h4gap : 4 ∣ d + 1 := h4E.trans hE12dvd
      have hm := Nat.dvd_iff_mod_eq_zero.mp h4gap
      rw [Nat.add_mod, hd4] at hm
      norm_num at hm
    have hE12mod : E12 % 4 = 2 := by
      have hm2 : E12 % 2 = 0 := Nat.even_iff.mp hE12even
      have hn0 : E12 % 4 ≠ 0 := fun hz => hnotFourE12 (Nat.dvd_of_mod_eq_zero hz)
      have hc := Nat.mod_mod_of_dvd E12 (by norm_num : 2 ∣ 4)
      have hlt := Nat.mod_lt E12 (by norm_num : 0 < 4)
      omega
    have hrestOdd : Odd (E11 * E13 * E15) := by
      rw [Nat.odd_mul, Nat.odd_mul]
      exact ⟨⟨hE11odd, hE13odd⟩, hE15odd⟩
    have hrestMod : (E11 * E13 * E15) % 4 = 1 ∨
        (E11 * E13 * E15) % 4 = 3 := by
      have hm2 := Nat.odd_iff.mp hrestOdd
      have hc := Nat.mod_mod_of_dvd (E11 * E13 * E15) (by norm_num : 2 ∣ 4)
      have hlt := Nat.mod_lt (E11 * E13 * E15) (by norm_num : 0 < 4)
      omega
    have hRBmod : RB % 4 = 2 := by
      have hreorder : RB = E12 * (E11 * E13 * E15) := by dsimp [RB]; ring
      rw [hreorder, Nat.mul_mod, hE12mod]
      rcases hrestMod with h1 | h3
      · rw [h1]
      · rw [h3]
    have hRBcopCB : Nat.Coprime RB CB := by
      have hcellCB (i : ℕ) (hi4 : i ≠ 4) :
          Nat.Coprime (canonicalOwnerCell data 1 i) CB := by
        have h2 := hpair 1 i 2 4 (by intro h; exact hi4 (congrArg Prod.snd h))
        have h3 := hpair 1 i 3 4 (by intro h; exact hi4 (congrArg Prod.snd h))
        have h4 := hpair 1 i 4 4 (by intro h; exact hi4 (congrArg Prod.snd h))
        have h5 := hpair 1 i 5 4 (by intro h; exact hi4 (congrArg Prod.snd h))
        simpa [CB, mul_assoc] using ((h2.mul_right h3).mul_right h4).mul_right h5
      have h11 := hcellCB 1 (by norm_num)
      have h12 := hcellCB 2 (by norm_num)
      have h13 := hcellCB 3 (by norm_num)
      have h15 := hcellCB 5 (by norm_num)
      simpa [RB, mul_assoc] using ((h11.mul_left h12).mul_left h13).mul_left h15
    have hCBodd : Odd CB := by
      have htwoRB : 2 ∣ RB := even_iff_two_dvd.mp hRBeven
      exact Nat.coprime_two_left.mp
        (Nat.Coprime.coprime_dvd_left htwoRB hRBcopCB)
    have hsumMod : (RB + 4 * CB) % 4 = 2 := by
      rw [Nat.add_mod, hRBmod]
      norm_num
    have hleftMod : (2 * (RB + 4 * CB)) % 8 = 4 := by
      rw [Nat.mul_mod]
      have hdecomp := Nat.mod_add_div (RB + 4 * CB) 4
      omega
    intro h8J
    have h8left : 8 ∣ 2 * (RB + 4 * CB) := by
      rw [hnorm]
      exact dvd_mul_of_dvd_right h8J (P ^ 2 * Q * A)
    have hz := Nat.dvd_iff_mod_eq_zero.mp h8left
    rw [hleftMod] at hz
    norm_num at hz
  · intro h8J
    exact h4J ((by norm_num : 4 ∣ 8).trans h8J)

/-- The nonlinear quotient has only six possible values.  The residual-three
row and column force `n = 1 (mod 3)` and `d = 0 (mod 3)`, whereas the exact
centered target is `1 (mod 3)`.  Hence `J` is coprime to three.  Removing the
entire `3^2` part from `J | 23040`, and combining with `8 ∤ J`, leaves
`J | 20`; the displayed six-value list is exact. -/
theorem k5_G12_fixed_cofactor_six_values
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
    Nat.Coprime J 3 ∧ J ∣ 20 ∧
      (J = 1 ∨ J = 2 ∨ J = 4 ∨ J = 5 ∨ J = 10 ∨ J = 20) := by
  dsimp only
  let P := canonicalOwnerCell data 4 1
  let Q := canonicalOwnerCell data 2 3
  let A := canonicalOwnerCell data 3 2
  let B := canonicalOwnerCell data 1 4
  let R := (n + 4) / P
  let C := (n + d + 1) / P
  let K := (R + C) / (P * Q)
  let J := K / (A * B)
  have hn5 : 3 ∣ n + 5 := by
    have hfac := canonical_lower_term_factorization data (j := 5)
    rw [hprofile.2.2.2.2.2.1] at hfac
    exact ⟨canonicalOwnerRow data 5, hfac⟩
  have hn3 : n % 3 = 1 := by
    have hm := Nat.dvd_iff_mod_eq_zero.mp hn5
    rw [Nat.add_mod] at hm
    omega
  have hnd5 : 3 ∣ n + d + 5 := by
    have hfac := canonical_upper_term_factorization data hfour (i := 5)
    rw [hprofile.2.2.2.2.2.2.2.2.2.2] at hfac
    refine ⟨canonicalOwnerColumn data 5, ?_⟩
    simpa [upperTermAfterFour, hprofile.1] using hfac
  have hd3 : d % 3 = 0 := by
    have hm := Nat.dvd_iff_mod_eq_zero.mp hnd5
    rw [Nat.add_mod, Nat.add_mod] at hm
    omega
  have hforced := k5_G12_anti_diagonal_owner_product_dvd_complement_quotient
    data hfour heq hprofile
  have htarget : 2 * n + d + 5 = P ^ 2 * Q * K := by
    have ht : (n + 3) + (n + d + 2) = P ^ 2 * Q * K := by
      simpa [P, Q, A, B, R, C, K] using hforced.2.2
    omega
  have hABdvdK : A * B ∣ K := hforced.1
  have hKeq : K = A * B * J := by
    dsimp [J]
    exact (Nat.mul_div_cancel' hABdvdK).symm
  have htargetJ : 2 * n + d + 5 = P ^ 2 * Q * A * B * J := by
    rw [htarget, hKeq]
    ring
  have htargetMod : (2 * n + d + 5) % 3 = 1 := by
    omega
  have hnot3J : ¬3 ∣ J := by
    intro h3J
    have h3target : 3 ∣ 2 * n + d + 5 := by
      rw [htargetJ]
      exact dvd_mul_of_dvd_right h3J (P ^ 2 * Q * A * B)
    have hz := Nat.dvd_iff_mod_eq_zero.mp h3target
    rw [htargetMod] at hz
    norm_num at hz
  have hcopJ3 : Nat.Coprime J 3 := by
    rw [Nat.coprime_comm]
    exact (Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 3)).mpr hnot3J
  have hJ23040 : J ∣ 23040 := by
    dsimp [J, K, R, C, P, Q, A, B]
    exact k5_G12_remaining_complement_quotient_dvd_23040
      data hfour hd heq hprofile htail hdlt hcells
  have hcopJ9 : Nat.Coprime J 9 := by
    simpa using hcopJ3.pow_right 2
  have hJ2560 : J ∣ 2560 := by
    have hprod : J ∣ 2560 * 9 := by norm_num at hJ23040 ⊢; exact hJ23040
    exact hcopJ9.dvd_of_dvd_mul_right hprod
  have hJne : J ≠ 0 := by
    intro hz
    apply hnot3J
    rw [hz]
    exact dvd_zero 3
  let g := Nat.gcd J 512
  have hg512 : g ∣ 512 := Nat.gcd_dvd_right J 512
  have hnot8J := k5_G12_fixed_cofactor_not_eight
    data hfour hd heq hprofile htail hdlt hcells
  have hnot8g : ¬8 ∣ g := by
    intro h8g
    exact hnot8J (h8g.trans (Nat.gcd_dvd_left J 512))
  have hg4 : g ∣ 4 := divisor_512_dvd_four_of_not_eight hg512 hnot8g
  have hred : J / g ∣ 5 := by
    apply reduced_modulus_dvd_of_dvd_coefficient_mul_coprime
      (P := J) (c := 512) (Q := 1) (U := 5) hJne
        (Nat.coprime_one_right J)
    simpa [g] using hJ2560
  have hgJ : g ∣ J := Nat.gcd_dvd_left J 512
  have hfactor : g * (J / g) = J := Nat.mul_div_cancel' hgJ
  have hJ20 : J ∣ 20 := by
    rw [← hfactor]
    simpa using Nat.mul_dvd_mul hg4 hred
  have hvalues : J = 1 ∨ J = 2 ∨ J = 4 ∨ J = 5 ∨ J = 10 ∨ J = 20 := by
    have hJle : J ≤ 20 := Nat.le_of_dvd (by norm_num) hJ20
    interval_cases J <;> norm_num at hJ20
    all_goals norm_num
  exact ⟨hcopJ3, hJ20, hvalues⟩

/-- With the six-value classification substituted back into the exact
complement sum, the formerly huge fixed row constant collapses from `11520`
to `10`: `n+4 < 10 P^2 Q A B`.  Thus the four anti-diagonal owners now carry
a fixed positive proportion of the entire fully owned row term. -/
theorem k5_G12_six_cofactor_owner_bound
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
    J ∣ 20 ∧
      R + C = (P * Q * (A * B)) * J ∧
      4 * R < 2 * ((P * Q * (A * B)) * J) ∧
      2 * ((P * Q * (A * B)) * J) < 5 * R ∧
      n + 4 < 10 * (P ^ 2 * Q * (A * B)) := by
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
  have hw := k5_G12_fixed_cofactor_narrow_window
    data hfour hd heq hprofile htail hdlt hcells
  have hsum : R + C = X * J := by
    simpa [P, Q, A, B, R, C, K, J, X] using hw.2.1
  have hlower : 4 * R < 2 * (X * J) := by
    simpa [P, Q, A, B, R, C, K, J, X] using hw.2.2.2.2.1
  have hupper : 2 * (X * J) < 5 * R := by
    simpa [P, Q, A, B, R, C, K, J, X] using hw.2.2.2.2.2.1
  have hsix := k5_G12_fixed_cofactor_six_values
    data hfour hd heq hprofile htail hdlt hcells
  have hJ20 : J ∣ 20 := by
    simpa [P, Q, A, B, R, C, K, J] using hsix.2.1
  have hJle : J ≤ 20 := Nat.le_of_dvd (by norm_num) hJ20
  have hXJle : X * J ≤ X * 20 := Nat.mul_le_mul_left X hJle
  have hRbound : R < 10 * X := by
    have htwoR : 2 * R < X * J := by omega
    have : 2 * R < X * 20 := htwoR.trans_le hXJle
    omega
  have hcomp := k5_G12_zero_crossing_product_dvd_complement_sum
    data hfour heq hprofile htail hdlt hcells
  have hrow : n + 4 = P * R := hcomp.1
  have hPpos : 0 < P := by dsimp [P]; exact canonicalOwnerCell_pos data
  have hnBound : n + 4 < 10 * (P ^ 2 * Q * (A * B)) := by
    rw [hrow]
    have hmul := (Nat.mul_lt_mul_left hPpos).mpr hRbound
    dsimp [X] at hmul
    convert hmul using 1
    ring
  exact ⟨hJ20, by simpa [X] using hsum, by simpa [X] using hlower,
    by simpa [X] using hupper, hnBound⟩

#print axioms k5_G12_fixed_cofactor_narrow_window
#print axioms k5_G12_fixed_cofactor_exterior_two_adic_constraint
#print axioms k5_G12_fixed_cofactor_not_eight
#print axioms k5_G12_fixed_cofactor_six_values
#print axioms k5_G12_six_cofactor_owner_bound

end Erdos686Variant
end Erdos686
