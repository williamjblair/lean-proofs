/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.K5.G12FixedCofactorWindow

/-!
# Erdős 686, k=5: parity of the fixed cofactor in the G=12 branch

The exact row-one and column-four factorizations are independent global
equations meeting at the owner `B`.  After cancelling `B`, their sum is

`2 (RB + 4 CB) = P^2 Q A J`.

The owners `P` and `Q` divide odd lower terms.  The owner `A` lies in column
two; the `G=12` profile and `4 | n+d+4` make the entire column-two owner
product odd.  Every cell in `RB` also lies in an odd upper column, so `RB`
is odd.  Thus the displayed equation has exactly one factor of two on its
left: `J` is even but not divisible by four.  Only `J=2` and `J=10` remain.
-/

namespace Erdos686
namespace Erdos686Variant

/-- The remaining fixed cofactor is exactly twice an odd number, hence only
two of the six previously possible values survive. -/
theorem k5_G12_fixed_cofactor_two_values
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
    Even J ∧ ¬4 ∣ J ∧ (J = 2 ∨ J = 10) := by
  dsimp only
  let P := canonicalOwnerCell data 4 1
  let Q := canonicalOwnerCell data 2 3
  let A := canonicalOwnerCell data 3 2
  let B := canonicalOwnerCell data 1 4
  let R := (n + 4) / P
  let C := (n + d + 1) / P
  let K := (R + C) / (P * Q)
  let J := K / (A * B)
  let RB := canonicalOwnerCell data 1 1 * canonicalOwnerCell data 1 2 *
    canonicalOwnerCell data 1 3 * canonicalOwnerCell data 1 5
  let CB := canonicalOwnerCell data 2 4 * canonicalOwnerCell data 3 4 *
    canonicalOwnerCell data 4 4 * canonicalOwnerCell data 5 4

  have hnEvenSucc : 2 ∣ n + 1 := by
    have hfac := canonical_lower_term_factorization data (j := 1)
    rw [hprofile.2.1] at hfac
    exact ⟨canonicalOwnerRow data 1, hfac⟩
  have hnOdd : Odd n := by
    rw [Nat.odd_iff]
    have hm := Nat.dvd_iff_mod_eq_zero.mp hnEvenSucc
    rw [Nat.add_mod] at hm
    omega
  have hPdvd : P ∣ n + 4 := by
    dsimp [P]
    exact canonicalOwnerCell_dvd_lower data
  have hQdvd : Q ∣ n + 2 := by
    dsimp [Q]
    exact canonicalOwnerCell_dvd_lower data
  have hPodd : Odd P := by
    apply Odd.of_dvd_nat (show Odd (n + 4) by
      rw [Nat.odd_iff]
      have hn := Nat.odd_iff.mp hnOdd
      omega)
    exact hPdvd
  have hQodd : Odd Q := by
    apply Odd.of_dvd_nat (show Odd (n + 2) by
      rw [Nat.odd_iff]
      have hn := Nat.odd_iff.mp hnOdd
      omega)
    exact hQdvd

  have hfourND4 : 4 ∣ n + d + 4 := by
    simpa [hprofile.1] using hfour
  have hnd2mod : (n + d + 2) % 4 = 2 := by
    have hm := Nat.dvd_iff_mod_eq_zero.mp hfourND4
    rw [Nat.add_mod, Nat.add_mod] at hm ⊢
    omega
  let CA := canonicalOwnerCell data 1 2 * canonicalOwnerCell data 2 2 *
    canonicalOwnerCell data 4 2 * canonicalOwnerCell data 5 2
  have hcolProdA : canonicalOwnerColumn data 2 = A * CA := by
    rw [← canonicalOwner_column_cell_product data]
    norm_num [A, CA, Finset.prod_Icc_succ_top]
    ring
  have hcolA : n + d + 2 = 2 * (A * CA) := by
    have hfac := canonical_upper_term_factorization data hfour (i := 2)
    rw [hprofile.2.2.2.2.2.2.2.1, hcolProdA] at hfac
    simpa [upperTermAfterFour, hprofile.1] using hfac
  have hACAOdd : Odd (A * CA) := by
    rw [Nat.odd_iff]
    have hmod : (2 * (A * CA)) % 4 = 2 := by
      rw [← hcolA]
      exact hnd2mod
    rw [Nat.mul_mod] at hmod
    have hlt := Nat.mod_lt (A * CA) (by norm_num : 0 < 2)
    omega
  have hAodd : Odd A := (Nat.odd_mul.mp hACAOdd).1

  have hndEven : Even (n + d) := by
    rw [even_iff_two_dvd, Nat.dvd_iff_mod_eq_zero]
    have hm := Nat.dvd_iff_mod_eq_zero.mp hfourND4
    rw [Nat.add_mod] at hm
    omega
  have hupperCellOdd (i : ℕ) (hterm : Odd (n + d + i)) :
      Odd (canonicalOwnerCell data 1 i) := by
    apply Odd.of_dvd_nat hterm
    exact dvd_trans (canonicalOwnerCell_dvd_upper data)
      (upperTermAfterFour_dvd_original hfour)
  have hE11odd : Odd (canonicalOwnerCell data 1 1) := by
    apply hupperCellOdd 1
    rw [Nat.odd_iff]
    have hm := Nat.even_iff.mp hndEven
    omega
  have hE13odd : Odd (canonicalOwnerCell data 1 3) := by
    apply hupperCellOdd 3
    rw [Nat.odd_iff]
    have hm := Nat.even_iff.mp hndEven
    omega
  have hE15odd : Odd (canonicalOwnerCell data 1 5) := by
    apply hupperCellOdd 5
    rw [Nat.odd_iff]
    have hm := Nat.even_iff.mp hndEven
    omega
  have hE12dvdAC : canonicalOwnerCell data 1 2 ∣ A * CA := by
    refine ⟨A * (canonicalOwnerCell data 2 2 *
      canonicalOwnerCell data 4 2 * canonicalOwnerCell data 5 2), ?_⟩
    dsimp [CA]
    ring
  have hE12odd : Odd (canonicalOwnerCell data 1 2) :=
    Odd.of_dvd_nat hACAOdd hE12dvdAC
  have hRBodd : Odd RB := by
    dsimp [RB]
    rw [Nat.odd_mul, Nat.odd_mul, Nat.odd_mul]
    exact ⟨⟨⟨hE11odd, hE12odd⟩, hE13odd⟩, hE15odd⟩

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
  have hrowProdB : canonicalOwnerRow data 1 = B * RB := by
    rw [← canonicalOwner_row_cell_product data]
    norm_num [B, RB, Finset.prod_Icc_succ_top]
    ring
  have hcolProdB : canonicalOwnerColumn data 4 = B * CB := by
    rw [← canonicalOwner_column_cell_product data]
    norm_num [B, CB, Finset.prod_Icc_succ_top]
    ring
  have hrowB : n + 1 = 2 * (B * RB) := by
    simpa [hprofile.2.1, hrowProdB] using
      canonical_lower_term_factorization data (j := 1)
  have hcolB : n + d + 4 = 8 * (B * CB) := by
    have hfac := canonical_upper_term_factorization data hfour (i := 4)
    rw [hprofile.2.2.2.2.2.2.2.2.2.1, hcolProdB] at hfac
    simpa [upperTermAfterFour, hprofile.1] using
      congrArg (fun z : ℕ => 4 * z) hfac
  have hBpos : 0 < B := by
    dsimp [B]
    exact canonicalOwnerCell_pos data
  have hglobal : 2 * (RB + 4 * CB) = P ^ 2 * Q * A * J := by
    apply Nat.mul_left_cancel hBpos
    calc
      B * (2 * (RB + 4 * CB)) = (n + 1) + (n + d + 4) := by
        rw [hrowB, hcolB]
        ring
      _ = P ^ 2 * Q * K := htarget
      _ = B * (P ^ 2 * Q * A * J) := by
        rw [hKeq]
        ring

  have hcoefficientOdd : Odd (P ^ 2 * Q * A) := by
    rw [Nat.odd_mul, Nat.odd_mul]
    exact ⟨⟨hPodd.pow, hQodd⟩, hAodd⟩
  have htwoProduct : 2 ∣ (P ^ 2 * Q * A) * J := by
    rw [← hglobal]
    exact ⟨RB + 4 * CB, by ring⟩
  have htwoJ : 2 ∣ J := by
    rcases (Nat.prime_two.dvd_mul.mp htwoProduct) with hcoeff | hJ
    · exact False.elim
        ((Nat.not_even_iff_odd.mpr hcoefficientOdd)
          (even_iff_two_dvd.mpr hcoeff))
    · exact hJ
  have hJeven : Even J := even_iff_two_dvd.mpr htwoJ
  have hinnerOdd : Odd (RB + 4 * CB) := by
    rw [Nat.odd_iff]
    have hm := Nat.odd_iff.mp hRBodd
    omega
  have hnotFourJ : ¬4 ∣ J := by
    intro hfourJ
    have hfourLeft : 4 ∣ 2 * (RB + 4 * CB) := by
      rw [hglobal]
      exact dvd_mul_of_dvd_right hfourJ (P ^ 2 * Q * A)
    rcases hinnerOdd with ⟨z, hz⟩
    rcases hfourLeft with ⟨w, hw⟩
    omega
  have hsix := k5_G12_fixed_cofactor_six_values
    data hfour hd heq hprofile htail hdlt hcells
  have hvalues : J = 1 ∨ J = 2 ∨ J = 4 ∨ J = 5 ∨ J = 10 ∨ J = 20 := by
    simpa [P, Q, A, B, R, C, K, J] using hsix.2.2
  rcases hvalues with h1 | h2 | h4 | h5 | h10 | h20
  · rw [h1] at htwoJ
    norm_num at htwoJ
  · exact ⟨hJeven, hnotFourJ, Or.inl h2⟩
  · exfalso
    apply hnotFourJ
    rw [h4]
  · rw [h5] at htwoJ
    norm_num at htwoJ
  · exact ⟨hJeven, hnotFourJ, Or.inr h10⟩
  · exfalso
    apply hnotFourJ
    rw [h20]
    norm_num

#print axioms k5_G12_fixed_cofactor_two_values

end Erdos686Variant
end Erdos686
