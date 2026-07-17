/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686K5ExceptionalCrossingSquare

/-!
# Erdős 686, k=5: full exceptional row-column square system

The exceptional unit row and unit column consist entirely of factors
coprime to six.  Consequently the exact local coefficients `24`, `6`, and
`4` can be cancelled at every cell, not merely at the central crossing.
This module records the resulting five primitive square defects on each
side of the crossing.
-/

namespace Erdos686
namespace Erdos686Variant

/-- Primitive row defect after cancelling the exact local coefficient.
The even-column orientation is chosen so the expression is positive in the
centered solution window. -/
def k5ExceptionalRowSquareDefect (n d j i : ℕ) : ℤ :=
  let x : ℤ := n + j
  let D : ℤ := (d + i - j : ℕ)
  match i with
  | 1 => D + 2 * x
  | 2 => 3 * x - D
  | 3 => D + 7 * x
  | 4 => 3 * x - D
  | 5 => D + 2 * x
  | _ => 0

/-- Primitive column defect after cancelling the exact local coefficient. -/
def k5ExceptionalColumnSquareDefect (n d i j : ℕ) : ℤ :=
  let y : ℤ := n + d + i
  let xj : ℤ := n + j
  match j with
  | 1 => y + 16 * xj
  | 2 => y - 4 * xj
  | 3 => 3 * y + 8 * xj
  | 4 => y - 4 * xj
  | 5 => y + 16 * xj
  | _ => 0

private theorem coprime_six_cancel_small_coefficient
    {P q : ℕ} {z : ℤ}
    (hcop : Nat.Coprime P 6)
    (hq : q ∣ 6 ^ 3)
    (hdiv : ((P : ℤ) ^ 2) ∣ (q : ℤ) * z) :
    ((P : ℤ) ^ 2) ∣ z := by
  have hPq : Nat.Coprime P q :=
    Nat.Coprime.of_dvd_right hq (Nat.Coprime.pow_right 3 hcop)
  have hP2q : Nat.Coprime (P ^ 2) q := Nat.Coprime.pow_left 2 hPq
  exact hP2q.isCoprime.dvd_of_dvd_mul_left (by simpa using hdiv)

/-- All five primitive square congruences in a fully owned exceptional row.
This theorem deliberately only assumes the exact properties used by the
cancellation: row/column divisibility and coprimality with six. -/
theorem k5_even_fullyOwned_row_square_defect_system
    {n d j : ℕ}
    (hj : j = 2 ∨ j = 4)
    (hd : 5 ≤ d)
    (P : ℕ → ℕ)
    (hcop : ∀ i ∈ Finset.Icc 1 5, Nat.Coprime (P i) 6)
    (hlower : ∀ i ∈ Finset.Icc 1 5, P i ∣ n + j)
    (hupper : ∀ i ∈ Finset.Icc 1 5, P i ∣ n + d + i)
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n) :
    ∀ i ∈ Finset.Icc 1 5,
      (((P i : ℕ) : ℤ) ^ 2) ∣ k5ExceptionalRowSquareDefect n d j i := by
  intro i hi
  have hjIcc : j ∈ Finset.Icc 1 5 := by
    rcases hj with rfl | rfl <;> norm_num
  have hraw := matched_owner_local_coefficients_dvd_sq
    hjIcc hi (hlower i hi) (hupper i hi) heq
  rw [localBlockCoefficient_eq_sign_mul_nat hi,
    localBlockCoefficient_eq_sign_mul_nat hjIcc] at hraw
  have hji : j ≤ d + i := by
    have hi1 := (Finset.mem_Icc.mp hi).1
    rcases hj with rfl | rfl <;> omega
  have hcastD :
      ((d + i - j : ℕ) : ℤ) = (d : ℤ) + (i : ℤ) - (j : ℤ) := by
    rw [Nat.cast_sub hji]
    push_cast
    rfl
  have hcopi := hcop i hi
  have hi1 := (Finset.mem_Icc.mp hi).1
  have hi5 := (Finset.mem_Icc.mp hi).2
  interval_cases i <;> rcases hj with rfl | rfl
  all_goals
    simp only [k5ExceptionalRowSquareDefect]
    rw [hcastD]
    push_cast at hraw ⊢
    norm_num [localBlockCoefficientNat] at hraw ⊢
  · apply coprime_six_cancel_small_coefficient hcopi (q := 24) (by norm_num)
    convert hraw using 1 <;> ring
  · apply coprime_six_cancel_small_coefficient hcopi (q := 24) (by norm_num)
    convert hraw using 1 <;> ring
  · apply coprime_six_cancel_small_coefficient hcopi (q := 6) (by norm_num)
    convert hraw using 1 <;> ring
  · apply coprime_six_cancel_small_coefficient hcopi (q := 6) (by norm_num)
    convert hraw using 1 <;> ring
  · apply coprime_six_cancel_small_coefficient hcopi (q := 4) (by norm_num)
    convert hraw using 1 <;> ring
  · apply coprime_six_cancel_small_coefficient hcopi (q := 4) (by norm_num)
    convert hraw using 1 <;> ring
  · apply coprime_six_cancel_small_coefficient hcopi (q := 6) (by norm_num)
    convert hraw using 1 <;> ring
  · apply coprime_six_cancel_small_coefficient hcopi (q := 6) (by norm_num)
    convert hraw using 1 <;> ring
  · apply coprime_six_cancel_small_coefficient hcopi (q := 24) (by norm_num)
    convert hraw using 1 <;> ring
  · apply coprime_six_cancel_small_coefficient hcopi (q := 24) (by norm_num)
    convert hraw using 1 <;> ring

set_option maxRecDepth 2000 in
/-- All five primitive square congruences in a fully owned exceptional
column. -/
theorem k5_even_fullyOwned_column_square_defect_system
    {n d i : ℕ}
    (hi : i = 2 ∨ i = 4)
    (P : ℕ → ℕ)
    (hcop : ∀ j ∈ Finset.Icc 1 5, Nat.Coprime (P j) 6)
    (hlower : ∀ j ∈ Finset.Icc 1 5, P j ∣ n + j)
    (hupper : ∀ j ∈ Finset.Icc 1 5, P j ∣ n + d + i)
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n) :
    ∀ j ∈ Finset.Icc 1 5,
      (((P j : ℕ) : ℤ) ^ 2) ∣ k5ExceptionalColumnSquareDefect n d i j := by
  intro j hj
  have hiIcc : i ∈ Finset.Icc 1 5 := by
    rcases hi with rfl | rfl <;> norm_num
  have hraw := matched_owner_local_coefficients_dvd_sq
    hj hiIcc (hlower j hj) (hupper j hj) heq
  rw [localBlockCoefficient_eq_sign_mul_nat hiIcc,
    localBlockCoefficient_eq_sign_mul_nat hj] at hraw
  have hj1 := (Finset.mem_Icc.mp hj).1
  have hj5 := (Finset.mem_Icc.mp hj).2
  have hcopj := hcop j hj
  interval_cases j <;> rcases hi with rfl | rfl
  all_goals
    simp only [k5ExceptionalColumnSquareDefect]
    push_cast at hraw ⊢
    norm_num [localBlockCoefficientNat] at hraw ⊢
  · apply coprime_six_cancel_small_coefficient hcopj (q := 6) (by norm_num)
    convert dvd_neg.mpr hraw using 1 <;> ring
  · apply coprime_six_cancel_small_coefficient hcopj (q := 6) (by norm_num)
    convert dvd_neg.mpr hraw using 1 <;> ring
  · apply coprime_six_cancel_small_coefficient hcopj (q := 6) (by norm_num)
    convert dvd_neg.mpr hraw using 1 <;> ring
  · apply coprime_six_cancel_small_coefficient hcopj (q := 6) (by norm_num)
    convert dvd_neg.mpr hraw using 1 <;> ring
  · apply coprime_six_cancel_small_coefficient hcopj (q := 2) (by norm_num)
    convert dvd_neg.mpr hraw using 1 <;> ring
  · apply coprime_six_cancel_small_coefficient hcopj (q := 2) (by norm_num)
    convert dvd_neg.mpr hraw using 1 <;> ring
  · apply coprime_six_cancel_small_coefficient hcopj (q := 6) (by norm_num)
    convert dvd_neg.mpr hraw using 1 <;> ring
  · apply coprime_six_cancel_small_coefficient hcopj (q := 6) (by norm_num)
    convert dvd_neg.mpr hraw using 1 <;> ring
  · apply coprime_six_cancel_small_coefficient hcopj (q := 6) (by norm_num)
    convert dvd_neg.mpr hraw using 1 <;> ring
  · apply coprime_six_cancel_small_coefficient hcopj (q := 6) (by norm_num)
    convert dvd_neg.mpr hraw using 1 <;> ring

/-- Multiplying the five row-square congruences turns full ownership into a
single exact square divisor of the row defect product. -/
theorem k5_fullyOwned_row_sq_dvd_defect_product
    {n d t j : ℕ} (data : CanonicalOwnerData 5 n d t)
    (hlower : canonicalLowerResidual data j = 1)
    (hsystem : ∀ i ∈ Finset.Icc 1 5,
      (((canonicalOwnerCell data j i : ℕ) : ℤ) ^ 2) ∣
        k5ExceptionalRowSquareDefect n d j i) :
    (((n + j : ℕ) : ℤ) ^ 2) ∣
      ∏ i ∈ Finset.Icc 1 5, k5ExceptionalRowSquareDefect n d j i := by
  have hdvd := Finset.prod_dvd_prod_of_dvd
    (s := Finset.Icc 1 5)
    (fun i => ((canonicalOwnerCell data j i : ℕ) : ℤ) ^ 2)
    (fun i => k5ExceptionalRowSquareDefect n d j i) hsystem
  rw [Finset.prod_pow] at hdvd
  have hrowNat :
      (∏ i ∈ Finset.Icc 1 5, canonicalOwnerCell data j i) = n + j := by
    calc
      _ = canonicalOwnerRow data j := canonicalOwner_row_cell_product data
      _ = n + j := by
        rw [canonical_lower_term_factorization data, hlower, one_mul]
  simpa only [← Nat.cast_prod, hrowNat] using hdvd

/-- Column analogue of the aggregate square divisor. -/
theorem k5_fullyOwned_column_sq_dvd_defect_product
    {n d t i : ℕ} (data : CanonicalOwnerData 5 n d t)
    (hit : i ≠ t)
    (hfour : 4 ∣ n + d + t)
    (hupper : canonicalUpperResidual data i = 1)
    (hsystem : ∀ j ∈ Finset.Icc 1 5,
      (((canonicalOwnerCell data j i : ℕ) : ℤ) ^ 2) ∣
        k5ExceptionalColumnSquareDefect n d i j) :
    (((n + d + i : ℕ) : ℤ) ^ 2) ∣
      ∏ j ∈ Finset.Icc 1 5, k5ExceptionalColumnSquareDefect n d i j := by
  have hdvd := Finset.prod_dvd_prod_of_dvd
    (s := Finset.Icc 1 5)
    (fun j => ((canonicalOwnerCell data j i : ℕ) : ℤ) ^ 2)
    (fun j => k5ExceptionalColumnSquareDefect n d i j) hsystem
  rw [Finset.prod_pow] at hdvd
  have hcolumnNat :
      (∏ j ∈ Finset.Icc 1 5, canonicalOwnerCell data j i) =
        n + d + i := by
    have hfactor := canonical_upper_term_factorization data hfour (i := i)
    simp only [if_neg hit, one_mul, hupper] at hfactor
    calc
      _ = canonicalOwnerColumn data i := canonicalOwner_column_cell_product data
      _ = n + d + i := hfactor.symm
  simpa only [← Nat.cast_prod, hcolumnNat] using hdvd

/-- The complete primitive square system on the nine distinct cells in an
exceptional fully owned row-column star. -/
def K5ExceptionalSquareStar
    {n d t : ℕ} (data : CanonicalOwnerData 5 n d t) (j i : ℕ) : Prop :=
  (∀ i' ∈ Finset.Icc 1 5,
    (((canonicalOwnerCell data j i' : ℕ) : ℤ) ^ 2) ∣
      k5ExceptionalRowSquareDefect n d j i') ∧
  (∀ j' ∈ Finset.Icc 1 5,
    (((canonicalOwnerCell data j' i : ℕ) : ℤ) ^ 2) ∣
      k5ExceptionalColumnSquareDefect n d i j')

/-- The four exact exceptional placements all carry the full nine-cell
primitive square system.  In particular, the conclusion retains the
independent row and column equations rather than only the shared crossing. -/
theorem k5_exceptional_full_square_star
    {n d t : ℕ} (data : CanonicalOwnerData 5 n d t)
    (ht : t ∈ Finset.Icc 1 5)
    (hfour : 4 ∣ n + d + t)
    (hblocks : upperBlockAfterFour 5 n d t = blockProduct 5 n)
    (htail : 10 ^ 1000 ≤ d)
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n)
    (hlower : K5ExceptionalResidualProfile (canonicalLowerResidual data))
    (hupper : K5ExceptionalResidualProfile (canonicalUpperResidual data)) :
    (d % 6 = 0 ∧ K5ExceptionalSquareStar data 2 2) ∨
    (d % 6 = 2 ∧ K5ExceptionalSquareStar data 2 4) ∨
    (d % 6 = 4 ∧ K5ExceptionalSquareStar data 4 2) ∨
    (d % 6 = 0 ∧ K5ExceptionalSquareStar data 4 4) := by
  have hd : 5 ≤ d := by
    have hbase : 5 ≤ 10 ^ 1000 := by
      rw [show 1000 = 999 + 1 by omega, pow_succ]
      have hp0 : 0 < (10 : ℕ) ^ 999 := pow_pos (by norm_num) _
      have hp : 1 ≤ (10 : ℕ) ^ 999 := hp0
      calc
        5 ≤ 1 * 10 := by norm_num
        _ ≤ 10 ^ 999 * 10 := Nat.mul_le_mul_right 10 hp
    exact le_trans hbase htail
  have hcases := k5_exceptional_exact_unit_crossing_constraints
    data ht hfour hblocks htail heq hlower hupper
  have hupperCop := k5_exceptional_unit_upper_terms_coprime_six
    data ht hfour hupper
  rcases hcases with hc | hc | hc | hc
  · left
    rcases hc with ⟨hmod, -, -, hu, -, -, hrowFactors, -⟩
    refine ⟨hmod, ?_, ?_⟩
    · apply k5_even_fullyOwned_row_square_defect_system
        (by left; rfl) hd (fun i' => canonicalOwnerCell data 2 i')
      · exact fun i' hi' => (hrowFactors i' hi').2.1
      · exact fun _ _ => canonicalOwnerCell_dvd_lower data
      · exact fun _ _ => dvd_trans (canonicalOwnerCell_dvd_upper data)
          (upperTermAfterFour_dvd_original hfour)
      · exact heq
    · have hyCop := hupperCop.1 hu
      apply k5_even_fullyOwned_column_square_defect_system
        (by left; rfl) (fun j' => canonicalOwnerCell data j' 2)
      · exact fun _ _ => hyCop.of_dvd_left
          (dvd_trans (canonicalOwnerCell_dvd_upper data)
            (upperTermAfterFour_dvd_original hfour))
      · exact fun _ _ => canonicalOwnerCell_dvd_lower data
      · exact fun _ _ => dvd_trans (canonicalOwnerCell_dvd_upper data)
          (upperTermAfterFour_dvd_original hfour)
      · exact heq
  · right; left
    rcases hc with ⟨hmod, -, -, hu, -, -, hrowFactors, -⟩
    refine ⟨hmod, ?_, ?_⟩
    · apply k5_even_fullyOwned_row_square_defect_system
        (by left; rfl) hd (fun i' => canonicalOwnerCell data 2 i')
      · exact fun i' hi' => (hrowFactors i' hi').2.1
      · exact fun _ _ => canonicalOwnerCell_dvd_lower data
      · exact fun _ _ => dvd_trans (canonicalOwnerCell_dvd_upper data)
          (upperTermAfterFour_dvd_original hfour)
      · exact heq
    · have hyCop := hupperCop.2 hu
      apply k5_even_fullyOwned_column_square_defect_system
        (by right; rfl) (fun j' => canonicalOwnerCell data j' 4)
      · exact fun _ _ => hyCop.of_dvd_left
          (dvd_trans (canonicalOwnerCell_dvd_upper data)
            (upperTermAfterFour_dvd_original hfour))
      · exact fun _ _ => canonicalOwnerCell_dvd_lower data
      · exact fun _ _ => dvd_trans (canonicalOwnerCell_dvd_upper data)
          (upperTermAfterFour_dvd_original hfour)
      · exact heq
  · right; right; left
    rcases hc with ⟨hmod, -, -, hu, -, -, hrowFactors, -⟩
    refine ⟨hmod, ?_, ?_⟩
    · apply k5_even_fullyOwned_row_square_defect_system
        (by right; rfl) hd (fun i' => canonicalOwnerCell data 4 i')
      · exact fun i' hi' => (hrowFactors i' hi').2.1
      · exact fun _ _ => canonicalOwnerCell_dvd_lower data
      · exact fun _ _ => dvd_trans (canonicalOwnerCell_dvd_upper data)
          (upperTermAfterFour_dvd_original hfour)
      · exact heq
    · have hyCop := hupperCop.1 hu
      apply k5_even_fullyOwned_column_square_defect_system
        (by left; rfl) (fun j' => canonicalOwnerCell data j' 2)
      · exact fun _ _ => hyCop.of_dvd_left
          (dvd_trans (canonicalOwnerCell_dvd_upper data)
            (upperTermAfterFour_dvd_original hfour))
      · exact fun _ _ => canonicalOwnerCell_dvd_lower data
      · exact fun _ _ => dvd_trans (canonicalOwnerCell_dvd_upper data)
          (upperTermAfterFour_dvd_original hfour)
      · exact heq
  · right; right; right
    rcases hc with ⟨hmod, -, -, hu, -, -, hrowFactors, -⟩
    refine ⟨hmod, ?_, ?_⟩
    · apply k5_even_fullyOwned_row_square_defect_system
        (by right; rfl) hd (fun i' => canonicalOwnerCell data 4 i')
      · exact fun i' hi' => (hrowFactors i' hi').2.1
      · exact fun _ _ => canonicalOwnerCell_dvd_lower data
      · exact fun _ _ => dvd_trans (canonicalOwnerCell_dvd_upper data)
          (upperTermAfterFour_dvd_original hfour)
      · exact heq
    · have hyCop := hupperCop.2 hu
      apply k5_even_fullyOwned_column_square_defect_system
        (by right; rfl) (fun j' => canonicalOwnerCell data j' 4)
      · exact fun _ _ => hyCop.of_dvd_left
          (dvd_trans (canonicalOwnerCell_dvd_upper data)
            (upperTermAfterFour_dvd_original hfour))
      · exact fun _ _ => canonicalOwnerCell_dvd_lower data
      · exact fun _ _ => dvd_trans (canonicalOwnerCell_dvd_upper data)
          (upperTermAfterFour_dvd_original hfour)
      · exact heq
#print axioms k5_even_fullyOwned_row_square_defect_system
#print axioms k5_even_fullyOwned_column_square_defect_system
#print axioms k5_fullyOwned_row_sq_dvd_defect_product
#print axioms k5_fullyOwned_column_sq_dvd_defect_product
#print axioms k5_exceptional_full_square_star

end Erdos686Variant
end Erdos686
