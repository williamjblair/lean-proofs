/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686K5CompleteSupportArithmetic

/-!
# Erdős 686, k=5: proper-global simultaneous CRT bounds

This module combines the two fully owned lower rows and two fully owned
modified upper columns available when the global residual is not `24`.
Pairwise owner coprimality upgrades the four separate diagonal divisibilities
to two product divisibilities with coprime moduli.  Thus both independent
row equations and both independent column equations survive simultaneously.
-/

namespace Erdos686
namespace Erdos686Variant

open scoped BigOperators

def k5RowDiagonalProduct (d j : ℕ) : ℕ :=
  ∏ i ∈ Finset.Icc 1 5, (d + i - j)

def k5ColumnDiagonalProduct (d i : ℕ) : ℕ :=
  ∏ j ∈ Finset.Icc 1 5, (d + i - j)

def k5DiagonalWindow (d : ℕ) : ℕ :=
  (d - 4) * (d - 3) * (d - 2) * (d - 1) * d *
    (d + 1) * (d + 2) * (d + 3) * (d + 4)

lemma k5RowDiagonalProduct_dvd_window {d j : ℕ} (hd : 5 ≤ d)
    (hj : j ∈ Finset.Icc 1 5) :
    k5RowDiagonalProduct d j ∣ k5DiagonalWindow d := by
  have hj1 := (Finset.mem_Icc.mp hj).1
  have hj5 := (Finset.mem_Icc.mp hj).2
  interval_cases j <;>
    norm_num [k5RowDiagonalProduct, k5DiagonalWindow,
      Finset.prod_Icc_succ_top]
  · refine ⟨(d - 4) * (d - 3) * (d - 2) * (d - 1), ?_⟩
    ring
  · have h21 : d + 1 - 2 = d - 1 := by omega
    have h22 : d + 2 - 2 = d := by omega
    have h23 : d + 3 - 2 = d + 1 := by omega
    have h24 : d + 4 - 2 = d + 2 := by omega
    have h25 : d + 5 - 2 = d + 3 := by omega
    rw [h23, h24, h25]
    refine ⟨(d - 4) * (d - 3) * (d - 2) * (d + 4), ?_⟩
    rw [h21]
    ring
  · have h31 : d + 1 - 3 = d - 2 := by omega
    have h32 : d + 2 - 3 = d - 1 := by omega
    have h33 : d + 3 - 3 = d := by omega
    have h34 : d + 4 - 3 = d + 1 := by omega
    have h35 : d + 5 - 3 = d + 2 := by omega
    rw [h34, h35]
    refine ⟨(d - 4) * (d - 3) * (d + 3) * (d + 4), ?_⟩
    rw [h31, h32]
    ring
  · have h41 : d + 1 - 4 = d - 3 := by omega
    have h42 : d + 2 - 4 = d - 2 := by omega
    have h43 : d + 3 - 4 = d - 1 := by omega
    have h44 : d + 4 - 4 = d := by omega
    have h45 : d + 5 - 4 = d + 1 := by omega
    rw [h45]
    refine ⟨(d - 4) * (d + 2) * (d + 3) * (d + 4), ?_⟩
    rw [h41, h42, h43]
    ring
  · have h51 : d + 1 - 5 = d - 4 := by omega
    have h52 : d + 2 - 5 = d - 3 := by omega
    have h53 : d + 3 - 5 = d - 2 := by omega
    have h54 : d + 4 - 5 = d - 1 := by omega
    have h55 : d + 5 - 5 = d := by omega
    refine ⟨(d + 1) * (d + 2) * (d + 3) * (d + 4), ?_⟩
    rw [h51, h52, h53, h54]
    ring

lemma k5ColumnDiagonalProduct_dvd_window {d i : ℕ} (hd : 5 ≤ d)
    (hi : i ∈ Finset.Icc 1 5) :
    k5ColumnDiagonalProduct d i ∣ k5DiagonalWindow d := by
  have hi1 := (Finset.mem_Icc.mp hi).1
  have hi5 := (Finset.mem_Icc.mp hi).2
  interval_cases i <;>
    norm_num [k5ColumnDiagonalProduct, k5DiagonalWindow,
      Finset.prod_Icc_succ_top]
  · have h12 : d + 1 - 2 = d - 1 := by omega
    have h13 : d + 1 - 3 = d - 2 := by omega
    have h14 : d + 1 - 4 = d - 3 := by omega
    have h15 : d + 1 - 5 = d - 4 := by omega
    rw [h12, h13, h14, h15]
    refine ⟨(d + 1) * (d + 2) * (d + 3) * (d + 4), ?_⟩
    ring
  · have h21 : d + 2 - 1 = d + 1 := by omega
    have h22 : d + 2 - 2 = d := by omega
    have h23 : d + 2 - 3 = d - 1 := by omega
    have h24 : d + 2 - 4 = d - 2 := by omega
    have h25 : d + 2 - 5 = d - 3 := by omega
    rw [h23, h24, h25]
    refine ⟨(d - 4) * (d + 2) * (d + 3) * (d + 4), ?_⟩
    ring
  · have h31 : d + 3 - 1 = d + 2 := by omega
    have h32 : d + 3 - 2 = d + 1 := by omega
    have h33 : d + 3 - 3 = d := by omega
    have h34 : d + 3 - 4 = d - 1 := by omega
    have h35 : d + 3 - 5 = d - 2 := by omega
    rw [h32, h34, h35]
    refine ⟨(d - 4) * (d - 3) * (d + 3) * (d + 4), ?_⟩
    ring
  · have h41 : d + 4 - 1 = d + 3 := by omega
    have h42 : d + 4 - 2 = d + 2 := by omega
    have h43 : d + 4 - 3 = d + 1 := by omega
    have h44 : d + 4 - 4 = d := by omega
    have h45 : d + 4 - 5 = d - 1 := by omega
    rw [h42, h43, h45]
    refine ⟨(d - 4) * (d - 3) * (d - 2) * (d + 4), ?_⟩
    ring
  · have h51 : d + 5 - 1 = d + 4 := by omega
    have h52 : d + 5 - 2 = d + 3 := by omega
    have h53 : d + 5 - 3 = d + 2 := by omega
    have h54 : d + 5 - 4 = d + 1 := by omega
    have h55 : d + 5 - 5 = d := by omega
    rw [h52, h53, h54]
    refine ⟨(d - 4) * (d - 3) * (d - 2) * (d - 1), ?_⟩
    ring

lemma k5RowDiagonalProduct_pos {d j : ℕ} (hd : 5 ≤ d)
    (hj : j ∈ Finset.Icc 1 5) :
    0 < k5RowDiagonalProduct d j := by
  apply Finset.prod_pos
  intro i hi
  have hi1 := (Finset.mem_Icc.mp hi).1
  have hj5 := (Finset.mem_Icc.mp hj).2
  omega

lemma k5ColumnDiagonalProduct_pos {d i : ℕ} (hd : 5 ≤ d)
    (hi : i ∈ Finset.Icc 1 5) :
    0 < k5ColumnDiagonalProduct d i := by
  apply Finset.prod_pos
  intro j hj
  have hi1 := (Finset.mem_Icc.mp hi).1
  have hj5 := (Finset.mem_Icc.mp hj).2
  omega

lemma k5RowDiagonalProduct_le_pow {d j : ℕ}
    (hj : j ∈ Finset.Icc 1 5) :
    k5RowDiagonalProduct d j ≤ (d + 4) ^ 5 := by
  calc
    k5RowDiagonalProduct d j ≤ ∏ _i ∈ Finset.Icc 1 5, (d + 4) := by
      apply Finset.prod_le_prod
      · intro i hi
        omega
      · intro i hi
        have hi5 := (Finset.mem_Icc.mp hi).2
        have hj1 := (Finset.mem_Icc.mp hj).1
        omega
    _ = (d + 4) ^ 5 := by norm_num [Finset.prod_Icc_succ_top]

lemma k5ColumnDiagonalProduct_le_pow {d i : ℕ}
    (hi : i ∈ Finset.Icc 1 5) :
    k5ColumnDiagonalProduct d i ≤ (d + 4) ^ 5 := by
  calc
    k5ColumnDiagonalProduct d i ≤ ∏ _j ∈ Finset.Icc 1 5, (d + 4) := by
      apply Finset.prod_le_prod
      · intro j hj
        omega
      · intro j hj
        have hi5 := (Finset.mem_Icc.mp hi).2
        have hj1 := (Finset.mem_Icc.mp hj).1
        omega
    _ = (d + 4) ^ 5 := by norm_num [Finset.prod_Icc_succ_top]

lemma k5DiagonalWindow_pos {d : ℕ} (hd : 5 ≤ d) :
    0 < k5DiagonalWindow d := by
  unfold k5DiagonalWindow
  have h4 : 0 < d - 4 := by omega
  have h3 : 0 < d - 3 := by omega
  have h2 : 0 < d - 2 := by omega
  have h1 : 0 < d - 1 := by omega
  positivity

lemma k5DiagonalWindow_le_pow {d : ℕ} :
    k5DiagonalWindow d ≤ (d + 4) ^ 9 := by
  unfold k5DiagonalWindow
  calc
    (d - 4) * (d - 3) * (d - 2) * (d - 1) * d *
        (d + 1) * (d + 2) * (d + 3) * (d + 4) ≤
        (d + 4) * (d + 4) * (d + 4) * (d + 4) * (d + 4) *
          (d + 4) * (d + 4) * (d + 4) * (d + 4) := by
      gcongr <;> omega
    _ = (d + 4) ^ 9 := by ring

/-- Two fully owned modified upper columns are coprime.  This includes a
possible distinguished column because the factor four has already been
removed in `upperTermAfterFour`. -/
theorem canonicalOwner_two_fullyOwned_modifiedUpper_columns_coprime
    {k n d t i₁ i₂ : ℕ}
    (data : CanonicalOwnerData k n d t)
    (hi₁ : i₁ ∈ Finset.Icc 1 k) (hi₂ : i₂ ∈ Finset.Icc 1 k)
    (hneq : i₁ ≠ i₂)
    (h₁ : canonicalUpperResidual data i₁ = 1)
    (h₂ : canonicalUpperResidual data i₂ = 1) :
    Nat.Coprime (upperTermAfterFour n d t i₁)
      (upperTermAfterFour n d t i₂) := by
  rw [canonical_modified_upper_term_factorization data,
    canonical_modified_upper_term_factorization data,
    h₁, h₂, one_mul, one_mul,
    ← canonicalOwner_column_cell_product data,
    ← canonicalOwner_column_cell_product data]
  apply Nat.Coprime.prod_left
  intro j₁ hj₁
  apply Nat.Coprime.prod_right
  intro j₂ hj₂
  apply canonicalOwnerCells_pairwise_coprime data
  intro heq
  have : i₁ = i₂ := congrArg Prod.snd heq
  exact hneq this

/-- A fully owned modified column divides its full five-diagonal product,
including at the distinguished divided-by-four index. -/
theorem canonicalOwner_fullyOwned_modifiedUpper_dvd_diagonalProduct
    {k n d t i : ℕ}
    (data : CanonicalOwnerData k n d t)
    (hd : k ≤ d) (hi : i ∈ Finset.Icc 1 k)
    (hfour : 4 ∣ n + d + t)
    (hupper : canonicalUpperResidual data i = 1) :
    upperTermAfterFour n d t i ∣
      ∏ j ∈ Finset.Icc 1 k, (d + i - j) := by
  rw [canonical_modified_upper_term_factorization data,
    hupper, one_mul, ← canonicalOwner_column_cell_product data]
  exact Finset.prod_dvd_prod_of_dvd _ _ fun j hj =>
    canonicalOwnerCell_dvd_shiftedDifference data hd hj hi hfour

/-- CRT product of the two independent fully owned lower-row equations. -/
theorem canonicalOwner_two_fullyOwned_lower_rows_product_dvd
    {k n d t j₁ j₂ : ℕ}
    (data : CanonicalOwnerData k n d t)
    (hd : k ≤ d)
    (hj₁ : j₁ ∈ Finset.Icc 1 k) (hj₂ : j₂ ∈ Finset.Icc 1 k)
    (hneq : j₁ ≠ j₂) (hfour : 4 ∣ n + d + t)
    (h₁ : canonicalLowerResidual data j₁ = 1)
    (h₂ : canonicalLowerResidual data j₂ = 1) :
    (n + j₁) * (n + j₂) ∣
      (∏ i ∈ Finset.Icc 1 k, (d + i - j₁)) *
        (∏ i ∈ Finset.Icc 1 k, (d + i - j₂)) := by
  have hcop : Nat.Coprime (n + j₁) (n + j₂) := by
    rcases le_total j₁ j₂ with hle | hle
    · exact (canonicalOwner_two_fullyOwned_lower_rows_coprime_offset
        data hj₁ hj₂ hneq hle h₁ h₂).1
    · exact (canonicalOwner_two_fullyOwned_lower_rows_coprime_offset
        data hj₂ hj₁ hneq.symm hle h₂ h₁).1.symm
  obtain ⟨a, ha⟩ := canonicalOwner_fullyOwned_lower_dvd_diagonalProduct
    data hd hj₁ hfour h₁
  obtain ⟨b, hb⟩ := canonicalOwner_fullyOwned_lower_dvd_diagonalProduct
    data hd hj₂ hfour h₂
  refine ⟨a * b, ?_⟩
  rw [ha, hb]
  ring

/-- CRT product of the two independent fully owned modified-column
equations. -/
theorem canonicalOwner_two_fullyOwned_modifiedUpper_product_dvd
    {k n d t i₁ i₂ : ℕ}
    (data : CanonicalOwnerData k n d t)
    (hd : k ≤ d)
    (hi₁ : i₁ ∈ Finset.Icc 1 k) (hi₂ : i₂ ∈ Finset.Icc 1 k)
    (hneq : i₁ ≠ i₂) (hfour : 4 ∣ n + d + t)
    (h₁ : canonicalUpperResidual data i₁ = 1)
    (h₂ : canonicalUpperResidual data i₂ = 1) :
    upperTermAfterFour n d t i₁ * upperTermAfterFour n d t i₂ ∣
      (∏ j ∈ Finset.Icc 1 k, (d + i₁ - j)) *
        (∏ j ∈ Finset.Icc 1 k, (d + i₂ - j)) := by
  obtain ⟨a, ha⟩ := canonicalOwner_fullyOwned_modifiedUpper_dvd_diagonalProduct
    data hd hi₁ hfour h₁
  obtain ⟨b, hb⟩ := canonicalOwner_fullyOwned_modifiedUpper_dvd_diagonalProduct
    data hd hi₂ hfour h₂
  refine ⟨a * b, ?_⟩
  rw [ha, hb]
  ring

/-- The two coprime fully owned lower terms divide one common degree-nine
diagonal window, rather than merely the product of two degree-five windows. -/
theorem k5_two_fullyOwned_lower_rows_product_dvd_diagonalWindow
    {n d t j₁ j₂ : ℕ}
    (data : CanonicalOwnerData 5 n d t) (hd : 5 ≤ d)
    (hj₁ : j₁ ∈ Finset.Icc 1 5) (hj₂ : j₂ ∈ Finset.Icc 1 5)
    (hneq : j₁ ≠ j₂) (hfour : 4 ∣ n + d + t)
    (h₁ : canonicalLowerResidual data j₁ = 1)
    (h₂ : canonicalLowerResidual data j₂ = 1) :
    (n + j₁) * (n + j₂) ∣ k5DiagonalWindow d := by
  have hcop : Nat.Coprime (n + j₁) (n + j₂) := by
    rcases le_total j₁ j₂ with hle | hle
    · exact (canonicalOwner_two_fullyOwned_lower_rows_coprime_offset
        data hj₁ hj₂ hneq hle h₁ h₂).1
    · exact (canonicalOwner_two_fullyOwned_lower_rows_coprime_offset
        data hj₂ hj₁ hneq.symm hle h₂ h₁).1.symm
  apply hcop.mul_dvd_of_dvd_of_dvd
  · exact dvd_trans
      (canonicalOwner_fullyOwned_lower_dvd_diagonalProduct
        data hd hj₁ hfour h₁)
      (k5RowDiagonalProduct_dvd_window hd hj₁)
  · exact dvd_trans
      (canonicalOwner_fullyOwned_lower_dvd_diagonalProduct
        data hd hj₂ hfour h₂)
      (k5RowDiagonalProduct_dvd_window hd hj₂)

/-- The two coprime fully owned modified upper terms likewise divide the
same degree-nine diagonal window. -/
theorem k5_two_fullyOwned_modifiedUpper_product_dvd_diagonalWindow
    {n d t i₁ i₂ : ℕ}
    (data : CanonicalOwnerData 5 n d t) (hd : 5 ≤ d)
    (hi₁ : i₁ ∈ Finset.Icc 1 5) (hi₂ : i₂ ∈ Finset.Icc 1 5)
    (hneq : i₁ ≠ i₂) (hfour : 4 ∣ n + d + t)
    (h₁ : canonicalUpperResidual data i₁ = 1)
    (h₂ : canonicalUpperResidual data i₂ = 1) :
    upperTermAfterFour n d t i₁ * upperTermAfterFour n d t i₂ ∣
      k5DiagonalWindow d := by
  have hcop := canonicalOwner_two_fullyOwned_modifiedUpper_columns_coprime
    data hi₁ hi₂ hneq h₁ h₂
  apply hcop.mul_dvd_of_dvd_of_dvd
  · exact dvd_trans
      (canonicalOwner_fullyOwned_modifiedUpper_dvd_diagonalProduct
        data hd hi₁ hfour h₁)
      (k5ColumnDiagonalProduct_dvd_window hd hi₁)
  · exact dvd_trans
      (canonicalOwner_fullyOwned_modifiedUpper_dvd_diagonalProduct
        data hd hi₂ hfour h₂)
      (k5ColumnDiagonalProduct_dvd_window hd hi₂)

/-- Proper global residuals supply two independent row moduli and two
independent modified-column moduli.  Each coprime pair divides the same
degree-nine diagonal window.  The four crossings remain nontrivial exact
gcds, so this is a simultaneous CRT elimination rather than four unrelated
one-row bounds. -/
theorem k5_proper_global_simultaneous_diagonal_window_bounds
    {n d t : ℕ} (data : CanonicalOwnerData 5 n d t)
    (ht : t ∈ Finset.Icc 1 5)
    (hfour : 4 ∣ n + d + t)
    (hblocks : upperBlockAfterFour 5 n d t = blockProduct 5 n)
    (htail : 10 ^ 1000 ≤ d)
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n)
    (hGne : canonicalOwnerResidual data ≠ 24) :
    ∃ j₁, j₁ ∈ Finset.Icc 1 5 ∧
      ∃ j₂, j₂ ∈ Finset.Icc 1 5 ∧ j₁ < j₂ ∧
      ∃ i₁, i₁ ∈ Finset.Icc 1 5 ∧
      ∃ i₂, i₂ ∈ Finset.Icc 1 5 ∧ i₁ ≠ i₂ ∧
        canonicalLowerResidual data j₁ = 1 ∧
        canonicalLowerResidual data j₂ = 1 ∧
        canonicalUpperResidual data i₁ = 1 ∧
        canonicalUpperResidual data i₂ = 1 ∧
        Nat.Coprime (n + j₁) (n + j₂) ∧
        Nat.Coprime (upperTermAfterFour n d t i₁)
          (upperTermAfterFour n d t i₂) ∧
        (n + j₁) * (n + j₂) ∣ k5DiagonalWindow d ∧
        upperTermAfterFour n d t i₁ * upperTermAfterFour n d t i₂ ∣
          k5DiagonalWindow d ∧
        Nat.lcm ((n + j₁) * (n + j₂))
          (upperTermAfterFour n d t i₁ * upperTermAfterFour n d t i₂) ∣
            k5DiagonalWindow d ∧
        (n + j₁) * (n + j₂) ≤ (d + 4) ^ 9 ∧
        upperTermAfterFour n d t i₁ * upperTermAfterFour n d t i₂ ≤
          (d + 4) ^ 9 ∧
        1 < canonicalOwnerCell data j₁ i₁ ∧
        1 < canonicalOwnerCell data j₁ i₂ ∧
        1 < canonicalOwnerCell data j₂ i₁ ∧
        1 < canonicalOwnerCell data j₂ i₂ ∧
        Nat.gcd (n + j₁) (upperTermAfterFour n d t i₁) =
          canonicalOwnerCell data j₁ i₁ ∧
        Nat.gcd (n + j₁) (upperTermAfterFour n d t i₂) =
          canonicalOwnerCell data j₁ i₂ ∧
        Nat.gcd (n + j₂) (upperTermAfterFour n d t i₁) =
          canonicalOwnerCell data j₂ i₁ ∧
        Nat.gcd (n + j₂) (upperTermAfterFour n d t i₂) =
          canonicalOwnerCell data j₂ i₂ := by
  have hfive : 5 ≤ 10 ^ 1000 := by
    rw [show 1000 = 999 + 1 by omega, pow_succ]
    have hp : 0 < 10 ^ 999 := pow_pos (by norm_num) _
    calc
      5 ≤ 1 * 10 := by norm_num
      _ ≤ 10 ^ 999 * 10 := Nat.mul_le_mul_right 10 hp
  have hd : 5 ≤ d := le_trans hfive htail
  obtain ⟨j₁, hj₁, j₂, hj₂, hjlt, hj₁one, hj₂one, hjcop,
      hoff, hgap1, hgap4⟩ :=
    k5_proper_global_two_coprime_lower_adjacent_equations data hGne
  obtain ⟨i₁, hi₁, i₂, hi₂, hine, hi₁one, hi₂one⟩ :=
    exists_two_k5_unit_upper_residuals_of_global_ne_twenty_four
      data ht hfour hblocks hGne
  have hicop := canonicalOwner_two_fullyOwned_modifiedUpper_columns_coprime
    data hi₁ hi₂ hine.symm hi₁one hi₂one
  have hrowdvd := k5_two_fullyOwned_lower_rows_product_dvd_diagonalWindow
    data hd hj₁ hj₂ hjlt.ne hfour hj₁one hj₂one
  have hcoldvd := k5_two_fullyOwned_modifiedUpper_product_dvd_diagonalWindow
    data hd hi₁ hi₂ hine.symm hfour hi₁one hi₂one
  have hlcmdvd : Nat.lcm ((n + j₁) * (n + j₂))
      (upperTermAfterFour n d t i₁ * upperTermAfterFour n d t i₂) ∣
        k5DiagonalWindow d := Nat.lcm_dvd hrowdvd hcoldvd
  have hwindowpos := k5DiagonalWindow_pos hd
  have hwindowle := k5DiagonalWindow_le_pow (d := d)
  have hrowle : (n + j₁) * (n + j₂) ≤ (d + 4) ^ 9 :=
    le_trans (Nat.le_of_dvd hwindowpos hrowdvd) hwindowle
  have hcolle : upperTermAfterFour n d t i₁ *
      upperTermAfterFour n d t i₂ ≤ (d + 4) ^ 9 :=
    le_trans (Nat.le_of_dvd hwindowpos hcoldvd) hwindowle
  have hcells := (k5_tail_complete_support_unit_cross
    data ht hfour hblocks htail heq).1
  refine ⟨j₁, hj₁, j₂, hj₂, hjlt,
    i₁, hi₁, i₂, hi₂, hine.symm,
    hj₁one, hj₂one, hi₁one, hi₂one, hjcop, hicop,
    hrowdvd, hcoldvd, hlcmdvd, hrowle, hcolle,
    hcells j₁ hj₁ i₁ hi₁, hcells j₁ hj₁ i₂ hi₂,
    hcells j₂ hj₂ i₁ hi₁, hcells j₂ hj₂ i₂ hi₂, ?_, ?_, ?_, ?_⟩
  · exact canonicalOwner_fullyOwned_gcd_modifiedUpper_eq_cell
      data hj₁ hi₁ hj₁one hi₁one
  · exact canonicalOwner_fullyOwned_gcd_modifiedUpper_eq_cell
      data hj₁ hi₂ hj₁one hi₂one
  · exact canonicalOwner_fullyOwned_gcd_modifiedUpper_eq_cell
      data hj₂ hi₁ hj₂one hi₁one
  · exact canonicalOwner_fullyOwned_gcd_modifiedUpper_eq_cell
      data hj₂ hi₂ hj₂one hi₂one

#print axioms k5_two_fullyOwned_lower_rows_product_dvd_diagonalWindow
#print axioms k5_two_fullyOwned_modifiedUpper_product_dvd_diagonalWindow
#print axioms k5_proper_global_simultaneous_diagonal_window_bounds

end Erdos686Variant
end Erdos686
