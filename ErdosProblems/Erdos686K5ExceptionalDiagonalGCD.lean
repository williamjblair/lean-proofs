/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686K5CompleteSupportArithmetic

/-!
# Erdős 686, k=5: exact diagonal gcd stars in the exceptional branch

The exceptional unit row has five owner factors coprime to six.  Distinct
shifted diagonals in that row differ by at most four.  Consequently no owner
from one diagonal can divide another diagonal, and every one of the five
owner divisibilities upgrades to an exact gcd.
-/

namespace Erdos686
namespace Erdos686Variant

open scoped BigOperators

private lemma canonicalOwnerCell_coprime_other_row_diagonal
    {n d t j h i : ℕ} (data : CanonicalOwnerData 5 n d t)
    (hd : 5 ≤ d) (hj : j ∈ Finset.Icc 1 5)
    (hh : h ∈ Finset.Icc 1 5) (hi : i ∈ Finset.Icc 1 5)
    (hne : h ≠ i) (hfour : 4 ∣ n + d + t)
    (hcop : Nat.Coprime (canonicalOwnerCell data j h) 6) :
    Nat.Coprime (canonicalOwnerCell data j h) (d + i - j) := by
  let g := Nat.gcd (canonicalOwnerCell data j h) (d + i - j)
  have hgOwner : g ∣ canonicalOwnerCell data j h := Nat.gcd_dvd_left _ _
  have hgTarget : g ∣ d + i - j := Nat.gcd_dvd_right _ _
  have hgSource : g ∣ d + h - j := dvd_trans hgOwner
    (canonicalOwnerCell_dvd_shiftedDifference data hd hj hh hfour)
  have hgCop : Nat.Coprime g 6 := hcop.of_dvd_left hgOwner
  have hg4 : g ≤ 4 := by
    rcases lt_or_gt_of_ne hne with hhi | hih
    · have hdiff : (d + i - j) - (d + h - j) = i - h := by
        have hj5 := (Finset.mem_Icc.mp hj).2
        omega
      have hgap : g ∣ i - h := by
        rw [← hdiff]
        exact Nat.dvd_sub hgTarget hgSource
      have hgapPos : 0 < i - h := by omega
      have hle := Nat.le_of_dvd hgapPos hgap
      have hi5 := (Finset.mem_Icc.mp hi).2
      have hh1 := (Finset.mem_Icc.mp hh).1
      omega
    · have hdiff : (d + h - j) - (d + i - j) = h - i := by
        have hj5 := (Finset.mem_Icc.mp hj).2
        omega
      have hgap : g ∣ h - i := by
        rw [← hdiff]
        exact Nat.dvd_sub hgSource hgTarget
      have hgapPos : 0 < h - i := by omega
      have hle := Nat.le_of_dvd hgapPos hgap
      have hh5 := (Finset.mem_Icc.mp hh).2
      have hi1 := (Finset.mem_Icc.mp hi).1
      omega
  change g = 1
  interval_cases g
  · norm_num [Nat.Coprime] at hgCop
  · rfl
  · norm_num [Nat.Coprime] at hgCop
  · norm_num [Nat.Coprime] at hgCop
  · norm_num [Nat.Coprime] at hgCop

/-- In a fully owned row whose five owner factors are coprime to six, every
owner is the exact gcd of the row term with its shifted diagonal. -/
theorem canonicalOwner_fullyOwned_row_exact_shifted_gcds_of_coprime_six
    {n d t j : ℕ} (data : CanonicalOwnerData 5 n d t)
    (hd : 5 ≤ d) (hj : j ∈ Finset.Icc 1 5)
    (hfour : 4 ∣ n + d + t)
    (hlower : canonicalLowerResidual data j = 1)
    (hcop : ∀ i ∈ Finset.Icc 1 5,
      Nat.Coprime (canonicalOwnerCell data j i) 6) :
    ∀ i ∈ Finset.Icc 1 5,
      Nat.gcd (n + j) (d + i - j) = canonicalOwnerCell data j i := by
  intro i hi
  let rest := ∏ h ∈ (Finset.Icc 1 5).erase i,
    canonicalOwnerCell data j h
  have hrow : n + j = canonicalOwnerCell data j i * rest := by
    calc
      n + j = canonicalOwnerRow data j := by
        rw [canonical_lower_term_factorization data, hlower, one_mul]
      _ = ∏ h ∈ Finset.Icc 1 5, canonicalOwnerCell data j h := by
        rw [canonicalOwner_row_cell_product data]
      _ = canonicalOwnerCell data j i * rest := by
        rw [← Finset.mul_prod_erase (Finset.Icc 1 5)
          (fun h => canonicalOwnerCell data j h) hi]
  have hrestCop : Nat.Coprime rest (d + i - j) := by
    dsimp [rest]
    apply Nat.Coprime.prod_left
    intro h hh
    exact canonicalOwnerCell_coprime_other_row_diagonal data hd hj
      (Finset.mem_of_mem_erase hh) hi (Finset.ne_of_mem_erase hh) hfour
      (hcop h (Finset.mem_of_mem_erase hh))
  apply Nat.dvd_antisymm
  · have hgTarget : Nat.gcd (n + j) (d + i - j) ∣ d + i - j :=
      Nat.gcd_dvd_right _ _
    have hgRest : Nat.Coprime (Nat.gcd (n + j) (d + i - j)) rest :=
      (hrestCop.coprime_dvd_right hgTarget).symm
    apply hgRest.dvd_of_dvd_mul_right
    rw [← hrow]
    exact Nat.gcd_dvd_left _ _
  · exact Nat.dvd_gcd (canonicalOwnerCell_dvd_lower data)
      (canonicalOwnerCell_dvd_shiftedDifference data hd hj hi hfour)

private lemma canonicalOwnerCell_coprime_other_column_diagonal
    {n d t i h j : ℕ} (data : CanonicalOwnerData 5 n d t)
    (hd : 5 ≤ d) (hi : i ∈ Finset.Icc 1 5)
    (hh : h ∈ Finset.Icc 1 5) (hj : j ∈ Finset.Icc 1 5)
    (hne : h ≠ j) (hfour : 4 ∣ n + d + t)
    (hcop : Nat.Coprime (canonicalOwnerCell data h i) 6) :
    Nat.Coprime (canonicalOwnerCell data h i) (d + i - j) := by
  let g := Nat.gcd (canonicalOwnerCell data h i) (d + i - j)
  have hgOwner : g ∣ canonicalOwnerCell data h i := Nat.gcd_dvd_left _ _
  have hgTarget : g ∣ d + i - j := Nat.gcd_dvd_right _ _
  have hgSource : g ∣ d + i - h := dvd_trans hgOwner
    (canonicalOwnerCell_dvd_shiftedDifference data hd hh hi hfour)
  have hgCop : Nat.Coprime g 6 := hcop.of_dvd_left hgOwner
  have hg4 : g ≤ 4 := by
    rcases lt_or_gt_of_ne hne with hhj | hjh
    · have hdiff : (d + i - h) - (d + i - j) = j - h := by
        have hi1 := (Finset.mem_Icc.mp hi).1
        have hh5 := (Finset.mem_Icc.mp hh).2
        have hj5 := (Finset.mem_Icc.mp hj).2
        omega
      have hgap : g ∣ j - h := by
        rw [← hdiff]
        exact Nat.dvd_sub hgSource hgTarget
      have hgapPos : 0 < j - h := by omega
      have hle := Nat.le_of_dvd hgapPos hgap
      have hj5 := (Finset.mem_Icc.mp hj).2
      have hh1 := (Finset.mem_Icc.mp hh).1
      omega
    · have hdiff : (d + i - j) - (d + i - h) = h - j := by
        have hi1 := (Finset.mem_Icc.mp hi).1
        have hh5 := (Finset.mem_Icc.mp hh).2
        have hj5 := (Finset.mem_Icc.mp hj).2
        omega
      have hgap : g ∣ h - j := by
        rw [← hdiff]
        exact Nat.dvd_sub hgTarget hgSource
      have hgapPos : 0 < h - j := by omega
      have hle := Nat.le_of_dvd hgapPos hgap
      have hh5 := (Finset.mem_Icc.mp hh).2
      have hj1 := (Finset.mem_Icc.mp hj).1
      omega
  change g = 1
  interval_cases g
  · norm_num [Nat.Coprime] at hgCop
  · rfl
  · norm_num [Nat.Coprime] at hgCop
  · norm_num [Nat.Coprime] at hgCop
  · norm_num [Nat.Coprime] at hgCop

/-- The column analogue: in a fully owned nondistinguished column whose
owner factors are coprime to six, every owner is the exact gcd of the upper
term with its shifted diagonal. -/
theorem canonicalOwner_fullyOwned_column_exact_shifted_gcds_of_coprime_six
    {n d t i : ℕ} (data : CanonicalOwnerData 5 n d t)
    (hd : 5 ≤ d) (hi : i ∈ Finset.Icc 1 5) (hit : i ≠ t)
    (hfour : 4 ∣ n + d + t)
    (hupper : canonicalUpperResidual data i = 1)
    (hcop : ∀ j ∈ Finset.Icc 1 5,
      Nat.Coprime (canonicalOwnerCell data j i) 6) :
    ∀ j ∈ Finset.Icc 1 5,
      Nat.gcd (n + d + i) (d + i - j) = canonicalOwnerCell data j i := by
  intro j hj
  let rest := ∏ h ∈ (Finset.Icc 1 5).erase j,
    canonicalOwnerCell data h i
  have hcolumn : n + d + i = canonicalOwnerCell data j i * rest := by
    calc
      n + d + i = canonicalOwnerColumn data i := by
        have hfactor := canonical_upper_term_factorization data hfour (i := i)
        simp only [if_neg hit, one_mul, hupper] at hfactor
        exact hfactor
      _ = ∏ h ∈ Finset.Icc 1 5, canonicalOwnerCell data h i := by
        rw [canonicalOwner_column_cell_product data]
      _ = canonicalOwnerCell data j i * rest := by
        rw [← Finset.mul_prod_erase (Finset.Icc 1 5)
          (fun h => canonicalOwnerCell data h i) hj]
  have hrestCop : Nat.Coprime rest (d + i - j) := by
    dsimp [rest]
    apply Nat.Coprime.prod_left
    intro h hh
    exact canonicalOwnerCell_coprime_other_column_diagonal data hd hi
      (Finset.mem_of_mem_erase hh) hj (Finset.ne_of_mem_erase hh) hfour
      (hcop h (Finset.mem_of_mem_erase hh))
  apply Nat.dvd_antisymm
  · have hgTarget : Nat.gcd (n + d + i) (d + i - j) ∣ d + i - j :=
      Nat.gcd_dvd_right _ _
    have hgRest : Nat.Coprime (Nat.gcd (n + d + i) (d + i - j)) rest :=
      (hrestCop.coprime_dvd_right hgTarget).symm
    apply hgRest.dvd_of_dvd_mul_right
    rw [← hcolumn]
    exact Nat.gcd_dvd_left _ _
  · exact Nat.dvd_gcd
      (dvd_trans (canonicalOwnerCell_dvd_upper data)
        (upperTermAfterFour_dvd_original hfour))
      (canonicalOwnerCell_dvd_shiftedDifference data hd hj hi hfour)

/-- The exact exceptional upper placement makes whichever even column is
fully owned coprime to six. -/
theorem k5_exceptional_unit_upper_terms_coprime_six
    {n d t : ℕ} (data : CanonicalOwnerData 5 n d t)
    (ht : t ∈ Finset.Icc 1 5) (hfour : 4 ∣ n + d + t)
    (hprofile : K5ExceptionalResidualProfile (canonicalUpperResidual data)) :
    (canonicalUpperResidual data 2 = 1 → Nat.Coprime (n + d + 2) 6) ∧
    (canonicalUpperResidual data 4 = 1 → Nat.Coprime (n + d + 4) 6) := by
  have hu := k5_exceptional_upper_exact_mod_twenty_four
    data ht hfour hprofile
  constructor
  · intro hunit
    rcases hu with hu | hu | hu | hu | hu | hu
    · apply Nat.coprime_of_mul_modEq_one 1
      change ((n + d + 2) * 1) % 6 = 1 % 6
      omega
    · apply Nat.coprime_of_mul_modEq_one 1
      change ((n + d + 2) * 1) % 6 = 1 % 6
      omega
    · apply Nat.coprime_of_mul_modEq_one 1
      change ((n + d + 2) * 1) % 6 = 1 % 6
      omega
    · omega
    · omega
    · omega
  · intro hunit
    rcases hu with hu | hu | hu | hu | hu | hu
    · omega
    · omega
    · omega
    · apply Nat.coprime_of_mul_modEq_one 5
      change ((n + d + 4) * 5) % 6 = 1 % 6
      omega
    · apply Nat.coprime_of_mul_modEq_one 5
      change ((n + d + 4) * 5) % 6 = 1 % 6
      omega
    · apply Nat.coprime_of_mul_modEq_one 5
      change ((n + d + 4) * 5) % 6 = 1 % 6
      omega

private lemma five_le_of_k5_tail {d : ℕ} (htail : 10 ^ 1000 ≤ d) : 5 ≤ d := by
  have hfive : 5 ≤ 10 ^ 1000 := by
    rw [show 1000 = 999 + 1 by omega, pow_succ]
    have hp0 : 0 < (10 : ℕ) ^ 999 := pow_pos (by norm_num) _
    have hp : 1 ≤ (10 : ℕ) ^ 999 := hp0
    calc
      5 ≤ 1 * 10 := by norm_num
      _ ≤ 10 ^ 999 * 10 := Nat.mul_le_mul_right 10 hp
  exact le_trans hfive htail

/-- The exceptional four-crossing residual upgrades to an exact nine-cell
gcd star: all five cells in the unit row and all five cells in the unit
column (with the crossing counted twice) are exact shifted gcds. -/
theorem k5_exceptional_exact_shifted_gcd_star
    {n d t : ℕ} (data : CanonicalOwnerData 5 n d t)
    (ht : t ∈ Finset.Icc 1 5)
    (hfour : 4 ∣ n + d + t)
    (hblocks : upperBlockAfterFour 5 n d t = blockProduct 5 n)
    (htail : 10 ^ 1000 ≤ d)
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n)
    (hlower : K5ExceptionalResidualProfile (canonicalLowerResidual data))
    (hupper : K5ExceptionalResidualProfile (canonicalUpperResidual data)) :
    (d % 6 = 0 ∧
      (∀ i ∈ Finset.Icc 1 5,
        Nat.gcd (n + 2) (d + i - 2) = canonicalOwnerCell data 2 i) ∧
      (∀ j ∈ Finset.Icc 1 5,
        Nat.gcd (n + d + 2) (d + 2 - j) = canonicalOwnerCell data j 2)) ∨
    (d % 6 = 2 ∧
      (∀ i ∈ Finset.Icc 1 5,
        Nat.gcd (n + 2) (d + i - 2) = canonicalOwnerCell data 2 i) ∧
      (∀ j ∈ Finset.Icc 1 5,
        Nat.gcd (n + d + 4) (d + 4 - j) = canonicalOwnerCell data j 4)) ∨
    (d % 6 = 4 ∧
      (∀ i ∈ Finset.Icc 1 5,
        Nat.gcd (n + 4) (d + i - 4) = canonicalOwnerCell data 4 i) ∧
      (∀ j ∈ Finset.Icc 1 5,
        Nat.gcd (n + d + 2) (d + 2 - j) = canonicalOwnerCell data j 2)) ∨
    (d % 6 = 0 ∧
      (∀ i ∈ Finset.Icc 1 5,
        Nat.gcd (n + 4) (d + i - 4) = canonicalOwnerCell data 4 i) ∧
      (∀ j ∈ Finset.Icc 1 5,
        Nat.gcd (n + d + 4) (d + 4 - j) = canonicalOwnerCell data j 4)) := by
  have hd : 5 ≤ d := five_le_of_k5_tail htail
  have hcross := k5_exceptional_exact_unit_crossing_constraints
    data ht hfour hblocks htail heq hlower hupper
  have hupperCop := k5_exceptional_unit_upper_terms_coprime_six
    data ht hfour hupper
  rcases hcross with hc | hc | hc | hc
  · left
    rcases hc.2 with
      ⟨hit, hl, hu, -, -, hrowFactors, -, -, -⟩
    have hrow := canonicalOwner_fullyOwned_row_exact_shifted_gcds_of_coprime_six
      data hd (by norm_num) hfour hl
      (fun i hi => (hrowFactors i hi).2.1)
    have htermCop := hupperCop.1 hu
    have hcolumn :=
      canonicalOwner_fullyOwned_column_exact_shifted_gcds_of_coprime_six
        data hd (by norm_num) hit hfour hu
        (fun j _ => htermCop.of_dvd_left
          (dvd_trans (canonicalOwnerCell_dvd_upper data)
            (upperTermAfterFour_dvd_original hfour)))
    exact ⟨hc.1, hrow, hcolumn⟩
  · right; left
    rcases hc.2 with
      ⟨hit, hl, hu, -, -, hrowFactors, -, -, -⟩
    have hrow := canonicalOwner_fullyOwned_row_exact_shifted_gcds_of_coprime_six
      data hd (by norm_num) hfour hl
      (fun i hi => (hrowFactors i hi).2.1)
    have htermCop := hupperCop.2 hu
    have hcolumn :=
      canonicalOwner_fullyOwned_column_exact_shifted_gcds_of_coprime_six
        data hd (by norm_num) hit hfour hu
        (fun j _ => htermCop.of_dvd_left
          (dvd_trans (canonicalOwnerCell_dvd_upper data)
            (upperTermAfterFour_dvd_original hfour)))
    exact ⟨hc.1, hrow, hcolumn⟩
  · right; right; left
    rcases hc.2 with
      ⟨hit, hl, hu, -, -, hrowFactors, -, -, -⟩
    have hrow := canonicalOwner_fullyOwned_row_exact_shifted_gcds_of_coprime_six
      data hd (by norm_num) hfour hl
      (fun i hi => (hrowFactors i hi).2.1)
    have htermCop := hupperCop.1 hu
    have hcolumn :=
      canonicalOwner_fullyOwned_column_exact_shifted_gcds_of_coprime_six
        data hd (by norm_num) hit hfour hu
        (fun j _ => htermCop.of_dvd_left
          (dvd_trans (canonicalOwnerCell_dvd_upper data)
            (upperTermAfterFour_dvd_original hfour)))
    exact ⟨hc.1, hrow, hcolumn⟩
  · right; right; right
    rcases hc.2 with
      ⟨hit, hl, hu, -, -, hrowFactors, -, -, -⟩
    have hrow := canonicalOwner_fullyOwned_row_exact_shifted_gcds_of_coprime_six
      data hd (by norm_num) hfour hl
      (fun i hi => (hrowFactors i hi).2.1)
    have htermCop := hupperCop.2 hu
    have hcolumn :=
      canonicalOwner_fullyOwned_column_exact_shifted_gcds_of_coprime_six
        data hd (by norm_num) hit hfour hu
        (fun j _ => htermCop.of_dvd_left
          (dvd_trans (canonicalOwnerCell_dvd_upper data)
            (upperTermAfterFour_dvd_original hfour)))
    exact ⟨hc.1, hrow, hcolumn⟩

/-- Multiplying an exact fully owned row/column gcd star eliminates the
owner cells completely and recovers the two arithmetic terms. -/
theorem canonicalOwner_exact_gcd_star_products_eq_terms
    {n d t j i : ℕ} (data : CanonicalOwnerData 5 n d t)
    (hd : 5 ≤ d) (hj : j ∈ Finset.Icc 1 5) (hi : i ∈ Finset.Icc 1 5)
    (hit : i ≠ t) (hfour : 4 ∣ n + d + t)
    (hlower : canonicalLowerResidual data j = 1)
    (hupper : canonicalUpperResidual data i = 1)
    (hrowCop : ∀ i' ∈ Finset.Icc 1 5,
      Nat.Coprime (canonicalOwnerCell data j i') 6)
    (hcolumnCop : ∀ j' ∈ Finset.Icc 1 5,
      Nat.Coprime (canonicalOwnerCell data j' i) 6) :
    (∏ i' ∈ Finset.Icc 1 5, Nat.gcd (n + j) (d + i' - j)) = n + j ∧
    (∏ j' ∈ Finset.Icc 1 5, Nat.gcd (n + d + i) (d + i - j')) =
      n + d + i := by
  have hrow := canonicalOwner_fullyOwned_row_exact_shifted_gcds_of_coprime_six
    data hd hj hfour hlower hrowCop
  have hcolumn :=
    canonicalOwner_fullyOwned_column_exact_shifted_gcds_of_coprime_six
      data hd hi hit hfour hupper hcolumnCop
  constructor
  · calc
      (∏ i' ∈ Finset.Icc 1 5, Nat.gcd (n + j) (d + i' - j)) =
          ∏ i' ∈ Finset.Icc 1 5, canonicalOwnerCell data j i' := by
            apply Finset.prod_congr rfl
            intro i' hi'
            exact hrow i' hi'
      _ = canonicalOwnerRow data j := canonicalOwner_row_cell_product data
      _ = n + j := by
        rw [canonical_lower_term_factorization data, hlower, one_mul]
  · calc
      (∏ j' ∈ Finset.Icc 1 5, Nat.gcd (n + d + i) (d + i - j')) =
          ∏ j' ∈ Finset.Icc 1 5, canonicalOwnerCell data j' i := by
            apply Finset.prod_congr rfl
            intro j' hj'
            exact hcolumn j' hj'
      _ = canonicalOwnerColumn data i := canonicalOwner_column_cell_product data
      _ = n + d + i := by
        have hfactor := canonical_upper_term_factorization data hfour (i := i)
        simp only [if_neg hit, one_mul, hupper] at hfactor
        exact hfactor.symm

/-- Pure arithmetic exceptional residual.  The owner matrix has disappeared:
one of four fixed `d mod 6` cases must satisfy simultaneous five-gcd product
identities for the corresponding lower and upper terms. -/
theorem k5_exceptional_pure_gcd_product_residual
    {n d t : ℕ} (data : CanonicalOwnerData 5 n d t)
    (ht : t ∈ Finset.Icc 1 5)
    (hfour : 4 ∣ n + d + t)
    (hblocks : upperBlockAfterFour 5 n d t = blockProduct 5 n)
    (htail : 10 ^ 1000 ≤ d)
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n)
    (hlower : K5ExceptionalResidualProfile (canonicalLowerResidual data))
    (hupper : K5ExceptionalResidualProfile (canonicalUpperResidual data)) :
    (d % 6 = 0 ∧
      (∏ i ∈ Finset.Icc 1 5, Nat.gcd (n + 2) (d + i - 2)) = n + 2 ∧
      (∏ j ∈ Finset.Icc 1 5, Nat.gcd (n + d + 2) (d + 2 - j)) =
        n + d + 2) ∨
    (d % 6 = 2 ∧
      (∏ i ∈ Finset.Icc 1 5, Nat.gcd (n + 2) (d + i - 2)) = n + 2 ∧
      (∏ j ∈ Finset.Icc 1 5, Nat.gcd (n + d + 4) (d + 4 - j)) =
        n + d + 4) ∨
    (d % 6 = 4 ∧
      (∏ i ∈ Finset.Icc 1 5, Nat.gcd (n + 4) (d + i - 4)) = n + 4 ∧
      (∏ j ∈ Finset.Icc 1 5, Nat.gcd (n + d + 2) (d + 2 - j)) =
        n + d + 2) ∨
    (d % 6 = 0 ∧
      (∏ i ∈ Finset.Icc 1 5, Nat.gcd (n + 4) (d + i - 4)) = n + 4 ∧
      (∏ j ∈ Finset.Icc 1 5, Nat.gcd (n + d + 4) (d + 4 - j)) =
        n + d + 4) := by
  have hd : 5 ≤ d := five_le_of_k5_tail htail
  have hcross := k5_exceptional_exact_unit_crossing_constraints
    data ht hfour hblocks htail heq hlower hupper
  have hupperCop := k5_exceptional_unit_upper_terms_coprime_six
    data ht hfour hupper
  rcases hcross with hc | hc | hc | hc
  · left
    rcases hc.2 with
      ⟨hit, hl, hu, -, -, hrowFactors, -, -, -⟩
    have htermCop := hupperCop.1 hu
    obtain ⟨hrow, hcolumn⟩ := canonicalOwner_exact_gcd_star_products_eq_terms
      data hd (by norm_num) (by norm_num) hit hfour hl hu
      (fun i hi => (hrowFactors i hi).2.1)
      (fun j _ => htermCop.of_dvd_left
        (dvd_trans (canonicalOwnerCell_dvd_upper data)
          (upperTermAfterFour_dvd_original hfour)))
    exact ⟨hc.1, hrow, hcolumn⟩
  · right; left
    rcases hc.2 with
      ⟨hit, hl, hu, -, -, hrowFactors, -, -, -⟩
    have htermCop := hupperCop.2 hu
    obtain ⟨hrow, hcolumn⟩ := canonicalOwner_exact_gcd_star_products_eq_terms
      data hd (by norm_num) (by norm_num) hit hfour hl hu
      (fun i hi => (hrowFactors i hi).2.1)
      (fun j _ => htermCop.of_dvd_left
        (dvd_trans (canonicalOwnerCell_dvd_upper data)
          (upperTermAfterFour_dvd_original hfour)))
    exact ⟨hc.1, hrow, hcolumn⟩
  · right; right; left
    rcases hc.2 with
      ⟨hit, hl, hu, -, -, hrowFactors, -, -, -⟩
    have htermCop := hupperCop.1 hu
    obtain ⟨hrow, hcolumn⟩ := canonicalOwner_exact_gcd_star_products_eq_terms
      data hd (by norm_num) (by norm_num) hit hfour hl hu
      (fun i hi => (hrowFactors i hi).2.1)
      (fun j _ => htermCop.of_dvd_left
        (dvd_trans (canonicalOwnerCell_dvd_upper data)
          (upperTermAfterFour_dvd_original hfour)))
    exact ⟨hc.1, hrow, hcolumn⟩
  · right; right; right
    rcases hc.2 with
      ⟨hit, hl, hu, -, -, hrowFactors, -, -, -⟩
    have htermCop := hupperCop.2 hu
    obtain ⟨hrow, hcolumn⟩ := canonicalOwner_exact_gcd_star_products_eq_terms
      data hd (by norm_num) (by norm_num) hit hfour hl hu
      (fun i hi => (hrowFactors i hi).2.1)
      (fun j _ => htermCop.of_dvd_left
        (dvd_trans (canonicalOwnerCell_dvd_upper data)
          (upperTermAfterFour_dvd_original hfour)))
    exact ⟨hc.1, hrow, hcolumn⟩

#print axioms canonicalOwner_fullyOwned_row_exact_shifted_gcds_of_coprime_six
#print axioms canonicalOwner_fullyOwned_column_exact_shifted_gcds_of_coprime_six
#print axioms k5_exceptional_unit_upper_terms_coprime_six
#print axioms k5_exceptional_exact_shifted_gcd_star
#print axioms canonicalOwner_exact_gcd_star_products_eq_terms
#print axioms k5_exceptional_pure_gcd_product_residual

end Erdos686Variant
end Erdos686
