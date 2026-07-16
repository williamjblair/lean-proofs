/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686K5AllPunctures

/-!
# Erdős 686, k=5: first global consequences of complete support

The puncture theorem forces every canonical cell to be nontrivial on the
`d >= 10^1000` tail.  Since the global residual divides `4! = 24`, while it
is also the product of five positive row residuals and of five positive
column residuals, at least one residual on each side must equal one.

This supplies a fully owned row and a fully owned column.  Their crossing
cell is nontrivial.  This is the first exact global interface after the local
proper-support campaign.
-/

namespace Erdos686
namespace Erdos686Variant

open scoped BigOperators

lemma canonicalOwnerCell_pos
    {k n d t j i : ℕ} (data : CanonicalOwnerData k n d t) :
    0 < canonicalOwnerCell data j i := by
  classical
  unfold canonicalOwnerCell canonicalOwnerPrimePower
  apply Finset.prod_pos
  intro p hp
  split
  · exact pow_pos (Nat.prime_of_mem_primeFactors hp).pos _
  · norm_num

lemma canonicalOwnerRow_pos
    {k n d t j : ℕ} (data : CanonicalOwnerData k n d t) :
    0 < canonicalOwnerRow data j := by
  classical
  unfold canonicalOwnerRow canonicalOwnerPrimePower
  apply Finset.prod_pos
  intro p hp
  split
  · exact pow_pos (Nat.prime_of_mem_primeFactors hp).pos _
  · norm_num

lemma canonicalOwnerColumn_pos
    {k n d t i : ℕ} (data : CanonicalOwnerData k n d t) :
    0 < canonicalOwnerColumn data i := by
  classical
  unfold canonicalOwnerColumn canonicalOwnerPrimePower
  apply Finset.prod_pos
  intro p hp
  split
  · exact pow_pos (Nat.prime_of_mem_primeFactors hp).pos _
  · norm_num

lemma canonicalLowerResidual_pos
    {k n d t j : ℕ} (data : CanonicalOwnerData k n d t)
    (hj : j ∈ Finset.Icc 1 k) :
    0 < canonicalLowerResidual data j := by
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hterm : 0 < n + j := by omega
  have hrow := canonicalOwnerRow_pos data (j := j)
  exact Nat.div_pos
    (Nat.le_of_dvd hterm (canonicalOwnerRow_dvd_lower data)) hrow

lemma canonicalUpperResidual_pos
    {k n d t i : ℕ} (data : CanonicalOwnerData k n d t)
    (ht : t ∈ Finset.Icc 1 k) (hi : i ∈ Finset.Icc 1 k)
    (hfour : 4 ∣ n + d + t) :
    0 < canonicalUpperResidual data i := by
  have hterm := upperTermAfterFour_pos ht hi hfour
  have hcolumn := canonicalOwnerColumn_pos data (i := i)
  exact Nat.div_pos
    (Nat.le_of_dvd hterm (canonicalOwnerColumn_dvd_upper data)) hcolumn

private lemma five_factor_product_le_twenty_four_has_unit
    (f : ℕ → ℕ)
    (hpos : ∀ j ∈ Finset.Icc 1 5, 0 < f j)
    (hle : (∏ j ∈ Finset.Icc 1 5, f j) ≤ 24) :
    ∃ j, j ∈ Finset.Icc 1 5 ∧ f j = 1 := by
  by_contra hnone
  push Not at hnone
  have hall : ∀ j ∈ Finset.Icc 1 5, 2 ≤ f j := by
    intro j hj
    have hp := hpos j hj
    have hn := hnone j hj
    omega
  have hprod :
      (∏ _j ∈ Finset.Icc 1 5, 2) ≤
        ∏ j ∈ Finset.Icc 1 5, f j := by
    apply Finset.prod_le_prod
    · intro j hj
      norm_num
    · intro j hj
      exact hall j hj
  have hconst : (∏ _j ∈ Finset.Icc 1 5, 2) = 32 := by norm_num
  rw [hconst] at hprod
  omega

theorem exists_k5_unit_lower_residual
    {n d t : ℕ} (data : CanonicalOwnerData 5 n d t) :
    ∃ j, j ∈ Finset.Icc 1 5 ∧ canonicalLowerResidual data j = 1 := by
  have hGpos : 0 < canonicalOwnerResidual data := by
    classical
    unfold canonicalOwnerResidual
    apply Finset.prod_pos
    intro p hp
    exact pow_pos (Nat.prime_of_mem_primeFactors hp).pos _
  have hGle : canonicalOwnerResidual data ≤ 24 := by
    have hdvd := canonicalOwnerResidual_dvd_factorial data
    have := Nat.le_of_dvd (by norm_num : 0 < (4 : ℕ).factorial) hdvd
    norm_num at this
    exact this
  apply five_factor_product_le_twenty_four_has_unit
  · intro j hj
    exact canonicalLowerResidual_pos data hj
  · rw [canonicalLowerResidual_product_eq_global data]
    exact hGle

theorem exists_k5_unit_upper_residual
    {n d t : ℕ} (data : CanonicalOwnerData 5 n d t)
    (ht : t ∈ Finset.Icc 1 5) (hfour : 4 ∣ n + d + t)
    (hblocks : upperBlockAfterFour 5 n d t = blockProduct 5 n) :
    ∃ i, i ∈ Finset.Icc 1 5 ∧ canonicalUpperResidual data i = 1 := by
  have hGle : canonicalOwnerResidual data ≤ 24 := by
    have hdvd := canonicalOwnerResidual_dvd_factorial data
    have := Nat.le_of_dvd (by norm_num : 0 < (4 : ℕ).factorial) hdvd
    norm_num at this
    exact this
  apply five_factor_product_le_twenty_four_has_unit
  · intro i hi
    exact canonicalUpperResidual_pos data ht hi hfour
  · rw [canonicalUpperResidual_product_eq_global data hblocks]
    exact hGle

/-- Every hypothetical complete-support tail solution has a fully owned row
and a fully owned column, and every cell (including their crossing) is
strictly larger than one. -/
theorem k5_tail_complete_support_unit_cross
    {n d t : ℕ}
    (data : CanonicalOwnerData 5 n d t)
    (ht : t ∈ Finset.Icc 1 5)
    (hfour : 4 ∣ n + d + t)
    (hblocks : upperBlockAfterFour 5 n d t = blockProduct 5 n)
    (htail : 10 ^ 1000 ≤ d)
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n) :
    (∀ j ∈ Finset.Icc 1 5, ∀ i ∈ Finset.Icc 1 5,
        1 < canonicalOwnerCell data j i) ∧
      (∃ j, j ∈ Finset.Icc 1 5 ∧ canonicalLowerResidual data j = 1) ∧
      (∃ i, i ∈ Finset.Icc 1 5 ∧ canonicalUpperResidual data i = 1) := by
  have hcells :
      ∀ j ∈ Finset.Icc 1 5, ∀ i ∈ Finset.Icc 1 5,
        1 < canonicalOwnerCell data j i := by
    intro j hj i hi
    have hpos := canonicalOwnerCell_pos data (j := j) (i := i)
    have hne : canonicalOwnerCell data j i ≠ 1 := by
      intro hone
      exact no_k5_tail_solution_of_proper_support data hfour htail heq
        ⟨j, hj, i, hi, hone⟩
    omega
  exact ⟨hcells, exists_k5_unit_lower_residual data,
    exists_k5_unit_upper_residual data ht hfour hblocks⟩

/-- Fully owned crossing in the exact row/column equation form consumed by
the next global elimination step. -/
theorem k5_tail_unit_cross_factorizations
    {n d t : ℕ}
    (data : CanonicalOwnerData 5 n d t)
    (ht : t ∈ Finset.Icc 1 5)
    (hfour : 4 ∣ n + d + t)
    (hblocks : upperBlockAfterFour 5 n d t = blockProduct 5 n)
    (htail : 10 ^ 1000 ≤ d)
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n) :
    ∃ j, j ∈ Finset.Icc 1 5 ∧
      ∃ i, i ∈ Finset.Icc 1 5 ∧
        1 < canonicalOwnerCell data j i ∧
        n + j =
          ∏ i' ∈ Finset.Icc 1 5, canonicalOwnerCell data j i' ∧
        n + d + i =
          (if i = t then 4 else 1) *
            ∏ j' ∈ Finset.Icc 1 5, canonicalOwnerCell data j' i := by
  obtain ⟨hcells, ⟨j, hj, hr⟩, ⟨i, hi, hs⟩⟩ :=
    k5_tail_complete_support_unit_cross
      data ht hfour hblocks htail heq
  refine ⟨j, hj, i, hi, hcells j hj i hi, ?_, ?_⟩
  · calc
      n + j =
          canonicalLowerResidual data j * canonicalOwnerRow data j :=
        canonical_lower_term_factorization data
      _ = canonicalOwnerRow data j := by rw [hr, one_mul]
      _ = ∏ i' ∈ Finset.Icc 1 5, canonicalOwnerCell data j i' := by
        rw [canonicalOwner_row_cell_product data]
  · calc
      n + d + i =
          (if i = t then 4 else 1) *
            canonicalUpperResidual data i * canonicalOwnerColumn data i :=
        canonical_upper_term_factorization data hfour
      _ = (if i = t then 4 else 1) * canonicalOwnerColumn data i := by
        rw [hs, mul_one]
      _ = (if i = t then 4 else 1) *
            ∏ j' ∈ Finset.Icc 1 5, canonicalOwnerCell data j' i := by
        rw [canonicalOwner_column_cell_product data]

#print axioms exists_k5_unit_lower_residual
#print axioms exists_k5_unit_upper_residual
#print axioms k5_tail_complete_support_unit_cross
#print axioms k5_tail_unit_cross_factorizations

end Erdos686Variant
end Erdos686
