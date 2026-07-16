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

private lemma proper_divisor_twenty_four_le_twelve
    {G : ℕ} (hdvd : G ∣ 24) (hne : G ≠ 24) :
    G ≤ 12 := by
  have hle : G ≤ 24 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases G <;> norm_num at hdvd
  all_goals omega

private lemma sixteen_le_four_factor_product
    {a b c d : ℕ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d) :
    16 ≤ a * b * c * d := by
  calc
    16 = (2 * 2) * (2 * 2) := by norm_num
    _ ≤ (a * b) * (c * d) :=
      Nat.mul_le_mul (Nat.mul_le_mul ha hb) (Nat.mul_le_mul hc hd)
    _ = a * b * c * d := by ring

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

/-- Unless the total residual is the exceptional divisor `24`, the five
lower residuals contain two distinct units.  Thus the proper-divisor branch
supplies two independent fully owned row equations. -/
theorem exists_two_k5_unit_lower_residuals_of_global_ne_twenty_four
    {n d t : ℕ} (data : CanonicalOwnerData 5 n d t)
    (hGne : canonicalOwnerResidual data ≠ 24) :
    ∃ j, j ∈ Finset.Icc 1 5 ∧
      ∃ j', j' ∈ Finset.Icc 1 5 ∧ j' ≠ j ∧
        canonicalLowerResidual data j = 1 ∧
        canonicalLowerResidual data j' = 1 := by
  obtain ⟨j, hj, hjone⟩ := exists_k5_unit_lower_residual data
  by_cases hsecond :
      ∃ j', j' ∈ Finset.Icc 1 5 ∧ j' ≠ j ∧
        canonicalLowerResidual data j' = 1
  · obtain ⟨j', hj', hne, hj'one⟩ := hsecond
    exact ⟨j, hj, j', hj', hne, hjone, hj'one⟩
  · exfalso
    have hge :
        ∀ j', j' ∈ Finset.Icc 1 5 → j' ≠ j →
          2 ≤ canonicalLowerResidual data j' := by
      intro j' hj' hne
      have hpos := canonicalLowerResidual_pos data hj'
      have hnotone : canonicalLowerResidual data j' ≠ 1 := by
        intro hone
        exact hsecond ⟨j', hj', hne, hone⟩
      omega
    have hGle : canonicalOwnerResidual data ≤ 12 :=
      proper_divisor_twenty_four_le_twelve
        (canonicalOwnerResidual_dvd_factorial data) hGne
    have hprod := canonicalLowerResidual_product_eq_global data
    norm_num [Finset.prod_Icc_succ_top] at hprod
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hj5 : j ≤ 5 := (Finset.mem_Icc.mp hj).2
    interval_cases j
    · have h2 := hge 2 (by norm_num) (by omega)
      have h3 := hge 3 (by norm_num) (by omega)
      have h4 := hge 4 (by norm_num) (by omega)
      have h5 := hge 5 (by norm_num) (by omega)
      simp only [hjone, one_mul] at hprod
      have hlower : 16 ≤ canonicalOwnerResidual data := by
        rw [← hprod]
        exact sixteen_le_four_factor_product h2 h3 h4 h5
      omega
    · have h1 := hge 1 (by norm_num) (by omega)
      have h3 := hge 3 (by norm_num) (by omega)
      have h4 := hge 4 (by norm_num) (by omega)
      have h5 := hge 5 (by norm_num) (by omega)
      simp only [hjone, mul_one] at hprod
      have hlower : 16 ≤ canonicalOwnerResidual data := by
        rw [← hprod]
        exact sixteen_le_four_factor_product h1 h3 h4 h5
      omega
    · have h1 := hge 1 (by norm_num) (by omega)
      have h2 := hge 2 (by norm_num) (by omega)
      have h4 := hge 4 (by norm_num) (by omega)
      have h5 := hge 5 (by norm_num) (by omega)
      simp only [hjone, mul_one] at hprod
      have hlower : 16 ≤ canonicalOwnerResidual data := by
        rw [← hprod]
        exact sixteen_le_four_factor_product h1 h2 h4 h5
      omega
    · have h1 := hge 1 (by norm_num) (by omega)
      have h2 := hge 2 (by norm_num) (by omega)
      have h3 := hge 3 (by norm_num) (by omega)
      have h5 := hge 5 (by norm_num) (by omega)
      simp only [hjone, mul_one] at hprod
      have hlower : 16 ≤ canonicalOwnerResidual data := by
        rw [← hprod]
        exact sixteen_le_four_factor_product h1 h2 h3 h5
      omega
    · have h1 := hge 1 (by norm_num) (by omega)
      have h2 := hge 2 (by norm_num) (by omega)
      have h3 := hge 3 (by norm_num) (by omega)
      have h4 := hge 4 (by norm_num) (by omega)
      simp only [hjone, mul_one] at hprod
      have hlower : 16 ≤ canonicalOwnerResidual data := by
        rw [← hprod]
        exact sixteen_le_four_factor_product h1 h2 h3 h4
      omega

/-- Unless the total residual is `24`, the modified upper residuals also
contain two distinct units, supplying two independent fully owned column
equations. -/
theorem exists_two_k5_unit_upper_residuals_of_global_ne_twenty_four
    {n d t : ℕ} (data : CanonicalOwnerData 5 n d t)
    (ht : t ∈ Finset.Icc 1 5) (hfour : 4 ∣ n + d + t)
    (hblocks : upperBlockAfterFour 5 n d t = blockProduct 5 n)
    (hGne : canonicalOwnerResidual data ≠ 24) :
    ∃ i, i ∈ Finset.Icc 1 5 ∧
      ∃ i', i' ∈ Finset.Icc 1 5 ∧ i' ≠ i ∧
        canonicalUpperResidual data i = 1 ∧
        canonicalUpperResidual data i' = 1 := by
  obtain ⟨i, hi, hione⟩ :=
    exists_k5_unit_upper_residual data ht hfour hblocks
  by_cases hsecond :
      ∃ i', i' ∈ Finset.Icc 1 5 ∧ i' ≠ i ∧
        canonicalUpperResidual data i' = 1
  · obtain ⟨i', hi', hne, hi'one⟩ := hsecond
    exact ⟨i, hi, i', hi', hne, hione, hi'one⟩
  · exfalso
    have hge :
        ∀ i', i' ∈ Finset.Icc 1 5 → i' ≠ i →
          2 ≤ canonicalUpperResidual data i' := by
      intro i' hi' hne
      have hpos := canonicalUpperResidual_pos data ht hi' hfour
      have hnotone : canonicalUpperResidual data i' ≠ 1 := by
        intro hone
        exact hsecond ⟨i', hi', hne, hone⟩
      omega
    have hGle : canonicalOwnerResidual data ≤ 12 :=
      proper_divisor_twenty_four_le_twelve
        (canonicalOwnerResidual_dvd_factorial data) hGne
    have hprod :=
      canonicalUpperResidual_product_eq_global data hblocks
    norm_num [Finset.prod_Icc_succ_top] at hprod
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    have hi5 : i ≤ 5 := (Finset.mem_Icc.mp hi).2
    interval_cases i
    · have h2 := hge 2 (by norm_num) (by omega)
      have h3 := hge 3 (by norm_num) (by omega)
      have h4 := hge 4 (by norm_num) (by omega)
      have h5 := hge 5 (by norm_num) (by omega)
      simp only [hione, one_mul] at hprod
      have hlower : 16 ≤ canonicalOwnerResidual data := by
        rw [← hprod]
        exact sixteen_le_four_factor_product h2 h3 h4 h5
      omega
    · have h1 := hge 1 (by norm_num) (by omega)
      have h3 := hge 3 (by norm_num) (by omega)
      have h4 := hge 4 (by norm_num) (by omega)
      have h5 := hge 5 (by norm_num) (by omega)
      simp only [hione, mul_one] at hprod
      have hlower : 16 ≤ canonicalOwnerResidual data := by
        rw [← hprod]
        exact sixteen_le_four_factor_product h1 h3 h4 h5
      omega
    · have h1 := hge 1 (by norm_num) (by omega)
      have h2 := hge 2 (by norm_num) (by omega)
      have h4 := hge 4 (by norm_num) (by omega)
      have h5 := hge 5 (by norm_num) (by omega)
      simp only [hione, mul_one] at hprod
      have hlower : 16 ≤ canonicalOwnerResidual data := by
        rw [← hprod]
        exact sixteen_le_four_factor_product h1 h2 h4 h5
      omega
    · have h1 := hge 1 (by norm_num) (by omega)
      have h2 := hge 2 (by norm_num) (by omega)
      have h3 := hge 3 (by norm_num) (by omega)
      have h5 := hge 5 (by norm_num) (by omega)
      simp only [hione, mul_one] at hprod
      have hlower : 16 ≤ canonicalOwnerResidual data := by
        rw [← hprod]
        exact sixteen_le_four_factor_product h1 h2 h3 h5
      omega
    · have h1 := hge 1 (by norm_num) (by omega)
      have h2 := hge 2 (by norm_num) (by omega)
      have h3 := hge 3 (by norm_num) (by omega)
      have h4 := hge 4 (by norm_num) (by omega)
      simp only [hione, mul_one] at hprod
      have hlower : 16 ≤ canonicalOwnerResidual data := by
        rw [← hprod]
        exact sixteen_le_four_factor_product h1 h2 h3 h4
      omega

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
#print axioms exists_two_k5_unit_lower_residuals_of_global_ne_twenty_four
#print axioms exists_two_k5_unit_upper_residuals_of_global_ne_twenty_four
#print axioms k5_tail_complete_support_unit_cross
#print axioms k5_tail_unit_cross_factorizations

end Erdos686Variant
end Erdos686
