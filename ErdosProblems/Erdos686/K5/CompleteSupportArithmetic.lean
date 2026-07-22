/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.K5.AllPunctures

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

private lemma eight_le_three_factor_product
    {a b c : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    8 ≤ a * b * c := by
  calc
    8 = (2 * 2) * 2 := by norm_num
    _ ≤ (a * b) * c :=
      Nat.mul_le_mul (Nat.mul_le_mul ha hb) hc
    _ = a * b * c := by ring

private lemma four_factor_product_eq_twenty_four_profile
    {a b c d : ℕ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d)
    (hprod : a * b * c * d = 24) :
    (a = 3 ∧ b = 2 ∧ c = 2 ∧ d = 2) ∨
    (a = 2 ∧ b = 3 ∧ c = 2 ∧ d = 2) ∨
    (a = 2 ∧ b = 2 ∧ c = 3 ∧ d = 2) ∨
    (a = 2 ∧ b = 2 ∧ c = 2 ∧ d = 3) := by
  have ha8 : 8 * a ≤ a * b * c * d := by
    have h8 := Nat.mul_le_mul_left a
      (eight_le_three_factor_product hb hc hd)
    nlinarith
  have hb8 : 8 * b ≤ a * b * c * d := by
    have h8 := Nat.mul_le_mul_left b
      (eight_le_three_factor_product ha hc hd)
    nlinarith
  have hc8 : 8 * c ≤ a * b * c * d := by
    have h8 := Nat.mul_le_mul_left c
      (eight_le_three_factor_product ha hb hd)
    nlinarith
  have hd8 : 8 * d ≤ a * b * c * d := by
    have h8 := Nat.mul_le_mul_left d
      (eight_le_three_factor_product ha hb hc)
    nlinarith
  have ha3 : a ≤ 3 := by omega
  have hb3 : b ≤ 3 := by omega
  have hc3 : c ≤ 3 := by omega
  have hd3 : d ≤ 3 := by omega
  interval_cases a
  all_goals interval_cases b
  all_goals interval_cases c
  all_goals interval_cases d
  all_goals norm_num at hprod
  all_goals norm_num

/-- The exact exceptional five-residual multiset: one unit, three twos, and
one three. -/
def K5ExceptionalResidualProfile (f : ℕ → ℕ) : Prop :=
  ((Finset.Icc 1 5).filter (fun r => f r = 1)).card = 1 ∧
  ((Finset.Icc 1 5).filter (fun r => f r = 2)).card = 3 ∧
  ((Finset.Icc 1 5).filter (fun r => f r = 3)).card = 1

private lemma Icc_one_five_eq :
    Finset.Icc 1 5 = ({1, 2, 3, 4, 5} : Finset ℕ) := by
  decide

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

/-- At global residual `24`, either two distinct lower residuals are units
or the entire lower residual vector has the exact exceptional multiset
`{1,2,2,2,3}`. -/
theorem k5_lower_residual_profile_of_global_eq_twenty_four
    {n d t : ℕ} (data : CanonicalOwnerData 5 n d t)
    (hG : canonicalOwnerResidual data = 24) :
    (∃ j, j ∈ Finset.Icc 1 5 ∧
      ∃ j', j' ∈ Finset.Icc 1 5 ∧ j' ≠ j ∧
        canonicalLowerResidual data j = 1 ∧
        canonicalLowerResidual data j' = 1) ∨
      K5ExceptionalResidualProfile (canonicalLowerResidual data) := by
  obtain ⟨j, hj, hjone⟩ := exists_k5_unit_lower_residual data
  by_cases hsecond :
      ∃ j', j' ∈ Finset.Icc 1 5 ∧ j' ≠ j ∧
        canonicalLowerResidual data j' = 1
  · obtain ⟨j', hj', hne, hj'one⟩ := hsecond
    exact Or.inl ⟨j, hj, j', hj', hne, hjone, hj'one⟩
  · right
    have hge :
        ∀ j', j' ∈ Finset.Icc 1 5 → j' ≠ j →
          2 ≤ canonicalLowerResidual data j' := by
      intro j' hj' hne
      have hpos := canonicalLowerResidual_pos data hj'
      have hnotone : canonicalLowerResidual data j' ≠ 1 := by
        intro hone
        exact hsecond ⟨j', hj', hne, hone⟩
      omega
    have hprod := canonicalLowerResidual_product_eq_global data
    rw [hG] at hprod
    norm_num [Finset.prod_Icc_succ_top] at hprod
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hj5 : j ≤ 5 := (Finset.mem_Icc.mp hj).2
    interval_cases j
    · have hp := four_factor_product_eq_twenty_four_profile
        (hge 2 (by norm_num) (by omega))
        (hge 3 (by norm_num) (by omega))
        (hge 4 (by norm_num) (by omega))
        (hge 5 (by norm_num) (by omega))
        (by simpa [hjone] using hprod)
      rcases hp with hp | hp | hp | hp <;>
        simp_all [K5ExceptionalResidualProfile, Icc_one_five_eq,
          Finset.filter_insert, Finset.filter_singleton]
    · have hp := four_factor_product_eq_twenty_four_profile
        (hge 1 (by norm_num) (by omega))
        (hge 3 (by norm_num) (by omega))
        (hge 4 (by norm_num) (by omega))
        (hge 5 (by norm_num) (by omega))
        (by simpa [hjone] using hprod)
      rcases hp with hp | hp | hp | hp <;>
        simp_all [K5ExceptionalResidualProfile, Icc_one_five_eq,
          Finset.filter_insert, Finset.filter_singleton]
    · have hp := four_factor_product_eq_twenty_four_profile
        (hge 1 (by norm_num) (by omega))
        (hge 2 (by norm_num) (by omega))
        (hge 4 (by norm_num) (by omega))
        (hge 5 (by norm_num) (by omega))
        (by simpa [hjone] using hprod)
      rcases hp with hp | hp | hp | hp <;>
        simp_all [K5ExceptionalResidualProfile, Icc_one_five_eq,
          Finset.filter_insert, Finset.filter_singleton]
    · have hp := four_factor_product_eq_twenty_four_profile
        (hge 1 (by norm_num) (by omega))
        (hge 2 (by norm_num) (by omega))
        (hge 3 (by norm_num) (by omega))
        (hge 5 (by norm_num) (by omega))
        (by simpa [hjone] using hprod)
      rcases hp with hp | hp | hp | hp <;>
        simp_all [K5ExceptionalResidualProfile, Icc_one_five_eq,
          Finset.filter_insert, Finset.filter_singleton]
    · have hp := four_factor_product_eq_twenty_four_profile
        (hge 1 (by norm_num) (by omega))
        (hge 2 (by norm_num) (by omega))
        (hge 3 (by norm_num) (by omega))
        (hge 4 (by norm_num) (by omega))
        (by simpa [hjone] using hprod)
      rcases hp with hp | hp | hp | hp <;>
        simp_all [K5ExceptionalResidualProfile, Icc_one_five_eq,
          Finset.filter_insert, Finset.filter_singleton]

/-- At global residual `24`, either two distinct modified upper residuals
are units or the upper residual vector has the same exact exceptional
multiset `{1,2,2,2,3}`. -/
theorem k5_upper_residual_profile_of_global_eq_twenty_four
    {n d t : ℕ} (data : CanonicalOwnerData 5 n d t)
    (ht : t ∈ Finset.Icc 1 5) (hfour : 4 ∣ n + d + t)
    (hblocks : upperBlockAfterFour 5 n d t = blockProduct 5 n)
    (hG : canonicalOwnerResidual data = 24) :
    (∃ i, i ∈ Finset.Icc 1 5 ∧
      ∃ i', i' ∈ Finset.Icc 1 5 ∧ i' ≠ i ∧
        canonicalUpperResidual data i = 1 ∧
        canonicalUpperResidual data i' = 1) ∨
      K5ExceptionalResidualProfile (canonicalUpperResidual data) := by
  obtain ⟨i, hi, hione⟩ :=
    exists_k5_unit_upper_residual data ht hfour hblocks
  by_cases hsecond :
      ∃ i', i' ∈ Finset.Icc 1 5 ∧ i' ≠ i ∧
        canonicalUpperResidual data i' = 1
  · obtain ⟨i', hi', hne, hi'one⟩ := hsecond
    exact Or.inl ⟨i, hi, i', hi', hne, hione, hi'one⟩
  · right
    have hge :
        ∀ i', i' ∈ Finset.Icc 1 5 → i' ≠ i →
          2 ≤ canonicalUpperResidual data i' := by
      intro i' hi' hne
      have hpos := canonicalUpperResidual_pos data ht hi' hfour
      have hnotone : canonicalUpperResidual data i' ≠ 1 := by
        intro hone
        exact hsecond ⟨i', hi', hne, hone⟩
      omega
    have hprod := canonicalUpperResidual_product_eq_global data hblocks
    rw [hG] at hprod
    norm_num [Finset.prod_Icc_succ_top] at hprod
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    have hi5 : i ≤ 5 := (Finset.mem_Icc.mp hi).2
    interval_cases i
    · have hp := four_factor_product_eq_twenty_four_profile
        (hge 2 (by norm_num) (by omega))
        (hge 3 (by norm_num) (by omega))
        (hge 4 (by norm_num) (by omega))
        (hge 5 (by norm_num) (by omega))
        (by simpa [hione] using hprod)
      rcases hp with hp | hp | hp | hp <;>
        simp_all [K5ExceptionalResidualProfile, Icc_one_five_eq,
          Finset.filter_insert, Finset.filter_singleton]
    · have hp := four_factor_product_eq_twenty_four_profile
        (hge 1 (by norm_num) (by omega))
        (hge 3 (by norm_num) (by omega))
        (hge 4 (by norm_num) (by omega))
        (hge 5 (by norm_num) (by omega))
        (by simpa [hione] using hprod)
      rcases hp with hp | hp | hp | hp <;>
        simp_all [K5ExceptionalResidualProfile, Icc_one_five_eq,
          Finset.filter_insert, Finset.filter_singleton]
    · have hp := four_factor_product_eq_twenty_four_profile
        (hge 1 (by norm_num) (by omega))
        (hge 2 (by norm_num) (by omega))
        (hge 4 (by norm_num) (by omega))
        (hge 5 (by norm_num) (by omega))
        (by simpa [hione] using hprod)
      rcases hp with hp | hp | hp | hp <;>
        simp_all [K5ExceptionalResidualProfile, Icc_one_five_eq,
          Finset.filter_insert, Finset.filter_singleton]
    · have hp := four_factor_product_eq_twenty_four_profile
        (hge 1 (by norm_num) (by omega))
        (hge 2 (by norm_num) (by omega))
        (hge 3 (by norm_num) (by omega))
        (hge 5 (by norm_num) (by omega))
        (by simpa [hione] using hprod)
      rcases hp with hp | hp | hp | hp <;>
        simp_all [K5ExceptionalResidualProfile, Icc_one_five_eq,
          Finset.filter_insert, Finset.filter_singleton]
    · have hp := four_factor_product_eq_twenty_four_profile
        (hge 1 (by norm_num) (by omega))
        (hge 2 (by norm_num) (by omega))
        (hge 3 (by norm_num) (by omega))
        (hge 4 (by norm_num) (by omega))
        (by simpa [hione] using hprod)
      rcases hp with hp | hp | hp | hp <;>
        simp_all [K5ExceptionalResidualProfile, Icc_one_five_eq,
          Finset.filter_insert, Finset.filter_singleton]

/-- The gcd of one canonical row product and one canonical column product is
exactly their crossing cell.  All other factors are pairwise coprime across
the two erased products. -/
theorem canonicalOwner_row_column_gcd_eq_cell
    {k n d t j i : ℕ}
    (data : CanonicalOwnerData k n d t)
    (hj : j ∈ Finset.Icc 1 k) (hi : i ∈ Finset.Icc 1 k) :
    Nat.gcd
      (∏ i' ∈ Finset.Icc 1 k, canonicalOwnerCell data j i')
      (∏ j' ∈ Finset.Icc 1 k, canonicalOwnerCell data j' i) =
        canonicalOwnerCell data j i := by
  classical
  let rowRest :=
    ∏ i' ∈ (Finset.Icc 1 k).erase i, canonicalOwnerCell data j i'
  let columnRest :=
    ∏ j' ∈ (Finset.Icc 1 k).erase j, canonicalOwnerCell data j' i
  have hcop : Nat.Coprime rowRest columnRest := by
    dsimp [rowRest, columnRest]
    apply Nat.Coprime.prod_left
    intro i' hi'
    have hi'ne : i' ≠ i := (Finset.mem_erase.mp hi').1
    apply Nat.Coprime.prod_right
    intro j' hj'
    apply canonicalOwnerCells_pairwise_coprime data
    intro heq
    have hii : i' = i := congrArg Prod.snd heq
    exact hi'ne hii
  rw [← Finset.mul_prod_erase (Finset.Icc 1 k)
      (fun i' => canonicalOwnerCell data j i') hi,
    ← Finset.mul_prod_erase (Finset.Icc 1 k)
      (fun j' => canonicalOwnerCell data j' i) hj]
  change Nat.gcd (canonicalOwnerCell data j i * rowRest)
      (canonicalOwnerCell data j i * columnRest) =
    canonicalOwnerCell data j i
  rw [Nat.gcd_mul_left, hcop.gcd_eq_one, mul_one]

/-- A fully owned lower row and fully owned modified upper column expose
their crossing owner as an exact gcd of the two arithmetic terms. -/
theorem canonicalOwner_fullyOwned_gcd_modifiedUpper_eq_cell
    {k n d t j i : ℕ}
    (data : CanonicalOwnerData k n d t)
    (hj : j ∈ Finset.Icc 1 k) (hi : i ∈ Finset.Icc 1 k)
    (hlower : canonicalLowerResidual data j = 1)
    (hupper : canonicalUpperResidual data i = 1) :
    Nat.gcd (n + j) (upperTermAfterFour n d t i) =
      canonicalOwnerCell data j i := by
  rw [canonical_lower_term_factorization data,
    canonical_modified_upper_term_factorization data,
    hlower, hupper, one_mul, one_mul,
    ← canonicalOwner_row_cell_product data,
    ← canonicalOwner_column_cell_product data]
  exact canonicalOwner_row_column_gcd_eq_cell data hj hi

/-- Away from the distinguished column, the modified upper term is the
original consecutive upper term, so the crossing cell is its exact gcd with
the fully owned lower term. -/
theorem canonicalOwner_fullyOwned_gcd_upper_eq_cell_of_ne
    {k n d t j i : ℕ}
    (data : CanonicalOwnerData k n d t)
    (hj : j ∈ Finset.Icc 1 k) (hi : i ∈ Finset.Icc 1 k)
    (hit : i ≠ t)
    (hlower : canonicalLowerResidual data j = 1)
    (hupper : canonicalUpperResidual data i = 1) :
    Nat.gcd (n + j) (n + d + i) =
      canonicalOwnerCell data j i := by
  simpa [upperTermAfterFour, hit] using
    canonicalOwner_fullyOwned_gcd_modifiedUpper_eq_cell
      data hj hi hlower hupper

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

/-- Off the exceptional global residual `24`, complete support yields a
`2 x 2` grid of nontrivial crossings whose four arithmetic gcds are exactly
the four canonical owner cells. -/
theorem k5_tail_proper_global_two_by_two_gcd_grid
    {n d t : ℕ}
    (data : CanonicalOwnerData 5 n d t)
    (ht : t ∈ Finset.Icc 1 5)
    (hfour : 4 ∣ n + d + t)
    (hblocks : upperBlockAfterFour 5 n d t = blockProduct 5 n)
    (htail : 10 ^ 1000 ≤ d)
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n)
    (hGne : canonicalOwnerResidual data ≠ 24) :
    ∃ j₁, j₁ ∈ Finset.Icc 1 5 ∧
      ∃ j₂, j₂ ∈ Finset.Icc 1 5 ∧ j₂ ≠ j₁ ∧
      ∃ i₁, i₁ ∈ Finset.Icc 1 5 ∧
      ∃ i₂, i₂ ∈ Finset.Icc 1 5 ∧ i₂ ≠ i₁ ∧
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
  obtain ⟨hcells, -, -⟩ :=
    k5_tail_complete_support_unit_cross
      data ht hfour hblocks htail heq
  obtain ⟨j₁, hj₁, j₂, hj₂, hjne, hj₁one, hj₂one⟩ :=
    exists_two_k5_unit_lower_residuals_of_global_ne_twenty_four data hGne
  obtain ⟨i₁, hi₁, i₂, hi₂, hine, hi₁one, hi₂one⟩ :=
    exists_two_k5_unit_upper_residuals_of_global_ne_twenty_four
      data ht hfour hblocks hGne
  refine ⟨j₁, hj₁, j₂, hj₂, hjne, i₁, hi₁, i₂, hi₂, hine,
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

/-- Since two distinct fully owned upper columns exist off `G=24`, at least
one is not distinguished.  One original upper consecutive term therefore
has two coprime nontrivial exact gcds with two distinct lower consecutive
terms. -/
theorem k5_tail_proper_global_common_upper_two_coprime_gcds
    {n d t : ℕ}
    (data : CanonicalOwnerData 5 n d t)
    (ht : t ∈ Finset.Icc 1 5)
    (hfour : 4 ∣ n + d + t)
    (hblocks : upperBlockAfterFour 5 n d t = blockProduct 5 n)
    (htail : 10 ^ 1000 ≤ d)
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n)
    (hGne : canonicalOwnerResidual data ≠ 24) :
    ∃ j₁, j₁ ∈ Finset.Icc 1 5 ∧
      ∃ j₂, j₂ ∈ Finset.Icc 1 5 ∧ j₂ ≠ j₁ ∧
      ∃ i, i ∈ Finset.Icc 1 5 ∧ i ≠ t ∧
        1 < Nat.gcd (n + j₁) (n + d + i) ∧
        1 < Nat.gcd (n + j₂) (n + d + i) ∧
        Nat.Coprime
          (Nat.gcd (n + j₁) (n + d + i))
          (Nat.gcd (n + j₂) (n + d + i)) := by
  obtain ⟨hcells, -, -⟩ :=
    k5_tail_complete_support_unit_cross
      data ht hfour hblocks htail heq
  obtain ⟨j₁, hj₁, j₂, hj₂, hjne, hj₁one, hj₂one⟩ :=
    exists_two_k5_unit_lower_residuals_of_global_ne_twenty_four data hGne
  obtain ⟨i₁, hi₁, i₂, hi₂, hine, hi₁one, hi₂one⟩ :=
    exists_two_k5_unit_upper_residuals_of_global_ne_twenty_four
      data ht hfour hblocks hGne
  obtain ⟨i, hi, hit, hione⟩ :
      ∃ i, i ∈ Finset.Icc 1 5 ∧ i ≠ t ∧
        canonicalUpperResidual data i = 1 := by
    by_cases hi₁t : i₁ = t
    · refine ⟨i₂, hi₂, ?_, hi₂one⟩
      intro hi₂t
      exact hine (hi₂t.trans hi₁t.symm)
    · exact ⟨i₁, hi₁, hi₁t, hi₁one⟩
  have hg₁ := canonicalOwner_fullyOwned_gcd_upper_eq_cell_of_ne
    data hj₁ hi hit hj₁one hione
  have hg₂ := canonicalOwner_fullyOwned_gcd_upper_eq_cell_of_ne
    data hj₂ hi hit hj₂one hione
  refine ⟨j₁, hj₁, j₂, hj₂, hjne, i, hi, hit, ?_, ?_, ?_⟩
  · rw [hg₁]
    exact hcells j₁ hj₁ i hi
  · rw [hg₂]
    exact hcells j₂ hj₂ i hi
  · rw [hg₁, hg₂]
    apply canonicalOwnerCells_pairwise_coprime data
    intro hequal
    have hj : j₁ = j₂ := congrArg Prod.fst hequal
    exact hjne hj.symm

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

private theorem three_residual_twos_force_base_odd
    {base : ℕ} {f : ℕ → ℕ}
    (hthree : ((Finset.Icc 1 5).filter (fun j => f j = 2)).card = 3)
    (hdvd : ∀ j, j ∈ Finset.Icc 1 5 → f j ∣ base + j) :
    base % 2 = 1 := by
  have hmodlt : base % 2 < 2 := Nat.mod_lt _ (by norm_num)
  by_contra hnot
  have hmod0 : base % 2 = 0 := by omega
  have h2base : 2 ∣ base := (Nat.dvd_iff_mod_eq_zero).mpr hmod0
  have hsubset :
      (Finset.Icc 1 5).filter (fun j => f j = 2) ⊆
        ({2, 4} : Finset ℕ) := by
    intro j hj
    have hjparts := Finset.mem_filter.mp hj
    have hjIcc := hjparts.1
    have hfj : f j = 2 := hjparts.2
    have h2term : 2 ∣ base + j := by
      simpa [hfj] using hdvd j hjIcc
    have h2j : 2 ∣ j := by
      have hbase_le : base ≤ base + j := Nat.le_add_right _ _
      have := Nat.dvd_sub h2term h2base
      simpa [Nat.add_sub_cancel_left] using this
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hjIcc).1
    have hj5 : j ≤ 5 := (Finset.mem_Icc.mp hjIcc).2
    interval_cases j <;> simp_all
  have hcard := Finset.card_le_card hsubset
  rw [hthree] at hcard
  norm_num at hcard

/-- An exceptional lower residual profile forces the lower block base to be
odd: three residual factors equal two, but an even base has only the two even
positions `2` and `4`. -/
theorem k5_exceptional_lower_base_odd
    {n d t : ℕ} (data : CanonicalOwnerData 5 n d t)
    (hprofile : K5ExceptionalResidualProfile (canonicalLowerResidual data)) :
    n % 2 = 1 := by
  apply three_residual_twos_force_base_odd hprofile.2.1
  intro j hj
  refine ⟨canonicalOwnerRow data j, ?_⟩
  exact canonical_lower_term_factorization data

/-- The same parity count on the modified upper residuals forces the original
upper block base `n+d` to be odd. -/
theorem k5_exceptional_upper_base_odd
    {n d t : ℕ} (data : CanonicalOwnerData 5 n d t)
    (hfour : 4 ∣ n + d + t)
    (hprofile : K5ExceptionalResidualProfile (canonicalUpperResidual data)) :
    (n + d) % 2 = 1 := by
  apply three_residual_twos_force_base_odd hprofile.2.1
  intro i hi
  exact dvd_trans
    ⟨canonicalOwnerColumn data i,
      canonical_modified_upper_term_factorization data⟩
    (upperTermAfterFour_dvd_original hfour)

/-- If both sides of the exceptional `G=24` branch have profile
`{1,2,2,2,3}`, then the gap is even. -/
theorem k5_exceptional_both_force_even_gap
    {n d t : ℕ} (data : CanonicalOwnerData 5 n d t)
    (hfour : 4 ∣ n + d + t)
    (hlower : K5ExceptionalResidualProfile (canonicalLowerResidual data))
    (hupper : K5ExceptionalResidualProfile (canonicalUpperResidual data)) :
    2 ∣ d := by
  have hn := k5_exceptional_lower_base_odd data hlower
  have hnd := k5_exceptional_upper_base_odd data hfour hupper
  omega

private theorem residual_twos_eq_odd_positions
    {base : ℕ} {f : ℕ → ℕ}
    (hodd : base % 2 = 1)
    (hthree : ((Finset.Icc 1 5).filter (fun j => f j = 2)).card = 3)
    (hdvd : ∀ j, j ∈ Finset.Icc 1 5 → f j ∣ base + j) :
    (Finset.Icc 1 5).filter (fun j => f j = 2) = {1, 3, 5} := by
  have hsubset :
      (Finset.Icc 1 5).filter (fun j => f j = 2) ⊆
        ({1, 3, 5} : Finset ℕ) := by
    intro j hj
    have hjparts := Finset.mem_filter.mp hj
    have hjIcc := hjparts.1
    have hfj : f j = 2 := hjparts.2
    have h2term : 2 ∣ base + j := by
      simpa [hfj] using hdvd j hjIcc
    have hsum0 : (base + j) % 2 = 0 :=
      (Nat.dvd_iff_mod_eq_zero).mp h2term
    rw [Nat.add_mod, hodd] at hsum0
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hjIcc).1
    have hj5 : j ≤ 5 := (Finset.mem_Icc.mp hjIcc).2
    interval_cases j <;> norm_num at hsum0 <;> simp
  apply Finset.eq_of_subset_of_card_le hsubset
  simpa [hthree]

/-- In an exceptional lower profile, the three residual factors equal to two
occur exactly at the odd block positions. -/
theorem k5_exceptional_lower_twos_eq_odd_positions
    {n d t : ℕ} (data : CanonicalOwnerData 5 n d t)
    (hprofile : K5ExceptionalResidualProfile (canonicalLowerResidual data)) :
    (Finset.Icc 1 5).filter
        (fun j => canonicalLowerResidual data j = 2) = {1, 3, 5} := by
  apply residual_twos_eq_odd_positions
    (k5_exceptional_lower_base_odd data hprofile) hprofile.2.1
  intro j hj
  exact ⟨canonicalOwnerRow data j, canonical_lower_term_factorization data⟩

/-- In an exceptional upper profile, the three residual factors equal to two
also occur exactly at the odd original upper-block positions. -/
theorem k5_exceptional_upper_twos_eq_odd_positions
    {n d t : ℕ} (data : CanonicalOwnerData 5 n d t)
    (hfour : 4 ∣ n + d + t)
    (hprofile : K5ExceptionalResidualProfile (canonicalUpperResidual data)) :
    (Finset.Icc 1 5).filter
        (fun i => canonicalUpperResidual data i = 2) = {1, 3, 5} := by
  apply residual_twos_eq_odd_positions
    (k5_exceptional_upper_base_odd data hfour hprofile) hprofile.2.1
  intro i hi
  exact dvd_trans
    ⟨canonicalOwnerColumn data i,
      canonical_modified_upper_term_factorization data⟩
    (upperTermAfterFour_dvd_original hfour)

/-- The distinguished divided-by-four upper position in an exceptional
profile is one of the odd positions and has residual exactly two. -/
theorem k5_exceptional_upper_residual_two_at_distinguished
    {n d t : ℕ} (data : CanonicalOwnerData 5 n d t)
    (ht : t ∈ Finset.Icc 1 5)
    (hfour : 4 ∣ n + d + t)
    (hprofile : K5ExceptionalResidualProfile (canonicalUpperResidual data)) :
    canonicalUpperResidual data t = 2 := by
  have hodd := k5_exceptional_upper_base_odd data hfour hprofile
  have heq :=
    k5_exceptional_upper_twos_eq_odd_positions data hfour hprofile
  have htodd : t ∈ ({1, 3, 5} : Finset ℕ) := by
    have hbaseodd : (n + d) % 2 = 1 := hodd
    have h2sum : 2 ∣ n + d + t := dvd_trans (by norm_num) hfour
    have hsum0 : (n + d + t) % 2 = 0 :=
      (Nat.dvd_iff_mod_eq_zero).mp h2sum
    rw [Nat.add_mod, hbaseodd] at hsum0
    have ht1 : 1 ≤ t := (Finset.mem_Icc.mp ht).1
    have ht5 : t ≤ 5 := (Finset.mem_Icc.mp ht).2
    interval_cases t <;> norm_num at hsum0 <;> simp
  have : t ∈ (Finset.Icc 1 5).filter
      (fun i => canonicalUpperResidual data i = 2) := by
    rw [heq]
    exact htodd
  exact (Finset.mem_filter.mp this).2

/-- The exceptional upper profile upgrades the distinguished divisibility
from four to eight. -/
theorem k5_exceptional_upper_eight_dvd_distinguished
    {n d t : ℕ} (data : CanonicalOwnerData 5 n d t)
    (ht : t ∈ Finset.Icc 1 5)
    (hfour : 4 ∣ n + d + t)
    (hprofile : K5ExceptionalResidualProfile (canonicalUpperResidual data)) :
    8 ∣ n + d + t := by
  have htwo := k5_exceptional_upper_residual_two_at_distinguished
    data ht hfour hprofile
  rw [canonical_upper_term_factorization data hfour, if_pos rfl, htwo]
  exact dvd_mul_right 8 (canonicalOwnerColumn data t)

private theorem exceptional_profile_even_allocation
    {f : ℕ → ℕ}
    (hprofile : K5ExceptionalResidualProfile f)
    (htwos : (Finset.Icc 1 5).filter (fun j => f j = 2) = {1, 3, 5}) :
    (f 2 = 1 ∧ f 4 = 3) ∨ (f 2 = 3 ∧ f 4 = 1) := by
  have hf1 : f 1 = 2 := by
    have : 1 ∈ (Finset.Icc 1 5).filter (fun j => f j = 2) := by
      rw [htwos]
      simp
    exact (Finset.mem_filter.mp this).2
  have hf3 : f 3 = 2 := by
    have : 3 ∈ (Finset.Icc 1 5).filter (fun j => f j = 2) := by
      rw [htwos]
      simp
    exact (Finset.mem_filter.mp this).2
  have hf5 : f 5 = 2 := by
    have : 5 ∈ (Finset.Icc 1 5).filter (fun j => f j = 2) := by
      rw [htwos]
      simp
    exact (Finset.mem_filter.mp this).2
  rcases hprofile with ⟨hone, _, hthree⟩
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hone
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hthree
  have haMem : a ∈ (Finset.Icc 1 5).filter (fun j => f j = 1) := by
    rw [ha]
    simp
  have hbMem : b ∈ (Finset.Icc 1 5).filter (fun j => f j = 3) := by
    rw [hb]
    simp
  have haIcc := (Finset.mem_filter.mp haMem).1
  have hfa := (Finset.mem_filter.mp haMem).2
  have hbIcc := (Finset.mem_filter.mp hbMem).1
  have hfb := (Finset.mem_filter.mp hbMem).2
  have ha1 : 1 ≤ a := (Finset.mem_Icc.mp haIcc).1
  have ha5 : a ≤ 5 := (Finset.mem_Icc.mp haIcc).2
  have hb1 : 1 ≤ b := (Finset.mem_Icc.mp hbIcc).1
  have hb5 : b ≤ 5 := (Finset.mem_Icc.mp hbIcc).2
  interval_cases a <;> interval_cases b <;> simp_all

private theorem exceptional_even_allocation_mod_three
    {base : ℕ} {f : ℕ → ℕ}
    (halloc : (f 2 = 1 ∧ f 4 = 3) ∨ (f 2 = 3 ∧ f 4 = 1))
    (hdvd : ∀ j, j ∈ Finset.Icc 1 5 → f j ∣ base + j) :
    (base % 3 = 2 ∧ f 2 = 1 ∧ f 4 = 3) ∨
      (base % 3 = 1 ∧ f 2 = 3 ∧ f 4 = 1) := by
  rcases halloc with halloc | halloc
  · left
    refine ⟨?_, halloc⟩
    have h3 : 3 ∣ base + 4 := by
      simpa [halloc.2] using hdvd 4 (by norm_num)
    have hmod : (base + 4) % 3 = 0 :=
      Nat.dvd_iff_mod_eq_zero.mp h3
    rw [Nat.add_mod] at hmod
    have := Nat.mod_lt base (by norm_num : 0 < 3)
    omega
  · right
    refine ⟨?_, halloc⟩
    have h3 : 3 ∣ base + 2 := by
      simpa [halloc.1] using hdvd 2 (by norm_num)
    have hmod : (base + 2) % 3 = 0 :=
      Nat.dvd_iff_mod_eq_zero.mp h3
    rw [Nat.add_mod] at hmod
    have := Nat.mod_lt base (by norm_num : 0 < 3)
    omega

private theorem eight_dvd_odd_offset_mod_eight
    {base t : ℕ}
    (htodd : t ∈ ({1, 3, 5} : Finset ℕ))
    (h8 : 8 ∣ base + t) :
    (t = 1 ∧ base % 8 = 7) ∨
      (t = 3 ∧ base % 8 = 5) ∨
      (t = 5 ∧ base % 8 = 3) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at htodd
  rcases htodd with rfl | rfl | rfl
  · left
    refine ⟨rfl, ?_⟩
    have hmod : (base + 1) % 8 = 0 := Nat.dvd_iff_mod_eq_zero.mp h8
    rw [Nat.add_mod] at hmod
    have := Nat.mod_lt base (by norm_num : 0 < 8)
    omega
  · right; left
    refine ⟨rfl, ?_⟩
    have hmod : (base + 3) % 8 = 0 := Nat.dvd_iff_mod_eq_zero.mp h8
    rw [Nat.add_mod] at hmod
    have := Nat.mod_lt base (by norm_num : 0 < 8)
    omega
  · right; right
    refine ⟨rfl, ?_⟩
    have hmod : (base + 5) % 8 = 0 := Nat.dvd_iff_mod_eq_zero.mp h8
    rw [Nat.add_mod] at hmod
    have := Nat.mod_lt base (by norm_num : 0 < 8)
    omega

/-- The exceptional lower profile has an exact even-position allocation.
The position carrying the residual `3` also determines the lower base
modulo six. -/
theorem k5_exceptional_lower_even_allocation_mod_six
    {n d t : ℕ} (data : CanonicalOwnerData 5 n d t)
    (hprofile : K5ExceptionalResidualProfile (canonicalLowerResidual data)) :
    (n % 6 = 5 ∧ canonicalLowerResidual data 2 = 1 ∧
        canonicalLowerResidual data 4 = 3) ∨
      (n % 6 = 1 ∧ canonicalLowerResidual data 2 = 3 ∧
        canonicalLowerResidual data 4 = 1) := by
  have halloc := exceptional_profile_even_allocation hprofile
    (k5_exceptional_lower_twos_eq_odd_positions data hprofile)
  have hmod3 := exceptional_even_allocation_mod_three halloc
    (fun j hj =>
      ⟨canonicalOwnerRow data j,
        canonical_lower_term_factorization data⟩)
  have hodd := k5_exceptional_lower_base_odd data hprofile
  rcases hmod3 with hmod3 | hmod3
  · left
    refine ⟨?_, hmod3.2⟩
    omega
  · right
    refine ⟨?_, hmod3.2⟩
    omega

/-- On the upper side, the even-position allocation modulo three and the
distinguished eight-divisibility combine by CRT.  This gives the exact six
possible placements modulo `24`, with no floating or search assumption. -/
theorem k5_exceptional_upper_exact_mod_twenty_four
    {n d t : ℕ} (data : CanonicalOwnerData 5 n d t)
    (ht : t ∈ Finset.Icc 1 5)
    (hfour : 4 ∣ n + d + t)
    (hprofile : K5ExceptionalResidualProfile (canonicalUpperResidual data)) :
    (t = 1 ∧ (n + d) % 24 = 23 ∧
        canonicalUpperResidual data 2 = 1 ∧
        canonicalUpperResidual data 4 = 3) ∨
      (t = 3 ∧ (n + d) % 24 = 5 ∧
        canonicalUpperResidual data 2 = 1 ∧
        canonicalUpperResidual data 4 = 3) ∨
      (t = 5 ∧ (n + d) % 24 = 11 ∧
        canonicalUpperResidual data 2 = 1 ∧
        canonicalUpperResidual data 4 = 3) ∨
      (t = 1 ∧ (n + d) % 24 = 7 ∧
        canonicalUpperResidual data 2 = 3 ∧
        canonicalUpperResidual data 4 = 1) ∨
      (t = 3 ∧ (n + d) % 24 = 13 ∧
        canonicalUpperResidual data 2 = 3 ∧
        canonicalUpperResidual data 4 = 1) ∨
      (t = 5 ∧ (n + d) % 24 = 19 ∧
        canonicalUpperResidual data 2 = 3 ∧
        canonicalUpperResidual data 4 = 1) := by
  have htwos :=
    k5_exceptional_upper_twos_eq_odd_positions data hfour hprofile
  have halloc := exceptional_profile_even_allocation hprofile htwos
  have hmod3 := exceptional_even_allocation_mod_three halloc
    (fun i hi => dvd_trans
      ⟨canonicalOwnerColumn data i,
        canonical_modified_upper_term_factorization data⟩
      (upperTermAfterFour_dvd_original hfour))
  have htTwo := k5_exceptional_upper_residual_two_at_distinguished
    data ht hfour hprofile
  have htodd : t ∈ ({1, 3, 5} : Finset ℕ) := by
    have htmem : t ∈ (Finset.Icc 1 5).filter
        (fun i => canonicalUpperResidual data i = 2) :=
      Finset.mem_filter.mpr ⟨ht, htTwo⟩
    rwa [htwos] at htmem
  have hmod8 := eight_dvd_odd_offset_mod_eight htodd
    (k5_exceptional_upper_eight_dvd_distinguished
      data ht hfour hprofile)
  rcases hmod3 with hmod3 | hmod3
  · rcases hmod8 with hmod8 | hmod8 | hmod8
    · exact Or.inl ⟨hmod8.1, by omega, hmod3.2⟩
    · exact Or.inr (Or.inl ⟨hmod8.1, by omega, hmod3.2⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hmod8.1, by omega, hmod3.2⟩))
  · rcases hmod8 with hmod8 | hmod8 | hmod8
    · exact Or.inr (Or.inr (Or.inr
        (Or.inl ⟨hmod8.1, by omega, hmod3.2⟩)))
    · exact Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl ⟨hmod8.1, by omega, hmod3.2⟩))))
    · exact Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr ⟨hmod8.1, by omega, hmod3.2⟩))))

/-- Simultaneous lower and upper exceptional profiles determine the gap
modulo six from the two even-position residual allocations.  Matching
placements force `6 | d`; the two crossed placements force residues `2`
and `4`, respectively. -/
theorem k5_exceptional_row_column_gap_mod_six
    {n d t : ℕ} (data : CanonicalOwnerData 5 n d t)
    (ht : t ∈ Finset.Icc 1 5)
    (hfour : 4 ∣ n + d + t)
    (hlower : K5ExceptionalResidualProfile (canonicalLowerResidual data))
    (hupper : K5ExceptionalResidualProfile (canonicalUpperResidual data)) :
    (d % 6 = 0 ∧ canonicalLowerResidual data 2 = 1 ∧
        canonicalLowerResidual data 4 = 3 ∧
        canonicalUpperResidual data 2 = 1 ∧
        canonicalUpperResidual data 4 = 3) ∨
      (d % 6 = 2 ∧ canonicalLowerResidual data 2 = 1 ∧
        canonicalLowerResidual data 4 = 3 ∧
        canonicalUpperResidual data 2 = 3 ∧
        canonicalUpperResidual data 4 = 1) ∨
      (d % 6 = 4 ∧ canonicalLowerResidual data 2 = 3 ∧
        canonicalLowerResidual data 4 = 1 ∧
        canonicalUpperResidual data 2 = 1 ∧
        canonicalUpperResidual data 4 = 3) ∨
      (d % 6 = 0 ∧ canonicalLowerResidual data 2 = 3 ∧
        canonicalLowerResidual data 4 = 1 ∧
        canonicalUpperResidual data 2 = 3 ∧
        canonicalUpperResidual data 4 = 1) := by
  have hl := k5_exceptional_lower_even_allocation_mod_six data hlower
  have hu := k5_exceptional_upper_exact_mod_twenty_four
    data ht hfour hupper
  rcases hl with hl | hl <;>
    rcases hu with hu | hu | hu | hu | hu | hu
  all_goals simp_all only [true_and, and_true]
  all_goals omega

/-! ## Global diagonal-product and adjacent-equation interfaces -/

/-- A fully owned row divides the product of its shifted diagonals.  This is
the first basis-free global use of all five row owners together: each cell
divides its own `d+i-j`, and the full row product is exactly `n+j`. -/
theorem canonicalOwner_fullyOwned_lower_dvd_diagonalProduct
    {k n d t j : ℕ}
    (data : CanonicalOwnerData k n d t)
    (hd : k ≤ d) (hj : j ∈ Finset.Icc 1 k)
    (hfour : 4 ∣ n + d + t)
    (hlower : canonicalLowerResidual data j = 1) :
    n + j ∣ ∏ i ∈ Finset.Icc 1 k, (d + i - j) := by
  rw [canonical_lower_term_factorization data, hlower, one_mul,
    ← canonicalOwner_row_cell_product data]
  exact Finset.prod_dvd_prod_of_dvd _ _ fun i hi =>
    canonicalOwnerCell_dvd_shiftedDifference data hd hj hi hfour

/-- A fully owned nondistinguished column divides the product of its five
shifted diagonals.  The nondistinguished hypothesis removes the exceptional
factor four, so the original upper term is exactly the column owner product. -/
theorem canonicalOwner_fullyOwned_upper_dvd_diagonalProduct_of_ne
    {k n d t i : ℕ}
    (data : CanonicalOwnerData k n d t)
    (hd : k ≤ d) (hi : i ∈ Finset.Icc 1 k)
    (hit : i ≠ t) (hfour : 4 ∣ n + d + t)
    (hupper : canonicalUpperResidual data i = 1) :
    n + d + i ∣ ∏ j ∈ Finset.Icc 1 k, (d + i - j) := by
  have hfactor := canonical_upper_term_factorization data hfour (i := i)
  simp only [if_neg hit, one_mul, hupper] at hfactor
  rw [hfactor, ← canonicalOwner_column_cell_product data]
  exact Finset.prod_dvd_prod_of_dvd _ _ fun j hj =>
    canonicalOwnerCell_dvd_shiftedDifference data hd hj hi hfour

/-- At a fully owned nondistinguished crossing, the owner is not merely a
divisor of the shifted difference: it is its exact gcd with the lower term. -/
theorem canonicalOwner_fullyOwned_gcd_shiftedDifference_eq_cell_of_ne
    {k n d t j i : ℕ}
    (data : CanonicalOwnerData k n d t)
    (hd : k ≤ d)
    (hj : j ∈ Finset.Icc 1 k) (hi : i ∈ Finset.Icc 1 k)
    (hit : i ≠ t)
    (hlower : canonicalLowerResidual data j = 1)
    (hupper : canonicalUpperResidual data i = 1) :
    Nat.gcd (n + j) (d + i - j) = canonicalOwnerCell data j i := by
  have hji : j ≤ d + i := by
    have hjk : j ≤ k := (Finset.mem_Icc.mp hj).2
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    omega
  have hadd : n + d + i = (d + i - j) + (n + j) := by omega
  have hg := canonicalOwner_fullyOwned_gcd_upper_eq_cell_of_ne
    data hj hi hit hlower hupper
  rw [hadd, Nat.gcd_add_self_right] at hg
  exact hg

/-- Two distinct fully owned lower rows are coprime.  Replacing the second
row by its adjacent difference shows that the first term is also coprime to
the exact row offset. -/
theorem canonicalOwner_two_fullyOwned_lower_rows_coprime_offset
    {k n d t j₁ j₂ : ℕ}
    (data : CanonicalOwnerData k n d t)
    (hj₁ : j₁ ∈ Finset.Icc 1 k) (hj₂ : j₂ ∈ Finset.Icc 1 k)
    (hneq : j₁ ≠ j₂) (hle : j₁ ≤ j₂)
    (h₁ : canonicalLowerResidual data j₁ = 1)
    (h₂ : canonicalLowerResidual data j₂ = 1) :
    Nat.Coprime (n + j₁) (n + j₂) ∧
      Nat.Coprime (n + j₁) (j₂ - j₁) := by
  have hrow₁ :
      n + j₁ = ∏ i ∈ Finset.Icc 1 k, canonicalOwnerCell data j₁ i := by
    rw [canonical_lower_term_factorization data, h₁, one_mul,
      canonicalOwner_row_cell_product data]
  have hrow₂ :
      n + j₂ = ∏ i ∈ Finset.Icc 1 k, canonicalOwnerCell data j₂ i := by
    rw [canonical_lower_term_factorization data, h₂, one_mul,
      canonicalOwner_row_cell_product data]
  have hcop : Nat.Coprime (n + j₁) (n + j₂) := by
    rw [hrow₁, hrow₂]
    apply Nat.Coprime.prod_left
    intro i₁ hi₁
    apply Nat.Coprime.prod_right
    intro i₂ hi₂
    apply canonicalOwnerCells_pairwise_coprime data
    intro heq
    have : j₁ = j₂ := congrArg Prod.fst heq
    exact hneq this
  refine ⟨hcop, ?_⟩
  have hadd : n + j₂ = (n + j₁) + (j₂ - j₁) := by omega
  rw [hadd] at hcop
  simpa using (Nat.coprime_self_add_right.mp hcop)

/-- On every proper-global-residual branch, two fully owned lower rows can
be ordered so that their exact adjacent equation has offset between one and
four, and the earlier lower term is coprime to both the later term and the
offset. -/
theorem k5_proper_global_two_coprime_lower_adjacent_equations
    {n d t : ℕ} (data : CanonicalOwnerData 5 n d t)
    (hGne : canonicalOwnerResidual data ≠ 24) :
    ∃ j₁, j₁ ∈ Finset.Icc 1 5 ∧
      ∃ j₂, j₂ ∈ Finset.Icc 1 5 ∧ j₁ < j₂ ∧
        canonicalLowerResidual data j₁ = 1 ∧
        canonicalLowerResidual data j₂ = 1 ∧
        Nat.Coprime (n + j₁) (n + j₂) ∧
        Nat.Coprime (n + j₁) (j₂ - j₁) ∧
        1 ≤ j₂ - j₁ ∧ j₂ - j₁ ≤ 4 := by
  obtain ⟨a, ha, b, hb, hba, haone, hbone⟩ :=
    exists_two_k5_unit_lower_residuals_of_global_ne_twenty_four data hGne
  rcases lt_or_gt_of_ne hba with hba' | hab
  · obtain ⟨hcop, hoff⟩ :=
      canonicalOwner_two_fullyOwned_lower_rows_coprime_offset
        data hb ha hba hba'.le hbone haone
    refine ⟨b, hb, a, ha, hba', hbone, haone, hcop, hoff, ?_, ?_⟩
    · omega
    · have ha5 := (Finset.mem_Icc.mp ha).2
      have hb1 := (Finset.mem_Icc.mp hb).1
      omega
  · obtain ⟨hcop, hoff⟩ :=
      canonicalOwner_two_fullyOwned_lower_rows_coprime_offset
        data ha hb hba.symm hab.le haone hbone
    refine ⟨a, ha, b, hb, hab, haone, hbone, hcop, hoff, ?_, ?_⟩
    · omega
    · have hb5 := (Finset.mem_Icc.mp hb).2
      have ha1 := (Finset.mem_Icc.mp ha).1
      omega

/-- Two distinct fully owned nondistinguished upper columns are coprime, and
the first upper term is coprime to the exact column offset. -/
theorem canonicalOwner_two_fullyOwned_upper_columns_coprime_offset
    {k n d t i₁ i₂ : ℕ}
    (data : CanonicalOwnerData k n d t)
    (hi₁ : i₁ ∈ Finset.Icc 1 k) (hi₂ : i₂ ∈ Finset.Icc 1 k)
    (hneq : i₁ ≠ i₂) (hle : i₁ ≤ i₂)
    (hi₁t : i₁ ≠ t) (hi₂t : i₂ ≠ t)
    (hfour : 4 ∣ n + d + t)
    (h₁ : canonicalUpperResidual data i₁ = 1)
    (h₂ : canonicalUpperResidual data i₂ = 1) :
    Nat.Coprime (n + d + i₁) (n + d + i₂) ∧
      Nat.Coprime (n + d + i₁) (i₂ - i₁) := by
  have hcol₁ :
      n + d + i₁ = ∏ j ∈ Finset.Icc 1 k, canonicalOwnerCell data j i₁ := by
    have hfactor := canonical_upper_term_factorization data hfour (i := i₁)
    simp only [if_neg hi₁t, one_mul, h₁] at hfactor
    rw [hfactor, canonicalOwner_column_cell_product data]
  have hcol₂ :
      n + d + i₂ = ∏ j ∈ Finset.Icc 1 k, canonicalOwnerCell data j i₂ := by
    have hfactor := canonical_upper_term_factorization data hfour (i := i₂)
    simp only [if_neg hi₂t, one_mul, h₂] at hfactor
    rw [hfactor, canonicalOwner_column_cell_product data]
  have hcop : Nat.Coprime (n + d + i₁) (n + d + i₂) := by
    rw [hcol₁, hcol₂]
    apply Nat.Coprime.prod_left
    intro j₁ hj₁
    apply Nat.Coprime.prod_right
    intro j₂ hj₂
    apply canonicalOwnerCells_pairwise_coprime data
    intro heq
    have : i₁ = i₂ := congrArg Prod.snd heq
    exact hneq this
  refine ⟨hcop, ?_⟩
  have hadd : n + d + i₂ = (n + d + i₁) + (i₂ - i₁) := by omega
  rw [hadd] at hcop
  simpa using (Nat.coprime_self_add_right.mp hcop)

private lemma five_le_of_one_lt_and_coprime_six
    {a : ℕ} (ha : 1 < a) (hcop : Nat.Coprime a 6) : 5 ≤ a := by
  by_contra hnot
  have ha4 : a ≤ 4 := by omega
  interval_cases a <;> norm_num [Nat.Coprime] at hcop

/-- If a lower term is coprime to six, complete support upgrades every cell
in its row to a shifted-diagonal divisor at least five. -/
theorem canonicalOwner_row_coprime_six_large_diagonal_factors
    {k n d t j : ℕ}
    (data : CanonicalOwnerData k n d t)
    (hd : k ≤ d) (hj : j ∈ Finset.Icc 1 k)
    (hfour : 4 ∣ n + d + t)
    (hterm : Nat.Coprime (n + j) 6)
    (hcells : ∀ i ∈ Finset.Icc 1 k, 1 < canonicalOwnerCell data j i) :
    ∀ i ∈ Finset.Icc 1 k,
      5 ≤ canonicalOwnerCell data j i ∧
      Nat.Coprime (canonicalOwnerCell data j i) 6 ∧
      canonicalOwnerCell data j i ∣ d + i - j := by
  intro i hi
  have hcop := hterm.of_dvd_left
    (canonicalOwnerCell_dvd_lower data (j := j) (i := i))
  exact ⟨five_le_of_one_lt_and_coprime_six (hcells i hi) hcop, hcop,
    canonicalOwnerCell_dvd_shiftedDifference data hd hj hi hfour⟩

/-- The exact symbolic payload carried by an exceptional fully owned
row/column crossing.  Besides the two unit residuals it records the exact
shifted gcd and both independent five-diagonal product divisibilities. -/
def K5ExceptionalUnitCrossingConstraint
    {n d t : ℕ} (data : CanonicalOwnerData 5 n d t) (j i : ℕ) : Prop :=
  i ≠ t ∧
  canonicalLowerResidual data j = 1 ∧
  canonicalUpperResidual data i = 1 ∧
  1 < canonicalOwnerCell data j i ∧
  Nat.Coprime (canonicalOwnerCell data j i) 6 ∧
  (∀ i' ∈ Finset.Icc 1 5,
    5 ≤ canonicalOwnerCell data j i' ∧
    Nat.Coprime (canonicalOwnerCell data j i') 6 ∧
    canonicalOwnerCell data j i' ∣ d + i' - j) ∧
  Nat.gcd (n + j) (d + i - j) = canonicalOwnerCell data j i ∧
  n + j ∣ ∏ i' ∈ Finset.Icc 1 5, (d + i' - j) ∧
  n + d + i ∣ ∏ j' ∈ Finset.Icc 1 5, (d + i - j')

/-- In the simultaneous exceptional branch there are only four possible
fully owned crossings.  In every case the crossing is nontrivial, coprime
to six, is the exact gcd with `d+i-j`, and the complete row and column give
independent five-diagonal product divisibilities. -/
theorem k5_exceptional_exact_unit_crossing_constraints
    {n d t : ℕ} (data : CanonicalOwnerData 5 n d t)
    (ht : t ∈ Finset.Icc 1 5)
    (hfour : 4 ∣ n + d + t)
    (hblocks : upperBlockAfterFour 5 n d t = blockProduct 5 n)
    (htail : 10 ^ 1000 ≤ d)
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n)
    (hlower : K5ExceptionalResidualProfile (canonicalLowerResidual data))
    (hupper : K5ExceptionalResidualProfile (canonicalUpperResidual data)) :
    (d % 6 = 0 ∧ K5ExceptionalUnitCrossingConstraint data 2 2) ∨
      (d % 6 = 2 ∧ K5ExceptionalUnitCrossingConstraint data 2 4) ∨
      (d % 6 = 4 ∧ K5ExceptionalUnitCrossingConstraint data 4 2) ∨
      (d % 6 = 0 ∧ K5ExceptionalUnitCrossingConstraint data 4 4) := by
  have hfive : 5 ≤ 10 ^ 1000 := by
    rw [show 1000 = 999 + 1 by omega, pow_succ]
    have hp : 0 < 10 ^ 999 := pow_pos (by norm_num) _
    have hp1 : 1 ≤ 10 ^ 999 := hp
    calc
      5 ≤ 1 * 10 := by norm_num
      _ ≤ 10 ^ 999 * 10 := Nat.mul_le_mul_right 10 hp1
  have hd : 5 ≤ d := le_trans hfive htail
  have hcells := (k5_tail_complete_support_unit_cross
    data ht hfour hblocks htail heq).1
  have htodd : t % 2 = 1 := by
    have hbase := k5_exceptional_upper_base_odd data hfour hupper
    have hsum : (n + d + t) % 2 = 0 :=
      Nat.dvd_iff_mod_eq_zero.mp (dvd_trans (by norm_num : 2 ∣ 4) hfour)
    omega
  have hl := k5_exceptional_lower_even_allocation_mod_six data hlower
  have hcases := k5_exceptional_row_column_gap_mod_six
    data ht hfour hlower hupper
  have hcop2 (hn : n % 6 = 5) : Nat.Coprime (n + 2) 6 := by
    apply Nat.coprime_of_mul_modEq_one 1
    change ((n + 2) * 1) % 6 = 1 % 6
    omega
  have hcop4 (hn : n % 6 = 1) : Nat.Coprime (n + 4) 6 := by
    apply Nat.coprime_of_mul_modEq_one 5
    change ((n + 4) * 5) % 6 = 1 % 6
    omega
  rcases hl with hl | hl
  · have hrowcop := hcop2 hl.1
    rcases hcases with hc | hc | hc | hc
    · left
      refine ⟨hc.1, ?_⟩
      have hit : 2 ≠ t := by omega
      refine ⟨hit, hc.2.1, hc.2.2.2.1, hcells 2 (by norm_num) 2 (by norm_num),
        hrowcop.of_dvd_left (canonicalOwnerCell_dvd_lower data),
        canonicalOwner_row_coprime_six_large_diagonal_factors
          data hd (by norm_num) hfour hrowcop (hcells 2 (by norm_num)), ?_, ?_, ?_⟩
      · exact canonicalOwner_fullyOwned_gcd_shiftedDifference_eq_cell_of_ne
          data hd (by norm_num) (by norm_num) hit hc.2.1 hc.2.2.2.1
      · exact canonicalOwner_fullyOwned_lower_dvd_diagonalProduct
          data hd (by norm_num) hfour hc.2.1
      · exact canonicalOwner_fullyOwned_upper_dvd_diagonalProduct_of_ne
          data hd (by norm_num) hit hfour hc.2.2.2.1
    · right; left
      refine ⟨hc.1, ?_⟩
      have hit : 4 ≠ t := by omega
      refine ⟨hit, hc.2.1, hc.2.2.2.2,
        hcells 2 (by norm_num) 4 (by norm_num),
        hrowcop.of_dvd_left (canonicalOwnerCell_dvd_lower data),
        canonicalOwner_row_coprime_six_large_diagonal_factors
          data hd (by norm_num) hfour hrowcop (hcells 2 (by norm_num)), ?_, ?_, ?_⟩
      · exact canonicalOwner_fullyOwned_gcd_shiftedDifference_eq_cell_of_ne
          data hd (by norm_num) (by norm_num) hit hc.2.1 hc.2.2.2.2
      · exact canonicalOwner_fullyOwned_lower_dvd_diagonalProduct
          data hd (by norm_num) hfour hc.2.1
      · exact canonicalOwner_fullyOwned_upper_dvd_diagonalProduct_of_ne
          data hd (by norm_num) hit hfour hc.2.2.2.2
    · omega
    · omega
  · have hrowcop := hcop4 hl.1
    rcases hcases with hc | hc | hc | hc
    · omega
    · omega
    · right; right; left
      refine ⟨hc.1, ?_⟩
      have hit : 2 ≠ t := by omega
      refine ⟨hit, hc.2.2.1, hc.2.2.2.1,
        hcells 4 (by norm_num) 2 (by norm_num),
        hrowcop.of_dvd_left (canonicalOwnerCell_dvd_lower data),
        canonicalOwner_row_coprime_six_large_diagonal_factors
          data hd (by norm_num) hfour hrowcop (hcells 4 (by norm_num)), ?_, ?_, ?_⟩
      · exact canonicalOwner_fullyOwned_gcd_shiftedDifference_eq_cell_of_ne
          data hd (by norm_num) (by norm_num) hit hc.2.2.1 hc.2.2.2.1
      · exact canonicalOwner_fullyOwned_lower_dvd_diagonalProduct
          data hd (by norm_num) hfour hc.2.2.1
      · exact canonicalOwner_fullyOwned_upper_dvd_diagonalProduct_of_ne
          data hd (by norm_num) hit hfour hc.2.2.2.1
    · right; right; right
      refine ⟨hc.1, ?_⟩
      have hit : 4 ≠ t := by omega
      refine ⟨hit, hc.2.2.1, hc.2.2.2.2,
        hcells 4 (by norm_num) 4 (by norm_num),
        hrowcop.of_dvd_left (canonicalOwnerCell_dvd_lower data),
        canonicalOwner_row_coprime_six_large_diagonal_factors
          data hd (by norm_num) hfour hrowcop (hcells 4 (by norm_num)), ?_, ?_, ?_⟩
      · exact canonicalOwner_fullyOwned_gcd_shiftedDifference_eq_cell_of_ne
          data hd (by norm_num) (by norm_num) hit hc.2.2.1 hc.2.2.2.2
      · exact canonicalOwner_fullyOwned_lower_dvd_diagonalProduct
          data hd (by norm_num) hfour hc.2.2.1
      · exact canonicalOwner_fullyOwned_upper_dvd_diagonalProduct_of_ne
          data hd (by norm_num) hit hfour hc.2.2.2.2

#print axioms exists_k5_unit_lower_residual
#print axioms exists_k5_unit_upper_residual
#print axioms k5_lower_residual_profile_of_global_eq_twenty_four
#print axioms k5_upper_residual_profile_of_global_eq_twenty_four
#print axioms canonicalOwner_row_column_gcd_eq_cell
#print axioms canonicalOwner_fullyOwned_gcd_modifiedUpper_eq_cell
#print axioms canonicalOwner_fullyOwned_gcd_upper_eq_cell_of_ne
#print axioms exists_two_k5_unit_lower_residuals_of_global_ne_twenty_four
#print axioms exists_two_k5_unit_upper_residuals_of_global_ne_twenty_four
#print axioms k5_tail_complete_support_unit_cross
#print axioms k5_tail_proper_global_two_by_two_gcd_grid
#print axioms k5_tail_proper_global_common_upper_two_coprime_gcds
#print axioms k5_tail_unit_cross_factorizations
#print axioms k5_exceptional_lower_base_odd
#print axioms k5_exceptional_upper_base_odd
#print axioms k5_exceptional_both_force_even_gap
#print axioms k5_exceptional_lower_twos_eq_odd_positions
#print axioms k5_exceptional_upper_twos_eq_odd_positions
#print axioms k5_exceptional_upper_residual_two_at_distinguished
#print axioms k5_exceptional_upper_eight_dvd_distinguished
#print axioms k5_exceptional_lower_even_allocation_mod_six
#print axioms k5_exceptional_upper_exact_mod_twenty_four
#print axioms k5_exceptional_row_column_gap_mod_six
#print axioms canonicalOwner_fullyOwned_lower_dvd_diagonalProduct
#print axioms canonicalOwner_fullyOwned_upper_dvd_diagonalProduct_of_ne
#print axioms canonicalOwner_fullyOwned_gcd_shiftedDifference_eq_cell_of_ne
#print axioms canonicalOwner_two_fullyOwned_lower_rows_coprime_offset
#print axioms k5_proper_global_two_coprime_lower_adjacent_equations
#print axioms canonicalOwner_two_fullyOwned_upper_columns_coprime_offset
#print axioms canonicalOwner_row_coprime_six_large_diagonal_factors
#print axioms k5_exceptional_exact_unit_crossing_constraints

end Erdos686Variant
end Erdos686
