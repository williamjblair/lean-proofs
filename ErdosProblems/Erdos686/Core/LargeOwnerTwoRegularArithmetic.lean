/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.Core.LargeOwnerCollisionStability
import ErdosProblems.Erdos686.Core.NormalizedMatching

/-!
# Erdős 686: exact arithmetic at a two-regular large-owner cell

This file isolates the first genuinely arithmetic consequences of having a
second nontrivial canonical owner in the row, signed diagonal, and column of
one owner cell.  After the common owner is removed, the upper-column partner
divides the sum of the row and diagonal cofactors.  The normalized owner-square
congruence also loses exactly one copy of the owner and gives a tangent
cofactor congruence.

The cofactors in these statements are not bounded.  Thus these lemmas do not,
by themselves, turn the two-regular support case into a fixed determinant or
resultant; a global cofactor-mass estimate is still needed for that step.
-/

namespace Erdos686
namespace Erdos686Variant

open scoped BigOperators

/-- The cofactor left in a lower term after removing its complete nontrivial
large-owner row aggregate. -/
def canonicalLargeOwnerRowCofactor
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t) (j : ℕ) : ℕ :=
  (n + j) / canonicalLargeOwnerRowAggregate data j

/-- Removing the trivial cells from a row does not change its owner product. -/
theorem canonicalLargeOwnerRowAggregate_eq_allCells
    {k n d t j : ℕ} (data : CanonicalOwnerData k n d t)
    (hj : j ∈ Finset.Icc 1 k) :
    canonicalLargeOwnerRowAggregate data j =
      ∏ i ∈ Finset.Icc 1 k, canonicalLargeOwnerCell data j i := by
  classical
  let cols := (Finset.Icc 1 k).filter
    (fun i => canonicalLargeOwnerCell data j i ≠ 1)
  calc
    canonicalLargeOwnerRowAggregate data j =
        ∏ i ∈ cols, canonicalLargeOwnerCell data j i := by
      unfold canonicalLargeOwnerRowAggregate canonicalLargeOwnerRowSupport
      apply Finset.prod_bij (fun e _ => e.2)
      · intro e he
        have heRow := (Finset.mem_filter.mp he).2
        have heSupport := (Finset.mem_filter.mp he).1
        have heSquare := Finset.mem_product.mp
          (Finset.mem_filter.mp heSupport).1
        have heNontrivial := (Finset.mem_filter.mp heSupport).2
        simp only [cols, Finset.mem_filter]
        exact ⟨heSquare.2, by simpa [heRow] using heNontrivial⟩
      · intro a ha b hb hab
        have haRow := (Finset.mem_filter.mp ha).2
        have hbRow := (Finset.mem_filter.mp hb).2
        apply Prod.ext
        · exact haRow.trans hbRow.symm
        · exact hab
      · intro i hi
        refine ⟨(j, i), ?_, rfl⟩
        have hi' := Finset.mem_filter.mp hi
        have hSquare :
            (j, i) ∈ (Finset.Icc 1 k).product (Finset.Icc 1 k) :=
          Finset.mem_product.mpr ⟨hj, hi'.1⟩
        have hSupport : (j, i) ∈ canonicalLargeOwnerSupport data :=
          Finset.mem_filter.mpr ⟨hSquare, hi'.2⟩
        exact Finset.mem_filter.mpr ⟨hSupport, rfl⟩
      · intro e he
        have heRow := (Finset.mem_filter.mp he).2
        simp [heRow]
    _ = ∏ i ∈ Finset.Icc 1 k,
        canonicalLargeOwnerCell data j i := by
      simp only [cols, Finset.prod_filter]
      apply Finset.prod_congr rfl
      intro i hi
      split <;> simp_all

/-- The lower term is exactly its large-owner row aggregate times its row
cofactor. -/
theorem canonicalLargeOwner_lower_term_factorization
    {k n d t j : ℕ} (data : CanonicalOwnerData k n d t) :
    n + j = canonicalLargeOwnerRowCofactor data j *
      canonicalLargeOwnerRowAggregate data j := by
  exact (Nat.div_mul_cancel
    (canonicalLargeOwnerRowSupport_product_dvd_lower data)).symm

/-- The complete row aggregates partition the total large-prime mass. -/
theorem canonicalLargeOwnerRowAggregate_product_eq_mass
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t) :
    (∏ j ∈ Finset.Icc 1 k, canonicalLargeOwnerRowAggregate data j) =
      kLargePart k (blockProduct k n) := by
  classical
  calc
    (∏ j ∈ Finset.Icc 1 k, canonicalLargeOwnerRowAggregate data j) =
        ∏ j ∈ Finset.Icc 1 k,
          ∏ i ∈ Finset.Icc 1 k,
            canonicalLargeOwnerCell data j i := by
      apply Finset.prod_congr rfl
      intro j hj
      exact canonicalLargeOwnerRowAggregate_eq_allCells data hj
    _ = kLargePart k (blockProduct k n) :=
      canonicalLargeOwner_allCells_eq_kLargePart data

/-- Exact global cofactor-mass identity.  The product of the lower-row
cofactors left after deleting all large owners is precisely the small-prime
part of the lower block. -/
theorem canonicalLargeOwnerRowCofactor_product_eq_smallPart
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t) :
    (∏ j ∈ Finset.Icc 1 k, canonicalLargeOwnerRowCofactor data j) =
      kSmallPart k (blockProduct k n) := by
  apply Nat.mul_right_cancel
    (Nat.pos_of_ne_zero (kLargePart_ne_zero k (blockProduct k n)))
  calc
    (∏ j ∈ Finset.Icc 1 k, canonicalLargeOwnerRowCofactor data j) *
          kLargePart k (blockProduct k n) =
        (∏ j ∈ Finset.Icc 1 k, canonicalLargeOwnerRowCofactor data j) *
          (∏ j ∈ Finset.Icc 1 k,
            canonicalLargeOwnerRowAggregate data j) := by
      rw [canonicalLargeOwnerRowAggregate_product_eq_mass]
    _ = ∏ j ∈ Finset.Icc 1 k,
        (canonicalLargeOwnerRowCofactor data j *
          canonicalLargeOwnerRowAggregate data j) := by
      rw [Finset.prod_mul_distrib]
    _ = blockProduct k n := by
      unfold blockProduct
      apply Finset.prod_congr rfl
      intro j hj
      exact (canonicalLargeOwner_lower_term_factorization data).symm
    _ = kSmallPart k (blockProduct k n) *
        kLargePart k (blockProduct k n) := by
      exact (kSmallPart_mul_kLargePart
        (ne_of_gt (blockProduct_pos k n))).symm

/-- The cofactor left in a modified upper term after removing its complete
large-owner column product. -/
def canonicalLargeOwnerColumnCofactor
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t) (i : ℕ) : ℕ :=
  upperTermAfterFour n d t i / canonicalLargeOwnerColumnProduct data i

private theorem pairwise_coprime_finset_product_dvd
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℕ) (z : ℕ)
    (hpair : (s : Set ι).Pairwise (Function.onFun Nat.Coprime f))
    (hdvd : ∀ x ∈ s, f x ∣ z) :
    (∏ x ∈ s, f x) ∣ z := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
      · apply Nat.Coprime.prod_right
        intro b hb
        exact hpair (by simp) (by simp [hb])
          (Ne.symm (ne_of_mem_of_not_mem hb ha))
      · exact hdvd a (by simp)
      · apply ih
        · intro x hx y hy hxy
          exact hpair (by simp [hx]) (by simp [hy]) hxy
        · intro x hx
          exact hdvd x (by simp [hx])

/-- The complete large-owner column product divides its modified upper term. -/
theorem canonicalLargeOwnerColumnProduct_dvd_modifiedUpper
    {k n d t i : ℕ} (data : CanonicalOwnerData k n d t)
    (hi : i ∈ Finset.Icc 1 k) :
    canonicalLargeOwnerColumnProduct data i ∣ upperTermAfterFour n d t i := by
  rw [← canonicalLargeOwnerColumnSupport_product_eq data hi]
  apply pairwise_coprime_finset_product_dvd
  · intro e he f hf hef
    exact canonicalLargeOwnerCells_pairwise_coprime data hef
  · intro e he
    have heColumn := (Finset.mem_filter.mp he).2
    simpa [heColumn] using
      (canonicalLargeOwnerCell_dvd_upper data (j := e.1) (i := e.2))

/-- The modified upper term is exactly its large-owner column product times
its column cofactor. -/
theorem canonicalLargeOwner_modified_upper_term_factorization
    {k n d t i : ℕ} (data : CanonicalOwnerData k n d t)
    (hi : i ∈ Finset.Icc 1 k) :
    upperTermAfterFour n d t i =
      canonicalLargeOwnerColumnCofactor data i *
        canonicalLargeOwnerColumnProduct data i := by
  exact (Nat.div_mul_cancel
    (canonicalLargeOwnerColumnProduct_dvd_modifiedUpper data hi)).symm

/-- Exact upper-column analogue of the lower-row cofactor-mass identity.
Whenever the four-removed upper block equals the lower block, the product of
all large-owner column cofactors is the same small-prime mass. -/
theorem canonicalLargeOwnerColumnCofactor_product_eq_smallPart
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    (hblocks : upperBlockAfterFour k n d t = blockProduct k n) :
    (∏ i ∈ Finset.Icc 1 k, canonicalLargeOwnerColumnCofactor data i) =
      kSmallPart k (blockProduct k n) := by
  apply Nat.mul_right_cancel
    (Nat.pos_of_ne_zero (kLargePart_ne_zero k (blockProduct k n)))
  calc
    (∏ i ∈ Finset.Icc 1 k, canonicalLargeOwnerColumnCofactor data i) *
          kLargePart k (blockProduct k n) =
        (∏ i ∈ Finset.Icc 1 k, canonicalLargeOwnerColumnCofactor data i) *
          (∏ i ∈ Finset.Icc 1 k,
            canonicalLargeOwnerColumnProduct data i) := by
      rw [← canonicalLargeOwnerSupport_product_eq_kLargePart,
        canonicalLargeOwnerSupport_product_eq_columnProducts]
    _ = ∏ i ∈ Finset.Icc 1 k,
        (canonicalLargeOwnerColumnCofactor data i *
          canonicalLargeOwnerColumnProduct data i) := by
      rw [Finset.prod_mul_distrib]
    _ = upperBlockAfterFour k n d t := by
      unfold upperBlockAfterFour
      apply Finset.prod_congr rfl
      intro i hi
      exact (canonicalLargeOwner_modified_upper_term_factorization
        data hi).symm
    _ = blockProduct k n := hblocks
    _ = kSmallPart k (blockProduct k n) *
        kLargePart k (blockProduct k n) := by
      exact (kSmallPart_mul_kLargePart
        (ne_of_gt (blockProduct_pos k n))).symm

/-- Exact degree-weighted row-cofactor product on the large-owner support. -/
theorem canonicalLargeOwnerSupport_rowCofactor_product_eq_weighted
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t) :
    (∏ e ∈ canonicalLargeOwnerSupport data,
      canonicalLargeOwnerRowCofactor data e.1) =
      ∏ j ∈ Finset.Icc 1 k,
        (canonicalLargeOwnerRowCofactor data j) ^
          (canonicalLargeOwnerRowSupport data j).card := by
  classical
  symm
  calc
    (∏ j ∈ Finset.Icc 1 k,
        (canonicalLargeOwnerRowCofactor data j) ^
          (canonicalLargeOwnerRowSupport data j).card) =
      ∏ j ∈ Finset.Icc 1 k,
        ∏ e ∈ canonicalLargeOwnerSupport data with e.1 = j,
          canonicalLargeOwnerRowCofactor data j := by
      apply Finset.prod_congr rfl
      intro j hj
      simp [canonicalLargeOwnerRowSupport, Finset.prod_const]
    _ = ∏ e ∈ canonicalLargeOwnerSupport data,
        canonicalLargeOwnerRowCofactor data e.1 := by
      apply Finset.prod_fiberwise_of_maps_to'
      intro e he
      exact (Finset.mem_product.mp (Finset.mem_filter.mp he).1).1

/-- Exact degree-weighted column-cofactor product on the large-owner support. -/
theorem canonicalLargeOwnerSupport_columnCofactor_product_eq_weighted
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t) :
    (∏ e ∈ canonicalLargeOwnerSupport data,
      canonicalLargeOwnerColumnCofactor data e.2) =
      ∏ i ∈ Finset.Icc 1 k,
        (canonicalLargeOwnerColumnCofactor data i) ^
          (canonicalLargeOwnerColumnSupport data i).card := by
  classical
  symm
  calc
    (∏ i ∈ Finset.Icc 1 k,
        (canonicalLargeOwnerColumnCofactor data i) ^
          (canonicalLargeOwnerColumnSupport data i).card) =
      ∏ i ∈ Finset.Icc 1 k,
        ∏ e ∈ canonicalLargeOwnerSupport data with e.2 = i,
          canonicalLargeOwnerColumnCofactor data i := by
      apply Finset.prod_congr rfl
      intro i hi
      simp [canonicalLargeOwnerColumnSupport, Finset.prod_const]
    _ = ∏ e ∈ canonicalLargeOwnerSupport data,
        canonicalLargeOwnerColumnCofactor data e.2 := by
      apply Finset.prod_fiberwise_of_maps_to'
      intro e he
      exact (Finset.mem_product.mp (Finset.mem_filter.mp he).1).2

/-- In the exactly two-regular row regime, every row cofactor occurs twice
on the support, so the support-weighted product is the square of the complete
small-prime mass. -/
theorem canonicalLargeOwnerSupport_rowCofactor_product_eq_smallPart_sq
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    (hrowTwo : ∀ j ∈ Finset.Icc 1 k,
      (canonicalLargeOwnerRowSupport data j).card = 2) :
    (∏ e ∈ canonicalLargeOwnerSupport data,
      canonicalLargeOwnerRowCofactor data e.1) =
      (kSmallPart k (blockProduct k n)) ^ 2 := by
  rw [canonicalLargeOwnerSupport_rowCofactor_product_eq_weighted]
  calc
    (∏ j ∈ Finset.Icc 1 k,
        canonicalLargeOwnerRowCofactor data j ^
          (canonicalLargeOwnerRowSupport data j).card) =
      ∏ j ∈ Finset.Icc 1 k,
        canonicalLargeOwnerRowCofactor data j ^ 2 := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [hrowTwo j hj]
    _ = (∏ j ∈ Finset.Icc 1 k,
        canonicalLargeOwnerRowCofactor data j) ^ 2 := by
      rw [Finset.prod_pow]
    _ = (kSmallPart k (blockProduct k n)) ^ 2 := by
      rw [canonicalLargeOwnerRowCofactor_product_eq_smallPart]

/-- The column analogue in the exactly two-regular regime. -/
theorem canonicalLargeOwnerSupport_columnCofactor_product_eq_smallPart_sq
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    (hblocks : upperBlockAfterFour k n d t = blockProduct k n)
    (hcolumnTwo : ∀ i ∈ Finset.Icc 1 k,
      (canonicalLargeOwnerColumnSupport data i).card = 2) :
    (∏ e ∈ canonicalLargeOwnerSupport data,
      canonicalLargeOwnerColumnCofactor data e.2) =
      (kSmallPart k (blockProduct k n)) ^ 2 := by
  rw [canonicalLargeOwnerSupport_columnCofactor_product_eq_weighted]
  calc
    (∏ i ∈ Finset.Icc 1 k,
        canonicalLargeOwnerColumnCofactor data i ^
          (canonicalLargeOwnerColumnSupport data i).card) =
      ∏ i ∈ Finset.Icc 1 k,
        canonicalLargeOwnerColumnCofactor data i ^ 2 := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [hcolumnTwo i hi]
    _ = (∏ i ∈ Finset.Icc 1 k,
        canonicalLargeOwnerColumnCofactor data i) ^ 2 := by
      rw [Finset.prod_pow]
    _ = (kSmallPart k (blockProduct k n)) ^ 2 := by
      rw [canonicalLargeOwnerColumnCofactor_product_eq_smallPart data hblocks]

/-- With two owners in every row and every column, the product over support
of the row-column cofactor load is exactly the fourth power of the small
prime mass. -/
theorem canonicalLargeOwnerSupport_rowColumnCofactor_product_eq_smallPart_pow_four
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    (hblocks : upperBlockAfterFour k n d t = blockProduct k n)
    (hrowTwo : ∀ j ∈ Finset.Icc 1 k,
      (canonicalLargeOwnerRowSupport data j).card = 2)
    (hcolumnTwo : ∀ i ∈ Finset.Icc 1 k,
      (canonicalLargeOwnerColumnSupport data i).card = 2) :
    (∏ e ∈ canonicalLargeOwnerSupport data,
      (canonicalLargeOwnerRowCofactor data e.1 *
        canonicalLargeOwnerColumnCofactor data e.2)) =
      (kSmallPart k (blockProduct k n)) ^ 4 := by
  rw [Finset.prod_mul_distrib,
    canonicalLargeOwnerSupport_rowCofactor_product_eq_smallPart_sq
      data hrowTwo,
    canonicalLargeOwnerSupport_columnCofactor_product_eq_smallPart_sq
      data hblocks hcolumnTwo]
  ring

/-- The other-owner product in the row through a support cell.  In an exact
two-owner row this is literally the owner at the other cell. -/
def canonicalLargeOwnerRowPartnerProduct
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    (e : ℕ × ℕ) : ℕ :=
  canonicalLargeOwnerRowAggregate data e.1 /
    canonicalLargeOwnerCell data e.1 e.2

/-- The row-partner product is bounded by the local row/diagonal collision
defect. -/
theorem canonicalLargeOwnerRowPartnerProduct_le_localCollisionDefect
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    (e : ℕ × ℕ) :
    canonicalLargeOwnerRowPartnerProduct data e ≤
      canonicalLargeOwnerLocalCollisionDefect data e := by
  unfold canonicalLargeOwnerRowPartnerProduct
    canonicalLargeOwnerLocalCollisionDefect
    canonicalLargeOwnerCollisionEnvelope
  exact Nat.div_le_div_right (le_max_left _ _)

/-- Exact degree-weighted row-aggregate product on the support. -/
theorem canonicalLargeOwnerSupport_rowAggregate_product_eq_weighted
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t) :
    (∏ e ∈ canonicalLargeOwnerSupport data,
      canonicalLargeOwnerRowAggregate data e.1) =
      ∏ j ∈ Finset.Icc 1 k,
        (canonicalLargeOwnerRowAggregate data j) ^
          (canonicalLargeOwnerRowSupport data j).card := by
  classical
  symm
  calc
    (∏ j ∈ Finset.Icc 1 k,
        canonicalLargeOwnerRowAggregate data j ^
          (canonicalLargeOwnerRowSupport data j).card) =
      ∏ j ∈ Finset.Icc 1 k,
        ∏ e ∈ canonicalLargeOwnerSupport data with e.1 = j,
          canonicalLargeOwnerRowAggregate data j := by
      apply Finset.prod_congr rfl
      intro j hj
      simp [canonicalLargeOwnerRowSupport, Finset.prod_const]
    _ = ∏ e ∈ canonicalLargeOwnerSupport data,
        canonicalLargeOwnerRowAggregate data e.1 := by
      apply Finset.prod_fiberwise_of_maps_to'
      intro e he
      exact (Finset.mem_product.mp (Finset.mem_filter.mp he).1).1

/-- In the exactly two-regular row regime, the product of the row-partner
products is exactly the complete large-prime mass. -/
theorem canonicalLargeOwnerRowPartnerProduct_product_eq_mass
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    (hrowTwo : ∀ j ∈ Finset.Icc 1 k,
      (canonicalLargeOwnerRowSupport data j).card = 2) :
    (∏ e ∈ canonicalLargeOwnerSupport data,
      canonicalLargeOwnerRowPartnerProduct data e) =
      kLargePart k (blockProduct k n) := by
  let M := kLargePart k (blockProduct k n)
  have hMpos : 0 < M := Nat.pos_of_ne_zero
    (kLargePart_ne_zero k (blockProduct k n))
  apply Nat.mul_left_cancel hMpos
  calc
    M * (∏ e ∈ canonicalLargeOwnerSupport data,
        canonicalLargeOwnerRowPartnerProduct data e) =
      (∏ e ∈ canonicalLargeOwnerSupport data,
          canonicalLargeOwnerCell data e.1 e.2) *
        (∏ e ∈ canonicalLargeOwnerSupport data,
          canonicalLargeOwnerRowPartnerProduct data e) := by
      rw [canonicalLargeOwnerSupport_product_eq_kLargePart]
    _ = ∏ e ∈ canonicalLargeOwnerSupport data,
        (canonicalLargeOwnerCell data e.1 e.2 *
          canonicalLargeOwnerRowPartnerProduct data e) := by
      rw [Finset.prod_mul_distrib]
    _ = ∏ e ∈ canonicalLargeOwnerSupport data,
        canonicalLargeOwnerRowAggregate data e.1 := by
      apply Finset.prod_congr rfl
      intro e he
      unfold canonicalLargeOwnerRowPartnerProduct
      exact Nat.mul_div_cancel'
        (canonicalLargeOwnerCell_dvd_rowAggregate data he)
    _ = ∏ j ∈ Finset.Icc 1 k,
        canonicalLargeOwnerRowAggregate data j ^
          (canonicalLargeOwnerRowSupport data j).card :=
      canonicalLargeOwnerSupport_rowAggregate_product_eq_weighted data
    _ = ∏ j ∈ Finset.Icc 1 k,
        canonicalLargeOwnerRowAggregate data j ^ 2 := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [hrowTwo j hj]
    _ = (∏ j ∈ Finset.Icc 1 k,
        canonicalLargeOwnerRowAggregate data j) ^ 2 := by
      rw [Finset.prod_pow]
    _ = M * M := by
      rw [canonicalLargeOwnerRowAggregate_product_eq_mass]
      simp only [M, pow_two]

/-- Exact two-regular collision stability bound.  If every lower row has two
nontrivial large owners, the global collision defect is at least the entire
large-prime mass.  Equivalently the collision product is at least the square
of that mass. -/
theorem canonicalLargeOwner_mass_le_collisionDefect_of_rowTwo
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    (hrowTwo : ∀ j ∈ Finset.Icc 1 k,
      (canonicalLargeOwnerRowSupport data j).card = 2) :
    kLargePart k (blockProduct k n) ≤
      canonicalLargeOwnerCollisionDefect data := by
  rw [← canonicalLargeOwnerRowPartnerProduct_product_eq_mass data hrowTwo]
  unfold canonicalLargeOwnerCollisionDefect
  apply Finset.prod_le_prod
  · intro e he
    exact Nat.zero_le _
  · intro e he
    exact canonicalLargeOwnerRowPartnerProduct_le_localCollisionDefect data e

/-- Collision-product form of the same exact stability estimate. -/
theorem canonicalLargeOwner_mass_sq_le_collisionProduct_of_rowTwo
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    (hrowTwo : ∀ j ∈ Finset.Icc 1 k,
      (canonicalLargeOwnerRowSupport data j).card = 2) :
    (kLargePart k (blockProduct k n)) ^ 2 ≤
      canonicalLargeOwnerCollisionProduct data := by
  rw [canonicalLargeOwnerCollisionProduct_eq_mass_mul_defect, pow_two]
  exact Nat.mul_le_mul_left _
    (canonicalLargeOwner_mass_le_collisionDefect_of_rowTwo data hrowTwo)

/-- Consolidated exact weighted stability package for a support with two
large owners in every row and every column.  It records the sharp global
cofactor exponents together with the unavoidable collision lower bound. -/
theorem canonicalLargeOwner_twoRegular_weighted_stability
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    (hblocks : upperBlockAfterFour k n d t = blockProduct k n)
    (hrowTwo : ∀ j ∈ Finset.Icc 1 k,
      (canonicalLargeOwnerRowSupport data j).card = 2)
    (hcolumnTwo : ∀ i ∈ Finset.Icc 1 k,
      (canonicalLargeOwnerColumnSupport data i).card = 2) :
    ((∏ e ∈ canonicalLargeOwnerSupport data,
        canonicalLargeOwnerRowCofactor data e.1) =
        (kSmallPart k (blockProduct k n)) ^ 2) ∧
      ((∏ e ∈ canonicalLargeOwnerSupport data,
        canonicalLargeOwnerColumnCofactor data e.2) =
        (kSmallPart k (blockProduct k n)) ^ 2) ∧
      ((∏ e ∈ canonicalLargeOwnerSupport data,
        canonicalLargeOwnerRowCofactor data e.1 *
          canonicalLargeOwnerColumnCofactor data e.2) =
        (kSmallPart k (blockProduct k n)) ^ 4) ∧
      ((∏ e ∈ canonicalLargeOwnerSupport data,
        canonicalLargeOwnerRowPartnerProduct data e) =
        kLargePart k (blockProduct k n)) ∧
      kLargePart k (blockProduct k n) ≤
        canonicalLargeOwnerCollisionDefect data := by
  exact ⟨
    canonicalLargeOwnerSupport_rowCofactor_product_eq_smallPart_sq
      data hrowTwo,
    canonicalLargeOwnerSupport_columnCofactor_product_eq_smallPart_sq
      data hblocks hcolumnTwo,
    canonicalLargeOwnerSupport_rowColumnCofactor_product_eq_smallPart_pow_four
      data hblocks hrowTwo hcolumnTwo,
    canonicalLargeOwnerRowPartnerProduct_product_eq_mass data hrowTwo,
    canonicalLargeOwner_mass_le_collisionDefect_of_rowTwo data hrowTwo⟩

/-- If two coprime factors `P,C` divide the sum of two quantities carrying
the common factor `P`, then the partner `C` divides the sum after `P` is
removed.  This is the exact secant relation among the three local cofactors. -/
theorem coprime_partner_dvd_cofactor_sum
    {P C R D r q : ℕ}
    (hcop : C.Coprime P)
    (hdiv : P * C ∣ P * R * r + P * D * q) :
    C ∣ R * r + D * q := by
  have hC : C ∣ P * R * r + P * D * q :=
    dvd_trans (Nat.dvd_mul_left C P) hdiv
  apply hcop.dvd_of_dvd_mul_left
  simpa [mul_add, mul_assoc] using hC

/-- Cancelling one nonzero owner from a square divisibility over `ℤ` is an
equivalence.  The nonzero hypothesis is explicit because the owner may be a
composite product of large prime powers. -/
theorem square_dvd_owner_mul_iff_owner_dvd_int
    {P T : ℤ} (hP : P ≠ 0) :
    P ^ 2 ∣ P * T ↔ P ∣ T := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    apply mul_left_cancel₀ hP
    calc
      P * T = P ^ 2 * c := hc
      _ = P * (P * c) := by ring
  · rintro ⟨c, rfl⟩
    exact ⟨c, by ring⟩

/-- Upper-form tangent consequence of the normalized owner-square
congruence.  Here `x=P*R*r` is the lower term and `z=P*C*s` is the upper
term.  The result is valid for arbitrary integral sign and coefficient data. -/
theorem normalized_square_implies_owner_dvd_column_cofactor_defect
    {P C R r s : ℕ} {a b sign x delta z : ℤ}
    (hP : P ≠ 0)
    (hx : x = (P : ℤ) * R * r)
    (hz : z = (P : ℤ) * C * s)
    (hupper : z = x + delta)
    (hsquare : (P : ℤ) ^ 2 ∣
      normalizedMatchingForm a b sign delta x) :
    (P : ℤ) ∣
      b * ((C : ℤ) * s) - 4 * sign * a * ((R : ℤ) * r) := by
  have hform :
      normalizedMatchingForm a b sign delta x =
        (P : ℤ) *
          (b * ((C : ℤ) * s) -
            4 * sign * a * ((R : ℤ) * r)) := by
    rw [normalizedMatchingForm_eq_upper_form, ← hupper, hx, hz]
    ring
  rw [hform] at hsquare
  exact (square_dvd_owner_mul_iff_owner_dvd_int
    (by exact_mod_cast hP)).mp hsquare

/-- The two exact local consequences packaged together.  This is the natural
interface for a row/diagonal/column partner configuration: the first output
is a secant cofactor divisor and the second is the tangent-defect divisor. -/
theorem two_regular_local_cofactor_relations
    {P C R D r q s : ℕ} {a b sign x delta z : ℤ}
    (hP : P ≠ 0)
    (hcop : C.Coprime P)
    (hxNat : (x : ℤ) = (P : ℤ) * R * r)
    (hzNat : z = (P : ℤ) * C * s)
    (hupper : z = x + delta)
    (hcolumn : P * C ∣ P * R * r + P * D * q)
    (hsquare : (P : ℤ) ^ 2 ∣
      normalizedMatchingForm a b sign delta x) :
    C ∣ R * r + D * q ∧
      (P : ℤ) ∣
        b * ((C : ℤ) * s) - 4 * sign * a * ((R : ℤ) * r) := by
  exact ⟨coprime_partner_dvd_cofactor_sum hcop hcolumn,
    normalized_square_implies_owner_dvd_column_cofactor_defect
      hP hxNat hzNat hupper hsquare⟩

/-- Actual canonical-owner specialization of the secant cofactor relation.
For a support cell `e`, suppose `rCell`, `dCell`, and `cCell` are distinct
partners in its row, signed diagonal, and column.  Pairwise coprimality and
the three canonical divisibility theorems extract exact cofactors, and the
column partner divides the row-plus-diagonal cofactor sum. -/
theorem canonicalLargeOwner_exists_partner_cofactors
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    (hd : k ≤ d) (hfour : 4 ∣ n + d + t)
    {e rCell dCell cCell : ℕ × ℕ}
    (he : e ∈ canonicalLargeOwnerSupport data)
    (hr : rCell ∈ canonicalLargeOwnerSupport data)
    (hdiag : dCell ∈ canonicalLargeOwnerSupport data)
    (hcol : cCell ∈ canonicalLargeOwnerSupport data)
    (her : e ≠ rCell) (hediag : e ≠ dCell) (hecol : e ≠ cCell)
    (hrRow : rCell.1 = e.1)
    (hdOffset : ownerCellOffset dCell = ownerCellOffset e)
    (hcColumn : cCell.2 = e.2) :
    ∃ r q s : ℕ,
      n + e.1 =
        canonicalLargeOwnerCell data e.1 e.2 *
          canonicalLargeOwnerCell data rCell.1 rCell.2 * r ∧
      d + e.2 - e.1 =
        canonicalLargeOwnerCell data e.1 e.2 *
          canonicalLargeOwnerCell data dCell.1 dCell.2 * q ∧
      n + d + e.2 =
        canonicalLargeOwnerCell data e.1 e.2 *
          canonicalLargeOwnerCell data cCell.1 cCell.2 * s ∧
      canonicalLargeOwnerCell data cCell.1 cCell.2 ∣
        canonicalLargeOwnerCell data rCell.1 rCell.2 * r +
          canonicalLargeOwnerCell data dCell.1 dCell.2 * q := by
  have _hrNontrivial := (Finset.mem_filter.mp hr).2
  have _hcolNontrivial := (Finset.mem_filter.mp hcol).2
  have hspec := canonicalLargeOwnerSupport_spec data hfour
  have heSquare := hspec.1 e he
  have hdSquare := hspec.1 dCell hdiag
  have hPR :
      (canonicalLargeOwnerCell data e.1 e.2).Coprime
        (canonicalLargeOwnerCell data rCell.1 rCell.2) :=
    canonicalLargeOwnerCells_pairwise_coprime data her
  have hPD :
      (canonicalLargeOwnerCell data e.1 e.2).Coprime
        (canonicalLargeOwnerCell data dCell.1 dCell.2) :=
    canonicalLargeOwnerCells_pairwise_coprime data hediag
  have hPC :
      (canonicalLargeOwnerCell data e.1 e.2).Coprime
        (canonicalLargeOwnerCell data cCell.1 cCell.2) :=
    canonicalLargeOwnerCells_pairwise_coprime data hecol
  have hPeRow := canonicalLargeOwnerCell_dvd_lower data
    (j := e.1) (i := e.2)
  have hPrRow := canonicalLargeOwnerCell_dvd_lower data
    (j := rCell.1) (i := rCell.2)
  have hPrRowAt : canonicalLargeOwnerCell data rCell.1 rCell.2 ∣
      n + e.1 := by
    rw [← hrRow]
    exact hPrRow
  have hrowProd := hPR.mul_dvd_of_dvd_of_dvd hPeRow hPrRowAt
  obtain ⟨r, hrFactor⟩ := hrowProd
  have hPeDiag := canonicalLargeOwnerCell_dvd_shiftedDifference data
    (j := e.1) (i := e.2) hfour
  have hPdDiag := canonicalLargeOwnerCell_dvd_shiftedDifference data
    (j := dCell.1) (i := dCell.2) hfour
  have hdiffEq : d + dCell.2 - dCell.1 = d + e.2 - e.1 := by
    simp only [ownerCellOffset, ownerDiagonalOffset, ownerCellColumn,
      ownerCellRow] at hdOffset
    have heRowK := (Finset.mem_Icc.mp heSquare.1).2
    have heColK := (Finset.mem_Icc.mp heSquare.2).2
    have hdRowK := (Finset.mem_Icc.mp hdSquare.1).2
    have hdColK := (Finset.mem_Icc.mp hdSquare.2).2
    omega
  rw [hdiffEq] at hPdDiag
  have hdiagProd := hPD.mul_dvd_of_dvd_of_dvd hPeDiag hPdDiag
  obtain ⟨q, hdiagFactor⟩ := hdiagProd
  have hPeCol := dvd_trans
    (canonicalLargeOwnerCell_dvd_upper data (j := e.1) (i := e.2))
    (upperTermAfterFour_dvd_original hfour)
  have hPcCol := dvd_trans
    (canonicalLargeOwnerCell_dvd_upper data
      (j := cCell.1) (i := cCell.2))
    (upperTermAfterFour_dvd_original hfour)
  have hPcColAt : canonicalLargeOwnerCell data cCell.1 cCell.2 ∣
      n + d + e.2 := by
    rw [← hcColumn]
    exact hPcCol
  have hcolProd := hPC.mul_dvd_of_dvd_of_dvd hPeCol hPcColAt
  obtain ⟨s, hcolFactor⟩ := hcolProd
  refine ⟨r, q, s, hrFactor, hdiagFactor, hcolFactor, ?_⟩
  apply coprime_partner_dvd_cofactor_sum hPC.symm
  refine ⟨s, ?_⟩
  calc
    canonicalLargeOwnerCell data e.1 e.2 *
          canonicalLargeOwnerCell data rCell.1 rCell.2 * r +
        canonicalLargeOwnerCell data e.1 e.2 *
          canonicalLargeOwnerCell data dCell.1 dCell.2 * q =
      (n + e.1) + (d + e.2 - e.1) := by
        rw [hrFactor, hdiagFactor]
    _ = n + d + e.2 := by
      have heRowLe : e.1 ≤ d + e.2 := by
        have heRowK := (Finset.mem_Icc.mp heSquare.1).2
        omega
      omega
    _ = canonicalLargeOwnerCell data e.1 e.2 *
          canonicalLargeOwnerCell data cCell.1 cCell.2 * s := hcolFactor

/-- Canonical-owner specialization of the tangent-defect cancellation.  Once
the row and column products through `e` have been factored, the normalized
owner-square theorem gives a congruence between their cofactors modulo the
entire (possibly composite) canonical owner. -/
theorem canonicalLargeOwner_tangent_cofactor_dvd
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    (hd : k ≤ d) (hfour : 4 ∣ n + d + t)
    {e rCell cCell : ℕ × ℕ} {r s : ℕ} {a b sign : ℤ}
    (he : e ∈ canonicalLargeOwnerSupport data)
    (hrFactor : n + e.1 =
      canonicalLargeOwnerCell data e.1 e.2 *
        canonicalLargeOwnerCell data rCell.1 rCell.2 * r)
    (hcolFactor : n + d + e.2 =
      canonicalLargeOwnerCell data e.1 e.2 *
        canonicalLargeOwnerCell data cCell.1 cCell.2 * s)
    (hsquare : (canonicalLargeOwnerCell data e.1 e.2 : ℤ) ^ 2 ∣
      normalizedMatchingForm a b sign
        ((d + e.2 - e.1 : ℕ) : ℤ) ((n + e.1 : ℕ) : ℤ)) :
    (canonicalLargeOwnerCell data e.1 e.2 : ℤ) ∣
      b * ((canonicalLargeOwnerCell data cCell.1 cCell.2 : ℤ) * s) -
        4 * sign * a *
          ((canonicalLargeOwnerCell data rCell.1 rCell.2 : ℤ) * r) := by
  have heSquare := (canonicalLargeOwnerSupport_spec data hfour).1 e he
  have hPgt := (canonicalLargeOwnerSupport_spec data hfour).2.1 e he
  have hPne : canonicalLargeOwnerCell data e.1 e.2 ≠ 0 := by omega
  have hx : ((n + e.1 : ℕ) : ℤ) =
      (canonicalLargeOwnerCell data e.1 e.2 : ℤ) *
        canonicalLargeOwnerCell data rCell.1 rCell.2 * r := by
    exact_mod_cast hrFactor
  have hz : ((n + d + e.2 : ℕ) : ℤ) =
      (canonicalLargeOwnerCell data e.1 e.2 : ℤ) *
        canonicalLargeOwnerCell data cCell.1 cCell.2 * s := by
    exact_mod_cast hcolFactor
  have hupperNat :
      n + d + e.2 = (n + e.1) + (d + e.2 - e.1) := by
    have heRowK := (Finset.mem_Icc.mp heSquare.1).2
    omega
  have hupperInt : ((n + d + e.2 : ℕ) : ℤ) =
      ((n + e.1 : ℕ) : ℤ) + ((d + e.2 - e.1 : ℕ) : ℤ) := by
    exact_mod_cast hupperNat
  exact normalized_square_implies_owner_dvd_column_cofactor_defect
    hPne hx hz hupperInt hsquare

#print axioms coprime_partner_dvd_cofactor_sum
#print axioms canonicalLargeOwnerRowAggregate_eq_allCells
#print axioms canonicalLargeOwner_lower_term_factorization
#print axioms canonicalLargeOwnerRowAggregate_product_eq_mass
#print axioms canonicalLargeOwnerRowCofactor_product_eq_smallPart
#print axioms canonicalLargeOwnerColumnProduct_dvd_modifiedUpper
#print axioms canonicalLargeOwner_modified_upper_term_factorization
#print axioms canonicalLargeOwnerColumnCofactor_product_eq_smallPart
#print axioms canonicalLargeOwnerSupport_rowCofactor_product_eq_weighted
#print axioms canonicalLargeOwnerSupport_columnCofactor_product_eq_weighted
#print axioms canonicalLargeOwnerSupport_rowCofactor_product_eq_smallPart_sq
#print axioms canonicalLargeOwnerSupport_columnCofactor_product_eq_smallPart_sq
#print axioms canonicalLargeOwnerSupport_rowColumnCofactor_product_eq_smallPart_pow_four
#print axioms canonicalLargeOwnerRowPartnerProduct_le_localCollisionDefect
#print axioms canonicalLargeOwnerSupport_rowAggregate_product_eq_weighted
#print axioms canonicalLargeOwnerRowPartnerProduct_product_eq_mass
#print axioms canonicalLargeOwner_mass_le_collisionDefect_of_rowTwo
#print axioms canonicalLargeOwner_mass_sq_le_collisionProduct_of_rowTwo
#print axioms canonicalLargeOwner_twoRegular_weighted_stability
#print axioms square_dvd_owner_mul_iff_owner_dvd_int
#print axioms normalized_square_implies_owner_dvd_column_cofactor_defect
#print axioms two_regular_local_cofactor_relations
#print axioms canonicalLargeOwner_exists_partner_cofactors
#print axioms canonicalLargeOwner_tangent_cofactor_dvd

end Erdos686Variant
end Erdos686
