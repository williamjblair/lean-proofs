/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.Core.CanonicalLargeOwnerCapacity

/-!
# Erdős 686: exact collision defect for canonical large owners

The row and signed-diagonal capacity products give a multiplicative measure
of how far the large-owner support is from a row-diagonal matching.  At a
cell `e`, compare its complete row product and complete diagonal product;
their maximum is the local collision envelope.  Dividing that envelope by
the owner at `e` gives the local collision cofactor.

The product of the envelopes is exactly the complete large-prime mass times
the product of the local cofactors.  If that defect is one, every local
cofactor is one, and pairwise coprimality then forces both row and diagonal
coordinates to be injective on the support.  No connectedness or
minimum-degree hypothesis is used.
-/

namespace Erdos686
namespace Erdos686Variant

open scoped BigOperators

/-- Complete large-owner product in one lower row. -/
def canonicalLargeOwnerRowAggregate
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t) (j : ℕ) : ℕ :=
  ∏ e ∈ canonicalLargeOwnerRowSupport data j,
    canonicalLargeOwnerCell data e.1 e.2

/-- Complete large-owner product on one signed diagonal. -/
def canonicalLargeOwnerDiagonalAggregate
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t) (h : ℕ) : ℕ :=
  ∏ e ∈ canonicalLargeOwnerDiagonalSupport data h,
    canonicalLargeOwnerCell data e.1 e.2

/-- The larger of the row and signed-diagonal aggregate products through a
cell. -/
def canonicalLargeOwnerCollisionEnvelope
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    (e : ℕ × ℕ) : ℕ :=
  max (canonicalLargeOwnerRowAggregate data e.1)
    (canonicalLargeOwnerDiagonalAggregate data
      (canonicalOwnerDiagonalIndex k e))

/-- Local multiplicative collision cofactor at a support cell. -/
def canonicalLargeOwnerLocalCollisionDefect
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    (e : ℕ × ℕ) : ℕ :=
  canonicalLargeOwnerCollisionEnvelope data e /
    canonicalLargeOwnerCell data e.1 e.2

/-- Product of all local collision envelopes. -/
def canonicalLargeOwnerCollisionProduct
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t) : ℕ :=
  ∏ e ∈ canonicalLargeOwnerSupport data,
    canonicalLargeOwnerCollisionEnvelope data e

/-- Product of all local collision cofactors. -/
def canonicalLargeOwnerCollisionDefect
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t) : ℕ :=
  ∏ e ∈ canonicalLargeOwnerSupport data,
    canonicalLargeOwnerLocalCollisionDefect data e

theorem canonicalLargeOwnerCell_dvd_rowAggregate
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    {e : ℕ × ℕ} (he : e ∈ canonicalLargeOwnerSupport data) :
    canonicalLargeOwnerCell data e.1 e.2 ∣
      canonicalLargeOwnerRowAggregate data e.1 := by
  classical
  unfold canonicalLargeOwnerRowAggregate
  apply Finset.dvd_prod_of_mem
  exact Finset.mem_filter.mpr ⟨he, rfl⟩

theorem canonicalLargeOwnerCell_dvd_diagonalAggregate
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    {e : ℕ × ℕ} (he : e ∈ canonicalLargeOwnerSupport data) :
    canonicalLargeOwnerCell data e.1 e.2 ∣
      canonicalLargeOwnerDiagonalAggregate data
        (canonicalOwnerDiagonalIndex k e) := by
  classical
  unfold canonicalLargeOwnerDiagonalAggregate
  apply Finset.dvd_prod_of_mem
  exact Finset.mem_filter.mpr ⟨he, rfl⟩

theorem canonicalLargeOwnerCell_dvd_collisionEnvelope
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    {e : ℕ × ℕ} (he : e ∈ canonicalLargeOwnerSupport data) :
    canonicalLargeOwnerCell data e.1 e.2 ∣
      canonicalLargeOwnerCollisionEnvelope data e := by
  unfold canonicalLargeOwnerCollisionEnvelope
  rcases max_choice
      (canonicalLargeOwnerRowAggregate data e.1)
      (canonicalLargeOwnerDiagonalAggregate data
        (canonicalOwnerDiagonalIndex k e)) with h | h
  · rw [h]
    exact canonicalLargeOwnerCell_dvd_rowAggregate data he
  · rw [h]
    exact canonicalLargeOwnerCell_dvd_diagonalAggregate data he

/-- Exact factorization of the collision product into total owner mass and
the basis-independent local collision defect. -/
theorem canonicalLargeOwnerCollisionProduct_eq_mass_mul_defect
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t) :
    canonicalLargeOwnerCollisionProduct data =
      kLargePart k (blockProduct k n) *
        canonicalLargeOwnerCollisionDefect data := by
  classical
  rw [← canonicalLargeOwnerSupport_product_eq_kLargePart data]
  unfold canonicalLargeOwnerCollisionProduct
  unfold canonicalLargeOwnerCollisionDefect
  unfold canonicalLargeOwnerLocalCollisionDefect
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro e he
  exact (Nat.mul_div_cancel'
    (canonicalLargeOwnerCell_dvd_collisionEnvelope data he)).symm

/-- Equality between the collision product and total owner mass is exactly
the statement that the collision defect is one. -/
theorem canonicalLargeOwnerCollisionProduct_eq_mass_iff_defect_eq_one
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t) :
    canonicalLargeOwnerCollisionProduct data =
        kLargePart k (blockProduct k n) ↔
      canonicalLargeOwnerCollisionDefect data = 1 := by
  rw [canonicalLargeOwnerCollisionProduct_eq_mass_mul_defect]
  constructor
  · intro h
    apply Nat.eq_of_mul_eq_mul_left
      (Nat.pos_of_ne_zero (kLargePart_ne_zero k (blockProduct k n)))
    simpa using h
  · intro h
    simp [h]

private theorem localCollisionDefect_eq_one_of_global
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    (hdefect : canonicalLargeOwnerCollisionDefect data = 1)
    {e : ℕ × ℕ} (he : e ∈ canonicalLargeOwnerSupport data) :
    canonicalLargeOwnerLocalCollisionDefect data e = 1 := by
  have hall := (Finset.prod_eq_one_iff.mp hdefect) e he
  simpa [canonicalLargeOwnerCollisionDefect] using hall

private theorem collisionEnvelope_eq_cell_of_defect_eq_one
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    (hdefect : canonicalLargeOwnerCollisionDefect data = 1)
    {e : ℕ × ℕ} (he : e ∈ canonicalLargeOwnerSupport data) :
    canonicalLargeOwnerCollisionEnvelope data e =
      canonicalLargeOwnerCell data e.1 e.2 := by
  have hlocal := localCollisionDefect_eq_one_of_global data hdefect he
  unfold canonicalLargeOwnerLocalCollisionDefect at hlocal
  have hdvd := canonicalLargeOwnerCell_dvd_collisionEnvelope data he
  have hmul := Nat.mul_div_cancel' hdvd
  rw [hlocal, mul_one] at hmul
  exact hmul.symm

private theorem canonicalLargeOwnerCell_gt_one_of_mem
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    {e : ℕ × ℕ} (he : e ∈ canonicalLargeOwnerSupport data) :
    1 < canonicalLargeOwnerCell data e.1 e.2 := by
  have hne := (Finset.mem_filter.mp he).2
  have hpos : 0 < canonicalLargeOwnerCell data e.1 e.2 := by
    unfold canonicalLargeOwnerCell
    apply Finset.prod_pos
    intro p hp
    split
    · exact pow_pos (prime_of_mem_factorization_support
        (Finset.mem_filter.mp hp).1).pos _
    · norm_num
  omega

private theorem canonicalLargeOwnerRowAggregate_pos
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t) (j : ℕ) :
    0 < canonicalLargeOwnerRowAggregate data j := by
  unfold canonicalLargeOwnerRowAggregate
  apply Finset.prod_pos
  intro e he
  exact lt_trans Nat.zero_lt_one
    (canonicalLargeOwnerCell_gt_one_of_mem data
      (Finset.mem_filter.mp he).1)

private theorem canonicalLargeOwnerDiagonalAggregate_pos
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t) (h : ℕ) :
    0 < canonicalLargeOwnerDiagonalAggregate data h := by
  unfold canonicalLargeOwnerDiagonalAggregate
  apply Finset.prod_pos
  intro e he
  exact lt_trans Nat.zero_lt_one
    (canonicalLargeOwnerCell_gt_one_of_mem data
      (Finset.mem_filter.mp he).1)

/-- Unit collision defect forces row injectivity on the complete nontrivial
large-owner support. -/
theorem canonicalLargeOwnerSupport_row_injective_of_collisionDefect_eq_one
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    (hdefect : canonicalLargeOwnerCollisionDefect data = 1) :
    ∀ a ∈ canonicalLargeOwnerSupport data,
      ∀ b ∈ canonicalLargeOwnerSupport data,
        ownerCellRow a = ownerCellRow b → a = b := by
  intro a ha b hb hrow
  by_contra hab
  have henv := collisionEnvelope_eq_cell_of_defect_eq_one data hdefect ha
  have hbDvdRow := canonicalLargeOwnerCell_dvd_rowAggregate data hb
  have hrowEq : b.1 = a.1 := by simpa [ownerCellRow] using hrow.symm
  have hbDvdRowA : canonicalLargeOwnerCell data b.1 b.2 ∣
      canonicalLargeOwnerRowAggregate data a.1 := by
    simpa [hrowEq] using hbDvdRow
  have hrowLeEnvelope : canonicalLargeOwnerRowAggregate data a.1 ≤
      canonicalLargeOwnerCollisionEnvelope data a := by
    exact le_max_left _ _
  have hrowPos : 0 < canonicalLargeOwnerRowAggregate data a.1 :=
    canonicalLargeOwnerRowAggregate_pos data a.1
  have haDvdRow := canonicalLargeOwnerCell_dvd_rowAggregate data ha
  have hrowEqA : canonicalLargeOwnerRowAggregate data a.1 =
      canonicalLargeOwnerCell data a.1 a.2 := by
    apply Nat.le_antisymm
    · simpa [henv] using hrowLeEnvelope
    · exact Nat.le_of_dvd hrowPos haDvdRow
  have hbDvdA : canonicalLargeOwnerCell data b.1 b.2 ∣
      canonicalLargeOwnerCell data a.1 a.2 := by
    rwa [← hrowEqA]
  have hcop := (canonicalLargeOwnerCells_pairwise_coprime data hab).symm
  have hbOne := hcop.eq_one_of_dvd hbDvdA
  have hbGt := canonicalLargeOwnerCell_gt_one_of_mem data hb
  omega

/-- Unit collision defect forces signed-diagonal injectivity on the complete
nontrivial large-owner support. -/
theorem canonicalLargeOwnerSupport_diagonal_injective_of_collisionDefect_eq_one
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    (hdefect : canonicalLargeOwnerCollisionDefect data = 1) :
    ∀ a ∈ canonicalLargeOwnerSupport data,
      ∀ b ∈ canonicalLargeOwnerSupport data,
        ownerCellOffset a = ownerCellOffset b → a = b := by
  intro a ha b hb hoffset
  have hrowEq : a.1 = b.1 := by
    by_contra hrow
    have hdiagIndex : canonicalOwnerDiagonalIndex k b =
        canonicalOwnerDiagonalIndex k a := by
      have haSquare := (Finset.mem_product.mp
        (Finset.mem_filter.mp ha).1)
      have hbSquare := (Finset.mem_product.mp
        (Finset.mem_filter.mp hb).1)
      simp only [canonicalOwnerDiagonalIndex, ownerCellOffset,
        ownerDiagonalOffset, ownerCellColumn, ownerCellRow] at *
      omega
    have henv := collisionEnvelope_eq_cell_of_defect_eq_one data hdefect ha
    have hbDvdDiag := canonicalLargeOwnerCell_dvd_diagonalAggregate data hb
    have hbDvdDiagA : canonicalLargeOwnerCell data b.1 b.2 ∣
        canonicalLargeOwnerDiagonalAggregate data
          (canonicalOwnerDiagonalIndex k a) := by
      simpa [hdiagIndex] using hbDvdDiag
    have hdiagLeEnvelope :
        canonicalLargeOwnerDiagonalAggregate data
            (canonicalOwnerDiagonalIndex k a) ≤
          canonicalLargeOwnerCollisionEnvelope data a := by
      exact le_max_right _ _
    have hdiagPos : 0 < canonicalLargeOwnerDiagonalAggregate data
        (canonicalOwnerDiagonalIndex k a) :=
      canonicalLargeOwnerDiagonalAggregate_pos data _
    have haDvdDiag := canonicalLargeOwnerCell_dvd_diagonalAggregate data ha
    have hdiagEq :
        canonicalLargeOwnerDiagonalAggregate data
            (canonicalOwnerDiagonalIndex k a) =
          canonicalLargeOwnerCell data a.1 a.2 := by
      apply Nat.le_antisymm
      · rw [← henv]
        exact hdiagLeEnvelope
      · exact Nat.le_of_dvd hdiagPos haDvdDiag
    have hbDvdA : canonicalLargeOwnerCell data b.1 b.2 ∣
        canonicalLargeOwnerCell data a.1 a.2 := by
      rwa [← hdiagEq]
    have hab : b ≠ a := by
      intro h
      exact hrow (congrArg Prod.fst h).symm
    have hcop := canonicalLargeOwnerCells_pairwise_coprime data hab
    have hbOne := hcop.eq_one_of_dvd hbDvdA
    have hbGt := canonicalLargeOwnerCell_gt_one_of_mem data hb
    omega
  have hcolEq : a.2 = b.2 := by
    simp only [ownerCellOffset, ownerDiagonalOffset, ownerCellColumn,
      ownerCellRow] at hoffset
    omega
  exact Prod.ext hrowEq hcolEq

/-- Defect one is an exact sufficient condition for the entire canonical
large-owner support to be a row-diagonal matching. -/
theorem canonicalLargeOwnerSupport_matching_of_collisionDefect_eq_one
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    (hdefect : canonicalLargeOwnerCollisionDefect data = 1) :
    (∀ a ∈ canonicalLargeOwnerSupport data,
      ∀ b ∈ canonicalLargeOwnerSupport data,
        ownerCellRow a = ownerCellRow b → a = b) ∧
    (∀ a ∈ canonicalLargeOwnerSupport data,
      ∀ b ∈ canonicalLargeOwnerSupport data,
        ownerCellOffset a = ownerCellOffset b → a = b) := by
  exact ⟨
    canonicalLargeOwnerSupport_row_injective_of_collisionDefect_eq_one
      data hdefect,
    canonicalLargeOwnerSupport_diagonal_injective_of_collisionDefect_eq_one
      data hdefect⟩

/-- Equality of the collision product and the complete large-prime mass is
an owner-facing sufficient condition for the full support to be a matching. -/
theorem canonicalLargeOwnerSupport_matching_of_collisionProduct_eq_mass
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    (hcollision : canonicalLargeOwnerCollisionProduct data =
      kLargePart k (blockProduct k n)) :
    (∀ a ∈ canonicalLargeOwnerSupport data,
      ∀ b ∈ canonicalLargeOwnerSupport data,
        ownerCellRow a = ownerCellRow b → a = b) ∧
    (∀ a ∈ canonicalLargeOwnerSupport data,
      ∀ b ∈ canonicalLargeOwnerSupport data,
        ownerCellOffset a = ownerCellOffset b → a = b) := by
  apply canonicalLargeOwnerSupport_matching_of_collisionDefect_eq_one data
  exact (canonicalLargeOwnerCollisionProduct_eq_mass_iff_defect_eq_one
    data).mp hcollision

/-- Exact multiplicative endpoint of the uniform two-regular relaxation.
If a support has `2*k` equal owners, every local row and diagonal envelope
is the square of that owner, and a selected matching has `k` cells, then the
collision product is exactly the square of the total mass while the matching
product is exactly its square root.  Thus the collision exponent two cannot
be improved by row/diagonal capacities alone. -/
theorem uniform_two_regular_collision_sharpness
    {α : Type*} (S T : Finset α) (P rowLoad diagonalLoad : α → ℕ)
    {k z : ℕ}
    (hT : T ⊆ S)
    (hScard : S.card = 2 * k)
    (hTcard : T.card = k)
    (hP : ∀ e ∈ S, P e = z)
    (hrow : ∀ e ∈ S, rowLoad e = z ^ 2)
    (hdiag : ∀ e ∈ S, diagonalLoad e = z ^ 2) :
    (∏ e ∈ S, max (rowLoad e) (diagonalLoad e)) =
        (∏ e ∈ S, P e) ^ 2 ∧
      (∏ e ∈ T, P e) ^ 2 = ∏ e ∈ S, P e := by
  classical
  have hPOnT : ∀ e ∈ T, P e = z := by
    intro e he
    exact hP e (hT he)
  constructor
  · calc
      (∏ e ∈ S, max (rowLoad e) (diagonalLoad e)) =
          ∏ _e ∈ S, z ^ 2 := by
            apply Finset.prod_congr rfl
            intro e he
            rw [hrow e he, hdiag e he]
            simp
      _ = (z ^ 2) ^ (2 * k) := by simp [Finset.prod_const, hScard]
      _ = (z ^ (2 * k)) ^ 2 := by ring
      _ = (∏ e ∈ S, P e) ^ 2 := by
        congr 1
        calc
          z ^ (2 * k) = ∏ _e ∈ S, z := by
            simp [Finset.prod_const, hScard]
          _ = ∏ e ∈ S, P e := by
            apply Finset.prod_congr rfl
            intro e he
            rw [hP e he]
  · calc
      (∏ e ∈ T, P e) ^ 2 = (z ^ k) ^ 2 := by
        congr 1
        calc
          (∏ e ∈ T, P e) = ∏ _e ∈ T, z := by
            apply Finset.prod_congr rfl
            intro e he
            rw [hPOnT e he]
          _ = z ^ k := by simp [Finset.prod_const, hTcard]
      _ = z ^ (2 * k) := by ring
      _ = ∏ _e ∈ S, z := by simp [Finset.prod_const, hScard]
      _ = ∏ e ∈ S, P e := by
        apply Finset.prod_congr rfl
        intro e he
        rw [hP e he]

#print axioms canonicalLargeOwnerCollisionProduct_eq_mass_mul_defect
#print axioms canonicalLargeOwnerCollisionProduct_eq_mass_iff_defect_eq_one
#print axioms canonicalLargeOwnerSupport_matching_of_collisionDefect_eq_one
#print axioms canonicalLargeOwnerSupport_matching_of_collisionProduct_eq_mass
#print axioms uniform_two_regular_collision_sharpness

end Erdos686Variant
end Erdos686
