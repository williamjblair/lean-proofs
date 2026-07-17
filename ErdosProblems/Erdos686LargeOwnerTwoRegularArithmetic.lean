/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686LargeOwnerCollisionStability
import ErdosProblems.Erdos686NormalizedMatching

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
#print axioms square_dvd_owner_mul_iff_owner_dvd_int
#print axioms normalized_square_implies_owner_dvd_column_cofactor_defect
#print axioms two_regular_local_cofactor_relations
#print axioms canonicalLargeOwner_exists_partner_cofactors
#print axioms canonicalLargeOwner_tangent_cofactor_dvd

end Erdos686Variant
end Erdos686
