/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.Core.CanonicalLargeOwnerSupport

/-!
# Erdős 686: multiplicative capacities for canonical large owners

The cardinality bounds on the large-owner support do not record the
arithmetic size available in a row or a signed diagonal.  This file supplies
that missing exact interface.

Every row fibre is a pairwise-coprime family of divisors of one lower term.
Every signed-diagonal fibre is a pairwise-coprime family of divisors of one
term in the centered difference window.  Consequently the complete
above-`k` mass divides both the lower-block lcm and the single
`(2*k-1)`-term centered difference product.

No connectivity, minimum-degree, or matching assumption is used.
-/

namespace Erdos686
namespace Erdos686Variant

open scoped BigOperators

/-- Natural index of the signed diagonal through a cell.  On the
`k × k` owner square it lies in `0, ..., 2*k-2`, and its centered-window
term is exactly `d+i-j`. -/
def canonicalOwnerDiagonalIndex (k : ℕ) (e : ℕ × ℕ) : ℕ :=
  k + e.2 - e.1 - 1

/-- Nontrivial large-owner cells in one lower row. -/
def canonicalLargeOwnerRowSupport
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t) (j : ℕ) :
    Finset (ℕ × ℕ) :=
  (canonicalLargeOwnerSupport data).filter (fun e => e.1 = j)

/-- Nontrivial large-owner cells on one signed diagonal. -/
def canonicalLargeOwnerDiagonalSupport
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t) (h : ℕ) :
    Finset (ℕ × ℕ) :=
  (canonicalLargeOwnerSupport data).filter
    (fun e => canonicalOwnerDiagonalIndex k e = h)

private theorem canonicalLargeOwnerSupport_pairwise_coprime
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t) :
    ((canonicalLargeOwnerSupport data : Finset (ℕ × ℕ)) :
        Set (ℕ × ℕ)).Pairwise
      (Function.onFun Nat.Coprime
        (fun e => canonicalLargeOwnerCell data e.1 e.2)) := by
  intro e he f hf hef
  exact canonicalLargeOwnerCells_pairwise_coprime data hef

private theorem finset_prod_dvd_of_pairwise_coprime_nat
    {ι : Type*}
    (s : Finset ι) (f : ι → ℕ) (z : ℕ)
    (hpair : (s : Set ι).Pairwise (Function.onFun Nat.Coprime f))
    (hdvd : ∀ x ∈ s, f x ∣ z) :
    (∏ x ∈ s, f x) ∣ z := by
  classical
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

/-- The product of all nontrivial above-`k` owners in one row divides the
single lower term in that row. -/
theorem canonicalLargeOwnerRowSupport_product_dvd_lower
    {k n d t j : ℕ} (data : CanonicalOwnerData k n d t) :
    (∏ e ∈ canonicalLargeOwnerRowSupport data j,
      canonicalLargeOwnerCell data e.1 e.2) ∣ n + j := by
  classical
  apply finset_prod_dvd_of_pairwise_coprime_nat
    (canonicalLargeOwnerRowSupport data j)
    (fun e => canonicalLargeOwnerCell data e.1 e.2) (n + j)
  · intro e he f hf hef
    exact canonicalLargeOwnerSupport_pairwise_coprime data
      (Finset.mem_filter.mp he).1 (Finset.mem_filter.mp hf).1 hef
  · intro e he
    have hrow := (Finset.mem_filter.mp he).2
    simpa [hrow] using
      (canonicalLargeOwnerCell_dvd_lower data (j := e.1) (i := e.2))

/-- Exact conversion from a cell's natural diagonal index to its shifted
difference. -/
theorem centeredDiffTerm_eq_shiftedDifference
    {k d : ℕ} {e : ℕ × ℕ}
    (hk : 1 ≤ k) (hd : k ≤ d)
    (he : e.1 ∈ Finset.Icc 1 k ∧ e.2 ∈ Finset.Icc 1 k) :
    d + canonicalOwnerDiagonalIndex k e - (k - 1) =
      d + e.2 - e.1 := by
  rcases e with ⟨j, i⟩
  simp only [canonicalOwnerDiagonalIndex] at *
  have hj := Finset.mem_Icc.mp he.1
  have hi := Finset.mem_Icc.mp he.2
  omega

/-- The product of all nontrivial above-`k` owners on one signed diagonal
divides the corresponding single centered-window term. -/
theorem canonicalLargeOwnerDiagonalSupport_product_dvd_centeredTerm
    {k n d t h : ℕ} (data : CanonicalOwnerData k n d t)
    (hk : 1 ≤ k) (hd : k ≤ d) (hfour : 4 ∣ n + d + t) :
    (∏ e ∈ canonicalLargeOwnerDiagonalSupport data h,
      canonicalLargeOwnerCell data e.1 e.2) ∣
        d + h - (k - 1) := by
  classical
  apply finset_prod_dvd_of_pairwise_coprime_nat
    (canonicalLargeOwnerDiagonalSupport data h)
    (fun e => canonicalLargeOwnerCell data e.1 e.2)
    (d + h - (k - 1))
  · intro e he f hf hef
    exact canonicalLargeOwnerSupport_pairwise_coprime data
      (Finset.mem_filter.mp he).1 (Finset.mem_filter.mp hf).1 hef
  · intro e he
    have heSupport := (Finset.mem_filter.mp he).1
    have heIndex := (Finset.mem_filter.mp he).2
    have heSquare :=
      (canonicalLargeOwnerSupport_spec data hfour).1 e heSupport
    rw [← heIndex]
    rw [centeredDiffTerm_eq_shiftedDifference hk hd heSquare]
    exact canonicalLargeOwnerCell_dvd_shiftedDifference data hfour

/-- The complete above-`k` mass divides the lcm of the lower block. -/
theorem kLargePart_dvd_lowerBlockLcm
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t) :
    kLargePart k (blockProduct k n) ∣ lowerBlockLcm k n := by
  classical
  rw [← canonicalLargeOwnerSupport_product_eq_kLargePart data]
  apply finset_prod_dvd_of_pairwise_coprime_nat
    (canonicalLargeOwnerSupport data)
    (fun e => canonicalLargeOwnerCell data e.1 e.2)
    (lowerBlockLcm k n)
  · exact canonicalLargeOwnerSupport_pairwise_coprime data
  · intro e he
    have heSquare :=
      Finset.mem_product.mp (Finset.mem_filter.mp he).1
    exact dvd_trans
      (canonicalLargeOwnerCell_dvd_lower data)
      (lower_block_term_dvd_lowerBlockLcm heSquare.1)

/-- Global multiplicative diagonal capacity: all above-`k` owner mass fits
inside the one centered window `(d-k+1)...(d+k-1)`. -/
theorem kLargePart_dvd_centeredDiffProduct
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    (hd : k ≤ d)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    kLargePart k (blockProduct k n) ∣ centeredDiffProduct k d := by
  exact dvd_trans (kLargePart_dvd_lowerBlockLcm data)
    (lower_lcm_dvd_centeredDiffProduct_four hd heq)

#print axioms canonicalLargeOwnerRowSupport_product_dvd_lower
#print axioms centeredDiffTerm_eq_shiftedDifference
#print axioms canonicalLargeOwnerDiagonalSupport_product_dvd_centeredTerm
#print axioms kLargePart_dvd_lowerBlockLcm
#print axioms kLargePart_dvd_centeredDiffProduct

end Erdos686Variant
end Erdos686
