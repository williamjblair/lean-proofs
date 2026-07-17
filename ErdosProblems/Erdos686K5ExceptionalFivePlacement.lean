/- leanprover/lean4:v4.29.1 mathlib v4.29.1 -/
import ErdosProblems.Erdos686K5ExceptionalEquationFacing

/-!
# Erdős 686, k=5: the five possible 5-adic exceptional placements

After the global quotient-product identity, an owner carrying the prime `5`
forces its designated target to be divisible by `125`.  This file substitutes
the five possible targets into the exact cubic.  The residue depends only on
the fully owned lower row (`j=2` or `j=4`), not on which exceptional upper
column is selected.
-/

namespace Erdos686
namespace Erdos686Variant

/-- Exact cubic residue table for the fully owned lower row `j=2`.  The five
entries correspond, in order, to owner columns `1,...,5`.  Column four is the
unique placement where the cubic has 5-adic valuation two rather than one. -/
theorem k5_exceptional_j2_five_placement_cubic_table
    (x t : ℤ) {i : ℕ} (hi : i = 2 ∨ i = 4) :
    (25 : ℤ) ∣ k5ExceptionalRowCollapseQuotient (5*x)
        (((i : ℤ)-1+125*t) - 2*(5*x)) 2 i - 5 ∧
    (25 : ℤ) ∣ k5ExceptionalRowCollapseQuotient (5*x)
        ((5*(5*x)+(i : ℤ)-2+125*t) - 2*(5*x)) 2 i - 10 ∧
    (25 : ℤ) ∣ k5ExceptionalRowCollapseQuotient (5*x)
        ((-5*(5*x)+(i : ℤ)-3+125*t) - 2*(5*x)) 2 i - 5 ∧
    (125 : ℤ) ∣ k5ExceptionalRowCollapseQuotient (5*x)
        ((5*(5*x)+(i : ℤ)-4+125*t) - 2*(5*x)) 2 i - 25 ∧
    (25 : ℤ) ∣ k5ExceptionalRowCollapseQuotient (5*x)
        (((i : ℤ)-5+125*t) - 2*(5*x)) 2 i - 5 := by
  constructor
  · rcases hi with rfl | rfl <;>
      simp only [k5ExceptionalRowCollapseQuotient] <;> norm_num <;>
      refine ⟨-2734375*t^3 + 421875*t^2*x - 131250*t^2 - 625*t*x^2 +
        13500*t*x - 1525*t + 25*x^3 + 10*x^2 + 11*x - 3, by ring⟩
  constructor
  · rcases hi with rfl | rfl <;>
      simp only [k5ExceptionalRowCollapseQuotient] <;> norm_num <;>
      refine ⟨-2734375*t^3 - 1218750*t^2*x - 65625*t^2 - 160000*t*x^2 -
        19500*t*x + 50*t - 5100*x^3 - 1260*x^2 - 60*x + 2, by ring⟩
  constructor
  · rcases hi with rfl | rfl <;>
      simp only [k5ExceptionalRowCollapseQuotient] <;> norm_num <;>
      refine ⟨-2734375*t^3 + 2062500*t^2*x - 497500*t*x^2 + 575*t +
        38900*x^3 + 20*x^2 - 212*x - 1, by ring⟩
  constructor
  · rcases hi with rfl | rfl <;>
      simp only [k5ExceptionalRowCollapseQuotient] <;> norm_num <;>
      refine ⟨-546875*t^3 - 243750*t^2*x + 13125*t^2 - 32000*t*x^2 +
        3900*t*x + 10*t - 1020*x^3 + 260*x^2 - 12*x - 1, by ring⟩
  · rcases hi with rfl | rfl <;>
      simp only [k5ExceptionalRowCollapseQuotient] <;> norm_num <;>
      refine ⟨-2734375*t^3 + 421875*t^2*x + 131250*t^2 - 625*t*x^2 -
        13500*t*x - 1525*t + 25*x^3 + 30*x^2 + 11*x + 1, by ring⟩

/-- Exact cubic residue table for `j=4`.  Here column two, rather than column
four, is the unique valuation-two placement. -/
theorem k5_exceptional_j4_five_placement_cubic_table
    (x t : ℤ) {i : ℕ} (hi : i = 2 ∨ i = 4) :
    (25 : ℤ) ∣ k5ExceptionalRowCollapseQuotient (5*x)
        (((i : ℤ)-1+125*t) - 2*(5*x)) 4 i - 20 ∧
    (125 : ℤ) ∣ k5ExceptionalRowCollapseQuotient (5*x)
        ((5*(5*x)+(i : ℤ)-2+125*t) - 2*(5*x)) 4 i - 100 ∧
    (25 : ℤ) ∣ k5ExceptionalRowCollapseQuotient (5*x)
        ((-5*(5*x)+(i : ℤ)-3+125*t) - 2*(5*x)) 4 i - 20 ∧
    (25 : ℤ) ∣ k5ExceptionalRowCollapseQuotient (5*x)
        ((5*(5*x)+(i : ℤ)-4+125*t) - 2*(5*x)) 4 i - 15 ∧
    (25 : ℤ) ∣ k5ExceptionalRowCollapseQuotient (5*x)
        (((i : ℤ)-5+125*t) - 2*(5*x)) 4 i - 20 := by
  constructor
  · rcases hi with rfl | rfl <;>
      simp only [k5ExceptionalRowCollapseQuotient] <;> norm_num <;>
      refine ⟨-2734375*t^3 + 421875*t^2*x - 131250*t^2 - 625*t*x^2 +
        13500*t*x - 1525*t + 25*x^3 - 30*x^2 + 11*x - 2, by ring⟩
  constructor
  · rcases hi with rfl | rfl <;>
      simp only [k5ExceptionalRowCollapseQuotient] <;> norm_num <;>
      refine ⟨-546875*t^3 - 243750*t^2*x - 13125*t^2 - 32000*t*x^2 -
        3900*t*x + 10*t - 1020*x^3 - 260*x^2 - 12*x, by ring⟩
  constructor
  · rcases hi with rfl | rfl <;>
      simp only [k5ExceptionalRowCollapseQuotient] <;> norm_num <;>
      refine ⟨-2734375*t^3 + 2062500*t^2*x - 497500*t*x^2 + 575*t +
        38900*x^3 - 20*x^2 - 212*x, by ring⟩
  constructor
  · rcases hi with rfl | rfl <;>
      simp only [k5ExceptionalRowCollapseQuotient] <;> norm_num <;>
      refine ⟨-2734375*t^3 - 1218750*t^2*x + 65625*t^2 - 160000*t*x^2 +
        19500*t*x + 50*t - 5100*x^3 + 1260*x^2 - 60*x - 3, by ring⟩
  · rcases hi with rfl | rfl <;>
      simp only [k5ExceptionalRowCollapseQuotient] <;> norm_num <;>
      refine ⟨-2734375*t^3 + 421875*t^2*x + 131250*t^2 - 625*t*x^2 -
        13500*t*x - 1525*t + 25*x^3 - 10*x^2 + 11*x + 2, by ring⟩

#print axioms k5_exceptional_j2_five_placement_cubic_table
#print axioms k5_exceptional_j4_five_placement_cubic_table

end Erdos686Variant
end Erdos686
