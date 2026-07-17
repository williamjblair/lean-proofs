/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686K5ExceptionalFullSquareSystem

/-!
# Erdős 686, k=5: exact collapse of the aggregate square eliminant

Multiplying the five primitive row defects looks like a new global
congruence.  In fact it is the original block equation modulo the square of
the fully owned lower term.  The column product has the same collapse, with
the exact scalar `-8192`, modulo the square of the upper term.

Thus any successful eliminant must retain individual row and column
cofactors; simply multiplying either five-cell square system cannot close the
exceptional tail.
-/

namespace Erdos686
namespace Erdos686Variant

/-- Five shifted factors with the term at position `h` centered at zero. -/
def k5ShiftedBlockZ (z : ℤ) (h : ℕ) : ℤ :=
  (z + 1 - h) * (z + 2 - h) * (z + 3 - h) *
    (z + 4 - h) * (z + 5 - h)

/-- Cleared quotient-four equation in lower-term/gap coordinates. -/
def k5ExceptionalEquationDefect (x D : ℤ) (j i : ℕ) : ℤ :=
  k5ShiftedBlockZ (x + D) i - 4 * k5ShiftedBlockZ x j

/-- Product of the five primitive row defects, expressed relative to the
crossing diagonal `D`. -/
def k5ExceptionalRowDefectProductZ (x D : ℤ) (i : ℕ) : ℤ :=
  (D + 1 - i + 2 * x) *
  (3 * x - (D + 2 - i)) *
  (D + 3 - i + 7 * x) *
  (3 * x - (D + 4 - i)) *
  (D + 5 - i + 2 * x)

/-- Product of the five primitive column defects. -/
def k5ExceptionalColumnDefectProductZ (x D : ℤ) (j : ℕ) : ℤ :=
  (x + D + 16 * (x + 1 - j)) *
  (x + D - 4 * (x + 2 - j)) *
  (3 * (x + D) + 8 * (x + 3 - j)) *
  (x + D - 4 * (x + 4 - j)) *
  (x + D + 16 * (x + 5 - j))

/-- Exact cubic quotient left after subtracting the block equation from the
row defect product. -/
def k5ExceptionalRowCollapseQuotient (x D : ℤ) (j i : ℕ) : ℤ :=
  if j = 2 ∧ i = 2 then
    5 * (-7*D^3 - 15*D^2*x - 21*D^2 + 23*D*x^2 - 30*D*x + 2*D +
      51*x^3 + 27*x^2 - 66*x + 12)
  else if j = 2 ∧ i = 4 then
    5 * (-7*D^3 - 15*D^2*x + 21*D^2 + 23*D*x^2 + 30*D*x + 2*D +
      51*x^3 - 19*x^2 - 66*x - 20)
  else if j = 4 ∧ i = 2 then
    5 * (-7*D^3 - 15*D^2*x - 21*D^2 + 23*D*x^2 - 30*D*x + 2*D +
      51*x^3 + 19*x^2 - 66*x + 20)
  else
    5 * (-7*D^3 - 15*D^2*x + 21*D^2 + 23*D*x^2 + 30*D*x + 2*D +
      51*x^3 - 27*x^2 - 66*x - 12)

/-- Exact cubic quotient in the column collapse identity. -/
def k5ExceptionalColumnCollapseQuotient (x D : ℤ) (j i : ℕ) : ℤ :=
  if j = 2 ∧ i = 2 then
    5 * (1639*D^3 + 4933*D^2*x + 8208*D^2 + 4997*D*x^2 +
      16512*D*x + 7616*D + 807*x^3 + 5616*x^2 + 7872*x - 6144)
  else if j = 2 ∧ i = 4 then
    5 * (1639*D^3 + 4933*D^2*x - 8176*D^2 + 4997*D*x^2 -
      16256*D*x + 7616*D + 807*x^3 - 10768*x^2 + 7872*x + 10240)
  else if j = 4 ∧ i = 2 then
    5 * (1639*D^3 + 4933*D^2*x + 8176*D^2 + 4997*D*x^2 +
      16256*D*x + 7616*D + 807*x^3 + 10768*x^2 + 7872*x - 10240)
  else
    5 * (1639*D^3 + 4933*D^2*x - 8208*D^2 + 4997*D*x^2 -
      16512*D*x + 7616*D + 807*x^3 - 5616*x^2 + 7872*x + 6144)

/-- Exact row collapse: the aggregate primitive defect differs from the
original equation by `x²` times an explicit cubic. -/
theorem k5_exceptional_row_aggregate_collapse
    (x D : ℤ) {j i : ℕ}
    (hj : j = 2 ∨ j = 4) (hi : i = 2 ∨ i = 4) :
    k5ExceptionalRowDefectProductZ x D i =
      k5ExceptionalEquationDefect x D j i +
        x ^ 2 * k5ExceptionalRowCollapseQuotient x D j i := by
  rcases hj with rfl | rfl <;> rcases hi with rfl | rfl <;>
    simp only [k5ExceptionalRowDefectProductZ,
      k5ExceptionalEquationDefect, k5ShiftedBlockZ,
      k5ExceptionalRowCollapseQuotient] <;> norm_num <;> ring

/-- Exact column collapse: after adding `8192` times the equation, the
aggregate column defect is divisible by the upper term square. -/
theorem k5_exceptional_column_aggregate_collapse
    (x D : ℤ) {j i : ℕ}
    (hj : j = 2 ∨ j = 4) (hi : i = 2 ∨ i = 4) :
    k5ExceptionalColumnDefectProductZ x D j =
      -8192 * k5ExceptionalEquationDefect x D j i +
        (x + D) ^ 2 * k5ExceptionalColumnCollapseQuotient x D j i := by
  rcases hj with rfl | rfl <;> rcases hi with rfl | rfl <;>
    simp only [k5ExceptionalColumnDefectProductZ,
      k5ExceptionalEquationDefect, k5ShiftedBlockZ,
      k5ExceptionalColumnCollapseQuotient] <;> norm_num <;> ring

/-- Consequently both aggregate square divisibilities follow formally from
the original equation alone; no owner or gcd hypothesis is needed. -/
theorem k5_exceptional_aggregate_squares_of_equation
    (x D : ℤ) {j i : ℕ}
    (hj : j = 2 ∨ j = 4) (hi : i = 2 ∨ i = 4)
    (heq : k5ExceptionalEquationDefect x D j i = 0) :
    x ^ 2 ∣ k5ExceptionalRowDefectProductZ x D i ∧
      (x + D) ^ 2 ∣ k5ExceptionalColumnDefectProductZ x D j := by
  constructor
  · rw [k5_exceptional_row_aggregate_collapse x D hj hi, heq, zero_add]
    exact dvd_mul_right _ _
  · rw [k5_exceptional_column_aggregate_collapse x D hj hi, heq,
      mul_zero, zero_add]
    exact dvd_mul_right _ _

/-- The first natural cofactor resultant also vanishes identically.  Modulo
the crossing cofactor one has `D = 3x`; after that substitution the column
cubic is exactly `-512` times the row cubic in every exceptional placement. -/
theorem k5_exceptional_crossing_cofactor_resultant_zero
    (x : ℤ) {j i : ℕ}
    (hj : j = 2 ∨ j = 4) (hi : i = 2 ∨ i = 4) :
    k5ExceptionalColumnCollapseQuotient x (3 * x) j i =
      -512 * k5ExceptionalRowCollapseQuotient x (3 * x) j i := by
  rcases hj with rfl | rfl <;> rcases hi with rfl | rfl <;>
    simp only [k5ExceptionalColumnCollapseQuotient,
      k5ExceptionalRowCollapseQuotient] <;> norm_num <;> ring

#print axioms k5_exceptional_row_aggregate_collapse
#print axioms k5_exceptional_column_aggregate_collapse
#print axioms k5_exceptional_aggregate_squares_of_equation
#print axioms k5_exceptional_crossing_cofactor_resultant_zero

end Erdos686Variant
end Erdos686
