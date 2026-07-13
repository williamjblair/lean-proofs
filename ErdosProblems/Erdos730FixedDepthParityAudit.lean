/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos730FixedDepthParity

/-!
# Audit surface for the Erdős 730 fixed-depth parity recurrence

The producer is checked at the empty-string boundary and at two concrete odd
alphabets.  For base five (`H=3`) at depth four, the exact counts are
`313` and `312`; for base seven (`H=4`) at depth three, they are `171` and
`172`.  These examples exercise both signs of the alternating discrepancy.
-/

namespace Erdos730

theorem audit_empty_digit_string_counts :
    evenDigitParityCount 3 2 0 = 1 ∧
      oddDigitParityCount 3 2 0 = 0 := by
  norm_num

theorem audit_base_five_depth_four_counts :
    evenDigitParityCount 3 2 4 = 313 ∧
      oddDigitParityCount 3 2 4 = 312 := by
  norm_num [evenDigitParityCount, oddDigitParityCount, digitParityCounts]

theorem audit_base_seven_depth_three_counts :
    evenDigitParityCount 4 3 3 = 171 ∧
      oddDigitParityCount 4 3 3 = 172 := by
  norm_num [evenDigitParityCount, oddDigitParityCount, digitParityCounts]

theorem audit_base_five_depth_four_absolute_error :
    Int.natAbs
        (2 * (evenDigitParityCount 3 2 4 : ℤ) - (5 ^ 4 : ℕ)) = 1 := by
  exact halfDigitParity_exactAbsoluteError 3 4 (by norm_num)

theorem audit_base_seven_depth_three_signed_error :
    2 * (evenDigitParityCount 4 3 3 : ℤ) - (7 ^ 3 : ℕ) = -1 := by
  norm_num [evenDigitParityCount, digitParityCounts]

theorem audit_base_five_depth_four_probability_error :
    |(evenDigitParityCount 3 2 4 : ℝ) / (5 ^ 4 : ℕ) - 1 / 2| =
      1 / 1250 := by
  rw [halfDigitParity_probabilityError 3 4 (by norm_num)]
  norm_num

theorem audit_depth_zero_probability_boundary :
    |(evenDigitParityCount 3 2 0 : ℝ) / (5 ^ 0 : ℕ) - 1 / 2| =
      1 / 2 := by
  rw [halfDigitParity_probabilityError 3 0 (by norm_num)]
  norm_num

#print axioms digitParityCounts_total
#print axioms digitParityCounts_intDifference
#print axioms halfDigitParity_intDifference
#print axioms halfDigitParity_total
#print axioms halfDigitParity_exactAbsoluteError
#print axioms halfDigitParity_realAbsoluteError
#print axioms halfDigitParity_probabilityError
#print axioms audit_empty_digit_string_counts
#print axioms audit_base_five_depth_four_counts
#print axioms audit_base_seven_depth_three_counts
#print axioms audit_base_five_depth_four_absolute_error
#print axioms audit_base_seven_depth_three_signed_error
#print axioms audit_base_five_depth_four_probability_error
#print axioms audit_depth_zero_probability_boundary

end Erdos730
