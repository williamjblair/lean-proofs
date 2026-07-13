/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos730FullDensityBudget

/-!
# Audit surface for the Erdős 730 logarithmic density budget

This module independently checks the two indexing boundaries (`r=0` and
`r=7`), the six `U` arguments, the final positive rational margin, and the
kernel-dependency surface of every substantive theorem in the certificate.
-/

namespace Erdos730

theorem audit_densityBudgetTerm_zero : densityBudgetTerm 0 = 0 := by
  simp [densityBudgetTerm]

theorem audit_densityBudgetTerm_one :
    densityBudgetTerm 1 = (1 / 4 : ℝ) * Real.log (3 / 2) := by
  norm_num [densityBudgetTerm]

theorem audit_tail_starts_at_seven :
    Real.log ((9 : ℝ) / 8) ≤ 1 / 8 := by
  have h := log_density_ratio_le_inv_succ 7
  norm_num at h ⊢
  exact h

theorem audit_six_U_arguments :
    2 * 1 + 3 = 5 ∧ 2 * 2 + 3 = 7 ∧ 2 * 3 + 3 = 9 ∧
      2 * 4 + 3 = 11 ∧ 2 * 5 + 3 = 13 ∧ 2 * 6 + 3 = 15 := by
  norm_num

theorem audit_target_margin_positive :
    (0 : ℝ) < (2344391769572639 : ℝ) / 22462131847034880000 := by
  norm_num

theorem audit_total_upper_below_target :
    (21498408212212214497 : ℝ) / 22462131847034880000 <
      (2393 : ℝ) / 2500 := by
  norm_num

#print axioms log_one_add_div_one_sub_lt_atanhLogUpper
#print axioms log_succ_div_pred_lt_U
#print axioms U_three
#print axioms U_five
#print axioms U_seven
#print axioms U_nine
#print axioms U_eleven
#print axioms U_thirteen
#print axioms U_fifteen
#print axioms log_density_ratio_lt_U
#print axioms densityBudgetTerm_summable
#print axioms densityBudget_tail_le
#print axioms densityBudget_finite_and_tail_certificate
#print axioms densityBudgetSeries_lt_certificate
#print axioms log_two_lt_U_three
#print axioms densityBudget_total_upper_identity
#print axioms densityBudget_total_lt_exact
#print axioms densityBudget_target_difference
#print axioms densityBudget_final_lt
#print axioms audit_densityBudgetTerm_zero
#print axioms audit_densityBudgetTerm_one
#print axioms audit_tail_starts_at_seven
#print axioms audit_six_U_arguments
#print axioms audit_target_margin_positive
#print axioms audit_total_upper_below_target

end Erdos730
