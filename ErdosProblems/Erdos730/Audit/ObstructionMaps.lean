/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos730.ObstructionMaps

/-!
# Audit surface for the Erdős 730 obstruction maps

The checks below independently pin the four slopes, the common quadratic
coefficient, all four residual linear coefficients, the two exceptional
factorizations, and the axiom surface of the substantive algebraic results.
-/

namespace Erdos730
namespace ObstructionMapsAudit

open ObstructionMaps

theorem audit_integer_slopes :
    42 * Tz = 222138 ∧ 72 * Tz = 380808 ∧
    28 * Tz = 148092 ∧ 72 * Tz = 380808 := by
  norm_num [Tz, FullDensityCore.T]

theorem audit_common_coefficient_numeric :
    12 * (222138 : ℤ) ^ 2 / 7 = 84591927504 ∧
    7 * (380808 : ℤ) ^ 2 / 12 = 84591927504 ∧
    54 * (148092 : ℤ) ^ 2 / 14 = 84591927504 ∧
    7 * (380808 : ℤ) ^ 2 / 12 = 84591927504 := by
  norm_num

theorem audit_common_coefficient_symbolic :
    3024 * Tz ^ 2 = 84591927504 := by
  norm_num [Tz, FullDensityCore.T]

theorem audit_residual_coefficients :
    (-246 : ℤ) * Tz = -1301094 ∧
    246 * Tz = 1301094 ∧
    258 * Tz = 1364562 ∧
    (-258 : ℤ) * Tz = -1364562 := by
  norm_num [Tz, FullDensityCore.T]

theorem audit_exceptional_factorizations :
    246 * FullDensityCore.T = 2 * 3 ^ 2 * 41 ^ 2 * 43 ∧
    258 * FullDensityCore.T = 2 * 3 ^ 2 * 41 * 43 ^ 2 := by
  norm_num [FullDensityCore.T]

/-- A concrete parity boundary check for the quotient-valued maps. -/
theorem audit_half_integrality_at_origin :
    2 * PhiR 0 1 = 3 * Sz 0 - 1 ∧
    2 * PhiS 0 1 = 3 * Rz 0 - 1 := by
  constructor
  · simpa using two_mul_PhiR (x := (0 : ℤ)) (c := (1 : ℤ)) (by norm_num)
  · simpa using two_mul_PhiS (x := (0 : ℤ)) (c := (1 : ℤ)) (by norm_num)

#print axioms Tz_eq
#print axioms branch_casts
#print axioms identity_PQz
#print axioms identity_RSz
#print axioms Rz_odd
#print axioms Sz_odd
#print axioms two_dvd_PhiR_numerator
#print axioms two_dvd_PhiS_numerator
#print axioms two_mul_PhiR
#print axioms two_mul_PhiS
#print axioms R_cofactor_odd
#print axioms S_cofactor_odd
#print axioms PhiP_cleared
#print axioms PhiQ_cleared
#print axioms PhiR_cleared
#print axioms PhiS_cleared
#print axioms common_quadratic_coefficient
#print axioms P_shift_branch
#print axioms Q_shift_branch
#print axioms R_shift_branch
#print axioms S_shift_branch
#print axioms R_progression_odd
#print axioms S_progression_odd
#print axioms PhiP_root_progression
#print axioms PhiQ_root_progression
#print axioms PhiR_root_progression
#print axioms PhiS_root_progression
#print axioms residual_linear_coefficients
#print axioms exceptional_coefficient_factorizations
#print axioms prime_dvd_residual_support
#print axioms audit_integer_slopes
#print axioms audit_common_coefficient_numeric
#print axioms audit_common_coefficient_symbolic
#print axioms audit_residual_coefficients
#print axioms audit_exceptional_factorizations
#print axioms audit_half_integrality_at_origin

end ObstructionMapsAudit
end Erdos730
