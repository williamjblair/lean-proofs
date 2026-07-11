/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos730FirstPowerRoutes

/-!
# Erdős 730 first-power routes: independent kernel audit

This module imports the frozen producer so its dependency is replayed, but
independently reproves each generic algebraic node used by the hostile audit.
It also kernel-checks the exact rational falsifiers, threshold witnesses, and
literal arithmetic of the short/non-top Q/S examples.

It does not assert the global prime/root aggregation, the exhaustive campaign
coverage bridge, or the remaining `1779/2500-delta` estimate.
-/

namespace Erdos730
namespace FirstPowerRoutesAudit

open UnitRangeBlock

/-- Independent proof of the fixed upper-output slope identity. -/
theorem fixed_upper_slope_audit
    (A B C u p z : ℤ) :
    p ^ 2 ∣
      quadraticBranch A p B C (u + p * z) -
        quadraticBranch A p B C u - p * z * B := by
  refine ⟨A * (2 * u * z + p * z ^ 2), ?_⟩
  simp [quadraticBranch]
  ring

/-- Independent cleared-form proof of the `6/5` endpoint normalization. -/
theorem endpoint_six_fifths_audit
    {C q P M N X : ℕ}
    (hcritical : 10 * P + 6 ≤ N)
    (hclass : q * (N - 1) ≤ X)
    (hcount : C * P ≤ M * (N + 2 * P)) :
    5 * C * q * P ≤ 6 * M * X := by
  have hcover : 5 * (N + 2 * P) ≤ 6 * (N - 1) := by
    omega
  have hcountFive : 5 * (C * P) ≤ 5 * (M * (N + 2 * P)) :=
    Nat.mul_le_mul_left 5 hcount
  have hqCover : q * (5 * (N + 2 * P)) ≤ q * (6 * (N - 1)) :=
    Nat.mul_le_mul_left q hcover
  have hqClass : q * (6 * (N - 1)) ≤ 6 * X := by
    calc
      q * (6 * (N - 1)) = 6 * (q * (N - 1)) := by ring
      _ ≤ 6 * X := Nat.mul_le_mul_left 6 hclass
  calc
    5 * C * q * P = q * (5 * (C * P)) := by ring
    _ ≤ q * (5 * (M * (N + 2 * P))) :=
      Nat.mul_le_mul_left q hcountFive
    _ = M * (q * (5 * (N + 2 * P))) := by ring
    _ ≤ M * (6 * X) :=
      Nat.mul_le_mul_left M (le_trans hqCover hqClass)
    _ = 6 * M * X := by ring

/-- Independent Q low-digit inequality. -/
theorem q_low_digit_audit
    {p c low : ℕ}
    (hc : 0 < c)
    (heq : 12 * low = 7 * p + 41 * c)
    (hsmall : 41 * c < 5 * p) :
    p < 2 * low ∧ low < p := by
  omega

/-- Independent S low-digit inequality. -/
theorem s_low_digit_audit
    {p c low : ℕ}
    (heq : 12 * low + 43 * c + 6 = 7 * p)
    (hsmall : 43 * c + 6 < p) :
    p < 2 * low ∧ low < p := by
  omega

/-- Independent Q square-threshold implication. -/
theorem q_square_threshold_audit
    {p c : ℕ}
    (hp : 66 ≤ p)
    (hsquare : c ^ 2 < p) :
    41 * c < 5 * p := by
  by_cases hc : c ≤ 8
  · omega
  · have hc9 : 9 ≤ c := by omega
    nlinarith [sq_nonneg (c : ℤ)]

/-- Independent S square-threshold implication. -/
theorem s_square_threshold_audit
    {p c : ℕ}
    (hp : 1856 ≤ p)
    (hsquare : c ^ 2 < p) :
    43 * c + 6 < p := by
  by_cases hc : c ≤ 43
  · omega
  · have hc44 : 44 ≤ c := by omega
    nlinarith [sq_nonneg (c : ℤ)]

/-- Exact rational falsifiers and retained finite boundary. -/
theorem aligned_ratio_audit :
    (2 : ℚ) < 125 / 54 ∧
    (2 : ℚ) < 7889 / 3072 ∧
    (7889 : ℚ) / 3072 < 8 / 3 := by
  norm_num

/-- Exact uninflated shortest-block falsifier. -/
theorem uninflated_ratio_audit :
    (1 : ℚ) < 5054 / 4125 := by
  norm_num

/-- Exact higher-power ceiling and residual arithmetic. -/
theorem budget_arithmetic_audit :
    (174 : ℚ) / 625 < 3 / 10 ∧
    (1 : ℚ) - 1 / 100 - 174 / 625 = 1779 / 2500 := by
  norm_num

/-- The natural-number threshold predecessors really fail. -/
theorem threshold_predecessors_audit :
    (8 : ℕ) ^ 2 < 65 ∧ ¬41 * 8 < 5 * 65 ∧
    (43 : ℕ) ^ 2 < 1855 ∧ ¬43 * 43 + 6 < 1855 := by
  norm_num

/-- Kernel primality certificate for the retained short witness. -/
theorem short_witness_prime_audit : Nat.Prime 30000001 := by
  norm_num

/-- Exact Q short/non-top witness arithmetic and base-`p` digits. -/
theorem q_short_witness_audit :
    72 * 5289 * 304699465 + 13 = 30000001 * 3867733 ∧
    3867733 % 30000001 ≠ 0 ∧
    30000001 < 3867733 ^ 2 ∧
    12 * 261788783513863207673 =
      7 * 30000001 * 3867733 ^ 2 + 41 * 3867733 ∧
    261788783513863207673 =
      714754 + 30000001 * 12202043 + 30000001 ^ 2 * 290876 ∧
    714754 < 15000001 ∧ 12202043 < 15000001 ∧ 290876 < 15000001 ∧
    714754 ≠ 0 := by
  norm_num

/-- Exact S short/non-top witness arithmetic and base-`p` digits. -/
theorem s_short_witness_audit :
    72 * 5289 * 101483822 + 19 = 30000001 * 1288195 ∧
    1288195 % 30000001 ≠ 0 ∧
    30000001 < 1288195 ^ 2 ∧
    12 * 29040312233443259482 + 43 * 1288195 + 6 =
      7 * 30000001 * 1288195 ^ 2 ∧
    29040312233443259482 =
      12883968 + 30000001 * 343247 + 30000001 ^ 2 * 32267 ∧
    12883968 < 15000001 ∧ 343247 < 15000001 ∧ 32267 < 15000001 ∧
    12883968 ≠ 15000000 := by
  norm_num

/-- Exact root-class and critical-length comparison at `X=2^57`. -/
theorem short_class_length_audit :
    1 + ((2 : ℕ) ^ 57 - 4699455) / 30000001 = 4803839443 ∧
    1 + ((2 : ℕ) ^ 57 - 11483819) / 30000001 = 4803839443 ∧
    4803839443 < 8892451300 := by
  norm_num

#print axioms fixed_upper_slope_audit
#print axioms endpoint_six_fifths_audit
#print axioms q_low_digit_audit
#print axioms s_low_digit_audit
#print axioms q_square_threshold_audit
#print axioms s_square_threshold_audit
#print axioms aligned_ratio_audit
#print axioms uninflated_ratio_audit
#print axioms budget_arithmetic_audit
#print axioms threshold_predecessors_audit
#print axioms short_witness_prime_audit
#print axioms q_short_witness_audit
#print axioms s_short_witness_audit
#print axioms short_class_length_audit

end FirstPowerRoutesAudit
end Erdos730
