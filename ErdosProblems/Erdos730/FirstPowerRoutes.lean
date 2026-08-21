/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos730.UnitRangeBlock

/-!
# Erdős 730: first-power block identities and endpoint sharpening

This module banks two algebraic nodes used by the independent attacks on
the remaining `a=1` range:

* at `a=r=1`, the upper output digit changes with the same branch slope
  on every aligned `p`-block;
* in the already-paid `a>=2` subrange, the critical length improves the
  root-class endpoint factor from `2` to `6/5`.

No first-power discrepancy or short/top sieve theorem is assumed here.
-/

namespace Erdos730
namespace FirstPowerRoutes

open UnitRangeBlock

/-- At `a=1`, subtracting the fixed linear block shift leaves a multiple of
`p^2`.  Modulo `p`, the upper output digit therefore moves by `B*z`,
independently of the low-block coordinate `u`. -/
theorem first_power_fixed_upper_slope
    (A B C u p z : ℤ) :
    p ^ 2 ∣
      quadraticBranch A p B C (u + p * z) -
        quadraticBranch A p B C u - p * z * B := by
  refine ⟨A * (2 * u * z + p * z ^ 2), ?_⟩
  simp [quadraticBranch]
  ring

/-- Improved division-free normalization for `r>=a>=2`.

The stronger critical input `10P+6<=N` gives
`(N+2P)/(N-1)<=6/5`; the conclusion is the corresponding cleared form
`C/X <= 6M/(5qP)`. -/
theorem normalized_block_cover_six_fifths
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

/-- Q-branch top-range digit exclusion.  Once
`12*low=7*p+41*c` and the cofactor is small enough that `41c<5p`, the
displayed `low` is a genuine base-`p` digit and is strictly above the
restricted half. -/
theorem q_top_low_digit_large
    {p c low : ℕ}
    (hc : 0 < c)
    (heq : 12 * low = 7 * p + 41 * c)
    (hsmall : 41 * c < 5 * p) :
    p < 2 * low ∧ low < p := by
  omega

/-- S-branch top-range digit exclusion.  Under the corresponding small
cofactor inequality, the low digit lies strictly between `p/2` and `p`. -/
theorem s_top_low_digit_large
    {p c low : ℕ}
    (heq : 12 * low + 43 * c + 6 = 7 * p)
    (hsmall : 43 * c + 6 < p) :
    p < 2 * low ∧ low < p := by
  omega

/-- In the two-digit top regime `c^2<p`, the Q-branch small-cofactor
hypothesis is automatic beyond the explicit finite threshold `p>=66`. -/
theorem q_top_small_cofactor_of_square_lt
    {p c : ℕ}
    (hp : 66 ≤ p)
    (hsquare : c ^ 2 < p) :
    41 * c < 5 * p := by
  by_cases hc : c ≤ 8
  · omega
  · have hc9 : 9 ≤ c := by omega
    nlinarith [sq_nonneg (c : ℤ)]

/-- In the two-digit top regime `c^2<p`, the S-branch small-cofactor
hypothesis is automatic beyond the explicit finite threshold `p>=1856`. -/
theorem s_top_small_cofactor_of_square_lt
    {p c : ℕ}
    (hp : 1856 ≤ p)
    (hsquare : c ^ 2 < p) :
    43 * c + 6 < p := by
  by_cases hc : c ≤ 43
  · omega
  · have hc44 : 44 ≤ c := by omega
    nlinarith [sq_nonneg (c : ℤ)]

/-- Q-branch top exclusion directly from the two-digit hypothesis, outside
an explicit finite prime range. -/
theorem q_top_two_digit_large
    {p c low : ℕ}
    (hp : 66 ≤ p)
    (hc : 0 < c)
    (hsquare : c ^ 2 < p)
    (heq : 12 * low = 7 * p + 41 * c) :
    p < 2 * low ∧ low < p :=
  q_top_low_digit_large hc heq
    (q_top_small_cofactor_of_square_lt hp hsquare)

/-- S-branch top exclusion directly from the two-digit hypothesis, outside
an explicit finite prime range. -/
theorem s_top_two_digit_large
    {p c low : ℕ}
    (hp : 1856 ≤ p)
    (hsquare : c ^ 2 < p)
    (heq : 12 * low + 43 * c + 6 = 7 * p) :
    p < 2 * low ∧ low < p :=
  s_top_low_digit_large heq
    (s_top_small_cofactor_of_square_lt hp hsquare)

/-- Rational ceiling for the sharpened four-branch `a>=2` payment. -/
theorem improved_higher_power_ceiling_lt_three_tenths :
    (174 : ℚ) / 625 < 3 / 10 := by
  norm_num

/-- Exact budget remaining after the strict-band `1/100` payment and the
sharpened `174/625` higher-power payment. -/
theorem remaining_first_power_budget :
    (1 : ℚ) - 1 / 100 - 174 / 625 = 1779 / 2500 := by
  norm_num

#print axioms first_power_fixed_upper_slope
#print axioms normalized_block_cover_six_fifths
#print axioms q_top_low_digit_large
#print axioms s_top_low_digit_large
#print axioms q_top_small_cofactor_of_square_lt
#print axioms s_top_small_cofactor_of_square_lt
#print axioms q_top_two_digit_large
#print axioms s_top_two_digit_large
#print axioms improved_higher_power_ceiling_lt_three_tenths
#print axioms remaining_first_power_budget

end FirstPowerRoutes
end Erdos730
