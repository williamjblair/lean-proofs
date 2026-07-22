/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.Core.TwoPrimeSecondLift

/-!
# Erdős 686: exact three-bucket local restrictions

Let three pairwise-coprime cleaned components occupy distinct residuals:

`X_i = a P^2`, `X_j = b Q^2`, `X_l = c R^2`, `d = g P Q R`.

The pairwise residual differences and the second local lift eliminate both
opposite squares.  At the `P` owner this gives the fixed divisibility

`P | 3 (C_i abc - 12 D_i g^2 (i-j)(i-l))`.

The third local lift has an equally exact composition:

`P^2 | -3 O_i + 180 E_i g^2 (i-j)(i-l) d`.

The second statement explains why the third lift does not by itself create a
new bounded resultant: modulo `P` its new term is already a multiple of the
gap.  This module proves the integer algebra only.  It does not assume or
assert that the three-bucket tail is closed.
-/

namespace Erdos686
namespace Erdos686Variant

/-- The fixed second-order obstruction at one of three cleaned owners. -/
def threeBucketSecondObstruction
    (C D a b c g deltaLeft deltaRight : ℤ) : ℤ :=
  3 * (C * a * b * c - 12 * D * g ^ 2 * deltaLeft * deltaRight)

/-- The composed third-order obstruction.  In applications
`gap = g * P * Q * R`. -/
def threeBucketThirdObstruction
    (C D E a b c g deltaLeft deltaRight gap : ℤ) : ℤ :=
  -3 * threeBucketSecondObstruction C D a b c g deltaLeft deltaRight +
    180 * E * g ^ 2 * deltaLeft * deltaRight * gap

private lemma pair_product_sub_fixed_dvd_sq
    {P Q R a b c deltaLeft deltaRight : ℤ}
    (hleft : a * P ^ 2 - b * Q ^ 2 = 3 * deltaLeft)
    (hright : a * P ^ 2 - c * R ^ 2 = 3 * deltaRight) :
    P ^ 2 ∣
      (b * Q ^ 2) * (c * R ^ 2) -
        9 * deltaLeft * deltaRight := by
  have hB : b * Q ^ 2 = a * P ^ 2 - 3 * deltaLeft := by
    linarith
  have hC : c * R ^ 2 = a * P ^ 2 - 3 * deltaRight := by
    linarith
  refine ⟨a ^ 2 * P ^ 2 - 3 * a * (deltaLeft + deltaRight), ?_⟩
  rw [hB, hC]
  ring

/-- Eliminate the two opposite square components from one second local lift.
No primality, positivity, or coprimality is needed for this algebraic step. -/
theorem three_bucket_second_obstruction_dvd
    {P Q R a b c g C D deltaLeft deltaRight : ℤ}
    (hlocal : P ∣
      3 * C * a - 4 * D * (g * Q * R) ^ 2)
    (hleft : a * P ^ 2 - b * Q ^ 2 = 3 * deltaLeft)
    (hright : a * P ^ 2 - c * R ^ 2 = 3 * deltaRight) :
    P ∣ threeBucketSecondObstruction
      C D a b c g deltaLeft deltaRight := by
  have hprodSq := pair_product_sub_fixed_dvd_sq hleft hright
  have hPpow : P ∣ P ^ 2 := dvd_pow_self P (by norm_num)
  have hprod : P ∣
      (b * Q ^ 2) * (c * R ^ 2) -
        9 * deltaLeft * deltaRight :=
    dvd_trans hPpow hprodSq
  have hlocalMul : P ∣
      (b * c) * (3 * C * a - 4 * D * (g * Q * R) ^ 2) :=
    dvd_mul_of_dvd_right hlocal (b * c)
  have hcorrection : P ∣
      4 * D * g ^ 2 *
        ((b * Q ^ 2) * (c * R ^ 2) -
          9 * deltaLeft * deltaRight) :=
    dvd_mul_of_dvd_right hprod (4 * D * g ^ 2)
  have hadd := dvd_add hlocalMul hcorrection
  convert hadd using 1 <;> simp [threeBucketSecondObstruction] <;> ring

/-- Compose the third local lift with the two exact residual differences.
The result is a square divisibility involving only the second obstruction and
one linear gap term. -/
theorem three_bucket_third_obstruction_dvd_sq
    {P Q R a b c g C D E deltaLeft deltaRight : ℤ}
    (hthird : P ^ 2 ∣
      -3 * (3 * C * a - 4 * D * (g * Q * R) ^ 2) +
        20 * E * P * (g * Q * R) ^ 3)
    (hleft : a * P ^ 2 - b * Q ^ 2 = 3 * deltaLeft)
    (hright : a * P ^ 2 - c * R ^ 2 = 3 * deltaRight) :
    P ^ 2 ∣ threeBucketThirdObstruction C D E a b c g
      deltaLeft deltaRight (g * P * Q * R) := by
  have hprodSq := pair_product_sub_fixed_dvd_sq hleft hright
  have hbase : P ^ 2 ∣
      (b * c) *
        (-3 * (3 * C * a - 4 * D * (g * Q * R) ^ 2) +
          20 * E * P * (g * Q * R) ^ 3) :=
    dvd_mul_of_dvd_right hthird (b * c)
  have hdiffBase : P ^ 2 ∣
      (12 * D * g ^ 2 + 20 * E * P * g ^ 3 * Q * R) *
        ((b * Q ^ 2) * (c * R ^ 2) -
          9 * deltaLeft * deltaRight) :=
    dvd_mul_of_dvd_right hprodSq
      (12 * D * g ^ 2 + 20 * E * P * g ^ 3 * Q * R)
  have hdiff : P ^ 2 ∣
      threeBucketThirdObstruction C D E a b c g
          deltaLeft deltaRight (g * P * Q * R) -
        (b * c) *
          (-3 * (3 * C * a - 4 * D * (g * Q * R) ^ 2) +
            20 * E * P * (g * Q * R) ^ 3) := by
    have hneg := dvd_neg.mpr hdiffBase
    convert hneg using 1 <;>
      simp [threeBucketThirdObstruction, threeBucketSecondObstruction] <;>
      ring
  have hadd := dvd_add hbase hdiff
  convert hadd using 1 <;> ring

/-- If two second obstructions vanish at the same positive scale, their two
coefficient slopes have zero cross determinant.  The target-row verifier
checks that this determinant never vanishes for two owners in one distinct
index triple. -/
theorem three_bucket_slope_determinant_eq_zero_of_two_zeros
    {C₁ D₁ delta₁ epsilon₁ C₂ D₂ delta₂ epsilon₂ t g : ℤ}
    (hg : g ≠ 0)
    (h₁ : C₁ * t - 12 * D₁ * g ^ 2 * delta₁ * epsilon₁ = 0)
    (h₂ : C₂ * t - 12 * D₂ * g ^ 2 * delta₂ * epsilon₂ = 0) :
    C₂ * D₁ * delta₁ * epsilon₁ =
      C₁ * D₂ * delta₂ * epsilon₂ := by
  have hcross :
      -12 * g ^ 2 *
        (C₂ * D₁ * delta₁ * epsilon₁ -
          C₁ * D₂ * delta₂ * epsilon₂) = 0 := by
    linear_combination C₂ * h₁ - C₁ * h₂
  have hcoeffNeg : (-12 : ℤ) * g ^ 2 ≠ 0 := by
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hg)
  have hzero :
      C₂ * D₁ * delta₁ * epsilon₁ -
        C₁ * D₂ * delta₂ * epsilon₂ = 0 :=
    (mul_eq_zero.mp hcross).resolve_left hcoeffNeg
  linarith

/-- The third composition has no new first-order residue modulo its owner:
its difference from `-3` times the second obstruction is a multiple of every
component dividing the gap. -/
theorem three_bucket_third_mod_owner_reduces_to_second
    {P C D E a b c g deltaLeft deltaRight gap : ℤ}
    (hPgap : P ∣ gap) :
    P ∣ threeBucketThirdObstruction C D E a b c g
        deltaLeft deltaRight gap +
      3 * threeBucketSecondObstruction
        C D a b c g deltaLeft deltaRight := by
  have hmul : P ∣
      180 * E * g ^ 2 * deltaLeft * deltaRight * gap :=
    dvd_mul_of_dvd_right hPgap
      (180 * E * g ^ 2 * deltaLeft * deltaRight)
  convert hmul using 1 <;>
    simp [threeBucketThirdObstruction] <;> ring

end Erdos686Variant
end Erdos686
