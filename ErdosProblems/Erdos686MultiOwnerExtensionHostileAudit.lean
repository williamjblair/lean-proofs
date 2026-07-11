/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686MultiOwnerExtension

/-! Independent hostile importer for the frozen multi-owner extension. -/

namespace Erdos686
namespace Erdos686Variant

open scoped BigOperators

/-- Independent arithmetic bridge from the scaled residual-product lower
bound to the cofactor-product lower bound used in the zero exclusion. -/
theorem hostile_scaled_lower_cancels_gap_square
    {K g d A L : ℕ}
    (hg : 0 < g) (hd : 0 < d)
    (hK : K * d ^ 2 < L)
    (hscaled : g ^ 2 * L < A * d ^ 2) :
    K * g ^ 2 < A := by
  have hleft := Nat.mul_lt_mul_of_pos_left hK (pow_pos hg 2)
  have hchain : (K * g ^ 2) * d ^ 2 < A * d ^ 2 := by
    calc
      (K * g ^ 2) * d ^ 2 = g ^ 2 * (K * d ^ 2) := by ring
      _ < g ^ 2 * L := hleft
      _ < A * d ^ 2 := hscaled
  exact (Nat.mul_lt_mul_right (pow_pos hd 2)).mp hchain

/-- Independent natAbs-level contradiction behind a zero second
obstruction: its bounded coefficient cannot pay for a larger positive
cofactor product. -/
theorem hostile_zero_coefficient_cannot_pay
    {A g K coeff C : ℕ}
    (hg : 0 < g) (hC : 0 < C)
    (hcoeff : coeff < K)
    (hA : K * g ^ 2 < A)
    (heq : 3 * C * A = coeff * g ^ 2) : False := by
  have hcoeffScaled : coeff * g ^ 2 < K * g ^ 2 :=
    Nat.mul_lt_mul_of_pos_right hcoeff (pow_pos hg 2)
  have hAle : A ≤ 3 * C * A := by nlinarith
  omega

-- The smallest reflected collision reported by the producer.
example :
    multiOwnerDelta ({1, 2, 4, 5} : Finset ℤ) 1 = -12 := by
  norm_num [multiOwnerDelta]

example : (24 : ℤ) * 900 = -4 * 50 * (-3) ^ 2 * (-12) := by norm_num
example : (24 : ℤ) * 900 = -4 * (-50) * (-3) ^ 2 * 12 := by norm_num

-- Exact uniform coefficient and the worst target boundary `t=4,d=10^120`.
example : multiOwnerZeroCoefficientBound =
    558515440794946289062500000000000001 := by
  norm_num [multiOwnerZeroCoefficientBound]

example : multiOwnerZeroCoefficientBound < 625 * (10 ^ 120) ^ 2 := by
  norm_num [multiOwnerZeroCoefficientBound]

-- Independently scanned target coefficient and delta maxima fit the public
-- theorem's deliberately looser ceilings.
example : (87178291200 : ℕ) < 10 ^ 12 := by norm_num
example : (283465647360 : ℕ) < 10 ^ 12 := by norm_num
example : (87178291200 : ℕ) ≤ 15 ^ 14 := by norm_num

#check multi_owner_opposite_product_modeq_sq
#check multi_owner_opposite_product_sub_dvd_sq
#check multi_owner_second_obstruction_dvd
#check multi_owner_third_obstruction_dvd_sq
#check multi_owner_cofactor_product_scaled_lower
#check multi_owner_target_cofactor_product_gt_zero_bound
#check multi_owner_zero_coefficient_natAbs_lt
#check bounded_multi_owner_second_obstruction_ne_zero
#check multi_owner_delta_natAbs_le_pow
#check target_multi_owner_second_obstruction_ne_zero

#print axioms multi_owner_opposite_product_modeq_sq
#print axioms multi_owner_opposite_product_sub_dvd_sq
#print axioms multi_owner_second_obstruction_dvd
#print axioms multi_owner_third_obstruction_dvd_sq
#print axioms multi_owner_cofactor_product_scaled_lower
#print axioms multi_owner_target_cofactor_product_gt_zero_bound
#print axioms multi_owner_zero_coefficient_natAbs_lt
#print axioms bounded_multi_owner_second_obstruction_ne_zero
#print axioms multi_owner_delta_natAbs_le_pow
#print axioms target_multi_owner_second_obstruction_ne_zero
#print axioms hostile_scaled_lower_cancels_gap_square
#print axioms hostile_zero_coefficient_cannot_pay

end Erdos686Variant
end Erdos686
