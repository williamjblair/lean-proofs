/- leanprover/lean4:v4.29.1 mathlib v4.29.1 -/
import ErdosProblems.Erdos686.K5.ExceptionalProfileClassification
import ErdosProblems.Erdos686.K5.ExceptionalAggregateNoGo

/-!
# Erdős 686, k=5: retain the global equation after exceptional CRT cancellation

The five designated owner-square congruences are local.  This file keeps the
independent global five-term equation and identifies the product of the five
signed square quotients with the explicit cubic left by the aggregate
collapse.  In particular, the quotient product is not a free parameter.
-/

namespace Erdos686
namespace Erdos686Variant

/-- The original five-term equation in the primitive crossing coordinates
`n+j = P*R` and `n+d+i = P*C`.  This is the independent global equation which
is lost if one retains only the five owner-square congruences. -/
theorem k5_exceptional_primitive_global_equation
    {n d P R C j i : ℕ}
    (hj : j = 2 ∨ j = 4) (hi : i = 2 ∨ i = 4)
    (hX : n + j = P * R) (hY : n + d + i = P * C)
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n) :
    k5ExceptionalEquationDefect
      ((P : ℤ) * (R : ℤ))
      ((P : ℤ) * (C : ℤ) - (P : ℤ) * (R : ℤ)) j i = 0 := by
  have hXZ : ((n + j : ℕ) : ℤ) = (P : ℤ) * (R : ℤ) := by
    exact_mod_cast hX
  have hYZ : ((n + d + i : ℕ) : ℤ) = (P : ℤ) * (C : ℤ) := by
    exact_mod_cast hY
  have heqZ : ((blockProduct 5 (n + d) : ℕ) : ℤ) =
      4 * ((blockProduct 5 n : ℕ) : ℤ) := by
    exact_mod_cast heq
  rcases hj with rfl | rfl <;> rcases hi with rfl | rfl <;>
    norm_num [k5ExceptionalEquationDefect, k5ShiftedBlockZ, blockProduct,
      Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton] at heqZ ⊢ <;>
    push_cast at heqZ hXZ hYZ <;>
    rw [← hXZ, ← hYZ] <;>
    linear_combination heqZ

/-- Fully expanded cubic after eliminating the crossing gap in favour of
`U = P(C+R)` and `X = PR`.  The four formulas make the lower-row placement
dependence explicit and are convenient for exact resultants or valuation
arguments. -/
theorem k5_exceptional_row_cubic_sum_coordinate_table (X U : ℤ) :
    k5ExceptionalRowCollapseQuotient X (U - 2 * X) 2 2 =
      5 * (-7*U^3 + 27*U^2*X - 21*U^2 - U*X^2 + 54*U*X +
        2*U + X^3 + 3*X^2 - 70*X + 12) ∧
    k5ExceptionalRowCollapseQuotient X (U - 2 * X) 2 4 =
      5 * (-7*U^3 + 27*U^2*X + 21*U^2 - U*X^2 - 54*U*X +
        2*U + X^3 + 5*X^2 - 70*X - 20) ∧
    k5ExceptionalRowCollapseQuotient X (U - 2 * X) 4 2 =
      5 * (-7*U^3 + 27*U^2*X - 21*U^2 - U*X^2 + 54*U*X +
        2*U + X^3 - 5*X^2 - 70*X + 20) ∧
    k5ExceptionalRowCollapseQuotient X (U - 2 * X) 4 4 =
      5 * (-7*U^3 + 27*U^2*X + 21*U^2 - U*X^2 - 54*U*X +
        2*U + X^3 - 3*X^2 - 70*X - 12) := by
  simp only [k5ExceptionalRowCollapseQuotient]
  norm_num
  repeat' apply And.intro
  all_goals ring

/-- In the unit-column-two orientation, division by all five designated owner
squares leaves exactly the explicit global cubic.  The final divisibility by
`5` is a consequence of the original equation, not of the local CRT system. -/
theorem k5_exceptional_i2_designated_quotient_global_cubic
    {X U zA zP zQ zB zW : ℤ} {j : ℕ}
    (hj : j = 2 ∨ j = 4) (hX0 : X ≠ 0)
    (hX : X = zA * zP * zQ * zB * zW)
    (heq : k5ExceptionalEquationDefect X (U - 2 * X) j 2 = 0)
    (hA : zA ^ 2 ∣ U - 1)
    (hP : zP ^ 2 ∣ 5 * X - U)
    (hQ : zQ ^ 2 ∣ U + 5 * X + 1)
    (hB : zB ^ 2 ∣ 5 * X - U - 2)
    (hW : zW ^ 2 ∣ U + 3) :
    ∃ qA qP qQ qB qW : ℤ,
      U - 1 = zA ^ 2 * qA ∧
      5 * X - U = zP ^ 2 * qP ∧
      U + 5 * X + 1 = zQ ^ 2 * qQ ∧
      5 * X - U - 2 = zB ^ 2 * qB ∧
      U + 3 = zW ^ 2 * qW ∧
      qA * qP * qQ * qB * qW =
        k5ExceptionalRowCollapseQuotient X (U - 2 * X) j 2 ∧
      (5 : ℤ) ∣ qA * qP * qQ * qB * qW := by
  obtain ⟨qA, qP, qQ, qB, qW, hqA, hqP, hqQ, hqB, hqW, hprod⟩ :=
    five_designated_square_quotient_product_identity hX hA hP hQ hB hW
  have hcollapse := k5_exceptional_row_aggregate_collapse
    X (U - 2 * X) hj (by left; rfl)
  rw [heq, zero_add] at hcollapse
  have hrow :
      (U - 1) * (5 * X - U) * (U + 5 * X + 1) *
          (5 * X - U - 2) * (U + 3) =
        X ^ 2 * k5ExceptionalRowCollapseQuotient X (U - 2 * X) j 2 := by
    rw [← hcollapse]
    simp only [k5ExceptionalRowDefectProductZ]
    ring
  have hquot : qA * qP * qQ * qB * qW =
      k5ExceptionalRowCollapseQuotient X (U - 2 * X) j 2 := by
    have hmul : X ^ 2 * (qA * qP * qQ * qB * qW) =
        X ^ 2 * k5ExceptionalRowCollapseQuotient X (U - 2 * X) j 2 := by
      rw [← hprod, hrow]
    exact mul_left_cancel₀ (pow_ne_zero 2 hX0) hmul
  refine ⟨qA, qP, qQ, qB, qW, hqA, hqP, hqQ, hqB, hqW, hquot, ?_⟩
  rw [hquot]
  rcases hj with rfl | rfl <;>
    norm_num [k5ExceptionalRowCollapseQuotient]

/-- The symmetric unit-column-four formula.  The owner order is reversed in
the row, but the same cancellation gives the exact global cubic and its fixed
factor `5`. -/
theorem k5_exceptional_i4_designated_quotient_global_cubic
    {X U zW zB zQ zP zA : ℤ} {j : ℕ}
    (hj : j = 2 ∨ j = 4) (hX0 : X ≠ 0)
    (hX : X = zW * zB * zQ * zP * zA)
    (heq : k5ExceptionalEquationDefect X (U - 2 * X) j 4 = 0)
    (hW : zW ^ 2 ∣ U - 3)
    (hB : zB ^ 2 ∣ 5 * X - U + 2)
    (hQ : zQ ^ 2 ∣ U + 5 * X - 1)
    (hP : zP ^ 2 ∣ 5 * X - U)
    (hA : zA ^ 2 ∣ U + 1) :
    ∃ qW qB qQ qP qA : ℤ,
      U - 3 = zW ^ 2 * qW ∧
      5 * X - U + 2 = zB ^ 2 * qB ∧
      U + 5 * X - 1 = zQ ^ 2 * qQ ∧
      5 * X - U = zP ^ 2 * qP ∧
      U + 1 = zA ^ 2 * qA ∧
      qW * qB * qQ * qP * qA =
        k5ExceptionalRowCollapseQuotient X (U - 2 * X) j 4 ∧
      (5 : ℤ) ∣ qW * qB * qQ * qP * qA := by
  obtain ⟨qW, qB, qQ, qP, qA, hqW, hqB, hqQ, hqP, hqA, hprod⟩ :=
    five_designated_square_quotient_product_identity hX hW hB hQ hP hA
  have hcollapse := k5_exceptional_row_aggregate_collapse
    X (U - 2 * X) hj (by right; rfl)
  rw [heq, zero_add] at hcollapse
  have hrow :
      (U - 3) * (5 * X - U + 2) * (U + 5 * X - 1) *
          (5 * X - U) * (U + 1) =
        X ^ 2 * k5ExceptionalRowCollapseQuotient X (U - 2 * X) j 4 := by
    rw [← hcollapse]
    simp only [k5ExceptionalRowDefectProductZ]
    ring
  have hquot : qW * qB * qQ * qP * qA =
      k5ExceptionalRowCollapseQuotient X (U - 2 * X) j 4 := by
    have hmul : X ^ 2 * (qW * qB * qQ * qP * qA) =
        X ^ 2 * k5ExceptionalRowCollapseQuotient X (U - 2 * X) j 4 := by
      rw [← hprod, hrow]
    exact mul_left_cancel₀ (pow_ne_zero 2 hX0) hmul
  refine ⟨qW, qB, qQ, qP, qA, hqW, hqB, hqQ, hqP, hqA, hquot, ?_⟩
  rw [hquot]
  rcases hj with rfl | rfl <;>
    norm_num [k5ExceptionalRowCollapseQuotient]

/-- Valuation lift supplied by the global cubic.  If `5` belongs to one
designated owner, the remainder table makes the other four targets prime to
`5`.  The fixed factor `5` in the global quotient product must therefore land
in the selected square quotient, raising its target divisibility from the
local square `25` to the genuinely global cube `125`. -/
theorem five_designated_global_factor_cube_lift
    {z₁ z₂ z₃ z₄ z₅ q₁ q₂ q₃ q₄ q₅ T₁ T₂ T₃ T₄ T₅ : ℤ}
    (hz : (5 : ℤ) ∣ z₁)
    (hT₁ : T₁ = z₁ ^ 2 * q₁)
    (hT₂ : T₂ = z₂ ^ 2 * q₂) (hT₃ : T₃ = z₃ ^ 2 * q₃)
    (hT₄ : T₄ = z₄ ^ 2 * q₄) (hT₅ : T₅ = z₅ ^ 2 * q₅)
    (hprod : (5 : ℤ) ∣ q₁ * q₂ * q₃ * q₄ * q₅)
    (h₂ : ¬ (5 : ℤ) ∣ T₂) (h₃ : ¬ (5 : ℤ) ∣ T₃)
    (h₄ : ¬ (5 : ℤ) ∣ T₄) (h₅ : ¬ (5 : ℤ) ∣ T₅) :
    (125 : ℤ) ∣ T₁ := by
  have hp : Prime (5 : ℤ) := by norm_num
  have hq₂ : ¬ (5 : ℤ) ∣ q₂ := by
    intro h
    apply h₂
    rw [hT₂]
    exact dvd_mul_of_dvd_right h _
  have hq₃ : ¬ (5 : ℤ) ∣ q₃ := by
    intro h
    apply h₃
    rw [hT₃]
    exact dvd_mul_of_dvd_right h _
  have hq₄ : ¬ (5 : ℤ) ∣ q₄ := by
    intro h
    apply h₄
    rw [hT₄]
    exact dvd_mul_of_dvd_right h _
  have hq₅ : ¬ (5 : ℤ) ∣ q₅ := by
    intro h
    apply h₅
    rw [hT₅]
    exact dvd_mul_of_dvd_right h _
  have hq₁ : (5 : ℤ) ∣ q₁ := by
    rcases hp.dvd_mul.mp hprod with hleft | hright
    · rcases hp.dvd_mul.mp hleft with hleft | hright
      · rcases hp.dvd_mul.mp hleft with hleft | hright
        · rcases hp.dvd_mul.mp hleft with hq₁ | hq₂'
          · exact hq₁
          · exact (hq₂ hq₂').elim
        · exact (hq₃ hright).elim
      · exact (hq₄ hright).elim
    · exact (hq₅ hright).elim
  rcases hz with ⟨a, ha⟩
  rcases hq₁ with ⟨b, hb⟩
  refine ⟨a ^ 2 * b, ?_⟩
  rw [hT₁, ha, hb]
  ring

#print axioms k5_exceptional_primitive_global_equation
#print axioms k5_exceptional_row_cubic_sum_coordinate_table
#print axioms k5_exceptional_i2_designated_quotient_global_cubic
#print axioms k5_exceptional_i4_designated_quotient_global_cubic
#print axioms five_designated_global_factor_cube_lift

end Erdos686Variant
end Erdos686
