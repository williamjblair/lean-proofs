/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686K5PrimitiveEuclideanConstraint

/-!
# Erdős 686, k=5: splitting restriction on the primitive Euclidean remainder

For a primitive centered solution write `z = g^2` and

`u + z*t = 4*v`.

The nonlinear scale resultant already gives

`t | 60*v^3*(5 - 17*z*v^2)`.

Primitivity makes `t` coprime to `v`, so the factor `v^3` can be cancelled
without any loss.  Consequently every prime divisor `p` of `t` away from
`2,3,5` makes `85` a square modulo `p`: explicitly

`(17*g*v)^2 = 85 (mod p)`.

This is an all-index arithmetic filter on the normalized remainder of the
forced continued-fraction convergent.  It is only a necessary congruence,
not a reformulation of the centered equation.
-/

namespace Erdos686
namespace Erdos686Variant

/-- The primitive scale quotient and the reduced denominator are coprime.
This is the cancellation input missing from the raw endpoint resultant. -/
theorem k5_primitive_scale_quotient_coprime_denominator
    {u v z t : ℕ} (hcop : Nat.Coprime u v)
    (hscale : u + z * t = 4 * v) :
    Nat.Coprime t v := by
  let h := Nat.gcd t v
  have hht : h ∣ t := Nat.gcd_dvd_left t v
  have hhv : h ∣ v := Nat.gcd_dvd_right t v
  have hhzt : h ∣ z * t := dvd_mul_of_dvd_right hht z
  have hh4v : h ∣ 4 * v := dvd_mul_of_dvd_right hhv 4
  have hhsum : h ∣ u + z * t := by simpa [hscale] using hh4v
  have hhsum' : h ∣ z * t + u := by simpa [Nat.add_comm] using hhsum
  have hhu : h ∣ u := (Nat.dvd_add_iff_right hhzt).mpr hhsum'
  have hhone : h ∣ 1 := by
    have : h ∣ Nat.gcd u v := Nat.dvd_gcd hhu hhv
    simpa [hcop.gcd_eq_one] using this
  exact Nat.dvd_one.mp hhone

/-- Cancellation of the primitive denominator from the opposite endpoint
resultant.  Unlike the raw resultant, this statement has no variable
factor multiplying the quadratic defect. -/
theorem k5_primitive_scale_quotient_dvd_reduced_quadratic
    {g u v t : ℕ} (hg : 0 < g)
    (hcop : Nat.Coprime u v)
    (hscale : u + g ^ 2 * t = 4 * v)
    (hsol : K5CenteredEq (g * u) (g * v)) :
    (t : ℤ) ∣ 60 * (5 - 17 * (g : ℤ) ^ 2 * (v : ℤ) ^ 2) := by
  have heq := k5_centered_primitive_factor_equation hg hsol
  have hres := k5_primitive_scale_residual_eq_zero
    (pow_pos hg 2) hscale heq
  have hraw := k5_primitive_scale_t_dvd_quadratic hres
  have htv := k5_primitive_scale_quotient_coprime_denominator hcop hscale
  have hcopZ : IsCoprime (t : ℤ) ((v : ℤ) ^ 3) := by
    exact (htv.pow_right 3).isCoprime
  apply hcopZ.dvd_of_dvd_mul_left
  simpa [mul_assoc, mul_left_comm, mul_comm] using hraw

/-- Every prime divisor of the normalized Euclidean remainder away from
`2,3,5` splits in `ℚ(√85)`.  The displayed witness makes the statement
an exact, directly checkable modular-square filter. -/
theorem k5_primitive_remainder_prime_splits_eighty_five
    {g u v t p : ℕ} (hg : 0 < g)
    (hcop : Nat.Coprime u v)
    (hscale : u + g ^ 2 * t = 4 * v)
    (hsol : K5CenteredEq (g * u) (g * v))
    (hp : Nat.Prime p) (hpt : p ∣ t) (hp60 : ¬ p ∣ 60) :
    ∃ x : ℕ, x ^ 2 ≡ 85 [MOD p] := by
  have hred := k5_primitive_scale_quotient_dvd_reduced_quadratic
    hg hcop hscale hsol
  have hptZ : (p : ℤ) ∣ (t : ℤ) := by exact_mod_cast hpt
  have hpdefect : (p : ℤ) ∣
      5 - 17 * (g : ℤ) ^ 2 * (v : ℤ) ^ 2 := by
    have hpProd : (p : ℤ) ∣
        (60 : ℤ) * (5 - 17 * (g : ℤ) ^ 2 * (v : ℤ) ^ 2) :=
      dvd_trans hptZ hred
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    rcases hpZ.dvd_mul.mp hpProd with hpFixed | hpDefect
    · exfalso
      apply hp60
      exact_mod_cast hpFixed
    · exact hpDefect
  refine ⟨17 * g * v, ?_⟩
  apply (Nat.modEq_iff_dvd).2
  have hmultiple : (p : ℤ) ∣
      17 * (5 - 17 * (g : ℤ) ^ 2 * (v : ℤ) ^ 2) :=
    dvd_mul_of_dvd_right hpdefect 17
  convert hmultiple using 1
  push_cast
  ring

/-- A scale-free computable filter stronger than the square-quotient and
six-overlap tests.  Both the divisor and the quadratic defect are calculated
from the convergent `(u,v)` alone. -/
theorem k5_odd_primitive_convergent_reduced_resultant_filter
    {g u v t : ℕ} (hg : 2 ≤ g) (hv : 2 ≤ v)
    (hodd : Nat.Coprime g 2) (hcop : Nat.Coprime u v)
    (hscale : u + g ^ 2 * t = 4 * v)
    (hlarge : 1425 ≤ g * v)
    (hsol : K5CenteredEq (g * u) (g * v)) :
    let Q :=
      5 * k5PrimitivePowerGap 3 u v / k5PrimitivePowerGap 5 u v
    let R :=
      5 * k5PrimitivePowerGap 3 u v % k5PrimitivePowerGap 5 u v
    ((R / 4 : ℕ) : ℤ) ∣
      60 * (5 - 17 * (Q : ℤ) * (v : ℤ) ^ 2) := by
  dsimp only
  have hconstraint := k5_odd_primitive_convergent_euclidean_constraint
    hg hv hodd hcop hscale hlarge hsol
  have hQ := hconstraint.2.1
  have hR := hconstraint.2.2.1
  have hRnorm :
      (5 * k5PrimitivePowerGap 3 u v %
          k5PrimitivePowerGap 5 u v) / 4 = t := by
    rw [hR]
    simp
  have hred := k5_primitive_scale_quotient_dvd_reduced_quadratic
    (by omega : 0 < g) hcop hscale hsol
  rw [hRnorm, hQ]
  norm_num at hred ⊢
  exact hred

/-- Continued-fraction-facing form of the splitting restriction.  Here the
prime is read directly from the normalized Euclidean remainder computed from
the convergent `(u,v)`; neither `g` nor the auxiliary quotient `t` appears in
the divisibility hypothesis. -/
theorem k5_odd_primitive_convergent_remainder_splitting_filter
    {g u v t : ℕ} (hg : 2 ≤ g) (hv : 2 ≤ v)
    (hodd : Nat.Coprime g 2) (hcop : Nat.Coprime u v)
    (hscale : u + g ^ 2 * t = 4 * v)
    (hlarge : 1425 ≤ g * v)
    (hsol : K5CenteredEq (g * u) (g * v)) :
    let R :=
      5 * k5PrimitivePowerGap 3 u v % k5PrimitivePowerGap 5 u v
    ∀ p : ℕ, Nat.Prime p → p ∣ R / 4 → ¬ p ∣ 60 →
      ∃ x : ℕ, x ^ 2 ≡ 85 [MOD p] := by
  dsimp only
  have hconstraint := k5_odd_primitive_convergent_euclidean_constraint
    hg hv hodd hcop hscale hlarge hsol
  have hR := hconstraint.2.2.1
  have hRnorm :
      (5 * k5PrimitivePowerGap 3 u v %
          k5PrimitivePowerGap 5 u v) / 4 = t := by
    rw [hR]
    simp
  intro p hp hpdvd hp60
  apply k5_primitive_remainder_prime_splits_eighty_five
    (by omega) hcop hscale hsol hp _ hp60
  simpa [hRnorm] using hpdvd

#print axioms k5_primitive_scale_quotient_coprime_denominator
#print axioms k5_primitive_scale_quotient_dvd_reduced_quadratic
#print axioms k5_primitive_remainder_prime_splits_eighty_five
#print axioms k5_odd_primitive_convergent_reduced_resultant_filter
#print axioms k5_odd_primitive_convergent_remainder_splitting_filter

end Erdos686Variant
end Erdos686
