/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.K5.RungeObstruction

/-!
# Erdős 686, k=5: exact genus-two quotient reduction

For the centered equation `P₅(X)=4P₅(Y)`, put `x=X/Y` and `s=Y²`.
The equation is quadratic in `s`; its discriminant is the genus-two curve

`y² = 9x⁶ + 64x⁵ - 200x³ + 64x + 144`.

This module banks the elementary forward map, the rationalized inverse
identity, and the unique denominator-zero rational exception. It does not
claim completeness of the rational points on the genus-two curve.
-/

namespace Erdos686
namespace Erdos686Variant

/-- The centered quintic `P₅`. -/
def k5PolynomialQ (z : ℚ) : ℚ :=
  z ^ 5 - 5 * z ^ 3 + 4 * z

/-- The quadratic equation in `s=Y²` after setting `x=X/Y`. -/
def k5GenusTwoQuadratic (x s : ℚ) : ℚ :=
  (x ^ 5 - 4) * s ^ 2 - 5 * (x ^ 3 - 4) * s + 4 * (x - 4)

/-- The sextic defining the genus-two quotient. -/
def k5GenusTwoRhs (x : ℚ) : ℚ :=
  9 * x ^ 6 + 64 * x ^ 5 - 200 * x ^ 3 + 64 * x + 144

/-- Affine rational points on the genus-two quotient. -/
def K5GenusTwoPoint (x y : ℚ) : Prop :=
  y ^ 2 = k5GenusTwoRhs x

/-- The discriminant coordinate attached to a quadratic root `s`. -/
def k5GenusTwoY (x s : ℚ) : ℚ :=
  2 * (x ^ 5 - 4) * s - 5 * (x ^ 3 - 4)

lemma k5_scaled_polynomial_sub (x u : ℚ) :
    k5PolynomialQ (x * u) - 4 * k5PolynomialQ u =
      u * k5GenusTwoQuadratic x (u ^ 2) := by
  simp only [k5PolynomialQ, k5GenusTwoQuadratic]
  ring

/-- For nonzero `u`, the centered quintic equation is exactly the quadratic
equation in `s=u²`. -/
theorem k5_scaled_equation_iff
    {x u : ℚ} (hu : u ≠ 0) :
    k5PolynomialQ (x * u) = 4 * k5PolynomialQ u ↔
      k5GenusTwoQuadratic x (u ^ 2) = 0 := by
  constructor
  · intro h
    have hz :
        k5PolynomialQ (x * u) - 4 * k5PolynomialQ u = 0 :=
      sub_eq_zero.mpr h
    rw [k5_scaled_polynomial_sub] at hz
    exact (mul_eq_zero.mp hz).resolve_left hu
  · intro h
    apply sub_eq_zero.mp
    rw [k5_scaled_polynomial_sub, h, mul_zero]

/-- Exact discriminant identity. -/
theorem k5_genusTwo_discriminant (x : ℚ) :
    25 * (x ^ 3 - 4) ^ 2 -
        16 * (x ^ 5 - 4) * (x - 4) =
      k5GenusTwoRhs x := by
  simp only [k5GenusTwoRhs]
  ring

/-- Every quadratic root maps to the genus-two quotient. -/
theorem k5_quadratic_to_genusTwo
    {x s : ℚ} (hquad : k5GenusTwoQuadratic x s = 0) :
    K5GenusTwoPoint x (k5GenusTwoY x s) := by
  have hid :
      k5GenusTwoY x s ^ 2 - k5GenusTwoRhs x =
        4 * (x ^ 5 - 4) * k5GenusTwoQuadratic x s := by
    simp only [k5GenusTwoY, k5GenusTwoRhs, k5GenusTwoQuadratic]
    ring
  rw [hquad, mul_zero] at hid
  unfold K5GenusTwoPoint
  exact sub_eq_zero.mp hid

/-- Rationalized inverse identity:
`(5(x³-4)-y)s = 8(x-4)`. -/
theorem k5_quadratic_inverse_relation
    {x s : ℚ} (hquad : k5GenusTwoQuadratic x s = 0) :
    (5 * (x ^ 3 - 4) - k5GenusTwoY x s) * s =
      8 * (x - 4) := by
  have hid :
      (5 * (x ^ 3 - 4) - k5GenusTwoY x s) * s -
          8 * (x - 4) =
        -2 * k5GenusTwoQuadratic x s := by
    simp only [k5GenusTwoY, k5GenusTwoQuadratic]
    ring
  rw [hquad, mul_zero] at hid
  exact sub_eq_zero.mp hid

/-- Away from the denominator-zero point, the rationalized inverse formula
recovers the quadratic root. -/
theorem k5_genusTwo_inverse_formula
    {x y s : ℚ}
    (hrel : (5 * (x ^ 3 - 4) - y) * s = 8 * (x - 4))
    (hden : 5 * (x ^ 3 - 4) - y ≠ 0) :
    s = 8 * (x - 4) / (5 * (x ^ 3 - 4) - y) := by
  apply (eq_div_iff hden).2
  simpa [mul_comm] using hrel

/-- The chosen inverse denominator vanishes at only the rational affine
point `(4,300)` on the genus-two curve. -/
theorem k5_genusTwo_denominator_zero
    {x y : ℚ}
    (hpoint : K5GenusTwoPoint x y)
    (hden : 5 * (x ^ 3 - 4) - y = 0) :
    x = 4 ∧ y = 300 := by
  have hy : y = 5 * (x ^ 3 - 4) := by
    linarith
  have hdisc := k5_genusTwo_discriminant x
  have hcurve : y ^ 2 = k5GenusTwoRhs x := hpoint
  have hprod : (x ^ 5 - 4) * (x - 4) = 0 := by
    rw [hy] at hcurve
    nlinarith
  rcases mul_eq_zero.mp hprod with hpow | hx
  · exact (four_ne_rat_fifth_power x (sub_eq_zero.mp hpow)).elim
  · have hx4 : x = 4 := by linarith
    subst x
    constructor
    · rfl
    · norm_num at hy ⊢
      exact hy

/-- The denominator-zero ratio `X/Y=4` cannot occur for a positive integral
centered solution. -/
theorem k5_ratio_four_no_positive_integral_solution
    {X Y : ℕ}
    (hY : 0 < Y)
    (hX : X = 4 * Y)
    (hsol : K5CenteredEq X Y) :
    False := by
  have hsolZ :
      (X : ℤ) ^ 5 + 4 * X + 20 * (Y : ℤ) ^ 3 =
        4 * (Y : ℤ) ^ 5 + 16 * Y + 5 * (X : ℤ) ^ 3 := by
    exact_mod_cast hsol
  have hXZ : (X : ℤ) = 4 * (Y : ℤ) := by
    exact_mod_cast hX
  rw [hXZ] at hsolZ
  have hYz : (0 : ℤ) < (Y : ℤ) := by
    exact_mod_cast hY
  have hfactor :
      (17 * (Y : ℤ) ^ 5 - 5 * (Y : ℤ) ^ 3) =
        (Y : ℤ) ^ 3 * (17 * (Y : ℤ) ^ 2 - 5) := by
    ring
  have hpositive :
      0 < (Y : ℤ) ^ 3 * (17 * (Y : ℤ) ^ 2 - 5) := by
    apply mul_pos
    · positivity
    · nlinarith [sq_nonneg ((Y : ℤ) - 1)]
  nlinarith

/-- Every positive integral centered solution supplies a rational point on
the genus-two quotient together with the exact inverse relation. -/
theorem k5_centered_solution_to_genusTwo
    {X Y : ℕ}
    (hY : 0 < Y)
    (hsol : K5CenteredEq X Y) :
    let x : ℚ := (X : ℚ) / (Y : ℚ)
    let s : ℚ := (Y : ℚ) ^ 2
    K5GenusTwoPoint x (k5GenusTwoY x s) ∧
      (5 * (x ^ 3 - 4) - k5GenusTwoY x s) * s =
        8 * (x - 4) := by
  dsimp
  have hYq : (Y : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hY)
  have hxy :
      ((X : ℚ) / (Y : ℚ)) * (Y : ℚ) = (X : ℚ) := by
    field_simp
  have hpoly :
      k5PolynomialQ (X : ℚ) = 4 * k5PolynomialQ (Y : ℚ) := by
    have hsolQ :
        (X : ℚ) ^ 5 + 4 * X + 20 * (Y : ℚ) ^ 3 =
          4 * (Y : ℚ) ^ 5 + 16 * Y + 5 * (X : ℚ) ^ 3 := by
      exact_mod_cast hsol
    simp only [k5PolynomialQ]
    linarith
  have hquad :
      k5GenusTwoQuadratic ((X : ℚ) / (Y : ℚ)) ((Y : ℚ) ^ 2) = 0 := by
    apply (k5_scaled_equation_iff hYq).1
    rw [hxy]
    exact hpoly
  exact ⟨k5_quadratic_to_genusTwo hquad,
    k5_quadratic_inverse_relation hquad⟩

#print axioms k5_scaled_equation_iff
#print axioms k5_genusTwo_discriminant
#print axioms k5_quadratic_to_genusTwo
#print axioms k5_quadratic_inverse_relation
#print axioms k5_genusTwo_inverse_formula
#print axioms k5_genusTwo_denominator_zero
#print axioms k5_ratio_four_no_positive_integral_solution
#print axioms k5_centered_solution_to_genusTwo

end Erdos686Variant
end Erdos686
