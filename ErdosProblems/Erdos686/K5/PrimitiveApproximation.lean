/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.K5.Approximation
import ErdosProblems.Erdos686.K5.PrimitiveScaleResultant
import Mathlib.NumberTheory.DiophantineApproximation.Basic

/-!
# Erdős 686, k=5: primitive approximation and odd-scale residue split

Reducing a centered solution by its common scale improves the approximation
constant by the square of that scale.  Thus every nontrivially scaled
solution lies in the strict `1/(2v^2)` Legendre regime, even though the
unreduced constant is slightly larger than `1/2`.

For odd scale this file also combines the nonlinear primitive resultant with
the square identity `z=g^2`, giving the exact six-value classification of
the possible scale/quotient overlap.
-/

namespace Erdos686
namespace Erdos686Variant

/-- The centered quintic factors after removing the common scale. -/
theorem k5_centered_primitive_factor_equation
    {g u v : ℕ} (hg : 0 < g)
    (hsol : K5CenteredEq (g * u) (g * v)) :
    (u : ℤ) * (((g : ℤ)^2)*(u : ℤ)^2-1) *
          (((g : ℤ)^2)*(u : ℤ)^2-4) =
        4*(v : ℤ)*(((g : ℤ)^2)*(v : ℤ)^2-1)*
          (((g : ℤ)^2)*(v : ℤ)^2-4) := by
  have hpoly := k5_centered_eq_iff_integer_polynomial.mp hsol
  have hscaled :
      (g : ℤ) * ((u : ℤ) * (((g : ℤ)^2)*(u : ℤ)^2-1) *
        (((g : ℤ)^2)*(u : ℤ)^2-4)) =
      (g : ℤ) * (4*(v : ℤ)*(((g : ℤ)^2)*(v : ℤ)^2-1)*
        (((g : ℤ)^2)*(v : ℤ)^2-4)) := by
    calc
      _ = k5PolynomialZ ((g*u : ℕ) : ℤ) := by
        simp only [k5PolynomialZ]
        push_cast
        ring
      _ = 4*k5PolynomialZ ((g*v : ℕ) : ℤ) := hpoly
      _ = _ := by
        simp only [k5PolynomialZ]
        push_cast
        ring
  exact mul_left_cancel₀ (by exact_mod_cast hg.ne') hscaled

/-- Removing a common scale `g` improves the approximation denominator by
the exact factor `g^2`. -/
theorem k5_primitive_alpha_approximation
    {g u v : ℕ} (hg : 0 < g) (hv : 0 < v)
    (hlarge : 1425 ≤ g * v)
    (hsol : K5CenteredEq (g * u) (g * v)) :
    |(u : ℝ)/(v : ℝ)-k5Alpha| <
      (k5ApproximationConstant : ℝ) /
        (((g : ℝ)^2)*(v : ℝ)^2) := by
  have happ := k5_alpha_approximation hlarge hsol
  have hgR : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
  have hvR : (v : ℝ) ≠ 0 := by exact_mod_cast hv.ne'
  have hratio : ((g*u : ℕ) : ℝ)/((g*v : ℕ) : ℝ) =
      (u : ℝ)/(v : ℝ) := by
    push_cast
    field_simp
  have hden : (((g*v : ℕ) : ℝ))^2 =
      ((g : ℝ)^2)*(v : ℝ)^2 := by
    push_cast
    ring
  rw [hratio, hden] at happ
  exact happ

/-- Every primitive reduction with nontrivial common scale satisfies the
strict classical Legendre threshold. -/
theorem k5_primitive_alpha_strict_legendre
    {g u v : ℕ} (hg : 2 ≤ g) (hv : 0 < v)
    (hlarge : 1425 ≤ g * v)
    (hsol : K5CenteredEq (g * u) (g * v)) :
    |(u : ℝ)/(v : ℝ)-k5Alpha| <
      1 / (2*(v : ℝ)^2) := by
  have hg0 : 0 < g := by omega
  have happ := k5_primitive_alpha_approximation hg0 hv hlarge hsol
  have hC : (k5ApproximationConstant : ℝ) < 9/16 := by
    norm_num [k5ApproximationConstant]
  have hgSq : (4 : ℝ) ≤ (g : ℝ)^2 := by
    have hgSqN : 2^2 ≤ g^2 := Nat.pow_le_pow_left hg 2
    exact_mod_cast hgSqN
  have hgSqPos : (0 : ℝ) < (g : ℝ)^2 := by positivity
  have hcoef : (k5ApproximationConstant : ℝ)/(g : ℝ)^2 < 1/2 := by
    apply (div_lt_iff₀ hgSqPos).2
    nlinarith
  have hvSqPos : (0 : ℝ) < (v : ℝ)^2 := by positivity
  calc
    |(u : ℝ)/(v : ℝ)-k5Alpha| <
        (k5ApproximationConstant : ℝ) /
          (((g : ℝ)^2)*(v : ℝ)^2) := happ
    _ = ((k5ApproximationConstant : ℝ)/(g : ℝ)^2)/(v : ℝ)^2 := by
      field_simp
    _ < ((1:ℝ)/2)/(v : ℝ)^2 :=
      div_lt_div_of_pos_right hcoef hvSqPos
    _ = 1/(2*(v : ℝ)^2) := by ring

/-- Formal Legendre conclusion: the reduced primitive ratio is an actual
continued-fraction convergent of `4^(1/5)`. -/
theorem k5_primitive_ratio_is_convergent
    {g u v : ℕ} (hg : 2 ≤ g) (hv : 0 < v)
    (hcop : Nat.Coprime u v)
    (hlarge : 1425 ≤ g * v)
    (hsol : K5CenteredEq (g * u) (g * v)) :
    ∃ n : ℕ, ((u : ℚ)/(v : ℚ)) = k5Alpha.convergent n := by
  have hleg := k5_primitive_alpha_strict_legendre hg hv hlarge hsol
  let q : ℚ := (u : ℚ)/(v : ℚ)
  have hcopZ : Nat.Coprime (u : ℤ).natAbs (v : ℤ).natAbs := by
    simpa using hcop
  have hdenZ : (q.den : ℤ) = (v : ℤ) := by
    dsimp [q]
    exact Rat.den_div_eq_of_coprime (by exact_mod_cast hv) hcopZ
  have hden : q.den = v := by exact_mod_cast hdenZ
  apply Real.exists_rat_eq_convergent
  rw [hden]
  have hq : (q : ℝ) = (u : ℝ)/(v : ℝ) := by
    norm_num [q]
  rw [hq, abs_sub_comm]
  exact hleg

/-- Exact finite classification of the odd primitive scale overlap. -/
theorem k5_odd_primitive_scale_overlap_six_values
    {g u v t : ℕ} (hg : 0 < g)
    (hodd : Nat.Coprime g 2)
    (hcop : Nat.Coprime u v)
    (hscale : u + g^2 * t = 4 * v)
    (hsol : K5CenteredEq (g * u) (g * v)) :
    Nat.gcd (g^2) t = 1 ∨ Nat.gcd (g^2) t = 3 ∨
      Nat.gcd (g^2) t = 5 ∨ Nat.gcd (g^2) t = 15 ∨
      Nat.gcd (g^2) t = 25 ∨ Nat.gcd (g^2) t = 75 := by
  have heq := k5_centered_primitive_factor_equation hg hsol
  have hoddSq : Nat.Coprime (g^2) 2 := by
    simpa using hodd.pow_left 2
  have hdvd := k5_odd_primitive_scale_gcd_dvd_seventy_five
    (pow_pos hg 2) hoddSq hcop hscale heq
  let h := Nat.gcd (g^2) t
  have hpos : 0 < h := Nat.gcd_pos_of_pos_left t (pow_pos hg 2)
  have hle : h ≤ 75 := Nat.le_of_dvd (by norm_num) hdvd
  change h ∣ 75 at hdvd
  change h = 1 ∨ h = 3 ∨ h = 5 ∨ h = 15 ∨ h = 25 ∨ h = 75
  interval_cases h
  all_goals solve | norm_num at hdvd | norm_num

/-- Combined odd-scale frontier: a nontrivial common scale simultaneously
forces the strict Legendre approximation and one of six exact overlap
values. -/
theorem k5_odd_primitive_tail_constraint_package
    {g u v t : ℕ} (hg : 2 ≤ g) (hv : 0 < v)
    (hodd : Nat.Coprime g 2)
    (hcop : Nat.Coprime u v)
    (hscale : u + g^2 * t = 4 * v)
    (hlarge : 1425 ≤ g * v)
    (hsol : K5CenteredEq (g * u) (g * v)) :
    |(u : ℝ)/(v : ℝ)-k5Alpha| < 1/(2*(v : ℝ)^2) ∧
      (Nat.gcd (g^2) t = 1 ∨ Nat.gcd (g^2) t = 3 ∨
        Nat.gcd (g^2) t = 5 ∨ Nat.gcd (g^2) t = 15 ∨
        Nat.gcd (g^2) t = 25 ∨ Nat.gcd (g^2) t = 75) := by
  exact ⟨k5_primitive_alpha_strict_legendre hg hv hlarge hsol,
    k5_odd_primitive_scale_overlap_six_values (by omega) hodd hcop hscale hsol⟩

/-- Continued-fraction form of the combined frontier. -/
theorem k5_odd_primitive_convergent_constraint_package
    {g u v t : ℕ} (hg : 2 ≤ g) (hv : 0 < v)
    (hodd : Nat.Coprime g 2)
    (hcop : Nat.Coprime u v)
    (hscale : u + g^2 * t = 4 * v)
    (hlarge : 1425 ≤ g * v)
    (hsol : K5CenteredEq (g * u) (g * v)) :
    (∃ n : ℕ, ((u : ℚ)/(v : ℚ)) = k5Alpha.convergent n) ∧
      (Nat.gcd (g^2) t = 1 ∨ Nat.gcd (g^2) t = 3 ∨
        Nat.gcd (g^2) t = 5 ∨ Nat.gcd (g^2) t = 15 ∨
        Nat.gcd (g^2) t = 25 ∨ Nat.gcd (g^2) t = 75) := by
  exact ⟨k5_primitive_ratio_is_convergent hg hv hcop hlarge hsol,
    k5_odd_primitive_scale_overlap_six_values (by omega) hodd hcop hscale hsol⟩

#print axioms k5_centered_primitive_factor_equation
#print axioms k5_primitive_alpha_approximation
#print axioms k5_primitive_alpha_strict_legendre
#print axioms k5_primitive_ratio_is_convergent
#print axioms k5_odd_primitive_scale_overlap_six_values
#print axioms k5_odd_primitive_tail_constraint_package
#print axioms k5_odd_primitive_convergent_constraint_package

end Erdos686Variant
end Erdos686
