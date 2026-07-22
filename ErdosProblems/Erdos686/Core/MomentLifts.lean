/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.Core.GlobalSquareLift

/-!
# Erdős 686: global moment-cancellation lifts

The multiplier `4 = 2^2` permits a second global coefficient cancellation.
For any integer polynomial satisfying `P(2d)=4P(d)`, the terms of degree
zero, one, and two can be removed explicitly, leaving

`d^3 | 3P(0)+2d*[z]P`.

The reflected evaluation `P(2d)=4P(-d)` similarly gives

`d^3 | 3P(0)-6d*[z]P`.

Applied to two exact residual progressions of the block equation, these are
unconditional cubic divisibility combinations.  They do not assert that a
residual product itself contains `d^3` and do not close an odd tail alone.
-/

namespace Erdos686
namespace Erdos686Variant

open Polynomial

/-- Quadratic-moment cancellation at the evaluations `d` and `2d`. -/
lemma cube_dvd_eval_two_sub_four_eval_add_low_moments
    (P : Polynomial ℤ) (d : ℤ) :
    d ^ 3 ∣ P.eval (2 * d) - 4 * P.eval d + 3 * P.eval 0 +
      2 * d * P.coeff 1 := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      have hadd := dvd_add hP hQ
      convert hadd using 1 <;>
        simp [Polynomial.eval_add, Polynomial.coeff_add] <;> ring
  | monomial m a =>
      by_cases hm0 : m = 0
      · subst m
        have hc1 : (Polynomial.C a).coeff 1 = 0 :=
          Polynomial.coeff_C_ne_zero (by norm_num)
        have hz : a - 4 * a + 3 * a = 0 := by ring
        rw [Polynomial.monomial_zero_left, hc1]
        simp [hz]
      by_cases hm1 : m = 1
      · subst m
        have hz : a * (2 * d) - 4 * (a * d) + 2 * d * a = 0 := by ring
        simpa [hz]
      by_cases hm2 : m = 2
      · subst m
        have hc1 : (Polynomial.monomial 2 a).coeff 1 = 0 := by
          rw [Polynomial.coeff_monomial]
          norm_num
        have hz : a * (2 * d) ^ 2 - 4 * (a * d ^ 2) = 0 := by ring
        rw [hc1]
        simpa [hz]
      have hm3 : 3 ≤ m := by omega
      have hd : d ^ 3 ∣ d ^ m := pow_dvd_pow d hm3
      have hmul : d ^ 3 ∣ a * (((2 : ℤ) ^ m - 4) * d ^ m) :=
        dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hd ((2 : ℤ) ^ m - 4)) a
      convert hmul using 1 <;>
        simp [Polynomial.eval_monomial, Polynomial.coeff_monomial,
          hm0, hm1, hm2] <;> ring

/-- Reflected quadratic-moment cancellation at `-d` and `2d`. -/
lemma cube_dvd_eval_two_sub_four_eval_neg_add_low_moments
    (P : Polynomial ℤ) (d : ℤ) :
    d ^ 3 ∣ P.eval (2 * d) - 4 * P.eval (-d) + 3 * P.eval 0 -
      6 * d * P.coeff 1 := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      have hadd := dvd_add hP hQ
      convert hadd using 1 <;>
        simp [Polynomial.eval_add, Polynomial.coeff_add] <;> ring
  | monomial m a =>
      by_cases hm0 : m = 0
      · subst m
        have hc1 : (Polynomial.C a).coeff 1 = 0 :=
          Polynomial.coeff_C_ne_zero (by norm_num)
        have hz : a - 4 * a + 3 * a = 0 := by ring
        rw [Polynomial.monomial_zero_left, hc1]
        simp [hz]
      by_cases hm1 : m = 1
      · subst m
        have hz :
            (Polynomial.monomial 1 a).eval (2 * d) -
                4 * (Polynomial.monomial 1 a).eval (-d) +
                3 * (Polynomial.monomial 1 a).eval 0 -
                6 * d * (Polynomial.monomial 1 a).coeff 1 = 0 := by
          simp [Polynomial.eval_monomial, Polynomial.coeff_monomial]
          ring
        rw [hz]
        simp
      by_cases hm2 : m = 2
      · subst m
        have hz :
            (Polynomial.monomial 2 a).eval (2 * d) -
                4 * (Polynomial.monomial 2 a).eval (-d) +
                3 * (Polynomial.monomial 2 a).eval 0 -
                6 * d * (Polynomial.monomial 2 a).coeff 1 = 0 := by
          simp [Polynomial.eval_monomial, Polynomial.coeff_monomial]
          ring
        rw [hz]
        simp
      have hm3 : 3 ≤ m := by omega
      have hd : d ^ 3 ∣ d ^ m := pow_dvd_pow d hm3
      have hmul : d ^ 3 ∣
          a * (((2 : ℤ) ^ m - 4 * (-1 : ℤ) ^ m) * d ^ m) :=
        dvd_mul_of_dvd_right
          (dvd_mul_of_dvd_right hd ((2 : ℤ) ^ m - 4 * (-1 : ℤ) ^ m)) a
      convert hmul using 1 <;>
        simp [Polynomial.eval_monomial, Polynomial.coeff_monomial,
          hm0, hm1, hm2] <;> ring

theorem cube_dvd_low_moments_of_eval_two_eq_four_eval
    {P : Polynomial ℤ} {d : ℤ}
    (heq : P.eval (2 * d) = 4 * P.eval d) :
    d ^ 3 ∣ 3 * P.eval 0 + 2 * d * P.coeff 1 := by
  have h := cube_dvd_eval_two_sub_four_eval_add_low_moments P d
  simpa [heq] using h

theorem cube_dvd_reflected_low_moments_of_eval_two_eq_four_eval_neg
    {P : Polynomial ℤ} {d : ℤ}
    (heq : P.eval (2 * d) = 4 * P.eval (-d)) :
    d ^ 3 ∣ 3 * P.eval 0 - 6 * d * P.coeff 1 := by
  have h := cube_dvd_eval_two_sub_four_eval_neg_add_low_moments P d
  simpa [heq] using h

/-- Residual `n+i-d`, whose shifts by `d` and `2d` are the lower and upper
block factors. -/
def lowerMomentResidual (n d i : ℕ) : ℤ :=
  ((n + i : ℕ) : ℤ) - (d : ℤ)

noncomputable def lowerMomentPolynomial (k n d : ℕ) : Polynomial ℤ :=
  ∏ i ∈ Finset.Icc 1 k,
    (Polynomial.X + Polynomial.C (lowerMomentResidual n d i))

lemma lowerMomentPolynomial_eval (k n d : ℕ) (z : ℤ) :
    (lowerMomentPolynomial k n d).eval z =
      ∏ i ∈ Finset.Icc 1 k, (z + lowerMomentResidual n d i) := by
  simp [lowerMomentPolynomial, lowerMomentResidual, Polynomial.eval_prod]

lemma lowerMomentPolynomial_eval_gap (k n d : ℕ) :
    (lowerMomentPolynomial k n d).eval (d : ℤ) =
      (blockProduct k n : ℤ) := by
  rw [lowerMomentPolynomial_eval]
  unfold blockProduct
  rw [Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro i _hi
  simp [lowerMomentResidual]

lemma lowerMomentPolynomial_eval_two_gap (k n d : ℕ) :
    (lowerMomentPolynomial k n d).eval (2 * (d : ℤ)) =
      (blockProduct k (n + d) : ℤ) := by
  rw [lowerMomentPolynomial_eval]
  unfold blockProduct
  rw [Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro i _hi
  simp [lowerMomentResidual]
  ring

/-- First global cubic moment lift. -/
theorem gap_cube_dvd_lowerMoment_combination
    {k n d : ℕ}
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    ((d : ℤ) ^ 3) ∣
      3 * (lowerMomentPolynomial k n d).eval 0 +
        2 * (d : ℤ) * (lowerMomentPolynomial k n d).coeff 1 := by
  apply cube_dvd_low_moments_of_eval_two_eq_four_eval
  rw [lowerMomentPolynomial_eval_two_gap, lowerMomentPolynomial_eval_gap,
    heq]
  push_cast
  ring

/-- Residual `3(n+i)+d`, whose shifts by `-d` and `2d` are three times the
lower and upper block factors. -/
def upperMomentResidual (n d i : ℕ) : ℤ :=
  3 * ((n + i : ℕ) : ℤ) + (d : ℤ)

noncomputable def upperMomentPolynomial (k n d : ℕ) : Polynomial ℤ :=
  ∏ i ∈ Finset.Icc 1 k,
    (Polynomial.X + Polynomial.C (upperMomentResidual n d i))

lemma upperMomentPolynomial_eval (k n d : ℕ) (z : ℤ) :
    (upperMomentPolynomial k n d).eval z =
      ∏ i ∈ Finset.Icc 1 k, (z + upperMomentResidual n d i) := by
  simp [upperMomentPolynomial, upperMomentResidual, Polynomial.eval_prod]

lemma upperMomentPolynomial_eval_neg_gap (k n d : ℕ) :
    (upperMomentPolynomial k n d).eval (-(d : ℤ)) =
      (3 : ℤ) ^ k * (blockProduct k n : ℤ) := by
  rw [upperMomentPolynomial_eval]
  unfold blockProduct
  have hcard : (Finset.Icc 1 k).card = k := by simp [Nat.card_Icc]
  calc
    (∏ i ∈ Finset.Icc 1 k,
        (-(d : ℤ) + upperMomentResidual n d i)) =
        ∏ i ∈ Finset.Icc 1 k, (3 * ((n + i : ℕ) : ℤ)) := by
          apply Finset.prod_congr rfl
          intro i _hi
          simp [upperMomentResidual]
    _ = (∏ _i ∈ Finset.Icc 1 k, (3 : ℤ)) *
          ∏ i ∈ Finset.Icc 1 k, ((n + i : ℕ) : ℤ) := by
          rw [← Finset.prod_mul_distrib]
    _ = (3 : ℤ) ^ k * (blockProduct k n : ℤ) := by
          simp [Finset.prod_const, hcard, blockProduct]

lemma upperMomentPolynomial_eval_two_gap (k n d : ℕ) :
    (upperMomentPolynomial k n d).eval (2 * (d : ℤ)) =
      (3 : ℤ) ^ k * (blockProduct k (n + d) : ℤ) := by
  rw [upperMomentPolynomial_eval]
  unfold blockProduct
  have hcard : (Finset.Icc 1 k).card = k := by simp [Nat.card_Icc]
  calc
    (∏ i ∈ Finset.Icc 1 k,
        (2 * (d : ℤ) + upperMomentResidual n d i)) =
        ∏ i ∈ Finset.Icc 1 k,
          (3 * (((n + d) + i : ℕ) : ℤ)) := by
          apply Finset.prod_congr rfl
          intro i _hi
          simp [upperMomentResidual]
          ring
    _ = (∏ _i ∈ Finset.Icc 1 k, (3 : ℤ)) *
          ∏ i ∈ Finset.Icc 1 k, ((((n + d) + i : ℕ) : ℤ)) := by
          rw [← Finset.prod_mul_distrib]
    _ = (3 : ℤ) ^ k * (blockProduct k (n + d) : ℤ) := by
          simp [Finset.prod_const, hcard, blockProduct]

/-- Reflected global cubic moment lift. -/
theorem gap_cube_dvd_upperMoment_combination
    {k n d : ℕ}
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    ((d : ℤ) ^ 3) ∣
      3 * (upperMomentPolynomial k n d).eval 0 -
        6 * (d : ℤ) * (upperMomentPolynomial k n d).coeff 1 := by
  apply cube_dvd_reflected_low_moments_of_eval_two_eq_four_eval_neg
  rw [upperMomentPolynomial_eval_two_gap, upperMomentPolynomial_eval_neg_gap,
    heq]
  push_cast
  ring

end Erdos686Variant
end Erdos686
