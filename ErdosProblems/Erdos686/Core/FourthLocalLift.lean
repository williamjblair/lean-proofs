/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.Core.GlobalResidualTwoPrime
import ErdosProblems.Erdos686.Core.ThreeBucketRestriction

/-!
# Erdős 686: fourth local lift for three cleaned owners

The signed local cofactor is retained through its cubic coefficient.  After
clearing the unavoidable powers of three, the exact fourth local congruence is

`H^3 | 3*T3 + H^2*(-9*D*A^2 + 36*E*A*M^2 + 84*F*M^4)`,

where `T3` is the already banked third-order residue.  In particular, setting
`A=0` would discard genuine correction terms.

For three square residuals, multiplying by the square of the two opposite
cofactors eliminates both opposite components modulo `P^3`.  The resulting
cyclic obstruction is proved below.  This module does not claim that those
three congruences enforce the verified short window.
-/

namespace Erdos686
namespace Erdos686Variant

open Polynomial
open scoped BigOperators

/-- Cubic coefficient in the signed local cofactor expansion. -/
noncomputable def localFourthCubic (k i : ℕ) : ℤ :=
  (localThirdPolynomial k i).coeff 3

private lemma fourth_dvd_polynomial_eval_sub_four_coefficients
    (P : Polynomial ℤ) (z : ℤ) :
    z ^ 4 ∣ P.eval z - P.coeff 0 - P.coeff 1 * z -
      P.coeff 2 * z ^ 2 - P.coeff 3 * z ^ 3 := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      have hadd := dvd_add hP hQ
      convert hadd using 1 <;> simp [Polynomial.eval_add] <;> ring
  | monomial m a =>
      by_cases hm0 : m = 0
      · subst m
        have hc1 : (Polynomial.C a).coeff 1 = 0 :=
          Polynomial.coeff_C_ne_zero (by norm_num)
        have hc2 : (Polynomial.C a).coeff 2 = 0 :=
          Polynomial.coeff_C_ne_zero (by norm_num)
        have hc3 : (Polynomial.C a).coeff 3 = 0 :=
          Polynomial.coeff_C_ne_zero (by norm_num)
        rw [Polynomial.monomial_zero_left, hc1, hc2, hc3]
        simp
      by_cases hm1 : m = 1
      · subst m
        have hc2 : (Polynomial.monomial 1 a).coeff 2 = 0 := by
          rw [Polynomial.coeff_monomial]
          norm_num
        have hc3 : (Polynomial.monomial 1 a).coeff 3 = 0 := by
          rw [Polynomial.coeff_monomial]
          norm_num
        rw [hc2, hc3]
        simp
      by_cases hm2 : m = 2
      · subst m
        have hc1 : (Polynomial.monomial 2 a).coeff 1 = 0 := by
          rw [Polynomial.coeff_monomial]
          norm_num
        have hc3 : (Polynomial.monomial 2 a).coeff 3 = 0 := by
          rw [Polynomial.coeff_monomial]
          norm_num
        rw [hc1, hc3]
        simp
      by_cases hm3 : m = 3
      · subst m
        have hc1 : (Polynomial.monomial 3 a).coeff 1 = 0 := by
          rw [Polynomial.coeff_monomial]
          norm_num
        have hc2 : (Polynomial.monomial 3 a).coeff 2 = 0 := by
          rw [Polynomial.coeff_monomial]
          norm_num
        rw [hc1, hc2]
        simp
      have hm4 : 4 ≤ m := by omega
      have hz : z ^ 4 ∣ z ^ m := pow_dvd_pow z hm4
      have hza : z ^ 4 ∣ a * z ^ m := dvd_mul_of_dvd_right hz a
      convert hza using 1 <;>
        simp [Polynomial.eval_monomial, Polynomial.coeff_monomial,
          hm0, hm1, hm2, hm3]

private lemma localFourthPolynomial_eval (k i : ℕ) (z : ℤ) :
    (localThirdPolynomial k i).eval z = localOffsetCofactor k i z := by
  unfold localThirdPolynomial localOffsetCofactor
  rw [Polynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro j hj
  simp
  ring

private lemma localFourthPolynomial_coeff_zero (k i : ℕ) :
    (localThirdPolynomial k i).coeff 0 = localSecondConstant k i := by
  unfold localThirdPolynomial localSecondConstant finsetAffineConstant
  simp [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_prod]

private lemma affinePolynomial_coeff_one_fourth
    {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℤ) :
    (∏ x ∈ s, (Polynomial.X + Polynomial.C (f x))).coeff 1 =
      finsetAffineLinear s f := by
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty]
      rw [Polynomial.coeff_one]
      simp [finsetAffineLinear]
  | @insert a s ha ih =>
      have hzero :
          (∏ x ∈ s, (Polynomial.X + Polynomial.C (f x))).coeff 0 =
            finsetAffineConstant s f := by
        rw [Polynomial.coeff_zero_eq_eval_zero]
        simp [finsetAffineConstant, Polynomial.eval_prod]
      have hleftZero :
          (Polynomial.X + Polynomial.C (f a)).coeff 0 = f a := by
        rw [Polynomial.coeff_add, Polynomial.coeff_X,
          Polynomial.coeff_C_zero]
        norm_num
      have hCOne : (Polynomial.C (f a)).coeff 1 = 0 :=
        Polynomial.coeff_C_ne_zero (by norm_num)
      have hleftOne :
          (Polynomial.X + Polynomial.C (f a)).coeff 1 = 1 := by
        rw [Polynomial.coeff_add, Polynomial.coeff_X, hCOne]
        norm_num
      rw [Finset.prod_insert ha, Polynomial.mul_coeff_one, ih,
        finsetAffineLinear_insert f ha, hzero, hleftZero, hleftOne]
      ring

private lemma localFourthPolynomial_coeff_one (k i : ℕ) :
    (localThirdPolynomial k i).coeff 1 = localSecondLinear k i := by
  unfold localThirdPolynomial localSecondLinear
  exact affinePolynomial_coeff_one_fourth ((Finset.Icc 1 k).erase i)
    (fun j => (j : ℤ) - (i : ℤ))

/-- Exact fourth-order Taylor remainder for the local cofactor. -/
theorem localOffsetCofactor_fourth_order (k i : ℕ) (z : ℤ) :
    z ^ 4 ∣ localOffsetCofactor k i z - localSecondConstant k i -
      localSecondLinear k i * z - localThirdQuadratic k i * z ^ 2 -
      localFourthCubic k i * z ^ 3 := by
  have h := fourth_dvd_polynomial_eval_sub_four_coefficients
    (localThirdPolynomial k i) z
  simpa [localFourthPolynomial_eval, localFourthPolynomial_coeff_zero,
    localFourthPolynomial_coeff_one, localThirdQuadratic,
    localFourthCubic] using h

/-- Pure integer algebra behind the fourth local lift.  The conclusion keeps
all cofactor-`A` corrections; no division by `3` is used. -/
theorem fourth_order_local_algebra
    {H L M A C D E F QL QU X : ℤ}
    (hH : H ≠ 0)
    (hL : L = H * X)
    (hres : 3 * L - H * M = A * H ^ 2)
    (heq : (L + H * M) * QU = 4 * L * QL)
    (hQL : H ^ 4 ∣ QL - C - D * L - E * L ^ 2 - F * L ^ 3)
    (hQU : H ^ 4 ∣ QU - C - D * (L + H * M) -
      E * (L + H * M) ^ 2 - F * (L + H * M) ^ 3) :
    H ^ 3 ∣
      3 * (-3 * (3 * C * A - 4 * D * M ^ 2) +
          20 * E * H * M ^ 3) +
        H ^ 2 * (-9 * D * A ^ 2 + 36 * E * A * M ^ 2 +
          84 * F * M ^ 4) := by
  let EL : ℤ := QL - C - D * L - E * L ^ 2 - F * L ^ 3
  let EU : ℤ := QU - C - D * (L + H * M) -
    E * (L + H * M) ^ 2 - F * (L + H * M) ^ 3
  let T : ℤ := -C * A + D * ((X + M) ^ 2 - 4 * X ^ 2) +
    H * E * ((X + M) ^ 3 - 4 * X ^ 3) +
    H ^ 2 * F * ((X + M) ^ 4 - 4 * X ^ 4)
  let target : ℤ :=
    3 * (-3 * (3 * C * A - 4 * D * M ^ 2) +
        20 * E * H * M ^ 3) +
      H ^ 2 * (-9 * D * A ^ 2 + 36 * E * A * M ^ 2 +
        84 * F * M ^ 4)
  have hLdiv : H ∣ L := ⟨X, hL⟩
  have hUdiv : H ∣ L + H * M :=
    dvd_add hLdiv (dvd_mul_right H M)
  have hEL : H ^ 4 ∣ EL := by simpa [EL] using hQL
  have hEU : H ^ 4 ∣ EU := by simpa [EU] using hQU
  have hLEL : H ^ 5 ∣ L * EL := by
    have hmul := mul_dvd_mul hLdiv hEL
    convert hmul using 1 <;> ring
  have hUEU : H ^ 5 ∣ (L + H * M) * EU := by
    have hmul := mul_dvd_mul hUdiv hEU
    convert hmul using 1 <;> ring
  have hbase : H ^ 5 ∣
      (L + H * M) *
          (C + D * (L + H * M) + E * (L + H * M) ^ 2 +
            F * (L + H * M) ^ 3) -
        4 * L * (C + D * L + E * L ^ 2 + F * L ^ 3) := by
    have hid :
        (L + H * M) *
            (C + D * (L + H * M) + E * (L + H * M) ^ 2 +
              F * (L + H * M) ^ 3) -
          4 * L * (C + D * L + E * L ^ 2 + F * L ^ 3) =
        4 * (L * EL) - (L + H * M) * EU := by
      calc
        (L + H * M) *
            (C + D * (L + H * M) + E * (L + H * M) ^ 2 +
              F * (L + H * M) ^ 3) -
          4 * L * (C + D * L + E * L ^ 2 + F * L ^ 3) =
            ((L + H * M) * QU - 4 * L * QL) +
              (4 * (L * (QL - C - D * L - E * L ^ 2 - F * L ^ 3)) -
                (L + H * M) *
                  (QU - C - D * (L + H * M) - E * (L + H * M) ^ 2 -
                    F * (L + H * M) ^ 3)) := by ring
        _ = 4 * (L * EL) - (L + H * M) * EU := by
          rw [heq]
          simp [EL, EU]
    rw [hid]
    exact dvd_sub (dvd_mul_of_dvd_right hLEL 4) hUEU
  have hbaseT : H ^ 5 ∣ H ^ 2 * T := by
    have hEq :
        (L + H * M) *
            (C + D * (L + H * M) + E * (L + H * M) ^ 2 +
              F * (L + H * M) ^ 3) -
          4 * L * (C + D * L + E * L ^ 2 + F * L ^ 3) = H ^ 2 * T := by
      dsimp [T]
      rw [hL]
      have hres' : 3 * (H * X) - H * M = A * H ^ 2 := by
        simpa [hL] using hres
      calc
        (H * X + H * M) *
            (C + D * (H * X + H * M) + E * (H * X + H * M) ^ 2 +
              F * (H * X + H * M) ^ 3) -
          4 * (H * X) *
            (C + D * (H * X) + E * (H * X) ^ 2 + F * (H * X) ^ 3) =
            -C * (3 * (H * X) - H * M) +
              H ^ 2 * D * ((X + M) ^ 2 - 4 * X ^ 2) +
              H ^ 3 * E * ((X + M) ^ 3 - 4 * X ^ 3) +
              H ^ 4 * F * ((X + M) ^ 4 - 4 * X ^ 4) := by ring
        _ = -C * (A * H ^ 2) +
              H ^ 2 * D * ((X + M) ^ 2 - 4 * X ^ 2) +
              H ^ 3 * E * ((X + M) ^ 3 - 4 * X ^ 3) +
              H ^ 4 * F * ((X + M) ^ 4 - 4 * X ^ 4) := by rw [hres']
        _ = H ^ 2 * T := by dsimp [T]; ring
    rw [← hEq]
    exact hbase
  have hT : H ^ 3 ∣ T := by
    rcases hbaseT with ⟨q, hq⟩
    refine ⟨q, ?_⟩
    apply mul_left_cancel₀ (pow_ne_zero 2 hH)
    calc
      H ^ 2 * T = H ^ 5 * q := hq
      _ = H ^ 2 * (H ^ 3 * q) := by ring
  have hrEq : 3 * X - M = A * H := by
    apply mul_left_cancel₀ hH
    calc
      H * (3 * X - M) = 3 * L - H * M := by rw [hL]; ring
      _ = A * H ^ 2 := hres
      _ = H * (A * H) := by ring
  have htargetDiff : H ^ 3 ∣ 27 * T - target := by
    refine ⟨
      80 * A * F * M ^ 3 + H * (-3 * A ^ 3 * E + 24 * A ^ 2 * F * M ^ 2) -
        A ^ 4 * F * H ^ 3, ?_⟩
    dsimp [T, target]
    have hM : M = 3 * X - A * H := by linarith
    rw [hM]
    ring
  have hTwentySevenT : H ^ 3 ∣ 27 * T :=
    dvd_mul_of_dvd_right hT 27
  have htarget := dvd_sub hTwentySevenT htargetDiff
  simpa [target] using htarget

/-- Fourth-order local lift for a clean divisor `h` with residual `a*h^2`. -/
theorem fourth_order_local_lift
    {k n d i h m a : ℕ}
    (hi : i ∈ Finset.Icc 1 k)
    (hh : 0 < h)
    (hd : d = h * m)
    (hfactor : h ∣ n + i)
    (hres : 3 * ((n + i : ℕ) : ℤ) - (d : ℤ) =
      (a : ℤ) * (h : ℤ) ^ 2)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    (h : ℤ) ^ 3 ∣
      3 * (-3 * (3 * localSecondConstant k i * (a : ℤ) -
          4 * localSecondLinear k i * (m : ℤ) ^ 2) +
        20 * localThirdQuadratic k i * (h : ℤ) * (m : ℤ) ^ 3) +
      (h : ℤ) ^ 2 *
        (-9 * localSecondLinear k i * (a : ℤ) ^ 2 +
          36 * localThirdQuadratic k i * (a : ℤ) * (m : ℤ) ^ 2 +
          84 * localFourthCubic k i * (m : ℤ) ^ 4) := by
  rcases hfactor with ⟨x, hx⟩
  let H : ℤ := (h : ℤ)
  let L : ℤ := ((n + i : ℕ) : ℤ)
  let M : ℤ := (m : ℤ)
  let A : ℤ := (a : ℤ)
  let C : ℤ := localSecondConstant k i
  let D : ℤ := localSecondLinear k i
  let E : ℤ := localThirdQuadratic k i
  let F : ℤ := localFourthCubic k i
  let X : ℤ := (x : ℤ)
  let QL : ℤ := localBlockCofactor k i (n : ℤ)
  let QU : ℤ := localBlockCofactor k i ((n + d : ℕ) : ℤ)
  have hH : H ≠ 0 := by
    dsimp [H]
    exact_mod_cast (Nat.ne_of_gt hh)
  have hL : L = H * X := by
    dsimp [L, H, X]
    exact_mod_cast hx
  have hdCast : (d : ℤ) = H * M := by
    dsimp [H, M]
    exact_mod_cast hd
  have hres' : 3 * L - H * M = A * H ^ 2 := by
    simpa [L, H, M, A, hdCast] using hres
  have heqInt :
      intBlockProduct k ((n + d : ℕ) : ℤ) =
        4 * intBlockProduct k (n : ℤ) := by
    rw [intBlockProduct_natCast, intBlockProduct_natCast]
    exact_mod_cast heq
  have heqLocal : (L + H * M) * QU = 4 * L * QL := by
    rw [intBlockProduct_eq_factor_mul_localBlockCofactor
        ((n + d : ℕ) : ℤ) hi,
      intBlockProduct_eq_factor_mul_localBlockCofactor (n : ℤ) hi] at heqInt
    dsimp [L, H, M, QL, QU]
    push_cast at heqInt ⊢
    rw [hd] at heqInt ⊢
    push_cast at heqInt ⊢
    convert heqInt using 1 <;> ring
  have hHL : H ∣ L := ⟨X, hL⟩
  have hHU : H ∣ L + H * M := dvd_add hHL (dvd_mul_right H M)
  have hHfourthLfourth : H ^ 4 ∣ L ^ 4 :=
    pow_dvd_pow_of_dvd hHL 4
  have hHfourthUfourth : H ^ 4 ∣ (L + H * M) ^ 4 :=
    pow_dvd_pow_of_dvd hHU 4
  have hQLexp : L ^ 4 ∣ QL - C - D * L - E * L ^ 2 - F * L ^ 3 := by
    have h := localOffsetCofactor_fourth_order k i L
    have hrel : localOffsetCofactor k i L = QL := by
      dsimp [L, QL]
      exact localOffsetCofactor_eq_localBlockCofactor
    simpa [hrel, C, D, E, F] using h
  have hQUexp : (L + H * M) ^ 4 ∣
      QU - C - D * (L + H * M) - E * (L + H * M) ^ 2 -
        F * (L + H * M) ^ 3 := by
    have h := localOffsetCofactor_fourth_order k i (L + H * M)
    have hU : L + H * M = ((n + d + i : ℕ) : ℤ) := by
      dsimp [L, H, M]
      push_cast
      rw [hd]
      push_cast
      ring
    have hrel : localOffsetCofactor k i (L + H * M) = QU := by
      rw [hU]
      dsimp [QU]
      have hlocal :=
        (localOffsetCofactor_eq_localBlockCofactor (k := k) (i := i)
          (n := n + d))
      convert hlocal using 1 <;> push_cast <;> ring
    simpa [hrel, C, D, E, F] using h
  have hQL' : H ^ 4 ∣ QL - C - D * L - E * L ^ 2 - F * L ^ 3 :=
    dvd_trans hHfourthLfourth hQLexp
  have hQU' : H ^ 4 ∣
      QU - C - D * (L + H * M) - E * (L + H * M) ^ 2 -
        F * (L + H * M) ^ 3 :=
    dvd_trans hHfourthUfourth hQUexp
  simpa [H, M, A, C, D, E, F] using
    fourth_order_local_algebra hH hL hres' heqLocal hQL' hQU'

/-- Correction polynomial left after eliminating both opposite squares from
the fourth local lift. -/
def threeBucketFourthCorrection
    (D E F t g deltaLeft deltaRight : ℤ) : ℤ :=
  -9 * D * t ^ 2 -
    108 * D * t * g ^ 2 * (deltaLeft + deltaRight) +
    324 * E * t * g ^ 2 * deltaLeft * deltaRight +
    6804 * F * g ^ 4 * (deltaLeft * deltaRight) ^ 2

/-- Fourth cyclic obstruction at the `P` owner. -/
def threeBucketFourthObstruction
    (P b c C D E F a g deltaLeft deltaRight gap : ℤ) : ℤ :=
  3 * b * c *
      threeBucketThirdObstruction C D E a b c g
        deltaLeft deltaRight gap +
    P ^ 2 * threeBucketFourthCorrection D E F (a * b * c) g
      deltaLeft deltaRight

/-- Refined third composition modulo `P^3`.  The extra term proportional to
`a*(deltaLeft+deltaRight)` is invisible in the banked modulo-`P^2` lift but
is essential at fourth order. -/
private theorem three_bucket_third_refined_mod_cube
    {P Q R a b c g C D E deltaLeft deltaRight : ℤ}
    (hleft : a * P ^ 2 - b * Q ^ 2 = 3 * deltaLeft)
    (hright : a * P ^ 2 - c * R ^ 2 = 3 * deltaRight) :
    P ^ 3 ∣
      b * c *
          (-3 * (3 * C * a - 4 * D * (g * Q * R) ^ 2) +
            20 * E * P * (g * Q * R) ^ 3) -
        threeBucketThirdObstruction C D E a b c g
          deltaLeft deltaRight (g * P * Q * R) +
        36 * a * D * g ^ 2 * P ^ 2 * (deltaLeft + deltaRight) := by
  have hB : b * Q ^ 2 = a * P ^ 2 - 3 * deltaLeft := by linarith
  have hC : c * R ^ 2 = a * P ^ 2 - 3 * deltaRight := by linarith
  have hZ :
      (b * Q ^ 2) * (c * R ^ 2) =
        a ^ 2 * P ^ 4 - 3 * a * P ^ 2 * (deltaLeft + deltaRight) +
          9 * deltaLeft * deltaRight := by
    rw [hB, hC]
    ring
  refine ⟨
    12 * D * g ^ 2 * a ^ 2 * P +
      20 * E * g ^ 3 * Q * R *
        (-3 * a * (deltaLeft + deltaRight) + a ^ 2 * P ^ 2), ?_⟩
  calc
    b * c *
          (-3 * (3 * C * a - 4 * D * (g * Q * R) ^ 2) +
            20 * E * P * (g * Q * R) ^ 3) -
        threeBucketThirdObstruction C D E a b c g
          deltaLeft deltaRight (g * P * Q * R) +
        36 * a * D * g ^ 2 * P ^ 2 * (deltaLeft + deltaRight) =
      (12 * D * g ^ 2 + 20 * E * P * g ^ 3 * Q * R) *
          ((b * Q ^ 2) * (c * R ^ 2) -
            9 * deltaLeft * deltaRight) +
        36 * a * D * g ^ 2 * P ^ 2 *
          (deltaLeft + deltaRight) := by
            simp [threeBucketThirdObstruction,
              threeBucketSecondObstruction]
            ring
    _ = (12 * D * g ^ 2 + 20 * E * P * g ^ 3 * Q * R) *
          (a ^ 2 * P ^ 4 -
            3 * a * P ^ 2 * (deltaLeft + deltaRight)) +
        36 * a * D * g ^ 2 * P ^ 2 *
          (deltaLeft + deltaRight) := by rw [hZ]; ring
    _ = P ^ 3 *
        (12 * D * g ^ 2 * a ^ 2 * P +
          20 * E * g ^ 3 * Q * R *
            (-3 * a * (deltaLeft + deltaRight) + a ^ 2 * P ^ 2)) := by ring

private theorem three_bucket_fourth_correction_mod_owner
    {P Q R a b c g D E F deltaLeft deltaRight : ℤ}
    (hleft : a * P ^ 2 - b * Q ^ 2 = 3 * deltaLeft)
    (hright : a * P ^ 2 - c * R ^ 2 = 3 * deltaRight) :
    P ∣
      (b * c) ^ 2 *
          (-9 * D * a ^ 2 + 36 * E * a * (g * Q * R) ^ 2 +
            84 * F * (g * Q * R) ^ 4) -
        (-9 * D * (a * b * c) ^ 2 +
          324 * E * (a * b * c) * g ^ 2 * deltaLeft * deltaRight +
          6804 * F * g ^ 4 * (deltaLeft * deltaRight) ^ 2) := by
  have hB : b * Q ^ 2 = a * P ^ 2 - 3 * deltaLeft := by linarith
  have hC : c * R ^ 2 = a * P ^ 2 - 3 * deltaRight := by linarith
  have hZ :
      (b * Q ^ 2) * (c * R ^ 2) =
        a ^ 2 * P ^ 4 - 3 * a * P ^ 2 * (deltaLeft + deltaRight) +
          9 * deltaLeft * deltaRight := by
    rw [hB, hC]
    ring
  refine ⟨
    12 * P * a * g ^ 2 *
      (P ^ 2 * a - 3 * deltaLeft - 3 * deltaRight) *
      (3 * (b * c) * E * a + 7 * F * P ^ 4 * a ^ 2 * g ^ 2 -
        21 * F * P ^ 2 * a * deltaLeft * g ^ 2 -
        21 * F * P ^ 2 * a * deltaRight * g ^ 2 +
        126 * F * deltaLeft * deltaRight * g ^ 2), ?_⟩
  calc
    (b * c) ^ 2 *
          (-9 * D * a ^ 2 + 36 * E * a * (g * Q * R) ^ 2 +
            84 * F * (g * Q * R) ^ 4) -
        (-9 * D * (a * b * c) ^ 2 +
          324 * E * (a * b * c) * g ^ 2 * deltaLeft * deltaRight +
          6804 * F * g ^ 4 * (deltaLeft * deltaRight) ^ 2) =
      -9 * D * a ^ 2 * (b * c) ^ 2 +
        36 * E * a * g ^ 2 * (b * c) *
          ((b * Q ^ 2) * (c * R ^ 2)) +
        84 * F * g ^ 4 * ((b * Q ^ 2) * (c * R ^ 2)) ^ 2 -
        (-9 * D * (a * b * c) ^ 2 +
          324 * E * (a * b * c) * g ^ 2 * deltaLeft * deltaRight +
          6804 * F * g ^ 4 * (deltaLeft * deltaRight) ^ 2) := by ring
    _ = -9 * D * a ^ 2 * (b * c) ^ 2 +
        36 * E * a * g ^ 2 * (b * c) *
          (a ^ 2 * P ^ 4 - 3 * a * P ^ 2 *
              (deltaLeft + deltaRight) + 9 * deltaLeft * deltaRight) +
        84 * F * g ^ 4 *
          (a ^ 2 * P ^ 4 - 3 * a * P ^ 2 *
              (deltaLeft + deltaRight) + 9 * deltaLeft * deltaRight) ^ 2 -
        (-9 * D * (a * b * c) ^ 2 +
          324 * E * (a * b * c) * g ^ 2 * deltaLeft * deltaRight +
          6804 * F * g ^ 4 * (deltaLeft * deltaRight) ^ 2) := by rw [hZ]
    _ = P *
        (12 * P * a * g ^ 2 *
          (P ^ 2 * a - 3 * deltaLeft - 3 * deltaRight) *
          (3 * (b * c) * E * a + 7 * F * P ^ 4 * a ^ 2 * g ^ 2 -
            21 * F * P ^ 2 * a * deltaLeft * g ^ 2 -
            21 * F * P ^ 2 * a * deltaRight * g ^ 2 +
            126 * F * deltaLeft * deltaRight * g ^ 2)) := by ring

/-- Compose the fourth local lift with both exact square-residual differences.
The conclusion is cyclic: relabeling `(P,a)` with either opposite pair gives
the other two owner congruences. -/
theorem three_bucket_fourth_obstruction_dvd_cube
    {P Q R a b c g C D E F deltaLeft deltaRight : ℤ}
    (hfourth : P ^ 3 ∣
      3 * (-3 * (3 * C * a - 4 * D * (g * Q * R) ^ 2) +
          20 * E * P * (g * Q * R) ^ 3) +
        P ^ 2 * (-9 * D * a ^ 2 + 36 * E * a * (g * Q * R) ^ 2 +
          84 * F * (g * Q * R) ^ 4))
    (hleft : a * P ^ 2 - b * Q ^ 2 = 3 * deltaLeft)
    (hright : a * P ^ 2 - c * R ^ 2 = 3 * deltaRight) :
    P ^ 3 ∣ threeBucketFourthObstruction P b c C D E F a g
      deltaLeft deltaRight (g * P * Q * R) := by
  let T3 : ℤ :=
    -3 * (3 * C * a - 4 * D * (g * Q * R) ^ 2) +
      20 * E * P * (g * Q * R) ^ 3
  let K : ℤ :=
    -9 * D * a ^ 2 + 36 * E * a * (g * Q * R) ^ 2 +
      84 * F * (g * Q * R) ^ 4
  let F3 : ℤ := threeBucketThirdObstruction C D E a b c g
    deltaLeft deltaRight (g * P * Q * R)
  let K0 : ℤ :=
    -9 * D * (a * b * c) ^ 2 +
      324 * E * (a * b * c) * g ^ 2 * deltaLeft * deltaRight +
      6804 * F * g ^ 4 * (deltaLeft * deltaRight) ^ 2
  have hrefined : P ^ 3 ∣
      b * c * T3 - F3 +
        36 * a * D * g ^ 2 * P ^ 2 * (deltaLeft + deltaRight) := by
    simpa [T3, F3] using
      three_bucket_third_refined_mod_cube hleft hright
  have hrefinedMul : P ^ 3 ∣
      3 * b * c *
        (b * c * T3 - F3 +
          36 * a * D * g ^ 2 * P ^ 2 *
            (deltaLeft + deltaRight)) :=
    dvd_mul_of_dvd_right hrefined (3 * b * c)
  have hK : P ∣ (b * c) ^ 2 * K - K0 := by
    simpa [K, K0] using
      three_bucket_fourth_correction_mod_owner hleft hright
  have hKmul : P ^ 3 ∣ P ^ 2 * ((b * c) ^ 2 * K - K0) := by
    rcases hK with ⟨w, hw⟩
    refine ⟨w, ?_⟩
    rw [hw]
    ring
  have hdiffRaw := dvd_add hrefinedMul hKmul
  have hdiff : P ^ 3 ∣
      (b * c) ^ 2 * (3 * T3 + P ^ 2 * K) -
        threeBucketFourthObstruction P b c C D E F a g
          deltaLeft deltaRight (g * P * Q * R) := by
    convert hdiffRaw using 1 <;>
      simp [threeBucketFourthObstruction, threeBucketFourthCorrection,
        T3, K, F3, K0] <;> ring
  have hraw : P ^ 3 ∣ (b * c) ^ 2 * (3 * T3 + P ^ 2 * K) := by
    have hbase : P ^ 3 ∣ 3 * T3 + P ^ 2 * K := by
      simpa [T3, K] using hfourth
    exact dvd_mul_of_dvd_right hbase ((b * c) ^ 2)
  have htarget := dvd_sub hraw hdiff
  convert htarget using 1 <;> ring

#print axioms localOffsetCofactor_fourth_order
#print axioms fourth_order_local_algebra
#print axioms fourth_order_local_lift
#print axioms three_bucket_fourth_obstruction_dvd_cube

end Erdos686Variant
end Erdos686
