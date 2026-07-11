/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686GlobalResidualConcentration
import ErdosProblems.Erdos686TwoPrimeSecondLift

/-!
# Erdős 686: third local lift and cleaned two-prime composition

This module is separate from the global-residual concentration core.  It
depends on the independently audited second-order local lift and adds the
quadratic Taylor coefficient needed when both second obstructions vanish.

Dependency SHA at composition time:

`Erdos686TwoPrimeSecondLift.lean =
 e4ec6011fa24122072aa35ddba80e12d8d7ab0f9cd37a290610a3b2e4d493dbd`.
-/

namespace Erdos686
namespace Erdos686Variant

open Polynomial
open scoped BigOperators

/-- Polynomial form of the local offset cofactor. -/
noncomputable def localThirdPolynomial (k i : ℕ) : Polynomial ℤ :=
  ∏ j ∈ (Finset.Icc 1 k).erase i,
    (Polynomial.X + Polynomial.C ((j : ℤ) - (i : ℤ)))

/-- Quadratic coefficient in the signed local cofactor expansion. -/
noncomputable def localThirdQuadratic (k i : ℕ) : ℤ :=
  (localThirdPolynomial k i).coeff 2

private lemma cube_dvd_polynomial_eval_sub_three_coefficients
    (P : Polynomial ℤ) (z : ℤ) :
    z ^ 3 ∣ P.eval z - P.coeff 0 - P.coeff 1 * z - P.coeff 2 * z ^ 2 := by
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
        rw [Polynomial.monomial_zero_left, hc1, hc2]
        simp
      by_cases hm1 : m = 1
      · subst m
        have hc2 : (Polynomial.monomial 1 a).coeff 2 = 0 := by
          rw [Polynomial.coeff_monomial]
          norm_num
        rw [hc2]
        simp
      by_cases hm2 : m = 2
      · subst m
        have hc1 : (Polynomial.monomial 2 a).coeff 1 = 0 := by
          rw [Polynomial.coeff_monomial]
          norm_num
        rw [hc1]
        simp
      have hm3 : 3 ≤ m := by omega
      have hz : z ^ 3 ∣ z ^ m := pow_dvd_pow z hm3
      have hza : z ^ 3 ∣ a * z ^ m := dvd_mul_of_dvd_right hz a
      convert hza using 1 <;>
        simp [Polynomial.eval_monomial, Polynomial.coeff_monomial, hm0, hm1, hm2]

private lemma localThirdPolynomial_eval (k i : ℕ) (z : ℤ) :
    (localThirdPolynomial k i).eval z = localOffsetCofactor k i z := by
  unfold localThirdPolynomial localOffsetCofactor
  rw [Polynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro j hj
  simp
  ring

private lemma localThirdPolynomial_coeff_zero (k i : ℕ) :
    (localThirdPolynomial k i).coeff 0 = localSecondConstant k i := by
  unfold localThirdPolynomial localSecondConstant finsetAffineConstant
  simp [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_prod]

private lemma affinePolynomial_coeff_one
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

private lemma localThirdPolynomial_coeff_one (k i : ℕ) :
    (localThirdPolynomial k i).coeff 1 = localSecondLinear k i := by
  unfold localThirdPolynomial localSecondLinear
  exact affinePolynomial_coeff_one ((Finset.Icc 1 k).erase i)
    (fun j => (j : ℤ) - (i : ℤ))

/-- Exact third-order Taylor remainder for the local cofactor. -/
theorem localOffsetCofactor_third_order (k i : ℕ) (z : ℤ) :
    z ^ 3 ∣ localOffsetCofactor k i z - localSecondConstant k i -
      localSecondLinear k i * z - localThirdQuadratic k i * z ^ 2 := by
  have h := cube_dvd_polynomial_eval_sub_three_coefficients
    (localThirdPolynomial k i) z
  simpa [localThirdPolynomial_eval, localThirdPolynomial_coeff_zero,
    localThirdPolynomial_coeff_one, localThirdQuadratic] using h

/-- Pure integer algebra behind the third local lift. -/
theorem third_order_local_algebra
    {H L M A C D E QL QU X : ℤ}
    (hH : H ≠ 0)
    (hL : L = H * X)
    (hres : 3 * L - H * M = A * H ^ 2)
    (heq : (L + H * M) * QU = 4 * L * QL)
    (hQL : H ^ 3 ∣ QL - C - D * L - E * L ^ 2)
    (hQU : H ^ 3 ∣ QU - C - D * (L + H * M) -
      E * (L + H * M) ^ 2) :
    H ^ 2 ∣
      -3 * (3 * C * A - 4 * D * M ^ 2) + 20 * E * H * M ^ 3 := by
  let EL : ℤ := QL - C - D * L - E * L ^ 2
  let EU : ℤ := QU - C - D * (L + H * M) - E * (L + H * M) ^ 2
  let T : ℤ := -C * A + D * ((X + M) ^ 2 - 4 * X ^ 2) +
    H * E * ((X + M) ^ 3 - 4 * X ^ 3)
  have hLdiv : H ∣ L := ⟨X, hL⟩
  have hUdiv : H ∣ L + H * M := dvd_add hLdiv (dvd_mul_right H M)
  have hEL : H ^ 3 ∣ EL := by simpa [EL] using hQL
  have hEU : H ^ 3 ∣ EU := by simpa [EU] using hQU
  have hLEL : H ^ 4 ∣ L * EL := by
    have hmul := mul_dvd_mul hLdiv hEL
    convert hmul using 1 <;> ring
  have hUEU : H ^ 4 ∣ (L + H * M) * EU := by
    have hmul := mul_dvd_mul hUdiv hEU
    convert hmul using 1 <;> ring
  have hbase : H ^ 4 ∣
      (L + H * M) *
          (C + D * (L + H * M) + E * (L + H * M) ^ 2) -
        4 * L * (C + D * L + E * L ^ 2) := by
    have hid :
        (L + H * M) *
            (C + D * (L + H * M) + E * (L + H * M) ^ 2) -
          4 * L * (C + D * L + E * L ^ 2) =
        4 * (L * EL) - (L + H * M) * EU := by
      calc
        (L + H * M) *
            (C + D * (L + H * M) + E * (L + H * M) ^ 2) -
          4 * L * (C + D * L + E * L ^ 2) =
            ((L + H * M) * QU - 4 * L * QL) +
              (4 * (L * (QL - C - D * L - E * L ^ 2)) -
                (L + H * M) *
                  (QU - C - D * (L + H * M) - E * (L + H * M) ^ 2)) := by
                    ring
        _ = 4 * (L * EL) - (L + H * M) * EU := by
          rw [heq]
          simp [EL, EU]
    rw [hid]
    exact dvd_sub (dvd_mul_of_dvd_right hLEL 4) hUEU
  have hbaseT : H ^ 4 ∣ H ^ 2 * T := by
    have hEq :
        (L + H * M) *
            (C + D * (L + H * M) + E * (L + H * M) ^ 2) -
          4 * L * (C + D * L + E * L ^ 2) = H ^ 2 * T := by
      dsimp [T]
      rw [hL]
      have hres' : 3 * (H * X) - H * M = A * H ^ 2 := by
        simpa [hL] using hres
      calc
        (H * X + H * M) *
            (C + D * (H * X + H * M) + E * (H * X + H * M) ^ 2) -
          4 * (H * X) * (C + D * (H * X) + E * (H * X) ^ 2) =
            -C * (3 * (H * X) - H * M) +
              H ^ 2 * D * ((X + M) ^ 2 - 4 * X ^ 2) +
              H ^ 3 * E * ((X + M) ^ 3 - 4 * X ^ 3) := by ring
        _ = -C * (A * H ^ 2) +
              H ^ 2 * D * ((X + M) ^ 2 - 4 * X ^ 2) +
              H ^ 3 * E * ((X + M) ^ 3 - 4 * X ^ 3) := by rw [hres']
        _ = H ^ 2 *
              (-C * A + D * ((X + M) ^ 2 - 4 * X ^ 2) +
                H * E * ((X + M) ^ 3 - 4 * X ^ 3)) := by ring
    rw [← hEq]
    exact hbase
  have hT : H ^ 2 ∣ T := by
    rcases hbaseT with ⟨q, hq⟩
    refine ⟨q, ?_⟩
    apply mul_left_cancel₀ (pow_ne_zero 2 hH)
    calc
      H ^ 2 * T = H ^ 4 * q := hq
      _ = H ^ 2 * (H ^ 2 * q) := by ring
  have hrEq : 3 * X - M = A * H := by
    apply mul_left_cancel₀ hH
    calc
      H * (3 * X - M) = 3 * L - H * M := by rw [hL]; ring
      _ = A * H ^ 2 := hres
      _ = H * (A * H) := by ring
  have htargetDiff : H ^ 2 ∣
      9 * T -
        (-3 * (3 * C * A - 4 * D * M ^ 2) + 20 * E * H * M ^ 3) := by
    refine ⟨-3 * A ^ 2 * D + 12 * A * E * M ^ 2 - A ^ 3 * E * H ^ 2, ?_⟩
    dsimp [T]
    have hM : M = 3 * X - A * H := by linarith
    rw [hM]
    ring
  have hNineT : H ^ 2 ∣ 9 * T := dvd_mul_of_dvd_right hT 9
  have htarget := dvd_sub hNineT htargetDiff
  convert htarget using 1 <;> ring

/-- Third-order local lift for a clean divisor `h` with residual `a*h^2`. -/
theorem third_order_local_lift
    {k n d i h m a : ℕ}
    (hi : i ∈ Finset.Icc 1 k)
    (hh : 0 < h)
    (hd : d = h * m)
    (hfactor : h ∣ n + i)
    (hres : 3 * ((n + i : ℕ) : ℤ) - (d : ℤ) =
      (a : ℤ) * (h : ℤ) ^ 2)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    (h : ℤ) ^ 2 ∣
      -3 * (3 * localSecondConstant k i * (a : ℤ) -
          4 * localSecondLinear k i * (m : ℤ) ^ 2) +
        20 * localThirdQuadratic k i * (h : ℤ) * (m : ℤ) ^ 3 := by
  rcases hfactor with ⟨x, hx⟩
  let H : ℤ := (h : ℤ)
  let L : ℤ := ((n + i : ℕ) : ℤ)
  let M : ℤ := (m : ℤ)
  let A : ℤ := (a : ℤ)
  let C : ℤ := localSecondConstant k i
  let D : ℤ := localSecondLinear k i
  let E : ℤ := localThirdQuadratic k i
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
  have hHcubeLcube : H ^ 3 ∣ L ^ 3 := by
    exact pow_dvd_pow_of_dvd hHL 3
  have hHcubeUcube : H ^ 3 ∣ (L + H * M) ^ 3 := by
    exact pow_dvd_pow_of_dvd hHU 3
  have hQLexp : L ^ 3 ∣ QL - C - D * L - E * L ^ 2 := by
    have h := localOffsetCofactor_third_order k i L
    have hrel : localOffsetCofactor k i L = QL := by
      dsimp [L, QL]
      exact localOffsetCofactor_eq_localBlockCofactor
    simpa [hrel, C, D, E] using h
  have hQUexp : (L + H * M) ^ 3 ∣
      QU - C - D * (L + H * M) - E * (L + H * M) ^ 2 := by
    have h := localOffsetCofactor_third_order k i (L + H * M)
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
    simpa [hrel, C, D, E] using h
  have hQL' : H ^ 3 ∣ QL - C - D * L - E * L ^ 2 :=
    dvd_trans hHcubeLcube hQLexp
  have hQU' : H ^ 3 ∣
      QU - C - D * (L + H * M) - E * (L + H * M) ^ 2 :=
    dvd_trans hHcubeUcube hQUexp
  simpa [H, M, A, C, D, E] using
    third_order_local_algebra hH hL hres' heqLocal hQL' hQU'

/-- Kernel-reduced quadratic-coefficient table for the six target rows. -/
def thirdIndexTable : ℕ → ℕ → Finset ℕ
  | 5, 1 => {2,3,4,5}
  | 5, 2 => {1,3,4,5}
  | 5, 3 => {1,2,4,5}
  | 5, 4 => {1,2,3,5}
  | 5, 5 => {1,2,3,4}
  | 7, 1 => {2,3,4,5,6,7}
  | 7, 2 => {1,3,4,5,6,7}
  | 7, 3 => {1,2,4,5,6,7}
  | 7, 4 => {1,2,3,5,6,7}
  | 7, 5 => {1,2,3,4,6,7}
  | 7, 6 => {1,2,3,4,5,7}
  | 7, 7 => {1,2,3,4,5,6}
  | 9, 1 => {2,3,4,5,6,7,8,9}
  | 9, 2 => {1,3,4,5,6,7,8,9}
  | 9, 3 => {1,2,4,5,6,7,8,9}
  | 9, 4 => {1,2,3,5,6,7,8,9}
  | 9, 5 => {1,2,3,4,6,7,8,9}
  | 9, 6 => {1,2,3,4,5,7,8,9}
  | 9, 7 => {1,2,3,4,5,6,8,9}
  | 9, 8 => {1,2,3,4,5,6,7,9}
  | 9, 9 => {1,2,3,4,5,6,7,8}
  | 11, 1 => {2,3,4,5,6,7,8,9,10,11}
  | 11, 2 => {1,3,4,5,6,7,8,9,10,11}
  | 11, 3 => {1,2,4,5,6,7,8,9,10,11}
  | 11, 4 => {1,2,3,5,6,7,8,9,10,11}
  | 11, 5 => {1,2,3,4,6,7,8,9,10,11}
  | 11, 6 => {1,2,3,4,5,7,8,9,10,11}
  | 11, 7 => {1,2,3,4,5,6,8,9,10,11}
  | 11, 8 => {1,2,3,4,5,6,7,9,10,11}
  | 11, 9 => {1,2,3,4,5,6,7,8,10,11}
  | 11, 10 => {1,2,3,4,5,6,7,8,9,11}
  | 11, 11 => {1,2,3,4,5,6,7,8,9,10}
  | 13, 1 => {2,3,4,5,6,7,8,9,10,11,12,13}
  | 13, 2 => {1,3,4,5,6,7,8,9,10,11,12,13}
  | 13, 3 => {1,2,4,5,6,7,8,9,10,11,12,13}
  | 13, 4 => {1,2,3,5,6,7,8,9,10,11,12,13}
  | 13, 5 => {1,2,3,4,6,7,8,9,10,11,12,13}
  | 13, 6 => {1,2,3,4,5,7,8,9,10,11,12,13}
  | 13, 7 => {1,2,3,4,5,6,8,9,10,11,12,13}
  | 13, 8 => {1,2,3,4,5,6,7,9,10,11,12,13}
  | 13, 9 => {1,2,3,4,5,6,7,8,10,11,12,13}
  | 13, 10 => {1,2,3,4,5,6,7,8,9,11,12,13}
  | 13, 11 => {1,2,3,4,5,6,7,8,9,10,12,13}
  | 13, 12 => {1,2,3,4,5,6,7,8,9,10,11,13}
  | 13, 13 => {1,2,3,4,5,6,7,8,9,10,11,12}
  | 15, 1 => {2,3,4,5,6,7,8,9,10,11,12,13,14,15}
  | 15, 2 => {1,3,4,5,6,7,8,9,10,11,12,13,14,15}
  | 15, 3 => {1,2,4,5,6,7,8,9,10,11,12,13,14,15}
  | 15, 4 => {1,2,3,5,6,7,8,9,10,11,12,13,14,15}
  | 15, 5 => {1,2,3,4,6,7,8,9,10,11,12,13,14,15}
  | 15, 6 => {1,2,3,4,5,7,8,9,10,11,12,13,14,15}
  | 15, 7 => {1,2,3,4,5,6,8,9,10,11,12,13,14,15}
  | 15, 8 => {1,2,3,4,5,6,7,9,10,11,12,13,14,15}
  | 15, 9 => {1,2,3,4,5,6,7,8,10,11,12,13,14,15}
  | 15, 10 => {1,2,3,4,5,6,7,8,9,11,12,13,14,15}
  | 15, 11 => {1,2,3,4,5,6,7,8,9,10,12,13,14,15}
  | 15, 12 => {1,2,3,4,5,6,7,8,9,10,11,13,14,15}
  | 15, 13 => {1,2,3,4,5,6,7,8,9,10,11,12,14,15}
  | 15, 14 => {1,2,3,4,5,6,7,8,9,10,11,12,13,15}
  | 15, 15 => {1,2,3,4,5,6,7,8,9,10,11,12,13,14}
  | _, _ => ∅

def thirdCoefficientTable : ℕ → ℕ → ℤ
  | 5, 1 => 35
  | 5, 2 => 5
  | 5, 3 => -5
  | 5, 4 => 5
  | 5, 5 => 35
  | 7, 1 => 1624
  | 7, 2 => 49
  | 7, 3 => -56
  | 7, 4 => 49
  | 7, 5 => -56
  | 7, 6 => 49
  | 7, 7 => 1624
  | 9, 1 => 118124
  | 9, 2 => -64
  | 9, 3 => -1324
  | 9, 4 => 944
  | 9, 5 => -820
  | 9, 6 => 944
  | 9, 7 => -1324
  | 9, 8 => -64
  | 9, 9 => 118124
  | 11, 1 => 12753576
  | 11, 2 => -146124
  | 11, 3 => -52184
  | 11, 4 => 34716
  | 11, 5 => -24024
  | 11, 6 => 21076
  | 11, 7 => -24024
  | 11, 8 => 34716
  | 11, 9 => -52184
  | 11, 10 => -146124
  | 11, 11 => 12753576
  | 13, 1 => 1931559552
  | 13, 2 => -30374136
  | 13, 3 => -2749968
  | 13, 4 => 2078856
  | 13, 5 => -1233024
  | 13, 6 => 870792
  | 13, 7 => -773136
  | 13, 8 => 870792
  | 13, 9 => -1233024
  | 13, 10 => 2078856
  | 13, 11 => -2749968
  | 13, 12 => -30374136
  | 13, 13 => 1931559552
  | 15, 1 => 392156797824
  | 15, 2 => -6793958016
  | 15, 3 => -117207936
  | 15, 4 => 180973584
  | 15, 5 => -98338176
  | 15, 6 => 58909824
  | 15, 7 => -42777216
  | 15, 8 => 38402064
  | 15, 9 => -42777216
  | 15, 10 => 58909824
  | 15, 11 => -98338176
  | 15, 12 => 180973584
  | 15, 13 => -117207936
  | 15, 14 => -6793958016
  | 15, 15 => 392156797824
  | _, _ => 0

set_option maxHeartbeats 1000000 in
private theorem localThirdIndex_eq_table
    {k i : ℕ}
    (hk : k = 5 ∨ k = 7 ∨ k = 9 ∨ k = 11 ∨ k = 13 ∨ k = 15)
    (hi : i ∈ Finset.Icc 1 k) :
    (Finset.Icc 1 k).erase i = thirdIndexTable k i := by
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rw [Finset.mem_Icc] at hi <;>
    rcases hi with ⟨hi1, hik⟩ <;>
    interval_cases i <;> decide

/-!
The explicit coefficient table is checked through a tiny integer recurrence,
rather than by normalizing sixty expanded polynomial products.  Besides making
the certificate easier to audit, this keeps compiled proof terms small enough
for the ordinary `lake build` code-generation path.
-/

/-- Linear coefficient of a product of affine factors, computed recursively. -/
private def listAffineLinear : List ℤ → ℤ
  | [] => 0
  | a :: l => l.prod + a * listAffineLinear l

/-- Quadratic coefficient of a product of affine factors, computed recursively. -/
private def listAffineQuadratic : List ℤ → ℤ
  | [] => 0
  | a :: l => listAffineLinear l + a * listAffineQuadratic l

private lemma affinePolynomial_mul_coeff_two (a : ℤ) (P : Polynomial ℤ) :
    ((Polynomial.X + Polynomial.C a) * P).coeff 2 =
      P.coeff 1 + a * P.coeff 2 := by
  rw [add_mul, Polynomial.coeff_add]
  rw [show 2 = 1 + 1 by norm_num, Polynomial.coeff_X_mul,
    Polynomial.coeff_C_mul]

private lemma listAffinePolynomial_coeff_zero (l : List ℤ) :
    ((l.map fun a => Polynomial.X + Polynomial.C a).prod).coeff 0 = l.prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.map_cons, List.prod_cons, Polynomial.coeff_zero_eq_eval_zero,
        Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X,
        Polynomial.eval_C]
      rw [← Polynomial.coeff_zero_eq_eval_zero, ih]
      simp

private lemma listAffinePolynomial_coeff_one (l : List ℤ) :
    ((l.map fun a => Polynomial.X + Polynomial.C a).prod).coeff 1 =
      listAffineLinear l := by
  induction l with
  | nil =>
      rw [List.map_nil, List.prod_nil, Polynomial.coeff_one]
      norm_num [listAffineLinear]
  | cons a l ih =>
      have hzero :
          (Polynomial.X + Polynomial.C a : Polynomial ℤ).coeff 0 = a := by
        simp [Polynomial.coeff_zero_eq_eval_zero]
      have hone :
          (Polynomial.X + Polynomial.C a : Polynomial ℤ).coeff 1 = 1 := by
        rw [Polynomial.coeff_add, Polynomial.coeff_X,
          Polynomial.coeff_C_ne_zero (by norm_num)]
        norm_num
      rw [List.map_cons, List.prod_cons, Polynomial.mul_coeff_one,
        listAffinePolynomial_coeff_zero, ih, hzero, hone]
      simp only [listAffineLinear]
      ring

private lemma listAffinePolynomial_coeff_two (l : List ℤ) :
    ((l.map fun a => Polynomial.X + Polynomial.C a).prod).coeff 2 =
      listAffineQuadratic l := by
  induction l with
  | nil =>
      rw [List.map_nil, List.prod_nil, Polynomial.coeff_one]
      norm_num [listAffineQuadratic]
  | cons a l ih =>
      rw [List.map_cons, List.prod_cons, affinePolynomial_mul_coeff_two,
        listAffinePolynomial_coeff_one, ih]
      rfl

/-- Canonical computable enumeration of the local indices. -/
private def localThirdIndexList (k i : ℕ) : List ℕ :=
  ((List.range k).map Nat.succ).erase i

private lemma localThirdIndexList_nodup (k i : ℕ) :
    (localThirdIndexList k i).Nodup := by
  apply List.Nodup.erase
  exact List.Nodup.map Nat.succ_injective List.nodup_range

private lemma localThirdIndexList_toFinset (k i : ℕ) :
    (localThirdIndexList k i).toFinset = (Finset.Icc 1 k).erase i := by
  have hnodup : ((List.range k).map Nat.succ).Nodup :=
    List.Nodup.map Nat.succ_injective List.nodup_range
  ext j
  rw [List.mem_toFinset, localThirdIndexList, hnodup.mem_erase_iff,
    Finset.mem_erase, Finset.mem_Icc]
  rw [List.mem_map]
  constructor
  · rintro ⟨hne, a, ha, haj⟩
    subst j
    exact ⟨hne, by omega, by simpa using ha⟩
  · rintro ⟨hne, hj1, hjk⟩
    refine ⟨hne, j - 1, ?_, Nat.succ_pred_eq_of_pos hj1⟩
    simpa [List.mem_range] using (show j - 1 < k by omega)

private lemma localThirdPolynomial_eq_list (k i : ℕ) :
    localThirdPolynomial k i =
      ((localThirdIndexList k i).map (fun (j : ℕ) =>
        (Polynomial.X : Polynomial ℤ) +
          Polynomial.C ((j : ℤ) - (i : ℤ)))).prod := by
  unfold localThirdPolynomial
  rw [← localThirdIndexList_toFinset]
  exact List.prod_toFinset
    (l := localThirdIndexList k i)
    (fun j : ℕ => (Polynomial.X : Polynomial ℤ) +
      Polynomial.C ((j : ℤ) - (i : ℤ)))
    (localThirdIndexList_nodup k i)

/-- Fast integer certificate for the quadratic local Taylor coefficient. -/
private def localThirdQuadraticFast (k i : ℕ) : ℤ :=
  listAffineQuadratic
    ((localThirdIndexList k i).map (fun (j : ℕ) => (j : ℤ) - (i : ℤ)))

private lemma localThirdQuadratic_eq_fast
    {k i : ℕ}
    (hk : k = 5 ∨ k = 7 ∨ k = 9 ∨ k = 11 ∨ k = 13 ∨ k = 15)
    (hi : i ∈ Finset.Icc 1 k) :
    localThirdQuadratic k i = localThirdQuadraticFast k i := by
  unfold localThirdQuadratic
  rw [localThirdPolynomial_eq_list]
  simpa [localThirdQuadraticFast, List.map_map, Function.comp_def] using
    listAffinePolynomial_coeff_two
      ((localThirdIndexList k i).map
        (fun (j : ℕ) => (j : ℤ) - (i : ℤ)))

/-- The finite-product quadratic coefficient agrees with the explicit table. -/
theorem localThirdQuadratic_eq_table
    {k i : ℕ}
    (hk : k = 5 ∨ k = 7 ∨ k = 9 ∨ k = 11 ∨ k = 13 ∨ k = 15)
    (hi : i ∈ Finset.Icc 1 k) :
    localThirdQuadratic k i = thirdCoefficientTable k i := by
  rw [localThirdQuadratic_eq_fast hk hi]
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rw [Finset.mem_Icc] at hi <;>
    rcases hi with ⟨hi1, hik⟩ <;>
    interval_cases i <;> decide

/-- All three signed local Taylor coefficients are small and the quadratic
coefficient is nonzero in every target row. -/
theorem target_local_taylor_bounds
    {k i : ℕ}
    (hk : k = 5 ∨ k = 7 ∨ k = 9 ∨ k = 11 ∨ k = 13 ∨ k = 15)
    (hi : i ∈ Finset.Icc 1 k) :
    Int.natAbs (localSecondConstant k i) < 10 ^ 12 ∧
      Int.natAbs (localSecondLinear k i) < 10 ^ 12 ∧
      Int.natAbs (localThirdQuadratic k i) < 10 ^ 12 ∧
      localThirdQuadratic k i ≠ 0 := by
  rw [localSecondConstant_eq_table hk hi,
    localSecondLinear_eq_table hk hi,
    localThirdQuadratic_eq_table hk hi]
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rw [Finset.mem_Icc] at hi <;>
    rcases hi with ⟨hi1, hik⟩ <;>
    interval_cases i <;> norm_num [secondCoefficientTable, thirdCoefficientTable]

/-- Pell substitution with a residual-cleaning cofactor `g`. -/
theorem clean_second_obstruction_divisibilities
    {P Q a b g : ℕ} {Cᵢ Dᵢ Cⱼ Dⱼ delta : ℤ}
    (hP : (P : ℤ) ∣
      3 * Cᵢ * (a : ℤ) - 4 * Dᵢ * ((g * Q : ℕ) : ℤ) ^ 2)
    (hQ : (Q : ℤ) ∣
      3 * Cⱼ * (b : ℤ) - 4 * Dⱼ * ((g * P : ℕ) : ℤ) ^ 2)
    (hPell : (a : ℤ) * (P : ℤ) ^ 2 - (b : ℤ) * (Q : ℤ) ^ 2 =
      3 * delta) :
    (P : ℤ) ∣ 3 * (Cᵢ * (a * b : ℕ) + 4 * Dᵢ * (g : ℤ) ^ 2 * delta) ∧
      (Q : ℤ) ∣ 3 * (Cⱼ * (a * b : ℕ) - 4 * Dⱼ * (g : ℤ) ^ 2 * delta) := by
  constructor
  · have hmul : (P : ℤ) ∣ (b : ℤ) *
        (3 * Cᵢ * (a : ℤ) - 4 * Dᵢ * ((g * Q : ℕ) : ℤ) ^ 2) :=
      dvd_mul_of_dvd_right hP (b : ℤ)
    have hpow : (P : ℤ) ∣
        4 * Dᵢ * (g : ℤ) ^ 2 * (a : ℤ) * (P : ℤ) ^ 2 :=
      dvd_mul_of_dvd_right (dvd_pow_self (P : ℤ) (by norm_num))
        (4 * Dᵢ * (g : ℤ) ^ 2 * (a : ℤ))
    have hadd := dvd_add hmul hpow
    convert hadd using 1
    push_cast at hPell ⊢
    linear_combination -4 * Dᵢ * (g : ℤ) ^ 2 * hPell
  · have hmul : (Q : ℤ) ∣ (a : ℤ) *
        (3 * Cⱼ * (b : ℤ) - 4 * Dⱼ * ((g * P : ℕ) : ℤ) ^ 2) :=
      dvd_mul_of_dvd_right hQ (a : ℤ)
    have hpow : (Q : ℤ) ∣
        4 * Dⱼ * (g : ℤ) ^ 2 * (b : ℤ) * (Q : ℤ) ^ 2 :=
      dvd_mul_of_dvd_right (dvd_pow_self (Q : ℤ) (by norm_num))
        (4 * Dⱼ * (g : ℤ) ^ 2 * (b : ℤ))
    have hadd := dvd_add hmul hpow
    convert hadd using 1
    push_cast at hPell ⊢
    linear_combination 4 * Dⱼ * (g : ℤ) ^ 2 * hPell

/-- When one cleaned second obstruction vanishes, the third local lift and
the Pell identity force the corresponding clean component into a bounded
integer independent of the opposite component. -/
theorem clean_third_zero_component_dvd
    {P Q a b g : ℕ} {C D E delta : ℤ}
    (hPpos : 0 < P)
    (hgpos : 0 < g)
    (hbpos : 0 < b)
    (hcop : P.Coprime Q)
    (hPell : (a : ℤ) * (P : ℤ) ^ 2 - (b : ℤ) * (Q : ℤ) ^ 2 =
      3 * delta)
    (hSecond : (P : ℤ) ∣
      3 * C * (a : ℤ) - 4 * D * ((g * Q : ℕ) : ℤ) ^ 2)
    (hThird : (P : ℤ) ^ 2 ∣
      -3 * (3 * C * (a : ℤ) - 4 * D * ((g * Q : ℕ) : ℤ) ^ 2) +
        20 * E * (P : ℤ) * ((g * Q : ℕ) : ℤ) ^ 3)
    (hzero : C * (a * b : ℕ) + 4 * D * (g : ℤ) ^ 2 * delta = 0) :
    P ∣ 20 * Int.natAbs E * b * g ^ 3 := by
  let Z : ℤ := 3 * C * (a : ℤ) - 4 * D * ((g * Q : ℕ) : ℤ) ^ 2
  rcases hSecond with ⟨z, hz⟩
  have hz' : Z = (P : ℤ) * z := by simpa [Z] using hz
  have hPne : (P : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hPpos)
  have hThirdLinear : (P : ℤ) ∣
      -3 * z + 20 * E * ((g * Q : ℕ) : ℤ) ^ 3 := by
    rcases hThird with ⟨w, hw⟩
    refine ⟨w, ?_⟩
    apply mul_left_cancel₀ hPne
    calc
      (P : ℤ) * (-3 * z + 20 * E * ((g * Q : ℕ) : ℤ) ^ 3) =
          -3 * Z + 20 * E * (P : ℤ) * ((g * Q : ℕ) : ℤ) ^ 3 := by
            rw [hz']
            ring
      _ = (P : ℤ) ^ 2 * w := hw
      _ = (P : ℤ) * ((P : ℤ) * w) := by ring
  have hbZ : (b : ℤ) * Z =
      -4 * D * (g : ℤ) ^ 2 * (a : ℤ) * (P : ℤ) ^ 2 := by
    dsimp [Z]
    push_cast at hPell hzero ⊢
    linear_combination 3 * hzero + 4 * D * (g : ℤ) ^ 2 * hPell
  have hbzDvd : (P : ℤ) ∣ (b : ℤ) * z := by
    refine ⟨-4 * D * (g : ℤ) ^ 2 * (a : ℤ), ?_⟩
    apply mul_left_cancel₀ hPne
    calc
      (P : ℤ) * ((b : ℤ) * z) = (b : ℤ) * Z := by rw [hz']; ring
      _ = -4 * D * (g : ℤ) ^ 2 * (a : ℤ) * (P : ℤ) ^ 2 := hbZ
      _ = (P : ℤ) * ((P : ℤ) *
          (-4 * D * (g : ℤ) ^ 2 * (a : ℤ))) := by ring
  have hmul := dvd_mul_of_dvd_right hThirdLinear (b : ℤ)
  have hfirst : (P : ℤ) ∣ -3 * ((b : ℤ) * z) :=
    dvd_mul_of_dvd_right hbzDvd (-3 : ℤ)
  have hraw : (P : ℤ) ∣
      20 * E * (b : ℤ) * ((g * Q : ℕ) : ℤ) ^ 3 := by
    have hsub := dvd_sub hmul hfirst
    convert hsub using 1 <;> ring
  have hnat : P ∣
      20 * Int.natAbs E * b * (g * Q) ^ 3 := by
    have habs := Int.natAbs_dvd_natAbs.mpr hraw
    simpa [Int.natAbs_mul, Int.natAbs_pow] using habs
  have hcopPow : P.Coprime (Q ^ 3) := hcop.pow_right 3
  have hfactored : P ∣
      (20 * Int.natAbs E * b * g ^ 3) * Q ^ 3 := by
    convert hnat using 1 <;> ring
  exact hcopPow.dvd_of_dvd_mul_right hfactored

/-- A deliberately loose obstruction constant; its square still leaves more
than one decimal order of magnitude below the target cutoff after the worst
two-component cleaning loss. -/
def cleanSecondObstructionBound : ℕ := 10 ^ 30

/-- Uniform two-component cleaning cofactor. -/
def cleanTwoPrimeLossBound : ℕ := 59049 ^ 2

private theorem clean_second_obstruction_abs_lt
    {C D delta : ℤ} {t g A : ℕ}
    (hgpos : 0 < g)
    (hA : A ≤ 35)
    (ht : t < A ^ 2 * g ^ 2)
    (hC : Int.natAbs C < 10 ^ 12)
    (hD : Int.natAbs D < 10 ^ 12)
    (hdelta : Int.natAbs delta < 15) :
    Int.natAbs (3 * (C * (t : ℤ) + 4 * D * (g : ℤ) ^ 2 * delta)) <
      cleanSecondObstructionBound * g ^ 2 := by
  have hA2 : A ^ 2 ≤ 35 ^ 2 := Nat.pow_le_pow_left hA 2
  have ht' : t < 35 ^ 2 * g ^ 2 :=
    lt_of_lt_of_le ht (Nat.mul_le_mul_right (g ^ 2) hA2)
  have htri := Int.natAbs_add_le (C * (t : ℤ))
    (4 * D * (g : ℤ) ^ 2 * delta)
  have htri' :
      Int.natAbs (C * (t : ℤ) + 4 * D * (g : ℤ) ^ 2 * delta) ≤
        Int.natAbs C * t + 4 * Int.natAbs D * g ^ 2 * Int.natAbs delta := by
    simpa [Int.natAbs_mul, Int.natAbs_pow] using htri
  have hct : Int.natAbs C * t < 10 ^ 12 * (35 ^ 2 * g ^ 2) :=
    Nat.mul_lt_mul_of_le_of_lt (Nat.le_of_lt hC) ht' (by norm_num)
  have hdg : 4 * Int.natAbs D * g ^ 2 * Int.natAbs delta ≤
      4 * 10 ^ 12 * g ^ 2 * 15 := by
    exact Nat.mul_le_mul
      (Nat.mul_le_mul
        (Nat.mul_le_mul (by omega : 4 ≤ 4) (Nat.le_of_lt hD))
        (le_rfl : g ^ 2 ≤ g ^ 2))
      (Nat.le_of_lt hdelta)
  have hinside :
      Int.natAbs (C * (t : ℤ) + 4 * D * (g : ℤ) ^ 2 * delta) <
        (10 ^ 12 * 35 ^ 2 + 4 * 10 ^ 12 * 15) * g ^ 2 := by
    calc
      Int.natAbs (C * (t : ℤ) + 4 * D * (g : ℤ) ^ 2 * delta) ≤
          Int.natAbs C * t + 4 * Int.natAbs D * g ^ 2 * Int.natAbs delta := htri'
      _ < 10 ^ 12 * (35 ^ 2 * g ^ 2) +
          4 * 10 ^ 12 * g ^ 2 * 15 := Nat.add_lt_add_of_lt_of_le hct hdg
      _ = (10 ^ 12 * 35 ^ 2 + 4 * 10 ^ 12 * 15) * g ^ 2 := by ring
  have hthree :
      Int.natAbs (3 * (C * (t : ℤ) + 4 * D * (g : ℤ) ^ 2 * delta)) =
        3 * Int.natAbs (C * (t : ℤ) + 4 * D * (g : ℤ) ^ 2 * delta) := by
    simp [Int.natAbs_mul]
  rw [hthree]
  have hmul := Nat.mul_lt_mul_of_pos_left hinside (by norm_num : 0 < 3)
  dsimp [cleanSecondObstructionBound]
  have hg2pos : 0 < g ^ 2 := pow_pos hgpos _
  nlinarith

private theorem clean_gap_lt_of_nonzero_second_obstruction
    {P Q g A b : ℕ} {L : ℤ}
    (hPpos : 0 < P)
    (hQpos : 0 < Q)
    (hgpos : 0 < g)
    (hbpos : 0 < b)
    (hbRatio : b * Q < A * (g * P))
    (hdiv : (P : ℤ) ∣ L)
    (hLne : L ≠ 0)
    (hLbound : Int.natAbs L < cleanSecondObstructionBound * g ^ 2) :
    g * P * Q < A * cleanSecondObstructionBound ^ 2 * g ^ 6 := by
  have hPle : P ≤ Int.natAbs L := by
    simpa using Int.natAbs_le_of_dvd_ne_zero hdiv hLne
  have hPB : P < cleanSecondObstructionBound * g ^ 2 :=
    lt_of_le_of_lt hPle hLbound
  have hQbQ : Q ≤ b * Q := by nlinarith
  have hQAP : Q < A * (g * P) := lt_of_le_of_lt hQbQ hbRatio
  have hApos : 0 < A := by
    have : 0 < A * (g * P) := lt_trans (Nat.mul_pos hbpos hQpos) hbRatio
    apply Nat.pos_of_ne_zero
    intro hA
    rw [hA, zero_mul] at this
    exact (Nat.lt_irrefl 0) this
  have hQBound : Q < A * (g * (cleanSecondObstructionBound * g ^ 2)) := by
    exact lt_trans hQAP (Nat.mul_lt_mul_of_pos_left
      (Nat.mul_lt_mul_of_pos_left hPB hgpos) hApos)
  calc
    g * P * Q < g * (cleanSecondObstructionBound * g ^ 2) * Q := by
      exact Nat.mul_lt_mul_of_pos_right
        (Nat.mul_lt_mul_of_pos_left hPB hgpos) hQpos
    _ < g * (cleanSecondObstructionBound * g ^ 2) *
        (A * (g * (cleanSecondObstructionBound * g ^ 2))) :=
      Nat.mul_lt_mul_of_pos_left hQBound
        (Nat.mul_pos hgpos (Nat.mul_pos (by norm_num [cleanSecondObstructionBound])
          (pow_pos hgpos _)))
    _ = A * cleanSecondObstructionBound ^ 2 * g ^ 6 := by ring

private lemma clean_generic_numeric_cutoff
    {A g : ℕ} (hA : A ≤ 35) (hg : g ≤ cleanTwoPrimeLossBound) :
    A * cleanSecondObstructionBound ^ 2 * g ^ 6 < 10 ^ 120 := by
  calc
    A * cleanSecondObstructionBound ^ 2 * g ^ 6 ≤
        35 * cleanSecondObstructionBound ^ 2 * cleanTwoPrimeLossBound ^ 6 :=
      Nat.mul_le_mul (Nat.mul_le_mul hA (le_rfl : cleanSecondObstructionBound ^ 2 ≤
        cleanSecondObstructionBound ^ 2)) (Nat.pow_le_pow_left hg 6)
    _ < 10 ^ 120 := by
      norm_num [cleanSecondObstructionBound, cleanTwoPrimeLossBound]

private lemma clean_third_numeric_cutoff
    {g : ℕ} (hg : g ≤ cleanTwoPrimeLossBound) :
    400 * (10 ^ 12) ^ 2 * 35 ^ 2 * g ^ 9 < 10 ^ 120 := by
  calc
    400 * (10 ^ 12) ^ 2 * 35 ^ 2 * g ^ 9 ≤
        400 * (10 ^ 12) ^ 2 * 35 ^ 2 * cleanTwoPrimeLossBound ^ 9 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hg 9)
    _ < 10 ^ 120 := by norm_num [cleanTwoPrimeLossBound]

/-- Abstract closure of two distinct cleaned residual buckets.  This theorem
contains the complete second/third obstruction split; the equation-level
wrapper below only has to construct its hypotheses. -/
theorem two_clean_residual_buckets_below_cutoff
    {k A P Q g i j a b : ℕ}
    (hk : k = 5 ∨ k = 7 ∨ k = 9 ∨ k = 11 ∨ k = 13 ∨ k = 15)
    (hi : i ∈ Finset.Icc 1 k)
    (hj : j ∈ Finset.Icc 1 k)
    (hij : i ≠ j)
    (hA : A ≤ 35)
    (hPpos : 0 < P)
    (hQpos : 0 < Q)
    (hgpos : 0 < g)
    (hapos : 0 < a)
    (hbpos : 0 < b)
    (hcop : P.Coprime Q)
    (hg : g ≤ cleanTwoPrimeLossBound)
    (haRatio : a * P < A * (g * Q))
    (hbRatio : b * Q < A * (g * P))
    (hab : a * b < A ^ 2 * g ^ 2)
    (hPell : (a : ℤ) * (P : ℤ) ^ 2 - (b : ℤ) * (Q : ℤ) ^ 2 =
      3 * ((i : ℤ) - (j : ℤ)))
    (hPSecond : (P : ℤ) ∣
      3 * localSecondConstant k i * (a : ℤ) -
        4 * localSecondLinear k i * ((g * Q : ℕ) : ℤ) ^ 2)
    (hQSecond : (Q : ℤ) ∣
      3 * localSecondConstant k j * (b : ℤ) -
        4 * localSecondLinear k j * ((g * P : ℕ) : ℤ) ^ 2)
    (hPThird : (P : ℤ) ^ 2 ∣
      -3 * (3 * localSecondConstant k i * (a : ℤ) -
        4 * localSecondLinear k i * ((g * Q : ℕ) : ℤ) ^ 2) +
      20 * localThirdQuadratic k i * (P : ℤ) * ((g * Q : ℕ) : ℤ) ^ 3)
    (hQThird : (Q : ℤ) ^ 2 ∣
      -3 * (3 * localSecondConstant k j * (b : ℤ) -
        4 * localSecondLinear k j * ((g * P : ℕ) : ℤ) ^ 2) +
      20 * localThirdQuadratic k j * (Q : ℤ) * ((g * P : ℕ) : ℤ) ^ 3) :
    g * P * Q < 10 ^ 120 := by
  let delta : ℤ := (i : ℤ) - (j : ℤ)
  let L : ℤ := 3 *
    (localSecondConstant k i * (a * b : ℕ) +
      4 * localSecondLinear k i * (g : ℤ) ^ 2 * delta)
  let R : ℤ := 3 *
    (localSecondConstant k j * (a * b : ℕ) -
      4 * localSecondLinear k j * (g : ℤ) ^ 2 * delta)
  have hobs := clean_second_obstruction_divisibilities
    hPSecond hQSecond (by simpa [delta] using hPell)
  have hPObs : (P : ℤ) ∣ L := by simpa [L, delta] using hobs.1
  have hQObs : (Q : ℤ) ∣ R := by simpa [R, delta] using hobs.2
  obtain ⟨hCi, hDi, hEi, hEine⟩ := target_local_taylor_bounds hk hi
  obtain ⟨hCj, hDj, hEj, hEjne⟩ := target_local_taylor_bounds hk hj
  have hk15 : k ≤ 15 := by
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have hdeltaEq : Int.natAbs delta = Nat.dist i j := by
    rcases le_total i j with hij' | hji'
    · have heq : delta = -((j - i : ℕ) : ℤ) := by
        dsimp [delta]
        push_cast
        omega
      rw [heq, Int.natAbs_neg, Int.natAbs_natCast,
        Nat.dist_eq_sub_of_le hij']
    · have heq : delta = ((i - j : ℕ) : ℤ) := by
        dsimp [delta]
        push_cast
        omega
      rw [heq, Int.natAbs_natCast,
        Nat.dist_eq_sub_of_le_right hji']
  have hdelta : Int.natAbs delta < 15 := by
    rw [hdeltaEq]
    have hi1 := (Finset.mem_Icc.mp hi).1
    have hj1 := (Finset.mem_Icc.mp hj).1
    have hi' := (Finset.mem_Icc.mp hi).2
    have hj' := (Finset.mem_Icc.mp hj).2
    rcases le_total i j with hij' | hji'
    · rw [Nat.dist_eq_sub_of_le hij']
      omega
    · rw [Nat.dist_eq_sub_of_le_right hji']
      omega
  have hLbound : Int.natAbs L < cleanSecondObstructionBound * g ^ 2 := by
    dsimp [L]
    exact clean_second_obstruction_abs_lt hgpos hA hab hCi hDi hdelta
  have hRbound : Int.natAbs R < cleanSecondObstructionBound * g ^ 2 := by
    dsimp [R]
    have hnegD : Int.natAbs (-localSecondLinear k j) =
        Int.natAbs (localSecondLinear k j) := Int.natAbs_neg _
    have h := clean_second_obstruction_abs_lt
      (C := localSecondConstant k j) (D := -localSecondLinear k j)
      (delta := delta) hgpos hA hab hCj (by simpa [hnegD] using hDj) hdelta
    convert h using 1 <;> push_cast <;> ring
  by_cases hLne : L ≠ 0
  · exact lt_trans
      (clean_gap_lt_of_nonzero_second_obstruction hPpos hQpos hgpos hbpos
        hbRatio hPObs hLne hLbound)
      (clean_generic_numeric_cutoff hA hg)
  by_cases hRne : R ≠ 0
  · have hsmall := clean_gap_lt_of_nonzero_second_obstruction
      hQpos hPpos hgpos hapos haRatio hQObs hRne hRbound
    have hreorder : g * P * Q = g * Q * P := by ring
    rw [hreorder]
    exact lt_trans hsmall (clean_generic_numeric_cutoff hA hg)
  have hLzero :
      localSecondConstant k i * (a * b : ℕ) +
        4 * localSecondLinear k i * (g : ℤ) ^ 2 * delta = 0 := by
    dsimp [L] at hLne
    by_contra hne
    exact hLne (mul_ne_zero (by norm_num) hne)
  have hRzero :
      localSecondConstant k j * (a * b : ℕ) -
        4 * localSecondLinear k j * (g : ℤ) ^ 2 * delta = 0 := by
    dsimp [R] at hRne
    by_contra hne
    exact hRne (mul_ne_zero (by norm_num) hne)
  have hPsmallDvd : P ∣
      20 * Int.natAbs (localThirdQuadratic k i) * b * g ^ 3 :=
    clean_third_zero_component_dvd hPpos hgpos hbpos hcop
      (by simpa [delta] using hPell) hPSecond hPThird hLzero
  have hQsmallDvd : Q ∣
      20 * Int.natAbs (localThirdQuadratic k j) * a * g ^ 3 := by
    apply clean_third_zero_component_dvd (a := b) (b := a)
      hQpos hgpos hapos hcop.symm
      (C := localSecondConstant k j) (D := localSecondLinear k j)
      (E := localThirdQuadratic k j) (delta := -delta)
    · calc
        (b : ℤ) * (Q : ℤ) ^ 2 - (a : ℤ) * (P : ℤ) ^ 2 =
            -((a : ℤ) * (P : ℤ) ^ 2 - (b : ℤ) * (Q : ℤ) ^ 2) := by ring
        _ = -(3 * delta) := by rw [hPell]
        _ = 3 * (-delta) := by ring
    · exact hQSecond
    · exact hQThird
    · convert hRzero using 1 <;> push_cast <;> ring
  have hEiPos : 0 < Int.natAbs (localThirdQuadratic k i) := by
    exact Int.natAbs_pos.mpr hEine
  have hEjPos : 0 < Int.natAbs (localThirdQuadratic k j) := by
    exact Int.natAbs_pos.mpr hEjne
  have hPsmall : P ≤
      20 * Int.natAbs (localThirdQuadratic k i) * b * g ^ 3 :=
    Nat.le_of_dvd
      (by positivity : 0 < 20 * Int.natAbs (localThirdQuadratic k i) * b * g ^ 3)
      hPsmallDvd
  have hQsmall : Q ≤
      20 * Int.natAbs (localThirdQuadratic k j) * a * g ^ 3 :=
    Nat.le_of_dvd
      (by positivity : 0 < 20 * Int.natAbs (localThirdQuadratic k j) * a * g ^ 3)
      hQsmallDvd
  have hprodBound : g * P * Q ≤
      400 * (Int.natAbs (localThirdQuadratic k i) *
        Int.natAbs (localThirdQuadratic k j)) * (a * b) * g ^ 7 := by
    calc
      g * P * Q ≤ g *
          (20 * Int.natAbs (localThirdQuadratic k i) * b * g ^ 3) *
          (20 * Int.natAbs (localThirdQuadratic k j) * a * g ^ 3) :=
        Nat.mul_le_mul (Nat.mul_le_mul (le_rfl : g ≤ g) hPsmall) hQsmall
      _ = 400 * (Int.natAbs (localThirdQuadratic k i) *
          Int.natAbs (localThirdQuadratic k j)) * (a * b) * g ^ 7 := by ring
  have hEprod : Int.natAbs (localThirdQuadratic k i) *
      Int.natAbs (localThirdQuadratic k j) ≤ (10 ^ 12) ^ 2 := by
    exact Nat.mul_le_mul (Nat.le_of_lt hEi) (Nat.le_of_lt hEj)
  have hpre :
      400 * (Int.natAbs (localThirdQuadratic k i) *
        Int.natAbs (localThirdQuadratic k j)) * (a * b) <
      400 * (10 ^ 12) ^ 2 * (A ^ 2 * g ^ 2) := by
    exact Nat.mul_lt_mul_of_le_of_lt
      (Nat.mul_le_mul_left 400 hEprod) hab (by norm_num)
  have hpreG := Nat.mul_lt_mul_of_pos_right hpre (pow_pos hgpos 7)
  have hA2 : A ^ 2 ≤ 35 ^ 2 := Nat.pow_le_pow_left hA 2
  have hthirdBound : g * P * Q <
      400 * (10 ^ 12) ^ 2 * 35 ^ 2 * g ^ 9 := by
    calc
      g * P * Q ≤ 400 * (Int.natAbs (localThirdQuadratic k i) *
          Int.natAbs (localThirdQuadratic k j)) * (a * b) * g ^ 7 := hprodBound
      _ < 400 * (10 ^ 12) ^ 2 * (A ^ 2 * g ^ 2) * g ^ 7 := hpreG
      _ ≤ 400 * (10 ^ 12) ^ 2 * (35 ^ 2 * g ^ 2) * g ^ 7 := by
        exact Nat.mul_le_mul_right (g ^ 7)
          (Nat.mul_le_mul_left (400 * (10 ^ 12) ^ 2)
            (Nat.mul_le_mul_right (g ^ 2) hA2))
      _ = 400 * (10 ^ 12) ^ 2 * 35 ^ 2 * g ^ 9 := by ring
  exact lt_trans hthirdBound (clean_third_numeric_cutoff hg)

/-- Complete equation-level closure for a gap with exactly two distinct prime
bases, with no lower bound on either base.  Small bases are cleaned by the
global residual concentration theorem before the second/third local lifts are
applied. -/
theorem two_prime_support_below_cutoff_of_global_residual_lifts
    {p q e f k n d C A : ℕ}
    (hp : p.Prime)
    (hq : q.Prime)
    (hpq : p ≠ q)
    (he : 0 < e)
    (hf : 0 < f)
    (hk : k = 5 ∨ k = 7 ∨ k = 9 ∨ k = 11 ∨ k = 13 ∨ k = 15)
    (hgap : d = p ^ e * q ^ f)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n)
    (hbase : n + 1 < C * d)
    (hA : A = 3 * C + 2)
    (hA35 : A ≤ 35) :
    d < 10 ^ 120 := by
  have hk5 : 5 ≤ k := by
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have hk15 : k ≤ 15 := by
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have hpPowPos : 0 < p ^ e := pow_pos hp.pos _
  have hqPowPos : 0 < q ^ f := pow_pos hq.pos _
  have hdpos : 0 < d := by rw [hgap]; positivity
  by_contra hnot
  have hlarge : 10 ^ 120 ≤ d := Nat.le_of_not_gt hnot
  have hkd : k ≤ d := by omega
  have hpDvdD : p ^ e ∣ d := by
    rw [hgap]
    exact dvd_mul_right _ _
  have hqDvdD : q ^ f ∣ d := by
    rw [hgap]
    exact dvd_mul_left _ _
  let tp : ℕ := globalResidualCleanExponent p e k
  let tq : ℕ := globalResidualCleanExponent q f k
  let P : ℕ := p ^ tp
  let Q : ℕ := q ^ tq
  let lp : ℕ := p ^ (e - tp)
  let lq : ℕ := q ^ (f - tq)
  let g : ℕ := lp * lq
  obtain ⟨i, hi, hPDvdD, hPFactor, hPSquare, hPComponent⟩ :=
    primePower_component_exists_globalResidual_clean hp he hk5 hkd hpDvdD heq
  obtain ⟨j, hj, hQDvdD, hQFactor, hQSquare, hQComponent⟩ :=
    primePower_component_exists_globalResidual_clean hq hf hk5 hkd hqDvdD heq
  have htpe : tp ≤ e := by
    dsimp [tp, globalResidualCleanExponent]
    omega
  have htqf : tq ≤ f := by
    dsimp [tq, globalResidualCleanExponent]
    omega
  have hpDecomp : p ^ e = P * lp := by
    dsimp [P, lp]
    rw [← pow_add]
    congr 1
    omega
  have hqDecomp : q ^ f = Q * lq := by
    dsimp [Q, lq]
    rw [← pow_add]
    congr 1
    omega
  have hgapClean : d = g * P * Q := by
    rw [hgap, hpDecomp, hqDecomp]
    dsimp [g]
    ring
  have hPpos : 0 < P := by dsimp [P]; exact pow_pos hp.pos _
  have hQpos : 0 < Q := by dsimp [Q]; exact pow_pos hq.pos _
  have hlppos : 0 < lp := by dsimp [lp]; exact pow_pos hp.pos _
  have hlqpos : 0 < lq := by dsimp [lq]; exact pow_pos hq.pos _
  have hgpos : 0 < g := by dsimp [g]; exact Nat.mul_pos hlppos hlqpos
  have hpLossFactor :
      p ^ globalResidualLossExponent p k ≤ 59049 := by
    calc
      p ^ globalResidualLossExponent p k ≤ if p = 3 then 59049 else 64 :=
        globalResidual_prime_loss_factor_le hp hk5 hk15
      _ ≤ 59049 := by split <;> norm_num
  have hqLossFactor :
      q ^ globalResidualLossExponent q k ≤ 59049 := by
    calc
      q ^ globalResidualLossExponent q k ≤ if q = 3 then 59049 else 64 :=
        globalResidual_prime_loss_factor_le hq hk5 hk15
      _ ≤ 59049 := by split <;> norm_num
  have hlp : lp ≤ 59049 := by
    have hexp : e - tp ≤ globalResidualLossExponent p k := by
      dsimp [tp, globalResidualCleanExponent]
      omega
    exact le_trans (Nat.pow_le_pow_right hp.pos hexp) hpLossFactor
  have hlq : lq ≤ 59049 := by
    have hexp : f - tq ≤ globalResidualLossExponent q k := by
      dsimp [tq, globalResidualCleanExponent]
      omega
    exact le_trans (Nat.pow_le_pow_right hq.pos hexp) hqLossFactor
  have hg : g ≤ cleanTwoPrimeLossBound := by
    dsimp [g, cleanTwoPrimeLossBound]
    exact Nat.mul_le_mul hlp hlq
  have hpNotDvdQ : ¬p ∣ q := by
    intro hdiv
    rcases (Nat.dvd_prime hq).mp hdiv with hp1 | hpq'
    · exact hp.ne_one hp1
    · exact hpq hpq'
  have hpqCoprime : p.Coprime q := hp.coprime_iff_not_dvd.mpr hpNotDvdQ
  have hcop : P.Coprime Q := by
    dsimp [P, Q]
    exact Nat.Coprime.pow tp tq hpqCoprime
  have hPSquare' : P ^ 2 ∣ localResidual n d i := by
    simpa [P, tp, globalLocalResidualNat, localResidual] using hPSquare
  have hQSquare' : Q ^ 2 ∣ localResidual n d j := by
    simpa [Q, tq, globalLocalResidualNat, localResidual] using hQSquare
  have hPFactor' : P ∣ n + i := by simpa [P, tp] using hPFactor
  have hQFactor' : Q ∣ n + j := by simpa [Q, tq] using hQFactor
  obtain ⟨hXiPos, hXiUpper⟩ :=
    localResidual_pos_lt_of_base_bound hk5 hkd hi heq hbase hA
  obtain ⟨hXjPos, hXjUpper⟩ :=
    localResidual_pos_lt_of_base_bound hk5 hkd hj heq hbase hA
  by_cases hij : i = j
  · subst j
    have hcopSq : (P ^ 2).Coprime (Q ^ 2) := Nat.Coprime.pow 2 2 hcop
    have hboth : P ^ 2 * Q ^ 2 ∣ localResidual n d i :=
      hcopSq.mul_dvd_of_dvd_of_dvd hPSquare' hQSquare'
    have hPQSq : (P * Q) ^ 2 ∣ localResidual n d i := by
      convert hboth using 1 <;> ring
    have hPQpos : 0 < P * Q := Nat.mul_pos hPpos hQpos
    have hsqLe : (P * Q) ^ 2 ≤ localResidual n d i :=
      Nat.le_of_dvd hXiPos hPQSq
    have hHlt : P * Q < A * g := by
      apply (Nat.mul_lt_mul_right hPQpos).mp
      calc
        (P * Q) * (P * Q) = (P * Q) ^ 2 := by ring
        _ ≤ localResidual n d i := hsqLe
        _ < A * d := hXiUpper
        _ = (A * g) * (P * Q) := by rw [hgapClean]; ring
    have hdSmall : d < A * g ^ 2 := by
      rw [hgapClean]
      calc
        g * P * Q = g * (P * Q) := by ring
        _ < g * (A * g) := Nat.mul_lt_mul_of_pos_left hHlt hgpos
        _ = A * g ^ 2 := by ring
    have hcut : A * g ^ 2 < 10 ^ 120 := by
      calc
        A * g ^ 2 ≤ 35 * cleanTwoPrimeLossBound ^ 2 :=
          Nat.mul_le_mul hA35 (Nat.pow_le_pow_left hg 2)
        _ < 10 ^ 120 := by norm_num [cleanTwoPrimeLossBound]
    exact hnot (lt_trans hdSmall hcut)
  · have hgapP : d = P * (g * Q) := by rw [hgapClean]; ring
    have hgapQ : d = Q * (g * P) := by rw [hgapClean]; ring
    obtain ⟨a, hapos, haeq, haRatio⟩ :=
      exists_positive_local_coefficient hPpos hgapP hXiPos hXiUpper hPSquare'
    obtain ⟨b, hbpos, hbeq, hbRatio⟩ :=
      exists_positive_local_coefficient hQpos hgapQ hXjPos hXjUpper hQSquare'
    have hAgPos : 0 < A * g := by
      have htarget : 0 < A * (g * Q) := lt_trans (Nat.mul_pos hapos hPpos) haRatio
      have hApos : 0 < A := by
        apply Nat.pos_of_ne_zero
        intro hA
        rw [hA, zero_mul] at htarget
        exact (Nat.lt_irrefl 0) htarget
      exact Nat.mul_pos hApos hgpos
    have haRatio' : a * P < (A * g) * Q := by simpa [mul_assoc] using haRatio
    have hbRatio' : b * Q < (A * g) * P := by simpa [mul_assoc] using hbRatio
    have hab' := coefficient_product_lt hbpos hPpos hQpos hAgPos haRatio' hbRatio'
    have hab : a * b < A ^ 2 * g ^ 2 := by
      simpa [Nat.mul_pow] using hab'
    have hXiCast : ((localResidual n d i : ℕ) : ℤ) =
        3 * ((n + i : ℕ) : ℤ) - (d : ℤ) := by
      unfold localResidual
      rw [Int.ofNat_sub (by
        unfold localResidual at hXiPos
        omega)]
      push_cast
      ring
    have hXjCast : ((localResidual n d j : ℕ) : ℤ) =
        3 * ((n + j : ℕ) : ℤ) - (d : ℤ) := by
      unfold localResidual
      rw [Int.ofNat_sub (by
        unfold localResidual at hXjPos
        omega)]
      push_cast
      ring
    have hresP : 3 * ((n + i : ℕ) : ℤ) - (d : ℤ) =
        (a : ℤ) * (P : ℤ) ^ 2 := by
      rw [← hXiCast, haeq]
      push_cast
      ring
    have hresQ : 3 * ((n + j : ℕ) : ℤ) - (d : ℤ) =
        (b : ℤ) * (Q : ℤ) ^ 2 := by
      rw [← hXjCast, hbeq]
      push_cast
      ring
    have hPell : (a : ℤ) * (P : ℤ) ^ 2 - (b : ℤ) * (Q : ℤ) ^ 2 =
        3 * ((i : ℤ) - (j : ℤ)) := by
      calc
        (a : ℤ) * (P : ℤ) ^ 2 - (b : ℤ) * (Q : ℤ) ^ 2 =
            (localResidual n d i : ℤ) - (localResidual n d j : ℤ) := by
              rw [haeq, hbeq]
              push_cast
              ring
        _ = 3 * ((i : ℤ) - (j : ℤ)) := by
          rw [hXiCast, hXjCast]
          push_cast
          ring
    have hPSecond := second_order_local_lift hi hPpos hgapP hPFactor' hresP heq
    have hQSecond := second_order_local_lift hj hQpos hgapQ hQFactor' hresQ heq
    have hPThird := third_order_local_lift hi hPpos hgapP hPFactor' hresP heq
    have hQThird := third_order_local_lift hj hQpos hgapQ hQFactor' hresQ heq
    have hsmall := two_clean_residual_buckets_below_cutoff hk hi hj hij hA35
      hPpos hQpos hgpos hapos hbpos hcop hg haRatio hbRatio hab hPell
      hPSecond hQSecond hPThird hQThird
    apply hnot
    simpa [hgapClean] using hsmall

end Erdos686Variant
end Erdos686
