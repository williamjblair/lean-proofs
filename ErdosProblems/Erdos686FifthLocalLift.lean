/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686ShortWindowQuotient

/-!
# Erdős 686: fifth local lift and the squared third-quotient congruence

Keeping the quartic coefficient of the signed local cofactor gives the exact
next Taylor obstruction

`H^4 | 3*G4 + 20*H^3*M^3*(12*A*F + 17*G*M^2)`.

For three cleaned buckets this composes cyclically.  If the third obstruction
is `P^2*z`, the fourth obstruction is `P^3*y`, and the fifth obstruction is
available, then the former congruence modulo `P` lifts to

`P^2 | 9*b*c*z + 3*J + P*L`.

This is a proper new necessary condition.  No claim is made here that the
three simultaneous squared congruences alone enforce the short window.
-/

namespace Erdos686
namespace Erdos686Variant

open Polynomial

/-- Quartic coefficient in the signed local cofactor expansion. -/
noncomputable def localFifthQuartic (k i : ℕ) : ℤ :=
  (localThirdPolynomial k i).coeff 4

private lemma fifth_dvd_polynomial_eval_sub_five_coefficients
    (P : Polynomial ℤ) (z : ℤ) :
    z ^ 5 ∣ P.eval z - P.coeff 0 - P.coeff 1 * z -
      P.coeff 2 * z ^ 2 - P.coeff 3 * z ^ 3 - P.coeff 4 * z ^ 4 := by
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
        have hc4 : (Polynomial.C a).coeff 4 = 0 :=
          Polynomial.coeff_C_ne_zero (by norm_num)
        rw [Polynomial.monomial_zero_left, hc1, hc2, hc3, hc4]
        simp
      by_cases hm1 : m = 1
      · subst m
        have hc2 : (Polynomial.monomial 1 a).coeff 2 = 0 := by
          rw [Polynomial.coeff_monomial]
          norm_num
        have hc3 : (Polynomial.monomial 1 a).coeff 3 = 0 := by
          rw [Polynomial.coeff_monomial]
          norm_num
        have hc4 : (Polynomial.monomial 1 a).coeff 4 = 0 := by
          rw [Polynomial.coeff_monomial]
          norm_num
        rw [hc2, hc3, hc4]
        simp
      by_cases hm2 : m = 2
      · subst m
        have hc1 : (Polynomial.monomial 2 a).coeff 1 = 0 := by
          rw [Polynomial.coeff_monomial]
          norm_num
        have hc3 : (Polynomial.monomial 2 a).coeff 3 = 0 := by
          rw [Polynomial.coeff_monomial]
          norm_num
        have hc4 : (Polynomial.monomial 2 a).coeff 4 = 0 := by
          rw [Polynomial.coeff_monomial]
          norm_num
        rw [hc1, hc3, hc4]
        simp
      by_cases hm3 : m = 3
      · subst m
        have hc1 : (Polynomial.monomial 3 a).coeff 1 = 0 := by
          rw [Polynomial.coeff_monomial]
          norm_num
        have hc2 : (Polynomial.monomial 3 a).coeff 2 = 0 := by
          rw [Polynomial.coeff_monomial]
          norm_num
        have hc4 : (Polynomial.monomial 3 a).coeff 4 = 0 := by
          rw [Polynomial.coeff_monomial]
          norm_num
        rw [hc1, hc2, hc4]
        simp
      by_cases hm4 : m = 4
      · subst m
        have hc1 : (Polynomial.monomial 4 a).coeff 1 = 0 := by
          rw [Polynomial.coeff_monomial]
          norm_num
        have hc2 : (Polynomial.monomial 4 a).coeff 2 = 0 := by
          rw [Polynomial.coeff_monomial]
          norm_num
        have hc3 : (Polynomial.monomial 4 a).coeff 3 = 0 := by
          rw [Polynomial.coeff_monomial]
          norm_num
        rw [hc1, hc2, hc3]
        simp
      have hm5 : 5 ≤ m := by omega
      have hz : z ^ 5 ∣ z ^ m := pow_dvd_pow z hm5
      have hza : z ^ 5 ∣ a * z ^ m := dvd_mul_of_dvd_right hz a
      convert hza using 1 <;>
        simp [Polynomial.eval_monomial, Polynomial.coeff_monomial,
          hm0, hm1, hm2, hm3, hm4]

private lemma localFifthPolynomial_eval (k i : ℕ) (z : ℤ) :
    (localThirdPolynomial k i).eval z = localOffsetCofactor k i z := by
  unfold localThirdPolynomial localOffsetCofactor
  rw [Polynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro j hj
  simp
  ring

private lemma localFifthPolynomial_coeff_zero (k i : ℕ) :
    (localThirdPolynomial k i).coeff 0 = localSecondConstant k i := by
  unfold localThirdPolynomial localSecondConstant finsetAffineConstant
  simp [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_prod]

private lemma affinePolynomial_coeff_one_fifth
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

private lemma localFifthPolynomial_coeff_one (k i : ℕ) :
    (localThirdPolynomial k i).coeff 1 = localSecondLinear k i := by
  unfold localThirdPolynomial localSecondLinear
  exact affinePolynomial_coeff_one_fifth ((Finset.Icc 1 k).erase i)
    (fun j => (j : ℤ) - (i : ℤ))

/-- Exact fifth-order Taylor remainder for the local cofactor. -/
theorem localOffsetCofactor_fifth_order (k i : ℕ) (z : ℤ) :
    z ^ 5 ∣ localOffsetCofactor k i z - localSecondConstant k i -
      localSecondLinear k i * z - localThirdQuadratic k i * z ^ 2 -
      localFourthCubic k i * z ^ 3 - localFifthQuartic k i * z ^ 4 := by
  have h := fifth_dvd_polynomial_eval_sub_five_coefficients
    (localThirdPolynomial k i) z
  simpa [localFifthPolynomial_eval, localFifthPolynomial_coeff_zero,
    localFifthPolynomial_coeff_one, localThirdQuadratic,
    localFourthCubic, localFifthQuartic] using h

/-- Pure integer algebra behind the fifth local lift. -/
theorem fifth_order_local_algebra
    {H L M A C D E F G QL QU X : ℤ}
    (hH : H ≠ 0)
    (hL : L = H * X)
    (hres : 3 * L - H * M = A * H ^ 2)
    (heq : (L + H * M) * QU = 4 * L * QL)
    (hQL : H ^ 5 ∣ QL - C - D * L - E * L ^ 2 - F * L ^ 3 - G * L ^ 4)
    (hQU : H ^ 5 ∣ QU - C - D * (L + H * M) -
      E * (L + H * M) ^ 2 - F * (L + H * M) ^ 3 -
      G * (L + H * M) ^ 4) :
    H ^ 4 ∣
      3 * (3 * (-3 * (3 * C * A - 4 * D * M ^ 2) +
            20 * E * H * M ^ 3) +
          H ^ 2 * (-9 * D * A ^ 2 + 36 * E * A * M ^ 2 +
            84 * F * M ^ 4)) +
        20 * H ^ 3 * M ^ 3 * (12 * A * F + 17 * G * M ^ 2) := by
  let EL : ℤ := QL - C - D * L - E * L ^ 2 - F * L ^ 3 - G * L ^ 4
  let EU : ℤ := QU - C - D * (L + H * M) -
    E * (L + H * M) ^ 2 - F * (L + H * M) ^ 3 -
    G * (L + H * M) ^ 4
  let T : ℤ := -C * A + D * ((X + M) ^ 2 - 4 * X ^ 2) +
    H * E * ((X + M) ^ 3 - 4 * X ^ 3) +
    H ^ 2 * F * ((X + M) ^ 4 - 4 * X ^ 4) +
    H ^ 3 * G * ((X + M) ^ 5 - 4 * X ^ 5)
  let target : ℤ :=
    3 * (3 * (-3 * (3 * C * A - 4 * D * M ^ 2) +
          20 * E * H * M ^ 3) +
        H ^ 2 * (-9 * D * A ^ 2 + 36 * E * A * M ^ 2 +
          84 * F * M ^ 4)) +
      20 * H ^ 3 * M ^ 3 * (12 * A * F + 17 * G * M ^ 2)
  have hLdiv : H ∣ L := ⟨X, hL⟩
  have hUdiv : H ∣ L + H * M :=
    dvd_add hLdiv (dvd_mul_right H M)
  have hEL : H ^ 5 ∣ EL := by simpa [EL] using hQL
  have hEU : H ^ 5 ∣ EU := by simpa [EU] using hQU
  have hLEL : H ^ 6 ∣ L * EL := by
    have hmul := mul_dvd_mul hLdiv hEL
    convert hmul using 1 <;> ring
  have hUEU : H ^ 6 ∣ (L + H * M) * EU := by
    have hmul := mul_dvd_mul hUdiv hEU
    convert hmul using 1 <;> ring
  have hbase : H ^ 6 ∣
      (L + H * M) *
          (C + D * (L + H * M) + E * (L + H * M) ^ 2 +
            F * (L + H * M) ^ 3 + G * (L + H * M) ^ 4) -
        4 * L * (C + D * L + E * L ^ 2 + F * L ^ 3 + G * L ^ 4) := by
    have hid :
        (L + H * M) *
            (C + D * (L + H * M) + E * (L + H * M) ^ 2 +
              F * (L + H * M) ^ 3 + G * (L + H * M) ^ 4) -
          4 * L * (C + D * L + E * L ^ 2 + F * L ^ 3 + G * L ^ 4) =
        4 * (L * EL) - (L + H * M) * EU := by
      calc
        (L + H * M) *
            (C + D * (L + H * M) + E * (L + H * M) ^ 2 +
              F * (L + H * M) ^ 3 + G * (L + H * M) ^ 4) -
          4 * L * (C + D * L + E * L ^ 2 + F * L ^ 3 + G * L ^ 4) =
            ((L + H * M) * QU - 4 * L * QL) +
              (4 * (L * EL) - (L + H * M) * EU) := by
                dsimp [EL, EU]
                ring
        _ = 4 * (L * EL) - (L + H * M) * EU := by rw [heq]; ring
    rw [hid]
    exact dvd_sub (dvd_mul_of_dvd_right hLEL 4) hUEU
  have hbaseT : H ^ 6 ∣ H ^ 2 * T := by
    have hEq :
        (L + H * M) *
            (C + D * (L + H * M) + E * (L + H * M) ^ 2 +
              F * (L + H * M) ^ 3 + G * (L + H * M) ^ 4) -
          4 * L * (C + D * L + E * L ^ 2 + F * L ^ 3 + G * L ^ 4) =
            H ^ 2 * T := by
      dsimp [T]
      rw [hL]
      have hres' : 3 * (H * X) - H * M = A * H ^ 2 := by
        simpa [hL] using hres
      calc
        (H * X + H * M) *
            (C + D * (H * X + H * M) + E * (H * X + H * M) ^ 2 +
              F * (H * X + H * M) ^ 3 + G * (H * X + H * M) ^ 4) -
          4 * (H * X) *
            (C + D * (H * X) + E * (H * X) ^ 2 +
              F * (H * X) ^ 3 + G * (H * X) ^ 4) =
            -C * (3 * (H * X) - H * M) +
              H ^ 2 * D * ((X + M) ^ 2 - 4 * X ^ 2) +
              H ^ 3 * E * ((X + M) ^ 3 - 4 * X ^ 3) +
              H ^ 4 * F * ((X + M) ^ 4 - 4 * X ^ 4) +
              H ^ 5 * G * ((X + M) ^ 5 - 4 * X ^ 5) := by ring
        _ = -C * (A * H ^ 2) +
              H ^ 2 * D * ((X + M) ^ 2 - 4 * X ^ 2) +
              H ^ 3 * E * ((X + M) ^ 3 - 4 * X ^ 3) +
              H ^ 4 * F * ((X + M) ^ 4 - 4 * X ^ 4) +
              H ^ 5 * G * ((X + M) ^ 5 - 4 * X ^ 5) := by rw [hres']
        _ = H ^ 2 * T := by dsimp [T]; ring
    rw [← hEq]
    exact hbase
  have hT : H ^ 4 ∣ T := by
    rcases hbaseT with ⟨q, hq⟩
    refine ⟨q, ?_⟩
    apply mul_left_cancel₀ (pow_ne_zero 2 hH)
    calc
      H ^ 2 * T = H ^ 6 * q := hq
      _ = H ^ 2 * (H ^ 4 * q) := by ring
  have hrEq : 3 * X - M = A * H := by
    apply mul_left_cancel₀ hH
    calc
      H * (3 * X - M) = 3 * L - H * M := by rw [hL]; ring
      _ = A * H ^ 2 := hres
      _ = H * (A * H) := by ring
  have htargetDiff : H ^ 4 ∣ 81 * T - target := by
    refine ⟨
      -9 * A ^ 3 * E + 72 * A ^ 2 * F * M ^ 2 + 420 * A * G * M ^ 4 +
        H * (200 * A ^ 2 * G * M ^ 3) +
        H ^ 2 * (-3 * A ^ 4 * F + 40 * A ^ 3 * G * M ^ 2) -
        H ^ 4 * A ^ 5 * G, ?_⟩
    dsimp [T, target]
    have hM : M = 3 * X - A * H := by linarith
    rw [hM]
    ring
  have hEightyOneT : H ^ 4 ∣ 81 * T :=
    dvd_mul_of_dvd_right hT 81
  have htarget := dvd_sub hEightyOneT htargetDiff
  simpa [target] using htarget

/-- Fifth-order local lift for a clean divisor `h` with residual `a*h^2`. -/
theorem fifth_order_local_lift
    {k n d i h m a : ℕ}
    (hi : i ∈ Finset.Icc 1 k)
    (hh : 0 < h)
    (hd : d = h * m)
    (hfactor : h ∣ n + i)
    (hres : 3 * ((n + i : ℕ) : ℤ) - (d : ℤ) =
      (a : ℤ) * (h : ℤ) ^ 2)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    (h : ℤ) ^ 4 ∣
      3 * (3 * (-3 * (3 * localSecondConstant k i * (a : ℤ) -
            4 * localSecondLinear k i * (m : ℤ) ^ 2) +
          20 * localThirdQuadratic k i * (h : ℤ) * (m : ℤ) ^ 3) +
        (h : ℤ) ^ 2 *
          (-9 * localSecondLinear k i * (a : ℤ) ^ 2 +
            36 * localThirdQuadratic k i * (a : ℤ) * (m : ℤ) ^ 2 +
            84 * localFourthCubic k i * (m : ℤ) ^ 4)) +
      20 * (h : ℤ) ^ 3 * (m : ℤ) ^ 3 *
        (12 * (a : ℤ) * localFourthCubic k i +
          17 * localFifthQuartic k i * (m : ℤ) ^ 2) := by
  rcases hfactor with ⟨x, hx⟩
  let H : ℤ := (h : ℤ)
  let L : ℤ := ((n + i : ℕ) : ℤ)
  let M : ℤ := (m : ℤ)
  let A : ℤ := (a : ℤ)
  let C : ℤ := localSecondConstant k i
  let D : ℤ := localSecondLinear k i
  let E : ℤ := localThirdQuadratic k i
  let F : ℤ := localFourthCubic k i
  let G : ℤ := localFifthQuartic k i
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
  have hHfiveLfive : H ^ 5 ∣ L ^ 5 := pow_dvd_pow_of_dvd hHL 5
  have hHfiveUfive : H ^ 5 ∣ (L + H * M) ^ 5 :=
    pow_dvd_pow_of_dvd hHU 5
  have hQLexp : L ^ 5 ∣
      QL - C - D * L - E * L ^ 2 - F * L ^ 3 - G * L ^ 4 := by
    have h := localOffsetCofactor_fifth_order k i L
    have hrel : localOffsetCofactor k i L = QL := by
      dsimp [L, QL]
      exact localOffsetCofactor_eq_localBlockCofactor
    simpa [hrel, C, D, E, F, G] using h
  have hQUexp : (L + H * M) ^ 5 ∣
      QU - C - D * (L + H * M) - E * (L + H * M) ^ 2 -
        F * (L + H * M) ^ 3 - G * (L + H * M) ^ 4 := by
    have h := localOffsetCofactor_fifth_order k i (L + H * M)
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
    simpa [hrel, C, D, E, F, G] using h
  have hQL' : H ^ 5 ∣
      QL - C - D * L - E * L ^ 2 - F * L ^ 3 - G * L ^ 4 :=
    dvd_trans hHfiveLfive hQLexp
  have hQU' : H ^ 5 ∣
      QU - C - D * (L + H * M) - E * (L + H * M) ^ 2 -
        F * (L + H * M) ^ 3 - G * (L + H * M) ^ 4 :=
    dvd_trans hHfiveUfive hQUexp
  simpa [H, M, A, C, D, E, F, G] using
    fifth_order_local_algebra hH hL hres' heqLocal hQL' hQU'

/-- New correction in the cyclic fifth obstruction. -/
def threeBucketFifthCorrection
    (E F G t g deltaLeft deltaRight : ℤ) : ℤ :=
  -540 * t * E * (deltaLeft + deltaRight) +
    2160 * t * F * deltaLeft * deltaRight +
    27540 * G * g ^ 2 * (deltaLeft * deltaRight) ^ 2

/-- Fifth cyclic obstruction at the `P` owner. -/
def threeBucketFifthObstruction
    (P Q R b c C D E F G a g deltaLeft deltaRight gap : ℤ) : ℤ :=
  3 * threeBucketFourthObstruction P b c C D E F a g
      deltaLeft deltaRight gap +
    P ^ 3 * g ^ 3 * Q * R *
      threeBucketFifthCorrection E F G (a * b * c) g
        deltaLeft deltaRight

private theorem fifth_composition_polynomial_dvd
    (P A a D E F G g M x y : ℤ) :
    let s := x + y
    let p := x * y
    let t := a * A
    let B := 9 * p - 3 * a * s * P ^ 2 + a ^ 2 * P ^ 4
    let d := P * M
    let J := -9 * D * t ^ 2 - 108 * D * t * g ^ 2 * s +
      324 * E * t * g ^ 2 * p + 6804 * F * g ^ 4 * p ^ 2
    let K5 := -540 * t * E * s + 2160 * t * F * p +
      27540 * G * g ^ 2 * p ^ 2
    P ^ 4 ∣
      3 * (3 * A * (12 * D + 20 * E * d) * g ^ 2 * (B - 9 * p) +
        P ^ 2 *
          ((-9 * D * t ^ 2 + 36 * E * t * g ^ 2 * B +
              84 * F * g ^ 4 * B ^ 2) - J)) +
      P ^ 3 * g ^ 2 * M *
        ((240 * t * F * B + 340 * G * g ^ 2 * B ^ 2) - K5) := by
  dsimp
  refine ⟨
    -4 * a * g ^ 2 *
      (-27 * A * D * a - 27 * A * E * P ^ 2 * a ^ 2 -
        45 * A * E * P * a * M + 81 * A * E * a * x +
        81 * A * E * a * y - 60 * A * F * P ^ 3 * a ^ 2 * M +
        180 * A * F * P * a * M * x + 180 * A * F * P * a * M * y -
        63 * F * P ^ 6 * a ^ 3 * g ^ 2 +
        378 * F * P ^ 4 * a ^ 2 * g ^ 2 * x +
        378 * F * P ^ 4 * a ^ 2 * g ^ 2 * y -
        567 * F * P ^ 2 * a * g ^ 2 * x ^ 2 -
        2268 * F * P ^ 2 * a * g ^ 2 * x * y -
        567 * F * P ^ 2 * a * g ^ 2 * y ^ 2 +
        3402 * F * g ^ 2 * x ^ 2 * y +
        3402 * F * g ^ 2 * x * y ^ 2 -
        85 * G * P ^ 7 * a ^ 3 * g ^ 2 * M +
        510 * G * P ^ 5 * a ^ 2 * g ^ 2 * M * x +
        510 * G * P ^ 5 * a ^ 2 * g ^ 2 * M * y -
        765 * G * P ^ 3 * a * g ^ 2 * M * x ^ 2 -
        3060 * G * P ^ 3 * a * g ^ 2 * M * x * y -
        765 * G * P ^ 3 * a * g ^ 2 * M * y ^ 2 +
        4590 * G * P * g ^ 2 * M * x ^ 2 * y +
        4590 * G * P * g ^ 2 * M * x * y ^ 2), ?_⟩
  ring

/-- Compose the fifth local lift with the two exact square-residual
differences.  This is the next cyclic obstruction after
`three_bucket_fourth_obstruction_dvd_cube`. -/
theorem three_bucket_fifth_obstruction_dvd_fourth
    {P Q R a b c g C D E F G deltaLeft deltaRight gap : ℤ}
    (hgap : gap = g * P * Q * R)
    (hfifth : P ^ 4 ∣
      3 * (3 * (-3 * (3 * C * a - 4 * D * (g * Q * R) ^ 2) +
            20 * E * P * (g * Q * R) ^ 3) +
          P ^ 2 * (-9 * D * a ^ 2 +
            36 * E * a * (g * Q * R) ^ 2 +
            84 * F * (g * Q * R) ^ 4)) +
        20 * P ^ 3 * (g * Q * R) ^ 3 *
          (12 * a * F + 17 * G * (g * Q * R) ^ 2))
    (hleft : a * P ^ 2 - b * Q ^ 2 = 3 * deltaLeft)
    (hright : a * P ^ 2 - c * R ^ 2 = 3 * deltaRight) :
    P ^ 4 ∣ threeBucketFifthObstruction P Q R b c C D E F G a g
      deltaLeft deltaRight gap := by
  let A : ℤ := b * c
  let B : ℤ := (b * Q ^ 2) * (c * R ^ 2)
  let M : ℤ := g * Q * R
  let p : ℤ := deltaLeft * deltaRight
  let s : ℤ := deltaLeft + deltaRight
  let t : ℤ := a * A
  let raw : ℤ :=
    3 * (3 * (-3 * (3 * C * a - 4 * D * M ^ 2) +
          20 * E * P * M ^ 3) +
        P ^ 2 * (-9 * D * a ^ 2 + 36 * E * a * M ^ 2 +
          84 * F * M ^ 4)) +
      20 * P ^ 3 * M ^ 3 * (12 * a * F + 17 * G * M ^ 2)
  let J : ℤ := threeBucketFourthCorrection D E F t g
    deltaLeft deltaRight
  let K5 : ℤ := threeBucketFifthCorrection E F G t g
    deltaLeft deltaRight
  let W5 : ℤ := threeBucketFifthObstruction P Q R b c C D E F G a g
    deltaLeft deltaRight gap
  have hB : B = 9 * p - 3 * a * s * P ^ 2 + a ^ 2 * P ^ 4 := by
    have hL : b * Q ^ 2 = a * P ^ 2 - 3 * deltaLeft := by linarith
    have hR : c * R ^ 2 = a * P ^ 2 - 3 * deltaRight := by linarith
    dsimp [B, p, s]
    rw [hL, hR]
    ring
  have hAM : A * M ^ 2 = g ^ 2 * B := by
    dsimp [A, M, B]
    ring
  have hgapM : gap = P * M := by
    dsimp [M]
    rw [hgap]
    ring
  have hbc : b * c = A := by rfl
  have habc : a * b * c = t := by
    dsimp [t, A]
    ring
  have hgqr : g ^ 3 * Q * R = g ^ 2 * M := by
    dsimp [M]
    ring
  have hAM' : (b * c) * M ^ 2 = g ^ 2 * B := by
    simpa [A] using hAM
  have hfifthTerm :
      P ^ 3 * g ^ 3 * Q * R *
          threeBucketFifthCorrection E F G (a * b * c) g
            deltaLeft deltaRight =
        P ^ 3 * g ^ 2 * M *
          threeBucketFifthCorrection E F G (a * b * c) g
            deltaLeft deltaRight := by
    dsimp [M]
    ring
  have hA2M2 : A ^ 2 * M ^ 2 = A * g ^ 2 * B := by
    calc
      A ^ 2 * M ^ 2 = A * (A * M ^ 2) := by ring
      _ = A * (g ^ 2 * B) := by rw [hAM]
      _ = A * g ^ 2 * B := by ring
  have hA2M3 : A ^ 2 * M ^ 3 = A * g ^ 2 * M * B := by
    calc
      A ^ 2 * M ^ 3 = A * M * (A * M ^ 2) := by ring
      _ = A * M * (g ^ 2 * B) := by rw [hAM]
      _ = A * g ^ 2 * M * B := by ring
  have hA2M4 : A ^ 2 * M ^ 4 = g ^ 4 * B ^ 2 := by
    calc
      A ^ 2 * M ^ 4 = (A * M ^ 2) ^ 2 := by ring
      _ = (g ^ 2 * B) ^ 2 := by rw [hAM]
      _ = g ^ 4 * B ^ 2 := by ring
  have hA2M5 : A ^ 2 * M ^ 5 = g ^ 4 * M * B ^ 2 := by
    calc
      A ^ 2 * M ^ 5 = M * (A * M ^ 2) ^ 2 := by ring
      _ = M * (g ^ 2 * B) ^ 2 := by rw [hAM]
      _ = g ^ 4 * M * B ^ 2 := by ring
  have hraw : P ^ 4 ∣ raw := by simpa [raw, M] using hfifth
  have hrawMul : P ^ 4 ∣ A ^ 2 * raw :=
    dvd_mul_of_dvd_right hraw (A ^ 2)
  have hdiffEq : A ^ 2 * raw - W5 =
      3 * (3 * A * (12 * D + 20 * E * gap) * g ^ 2 * (B - 9 * p) +
        P ^ 2 *
          ((-9 * D * t ^ 2 + 36 * E * t * g ^ 2 * B +
              84 * F * g ^ 4 * B ^ 2) - J)) +
      P ^ 3 * g ^ 2 * M *
        ((240 * t * F * B + 340 * G * g ^ 2 * B ^ 2) - K5) := by
    dsimp [raw, W5, threeBucketFifthObstruction,
      threeBucketFourthObstruction, threeBucketThirdObstruction,
      threeBucketSecondObstruction, threeBucketFourthCorrection,
      threeBucketFifthCorrection, J, K5, A, t, p, s]
    rw [hgapM]
    dsimp [M] at hAM' ⊢
    linear_combination
      4 * (27 * (b * c) * D + 45 * (b * c) * E * M * P +
        27 * (b * c) * E * P ^ 2 * a +
        63 * (b * c) * F * M ^ 2 * P ^ 2 +
        60 * (b * c) * F * M * P ^ 3 * a +
        85 * (b * c) * G * M ^ 3 * P ^ 3 +
        63 * B * F * P ^ 2 * g ^ 2 +
        85 * B * G * M * P ^ 3 * g ^ 2) * hAM'
  have hpoly := fifth_composition_polynomial_dvd
    P A a D E F G g M deltaLeft deltaRight
  have hdiff : P ^ 4 ∣ A ^ 2 * raw - W5 := by
    rw [hdiffEq, hB, hgapM]
    dsimp [A, t, p, s, J, K5, threeBucketFourthCorrection,
      threeBucketFifthCorrection] at hpoly ⊢
    convert hpoly using 1 <;> ring
  have htarget := dvd_sub hrawMul hdiff
  simpa [W5] using htarget

/-- Equation-facing fifth cyclic obstruction for one bucket of a supplied
three-bucket decomposition.  The two residual-difference hypotheses are
derived from the actual step-three residuals rather than postulated. -/
theorem target_three_bucket_fifth_obstruction_dvd_fourth
    {k n d i j l P Q R a b c g : ℕ}
    (hi : i ∈ Finset.Icc 1 k)
    (hPpos : 0 < P)
    (hdecomp : d = g * P * Q * R)
    (hPfactor : P ∣ n + i)
    (hPi : 3 * ((n + i : ℕ) : ℤ) - (d : ℤ) =
      (a : ℤ) * (P : ℤ) ^ 2)
    (hQj : 3 * ((n + j : ℕ) : ℤ) - (d : ℤ) =
      (b : ℤ) * (Q : ℤ) ^ 2)
    (hRl : 3 * ((n + l : ℕ) : ℤ) - (d : ℤ) =
      (c : ℤ) * (R : ℤ) ^ 2)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    ((P : ℤ) ^ 4) ∣
      threeBucketFifthObstruction (P : ℤ) (Q : ℤ) (R : ℤ)
        (b : ℤ) (c : ℤ)
        (localSecondConstant k i) (localSecondLinear k i)
        (localThirdQuadratic k i) (localFourthCubic k i)
        (localFifthQuartic k i) (a : ℤ) (g : ℤ)
        ((i : ℤ) - (j : ℤ)) ((i : ℤ) - (l : ℤ)) (d : ℤ) := by
  have hdP : d = P * (g * Q * R) := by rw [hdecomp]; ring
  have hlocal := fifth_order_local_lift
    (k := k) (n := n) (d := d) (i := i)
    (h := P) (m := g * Q * R) (a := a)
    hi hPpos hdP hPfactor hPi heq
  have hgapInt : (d : ℤ) = (g : ℤ) * (P : ℤ) * (Q : ℤ) * (R : ℤ) := by
    exact_mod_cast hdecomp
  have hleft :
      (a : ℤ) * (P : ℤ) ^ 2 - (b : ℤ) * (Q : ℤ) ^ 2 =
        3 * ((i : ℤ) - (j : ℤ)) := by
    rw [← hPi, ← hQj]
    push_cast
    ring
  have hright :
      (a : ℤ) * (P : ℤ) ^ 2 - (c : ℤ) * (R : ℤ) ^ 2 =
        3 * ((i : ℤ) - (l : ℤ)) := by
    rw [← hPi, ← hRl]
    push_cast
    ring
  apply three_bucket_fifth_obstruction_dvd_fourth hgapInt
  · simpa using hlocal
  · exact hleft
  · exact hright

/-- Cancel `P^3` from a `P^4` divisibility. -/
theorem cube_factor_cancel_from_fourth_dvd
    {P W : ℤ} (hP : P ≠ 0) (hdiv : P ^ 4 ∣ P ^ 3 * W) :
    P ∣ W := by
  rcases hdiv with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  apply mul_left_cancel₀ (pow_ne_zero 3 hP)
  calc
    P ^ 3 * W = P ^ 4 * q := hq
    _ = P ^ 3 * (P * q) := by ring

/-- Once the fourth obstruction is named as `P^3*y`, fifth order gives one
ordinary congruence on the fourth quotient. -/
theorem three_bucket_fifth_to_fourth_quotient
    {P W L y : ℤ}
    (hP : P ≠ 0)
    (hW : W = P ^ 3 * y)
    (hfifth : P ^ 4 ∣ 3 * W + P ^ 3 * L) :
    P ∣ 3 * y + L := by
  have hraw : P ^ 4 ∣ P ^ 3 * (3 * y + L) := by
    convert hfifth using 1 <;> rw [hW] <;> ring
  exact cube_factor_cancel_from_fourth_dvd hP hraw

/-- Eliminate the fourth quotient and lift the former modulo-`P` third
quotient congruence to a congruence modulo `P^2`. -/
theorem three_bucket_fifth_to_third_quotient_sq
    {P b c T J L z y : ℤ}
    (hP : P ≠ 0)
    (hT : T = P ^ 2 * z)
    (hW : 3 * b * c * T + P ^ 2 * J = P ^ 3 * y)
    (hfifth : P ^ 4 ∣
      3 * (3 * b * c * T + P ^ 2 * J) + P ^ 3 * L) :
    P ^ 2 ∣ 9 * b * c * z + 3 * J + P * L := by
  have hquot : P * y = 3 * b * c * z + J := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hP)
    calc
      P ^ 2 * (P * y) = P ^ 3 * y := by ring
      _ = 3 * b * c * T + P ^ 2 * J := hW.symm
      _ = P ^ 2 * (3 * b * c * z + J) := by rw [hT]; ring
  have hy : P ∣ 3 * y + L := by
    apply three_bucket_fifth_to_fourth_quotient hP hW
    exact hfifth
  rcases hy with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  calc
    9 * b * c * z + 3 * J + P * L =
        3 * (P * y) + P * L := by rw [hquot]; ring
    _ = P * (3 * y + L) := by ring
    _ = P * (P * q) := by rw [hq]
    _ = P ^ 2 * q := by ring

/-- Direct squared congruence for the named third quotient, using the banked
fourth obstruction and the new fifth cyclic obstruction. -/
theorem three_bucket_fifth_obstruction_to_third_quotient_sq
    {P Q R b c C D E F G a g deltaLeft deltaRight gap z : ℤ}
    (hP : P ≠ 0)
    (hthird :
      threeBucketThirdObstruction C D E a b c g
          deltaLeft deltaRight gap = P ^ 2 * z)
    (hfourth : P ^ 3 ∣
      threeBucketFourthObstruction P b c C D E F a g
        deltaLeft deltaRight gap)
    (hfifth : P ^ 4 ∣
      threeBucketFifthObstruction P Q R b c C D E F G a g
        deltaLeft deltaRight gap) :
    P ^ 2 ∣
      9 * b * c * z +
        3 * threeBucketFourthCorrection D E F (a * b * c) g
          deltaLeft deltaRight +
        P * (g ^ 3 * Q * R *
          threeBucketFifthCorrection E F G (a * b * c) g
            deltaLeft deltaRight) := by
  rcases hfourth with ⟨y, hy⟩
  apply three_bucket_fifth_to_third_quotient_sq
      (P := P) (b := b) (c := c)
      (T := threeBucketThirdObstruction C D E a b c g
        deltaLeft deltaRight gap)
      (J := threeBucketFourthCorrection D E F (a * b * c) g
        deltaLeft deltaRight)
      (L := g ^ 3 * Q * R *
        threeBucketFifthCorrection E F G (a * b * c) g
          deltaLeft deltaRight)
      (z := z) (y := y) hP hthird
  · simpa [threeBucketFourthObstruction] using hy
  · convert hfifth using 1 <;>
      simp [threeBucketFifthObstruction,
        threeBucketFourthObstruction] <;> ring

/-- Fixed coefficient after eliminating the cofactor product from the
squared fifth-to-third quotient congruence.  Unlike the fourth-order fixed
coefficient, this one is generically quadratic in the gap. -/
def threeBucketReducedFifthCoefficient
    (C D E F G gap deltaLeft deltaRight : ℤ) : ℤ :=
  let p := deltaLeft * deltaRight;
  let s := deltaLeft + deltaRight;
  8748 * p *
    (189 * C ^ 2 * F * p + 255 * C ^ 2 * G * gap * p -
      36 * C * D ^ 2 * s - 120 * C * D * E * gap * s +
      108 * C * D * E * p + 240 * C * D * F * gap * p -
      100 * C * E ^ 2 * gap ^ 2 * s +
      180 * C * E ^ 2 * gap * p +
      400 * C * E * F * gap ^ 2 * p - 36 * D ^ 3 * p -
      120 * D ^ 2 * E * gap * p -
      100 * D * E ^ 2 * gap ^ 2 * p)

/-- Coefficient of the term linear in the gap after the reduced fifth
coefficient is split by gap degree.  This is an exact signed polynomial; it
does not include the fourth-order constant term. -/
def threeBucketReducedFifthLinearCoefficient
    (C D E F G deltaLeft deltaRight : ℤ) : ℤ :=
  let p := deltaLeft * deltaRight;
  let s := deltaLeft + deltaRight;
  8748 * p *
    (255 * C ^ 2 * G * p - 120 * C * D * E * s +
      240 * C * D * F * p + 180 * C * E ^ 2 * p -
      120 * D ^ 2 * E * p)

/-- Coefficient of the term quadratic in the gap after the reduced fifth
coefficient is split by gap degree. -/
def threeBucketReducedFifthQuadraticCoefficient
    (C D E F deltaLeft deltaRight : ℤ) : ℤ :=
  let p := deltaLeft * deltaRight;
  let s := deltaLeft + deltaRight;
  8748 * p *
    (-100 * C * E ^ 2 * s + 400 * C * E * F * p -
      100 * D * E ^ 2 * p)

/-- Exact gap-degree decomposition of the reduced fifth coefficient.  Its
constant term is precisely twenty-seven times the reduced fourth
coefficient, so eliminating the fourth numerator leaves a new quotient
congruence rather than a fixed component bound. -/
theorem three_bucket_reduced_fifth_coefficient_decomposition
    (C D E F G gap deltaLeft deltaRight : ℤ) :
    threeBucketReducedFifthCoefficient C D E F G gap
        deltaLeft deltaRight =
      27 * threeBucketReducedFourthCoefficient C D E F
        deltaLeft deltaRight +
      gap * threeBucketReducedFifthLinearCoefficient C D E F G
        deltaLeft deltaRight +
      gap ^ 2 * threeBucketReducedFifthQuadraticCoefficient C D E F
        deltaLeft deltaRight := by
  simp [threeBucketReducedFifthCoefficient,
    threeBucketReducedFourthCoefficient,
    threeBucketReducedFifthLinearCoefficient,
    threeBucketReducedFifthQuadraticCoefficient]
  ring

/-- The load-bearing failed-resultant certificate: at zero gap, fifth order
reproduces exactly twenty-seven times the fourth-order fixed coefficient. -/
theorem three_bucket_reduced_fifth_coefficient_at_zero
    (C D E F G deltaLeft deltaRight : ℤ) :
    threeBucketReducedFifthCoefficient C D E F G 0
        deltaLeft deltaRight =
      27 * threeBucketReducedFourthCoefficient C D E F
        deltaLeft deltaRight := by
  rw [three_bucket_reduced_fifth_coefficient_decomposition]
  ring

def threeBucketReducedFifthMultiplier
    (C D E F t g gap deltaLeft deltaRight : ℤ) : ℤ :=
  let p := deltaLeft * deltaRight;
  let s := deltaLeft + deltaRight;
  -243 *
    (-12 * C * D * g ^ 2 * s - C * D * t -
      20 * C * E * gap * g ^ 2 * s + 36 * C * E * g ^ 2 * p +
      80 * C * F * gap * g ^ 2 * p - 12 * D ^ 2 * g ^ 2 * p -
      20 * D * E * gap * g ^ 2 * p)

/-- Exact reduction identity for the fifth correction. -/
theorem three_bucket_reduced_fifth_identity
    (C D E F G t g gap deltaLeft deltaRight : ℤ) :
    81 * C ^ 2 *
        (3 * threeBucketFourthCorrection D E F t g
            deltaLeft deltaRight +
          g ^ 2 * gap *
            threeBucketFifthCorrection E F G t g
              deltaLeft deltaRight) =
      threeBucketReducedFifthMultiplier C D E F t g gap
          deltaLeft deltaRight *
        (-9 * C * t + 108 * D * g ^ 2 * deltaLeft * deltaRight +
          180 * E * g ^ 2 * deltaLeft * deltaRight * gap) +
      threeBucketReducedFifthCoefficient C D E F G gap
          deltaLeft deltaRight * g ^ 4 := by
  simp [threeBucketFourthCorrection, threeBucketFifthCorrection,
    threeBucketReducedFifthMultiplier,
    threeBucketReducedFifthCoefficient]
  ring

/-- Fixed-coefficient consequence of the squared fifth quotient congruence.
The displayed gap-quadratic coefficient is the exact remaining term. -/
theorem three_bucket_reduced_fifth_quotient_sq_dvd
    {P C D E F G t g gap b c z deltaLeft deltaRight : ℤ}
    (hthird : P ^ 2 ∣
      -9 * C * t + 108 * D * g ^ 2 * deltaLeft * deltaRight +
        180 * E * g ^ 2 * deltaLeft * deltaRight * gap)
    (hfifthQuotient : P ^ 2 ∣
      9 * b * c * z +
        3 * threeBucketFourthCorrection D E F t g
          deltaLeft deltaRight +
        g ^ 2 * gap *
          threeBucketFifthCorrection E F G t g
            deltaLeft deltaRight) :
    P ^ 2 ∣
      729 * C ^ 2 * b * c * z +
        threeBucketReducedFifthCoefficient C D E F G gap
          deltaLeft deltaRight * g ^ 4 := by
  have hq := dvd_mul_of_dvd_right hfifthQuotient (81 * C ^ 2)
  have ht := dvd_mul_of_dvd_right hthird
    (threeBucketReducedFifthMultiplier C D E F t g gap
      deltaLeft deltaRight)
  have hdiff := dvd_sub hq ht
  convert hdiff using 1 <;>
    simp [threeBucketReducedFifthMultiplier,
      threeBucketReducedFifthCoefficient,
      threeBucketFourthCorrection, threeBucketFifthCorrection] <;> ring

/-- Normalize the reduced fifth square divisibility by a named reduced
fourth quotient.  When `gap = P*M`, the quadratic gap term disappears after
one cancellation, while the linear term survives.  The conclusion controls
the new quotient `q`; it is not a component bound. -/
theorem three_bucket_reduced_fifth_normalized_quotient_dvd
    {P C D E F G g gap b c z q M deltaLeft deltaRight : ℤ}
    (hP : P ≠ 0)
    (hgap : gap = P * M)
    (hfourth :
      27 * C ^ 2 * b * c * z +
          threeBucketReducedFourthCoefficient C D E F
            deltaLeft deltaRight * g ^ 4 =
        P * q)
    (hfifth : P ^ 2 ∣
      729 * C ^ 2 * b * c * z +
        threeBucketReducedFifthCoefficient C D E F G gap
          deltaLeft deltaRight * g ^ 4) :
    P ∣ 27 * q + M *
      threeBucketReducedFifthLinearCoefficient C D E F G
        deltaLeft deltaRight * g ^ 4 := by
  let R1 : ℤ := threeBucketReducedFifthLinearCoefficient C D E F G
    deltaLeft deltaRight
  let R2 : ℤ := threeBucketReducedFifthQuadraticCoefficient C D E F
    deltaLeft deltaRight
  have hrewrite :
      729 * C ^ 2 * b * c * z +
          threeBucketReducedFifthCoefficient C D E F G gap
            deltaLeft deltaRight * g ^ 4 =
        P * (27 * q + M * R1 * g ^ 4 +
          P * M ^ 2 * R2 * g ^ 4) := by
    rw [three_bucket_reduced_fifth_coefficient_decomposition, hgap]
    dsimp [R1, R2]
    linear_combination 27 * hfourth
  have hwhole : P ^ 2 ∣
      P * (27 * q + M * R1 * g ^ 4 +
        P * M ^ 2 * R2 * g ^ 4) := by
    rw [← hrewrite]
    exact hfifth
  have hcancel : P ∣
      27 * q + M * R1 * g ^ 4 + P * M ^ 2 * R2 * g ^ 4 := by
    rcases hwhole with ⟨w, hw⟩
    refine ⟨w, ?_⟩
    apply mul_left_cancel₀ hP
    calc
      P * (27 * q + M * R1 * g ^ 4 + P * M ^ 2 * R2 * g ^ 4) =
          P ^ 2 * w := hw
      _ = P * (P * w) := by ring
  have hquadratic : P ∣ P * M ^ 2 * R2 * g ^ 4 := by
    refine ⟨M ^ 2 * R2 * g ^ 4, ?_⟩
    ring
  have hlinear := dvd_sub hcancel hquadratic
  simpa [R1] using hlinear

/-- Converse reconstruction of the reduced fifth square divisibility from
the normalized quotient congruence and the exact fourth quotient identity. -/
theorem three_bucket_reduced_fifth_sq_dvd_of_normalized_quotient
    {P C D E F G g gap b c z q M deltaLeft deltaRight : ℤ}
    (hgap : gap = P * M)
    (hfourth :
      27 * C ^ 2 * b * c * z +
          threeBucketReducedFourthCoefficient C D E F
            deltaLeft deltaRight * g ^ 4 =
        P * q)
    (hnormalized : P ∣ 27 * q + M *
      threeBucketReducedFifthLinearCoefficient C D E F G
        deltaLeft deltaRight * g ^ 4) :
    P ^ 2 ∣
      729 * C ^ 2 * b * c * z +
        threeBucketReducedFifthCoefficient C D E F G gap
          deltaLeft deltaRight * g ^ 4 := by
  let R1 : ℤ := threeBucketReducedFifthLinearCoefficient C D E F G
    deltaLeft deltaRight
  let R2 : ℤ := threeBucketReducedFifthQuadraticCoefficient C D E F
    deltaLeft deltaRight
  rcases hnormalized with ⟨w, hw⟩
  refine ⟨w + M ^ 2 * R2 * g ^ 4, ?_⟩
  rw [three_bucket_reduced_fifth_coefficient_decomposition, hgap]
  dsimp [R1, R2] at hw ⊢
  linear_combination 27 * hfourth + P * hw

/-- Exact equivalence between the reduced fifth square divisibility and its
normalized fourth-quotient lift when the component is nonzero. -/
theorem three_bucket_reduced_fifth_normalized_quotient_iff
    {P C D E F G g gap b c z q M deltaLeft deltaRight : ℤ}
    (hP : P ≠ 0)
    (hgap : gap = P * M)
    (hfourth :
      27 * C ^ 2 * b * c * z +
          threeBucketReducedFourthCoefficient C D E F
            deltaLeft deltaRight * g ^ 4 =
        P * q) :
    P ^ 2 ∣
        729 * C ^ 2 * b * c * z +
          threeBucketReducedFifthCoefficient C D E F G gap
            deltaLeft deltaRight * g ^ 4 ↔
      P ∣ 27 * q + M *
        threeBucketReducedFifthLinearCoefficient C D E F G
          deltaLeft deltaRight * g ^ 4 := by
  constructor
  · exact three_bucket_reduced_fifth_normalized_quotient_dvd
      hP hgap hfourth
  · exact three_bucket_reduced_fifth_sq_dvd_of_normalized_quotient
      hgap hfourth

#print axioms localOffsetCofactor_fifth_order
#print axioms fifth_order_local_algebra
#print axioms fifth_order_local_lift
#print axioms three_bucket_fifth_obstruction_dvd_fourth
#print axioms target_three_bucket_fifth_obstruction_dvd_fourth
#print axioms cube_factor_cancel_from_fourth_dvd
#print axioms three_bucket_fifth_to_fourth_quotient
#print axioms three_bucket_fifth_to_third_quotient_sq
#print axioms three_bucket_fifth_obstruction_to_third_quotient_sq
#print axioms three_bucket_reduced_fifth_identity
#print axioms three_bucket_reduced_fifth_quotient_sq_dvd
#print axioms three_bucket_reduced_fifth_coefficient_decomposition
#print axioms three_bucket_reduced_fifth_coefficient_at_zero
#print axioms three_bucket_reduced_fifth_normalized_quotient_dvd
#print axioms three_bucket_reduced_fifth_sq_dvd_of_normalized_quotient
#print axioms three_bucket_reduced_fifth_normalized_quotient_iff

end Erdos686Variant
end Erdos686
