/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.Core.PadicLift

/-!
# Erdős 686: global quadratic residual lift

For `X_i = 3(n+i)-d`, multiplying the exact block equation by `3^k`
rewrites it as

`prod_i (X_i+4d) = 4 prod_i (X_i+d)`.

The constant terms differ by a factor three, the linear terms cancel, and
every higher coefficient `4^r-4` is divisible by three.  Consequently the
whole gap square divides the product of the residuals, without a prime-base
or localization hypothesis.
-/

namespace Erdos686
namespace Erdos686Variant

open Polynomial

/-- The polynomial identity behind the global square lift. -/
lemma three_mul_sq_dvd_eval_four_sub_four_eval_add_three_eval_zero
    (P : Polynomial ℤ) (d : ℤ) :
    3 * d ^ 2 ∣ P.eval (4 * d) - 4 * P.eval d + 3 * P.eval 0 := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      have hadd := dvd_add hP hQ
      convert hadd using 1 <;> simp [Polynomial.eval_add] <;> ring
  | monomial m a =>
      by_cases hm0 : m = 0
      · subst m
        have hz : a - 4 * a + 3 * a = 0 := by ring
        simpa [hz]
      by_cases hm1 : m = 1
      · subst m
        have hz : a * (4 * d) - 4 * (a * d) = 0 := by ring
        simpa [hz]
      have hm2 : 2 ≤ m := by omega
      have hmod : (4 : ℤ) ^ m ≡ 4 [ZMOD 3] := by
        have h4 : (4 : ℤ) ≡ 1 [ZMOD 3] := by norm_num
        have hpow := h4.pow m
        calc
          (4 : ℤ) ^ m ≡ 1 ^ m [ZMOD 3] := hpow
          _ = 1 := by simp
          _ ≡ 4 [ZMOD 3] := h4.symm
      have hthree : (3 : ℤ) ∣ (4 : ℤ) ^ m - 4 := by
        exact Int.modEq_iff_dvd.mp hmod.symm
      have hdsq : d ^ 2 ∣ d ^ m := pow_dvd_pow d hm2
      have hprod : 3 * d ^ 2 ∣ ((4 : ℤ) ^ m - 4) * d ^ m :=
        mul_dvd_mul hthree hdsq
      have hprodA : 3 * d ^ 2 ∣ a * (((4 : ℤ) ^ m - 4) * d ^ m) :=
        dvd_mul_of_dvd_right hprod a
      convert hprodA using 1 <;>
        simp [Polynomial.eval_monomial, hm0] <;> ring

/-- If a polynomial takes values in the ratio four at `d` and `4d`, its
constant term is divisible by `d^2`. -/
theorem sq_dvd_eval_zero_of_eval_four_eq_four_eval
    {P : Polynomial ℤ} {d : ℤ}
    (heq : P.eval (4 * d) = 4 * P.eval d) :
    d ^ 2 ∣ P.eval 0 := by
  have h := three_mul_sq_dvd_eval_four_sub_four_eval_add_three_eval_zero P d
  have hthree : 3 * d ^ 2 ∣ 3 * P.eval 0 := by
    simpa [heq] using h
  exact (mul_dvd_mul_iff_left (by norm_num : (3 : ℤ) ≠ 0)).mp (by
    simpa [mul_assoc] using hthree)

/-- Signed residual at the factor indexed by `i`. -/
def globalLocalResidual (n d i : ℕ) : ℤ :=
  3 * ((n + i : ℕ) : ℤ) - (d : ℤ)

/-- The residual product as a polynomial evaluation. -/
noncomputable def globalResidualPolynomial (k n d : ℕ) : Polynomial ℤ :=
  ∏ i ∈ Finset.Icc 1 k, (Polynomial.X + Polynomial.C (globalLocalResidual n d i))

lemma globalResidualPolynomial_eval (k n d : ℕ) (z : ℤ) :
    (globalResidualPolynomial k n d).eval z =
      ∏ i ∈ Finset.Icc 1 k, (z + globalLocalResidual n d i) := by
  simp [globalResidualPolynomial, globalLocalResidual, Polynomial.eval_prod]

lemma globalResidualPolynomial_eval_gap (k n d : ℕ) :
    (globalResidualPolynomial k n d).eval (d : ℤ) =
      (3 : ℤ) ^ k * (blockProduct k n : ℤ) := by
  rw [globalResidualPolynomial_eval]
  unfold blockProduct
  have hcard : (Finset.Icc 1 k).card = k := by simp [Nat.card_Icc]
  calc
    (∏ i ∈ Finset.Icc 1 k, ((d : ℤ) + globalLocalResidual n d i)) =
        ∏ i ∈ Finset.Icc 1 k, (3 * ((n + i : ℕ) : ℤ)) := by
          apply Finset.prod_congr rfl
          intro i _hi
          simp [globalLocalResidual]
    _ = (∏ _i ∈ Finset.Icc 1 k, (3 : ℤ)) *
          ∏ i ∈ Finset.Icc 1 k, ((n + i : ℕ) : ℤ) := by
          rw [← Finset.prod_mul_distrib]
    _ = (3 : ℤ) ^ k * (blockProduct k n : ℤ) := by
          simp [Finset.prod_const, hcard, blockProduct]

lemma globalResidualPolynomial_eval_four_gap (k n d : ℕ) :
    (globalResidualPolynomial k n d).eval (4 * (d : ℤ)) =
      (3 : ℤ) ^ k * (blockProduct k (n + d) : ℤ) := by
  rw [globalResidualPolynomial_eval]
  unfold blockProduct
  have hcard : (Finset.Icc 1 k).card = k := by simp [Nat.card_Icc]
  calc
    (∏ i ∈ Finset.Icc 1 k,
        (4 * (d : ℤ) + globalLocalResidual n d i)) =
        ∏ i ∈ Finset.Icc 1 k, (3 * (((n + d) + i : ℕ) : ℤ)) := by
          apply Finset.prod_congr rfl
          intro i _hi
          simp [globalLocalResidual]
          ring
    _ = (∏ _i ∈ Finset.Icc 1 k, (3 : ℤ)) *
          ∏ i ∈ Finset.Icc 1 k, ((((n + d) + i : ℕ) : ℤ)) := by
          rw [← Finset.prod_mul_distrib]
    _ = (3 : ℤ) ^ k * (blockProduct k (n + d) : ℤ) := by
          simp [Finset.prod_const, hcard, blockProduct]

/-- **Global square lift.**  Every exact multiplier-four block equation
forces the square of the whole gap to divide the product of the signed local
residuals `3(n+i)-d`. -/
theorem gap_sq_dvd_globalLocalResidual_product
    {k n d : ℕ}
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    ((d : ℤ) ^ 2) ∣
      ∏ i ∈ Finset.Icc 1 k, globalLocalResidual n d i := by
  let P := globalResidualPolynomial k n d
  have heval : P.eval (4 * (d : ℤ)) = 4 * P.eval (d : ℤ) := by
    dsimp [P]
    rw [globalResidualPolynomial_eval_four_gap,
      globalResidualPolynomial_eval_gap, heq]
    push_cast
    ring
  have hsquare := sq_dvd_eval_zero_of_eval_four_eq_four_eval heval
  simpa [P, globalResidualPolynomial_eval] using hsquare

/-- Natural-number residual in the live positive range. -/
def globalLocalResidualNat (n d i : ℕ) : ℕ :=
  3 * (n + i) - d

lemma globalLocalResidualNat_cast
    {n d i : ℕ} (hpos : d ≤ 3 * (n + i)) :
    ((globalLocalResidualNat n d i : ℕ) : ℤ) = globalLocalResidual n d i := by
  unfold globalLocalResidualNat globalLocalResidual
  rw [Int.ofNat_sub hpos]
  push_cast
  ring

/-- Natural-number form of the global square lift in the separated
`k>=5`, `d>=k` range. -/
theorem gap_sq_dvd_globalLocalResidualNat_product
    {k n d : ℕ} (hk5 : 5 ≤ k) (hkd : k ≤ d)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    d ^ 2 ∣ ∏ i ∈ Finset.Icc 1 k, globalLocalResidualNat n d i := by
  have hgap := twice_gap_lt_n_of_four_solution hk5 hkd heq
  have hpositive : ∀ i ∈ Finset.Icc 1 k, d ≤ 3 * (n + i) := by
    intro i hi
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    omega
  have hsigned := gap_sq_dvd_globalLocalResidual_product heq
  have hcast :
      (((∏ i ∈ Finset.Icc 1 k, globalLocalResidualNat n d i : ℕ) : ℤ)) =
        ∏ i ∈ Finset.Icc 1 k, globalLocalResidual n d i := by
    rw [Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro i hi
    exact globalLocalResidualNat_cast (hpositive i hi)
  have hcastDvd : (((d ^ 2 : ℕ) : ℤ)) ∣
      (((∏ i ∈ Finset.Icc 1 k, globalLocalResidualNat n d i : ℕ) : ℤ)) := by
    rw [hcast]
    simpa using hsigned
  exact Int.natCast_dvd_natCast.mp hcastDvd

end Erdos686Variant
end Erdos686
