/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686LowDegreeOsculation
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Erdős 686: osculation Taylor and global square divisibility

This module proves the exact first-order Taylor congruence for the low-degree
bivariate osculation polynomials.  At an owner node `(j,rho)`, the displacement
to `(-n,-d)` is `(-(n+j), -(d+rho))`; this sign convention is kept explicit in
the local owner theorem.
-/

namespace Erdos686
namespace Erdos686Variant

open scoped BigOperators

/-- Powers at arguments differing by a multiple of `P` are congruent modulo
`P`. -/
theorem power_difference_dvd
    (P x h : ℤ) (a : ℕ) (hh : P ∣ h) :
    P ∣ (x + h) ^ a - x ^ a := by
  apply Int.modEq_iff_dvd.mp
  apply Int.ModEq.pow a
  apply Int.modEq_iff_dvd.mpr
  simpa using hh

/-- Exact first-order Taylor remainder for one univariate monomial. -/
theorem power_first_order_remainder_dvd
    (P x h : ℤ) (a : ℕ) (hh : P ∣ h) :
    P ^ 2 ∣ (x + h) ^ a - x ^ a - (a : ℤ) * x ^ (a - 1) * h := by
  induction a with
  | zero => simp
  | succ a ih =>
      cases a with
      | zero => simp
      | succ a =>
          rcases ih with ⟨q, hq⟩
          rcases hh with ⟨t, rfl⟩
          refine ⟨q * (x + P * t) + (a + 1 : ℤ) * x ^ a * t ^ 2, ?_⟩
          calc
            (x + P * t) ^ (a + 1 + 1) - x ^ (a + 1 + 1) -
                (↑(a + 1 + 1) : ℤ) * x ^ (a + 1 + 1 - 1) * (P * t) =
              ((x + P * t) ^ (a + 1) - x ^ (a + 1) -
                  (↑(a + 1) : ℤ) * x ^ (a + 1 - 1) * (P * t)) *
                (x + P * t) +
                  (a + 1 : ℤ) * x ^ a * (P * t) ^ 2 := by
                    simp only [Nat.cast_add, Nat.cast_one,
                      Nat.add_sub_cancel, pow_succ]
                    ring
            _ = P ^ 2 *
                (q * (x + P * t) + (a + 1 : ℤ) * x ^ a * t ^ 2) := by
                  rw [hq]
                  ring

/-- Exact first-order bivariate Taylor remainder for one monomial. -/
theorem monomial_first_order_remainder_dvd
    (P x y hx hy : ℤ) (a c : ℕ)
    (hhx : P ∣ hx) (hhy : P ∣ hy) :
    P ^ 2 ∣
      (x + hx) ^ a * (y + hy) ^ c - x ^ a * y ^ c -
        hx * ((a : ℤ) * x ^ (a - 1) * y ^ c) -
        hy * ((c : ℤ) * x ^ a * y ^ (c - 1)) := by
  rcases power_first_order_remainder_dvd P x hx a hhx with ⟨qx, hqx⟩
  rcases power_first_order_remainder_dvd P y hy c hhy with ⟨qy, hqy⟩
  rcases power_difference_dvd P y hy c hhy with ⟨qdy, hqdy⟩
  rcases hhx with ⟨tx, rfl⟩
  refine ⟨qx * (y + hy) ^ c +
      tx * ((a : ℤ) * x ^ (a - 1)) * qdy + x ^ a * qy, ?_⟩
  calc
    (x + P * tx) ^ a * (y + hy) ^ c - x ^ a * y ^ c -
          P * tx * ((a : ℤ) * x ^ (a - 1) * y ^ c) -
          hy * ((c : ℤ) * x ^ a * y ^ (c - 1)) =
      ((x + P * tx) ^ a - x ^ a -
          (a : ℤ) * x ^ (a - 1) * (P * tx)) * (y + hy) ^ c +
        P * tx * ((a : ℤ) * x ^ (a - 1)) *
          ((y + hy) ^ c - y ^ c) +
        x ^ a * ((y + hy) ^ c - y ^ c -
          (c : ℤ) * y ^ (c - 1) * hy) := by ring
    _ = P ^ 2 * (qx * (y + hy) ^ c +
          tx * ((a : ℤ) * x ^ (a - 1)) * qdy + x ^ a * qy) := by
      rw [hqx, hqy, hqdy]
      ring

/-- The first-order Taylor remainder for one osculation-basis monomial is
divisible by `P^2`. -/
theorem osculation_monomial_first_order_remainder_dvd
    {r : ℕ} (u : OsculationMonomial r)
    (P x y hx hy : ℤ) (hhx : P ∣ hx) (hhy : P ∣ hy) :
    P ^ 2 ∣
      osculationMonomialValue u (x + hx) (y + hy) -
        osculationMonomialValue u x y -
        hx * osculationMonomialDX u x y -
        hy * osculationMonomialDY u x y := by
  simpa [osculationMonomialValue, osculationMonomialDX,
    osculationMonomialDY, mul_assoc, mul_left_comm, mul_comm] using
    monomial_first_order_remainder_dvd P x y hx hy
      u.xExponent u.yExponent hhx hhy

/-- Exact first-order bivariate Taylor congruence for every coefficient vector
in the low-degree osculation basis. -/
theorem osculation_first_order_remainder_dvd
    {r : ℕ} (coeff : OsculationMonomial r → ℤ)
    (P x y hx hy : ℤ) (hhx : P ∣ hx) (hhy : P ∣ hy) :
    P ^ 2 ∣
      osculationEvaluate coeff (x + hx) (y + hy) -
        osculationEvaluate coeff x y -
        hx * osculationEvaluateDX coeff x y -
        hy * osculationEvaluateDY coeff x y := by
  rw [show osculationEvaluate coeff (x + hx) (y + hy) -
          osculationEvaluate coeff x y -
          hx * osculationEvaluateDX coeff x y -
          hy * osculationEvaluateDY coeff x y =
      ∑ u, coeff u *
        (osculationMonomialValue u (x + hx) (y + hy) -
          osculationMonomialValue u x y -
          hx * osculationMonomialDX u x y -
          hy * osculationMonomialDY u x y) by
    simp only [osculationEvaluate, osculationEvaluateDX,
      osculationEvaluateDY, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro u hu
    ring]
  apply Finset.dvd_sum
  intro u hu
  exact dvd_mul_of_dvd_right
    (osculation_monomial_first_order_remainder_dvd u P x y hx hy hhx hhy)
    (coeff u)

/-- Local owner-square theorem.  The exact displacement from the interpolation
node `(j,rho)` to the target `(-n,-d)` is `(-n-j,-d-rho)`.  The normalized
owner-square congruence and the directional derivative condition kill its
linear Taylor term modulo `P^2`; coprimality with `b` justifies cancellation
modulo the composite modulus `P^2`. -/
theorem osculation_owner_square_dvd
    {r : ℕ} (coeff : OsculationMonomial r → ℤ)
    (P b A n d j rho : ℤ)
    (hvalue : osculationEvaluate coeff j rho = 0)
    (hdirection : b * osculationEvaluateDX coeff j rho +
      A * osculationEvaluateDY coeff j rho = 0)
    (hn : P ∣ n + j) (hd : P ∣ d + rho)
    (hsquare : P ^ 2 ∣ b * (d + rho) - A * (n + j))
    (hcop : IsCoprime P b) :
    P ^ 2 ∣ osculationEvaluate coeff (-n) (-d) := by
  let Fx := osculationEvaluateDX coeff j rho
  let Fy := osculationEvaluateDY coeff j rho
  let linear := (n + j) * Fx + (d + rho) * Fy
  have hlinear_mul : P ^ 2 ∣ linear * b := by
    rcases hsquare with ⟨q, hq⟩
    refine ⟨q * Fy, ?_⟩
    dsimp [linear, Fx, Fy]
    calc
      ((n + j) * osculationEvaluateDX coeff j rho +
          (d + rho) * osculationEvaluateDY coeff j rho) * b =
        (b * (d + rho) - A * (n + j)) *
            osculationEvaluateDY coeff j rho +
          (n + j) *
            (b * osculationEvaluateDX coeff j rho +
              A * osculationEvaluateDY coeff j rho) := by ring
      _ = (b * (d + rho) - A * (n + j)) *
          osculationEvaluateDY coeff j rho := by rw [hdirection]; ring
      _ = P ^ 2 * (q * osculationEvaluateDY coeff j rho) := by
            rw [hq]
            ring
  have hlinear : P ^ 2 ∣ linear :=
    hcop.pow_left.dvd_of_dvd_mul_right hlinear_mul
  have hnx : P ∣ -n - j := by
    rcases hn with ⟨q, hq⟩
    refine ⟨-q, ?_⟩
    calc
      -n - j = -(n + j) := by ring
      _ = -(P * q) := by rw [hq]
      _ = P * -q := by ring
  have hdy : P ∣ -d - rho := by
    rcases hd with ⟨q, hq⟩
    refine ⟨-q, ?_⟩
    calc
      -d - rho = -(d + rho) := by ring
      _ = -(P * q) := by rw [hq]
      _ = P * -q := by ring
  have htaylor := osculation_first_order_remainder_dvd coeff
    P j rho (-n - j) (-d - rho) hnx hdy
  have hxarg : j + (-n - j) = -n := by ring
  have hyarg : rho + (-d - rho) = -d := by ring
  have hsum : P ^ 2 ∣ osculationEvaluate coeff (-n) (-d) + linear := by
    rw [show osculationEvaluate coeff (-n) (-d) + linear =
        osculationEvaluate coeff (-n) (-d) -
          osculationEvaluate coeff j rho -
          (-n - j) * osculationEvaluateDX coeff j rho -
          (-d - rho) * osculationEvaluateDY coeff j rho by
      rw [hvalue]
      dsimp [linear, Fx, Fy]
      ring]
    simpa only [hxarg, hyarg] using htaylor
  have hdiff := dvd_sub hsum hlinear
  simpa using hdiff

/-- Pairwise-coprime local square divisors multiply to the square of the
support product. -/
theorem pairwise_coprime_product_square_dvd
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (P : ι → ℤ) (z : ℤ)
    (hcop : (s : Set ι).Pairwise (fun i j => IsCoprime (P i) (P j)))
    (hlocal : ∀ i ∈ s, P i ^ 2 ∣ z) :
    (∏ i ∈ s, P i) ^ 2 ∣ z := by
  rw [← Finset.prod_pow]
  apply Finset.prod_dvd_of_coprime
  · intro i hi j hj hij
    exact (hcop hi hj hij).pow_left.pow_right
  · exact hlocal

/-- Global low-degree osculation theorem over a finite pairwise-coprime owner
support. -/
theorem osculation_support_product_square_dvd
    {ι : Type*} [DecidableEq ι] {r : ℕ}
    (s : Finset ι) (coeff : OsculationMonomial r → ℤ)
    (P b A j rho : ι → ℤ) (n d : ℤ)
    (hpair : (s : Set ι).Pairwise (fun i j => IsCoprime (P i) (P j)))
    (hvalue : ∀ e ∈ s, osculationEvaluate coeff (j e) (rho e) = 0)
    (hdirection : ∀ e ∈ s,
      b e * osculationEvaluateDX coeff (j e) (rho e) +
        A e * osculationEvaluateDY coeff (j e) (rho e) = 0)
    (hn : ∀ e ∈ s, P e ∣ n + j e)
    (hd : ∀ e ∈ s, P e ∣ d + rho e)
    (hsquare : ∀ e ∈ s,
      P e ^ 2 ∣ b e * (d + rho e) - A e * (n + j e))
    (hcop : ∀ e ∈ s, IsCoprime (P e) (b e)) :
    (∏ e ∈ s, P e) ^ 2 ∣ osculationEvaluate coeff (-n) (-d) := by
  apply pairwise_coprime_product_square_dvd s P _ hpair
  intro e he
  exact osculation_owner_square_dvd coeff (P e) (b e) (A e)
    n d (j e) (rho e) (hvalue e he) (hdirection e he)
    (hn e he) (hd e he) (hsquare e he) (hcop e he)

/-- Exact final cancellation step: an integer strictly smaller in absolute
value than a positive natural square that divides it must vanish. -/
theorem integer_eq_zero_of_square_dvd_of_natAbs_lt
    {M : ℕ} {z : ℤ}
    (hdvd : ((M ^ 2 : ℕ) : ℤ) ∣ z)
    (hsmall : z.natAbs < M ^ 2) :
    z = 0 := by
  by_contra hz
  have hzpos : 0 < z.natAbs := Int.natAbs_pos.mpr hz
  have hdvdNat : M ^ 2 ∣ z.natAbs := by
    simpa using Int.natAbs_dvd_natAbs.mpr hdvd
  have hle : M ^ 2 ≤ z.natAbs := Nat.le_of_dvd hzpos hdvdNat
  omega

/-- Cancellation interface used after the exact large-prime mass comparison. -/
theorem osculation_evaluate_eq_zero_of_product_square_bound
    {r : ℕ} (coeff : OsculationMonomial r → ℤ)
    (M : ℕ) (n d : ℤ)
    (hdvd : ((M ^ 2 : ℕ) : ℤ) ∣
      osculationEvaluate coeff (-n) (-d))
    (hsmall :
      (osculationEvaluate coeff (-n) (-d)).natAbs < M ^ 2) :
    osculationEvaluate coeff (-n) (-d) = 0 :=
  integer_eq_zero_of_square_dvd_of_natAbs_lt hdvd hsmall

#print axioms power_first_order_remainder_dvd
#print axioms osculation_first_order_remainder_dvd
#print axioms osculation_owner_square_dvd
#print axioms pairwise_coprime_product_square_dvd
#print axioms osculation_support_product_square_dvd
#print axioms integer_eq_zero_of_square_dvd_of_natAbs_lt
#print axioms osculation_evaluate_eq_zero_of_product_square_bound

end Erdos686Variant
end Erdos686
