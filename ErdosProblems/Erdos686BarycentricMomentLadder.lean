/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686BarycentricMatching
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Erdős 686: barycentric moment-block cancellation ladder

This module isolates the exact expansion at infinity used by the repaired
barycentric matching argument.  The recurrence for `momentNumerator` is a
finite polynomial identity; no formal Laurent-series division is hidden in
the statement.  We also record the rational two-adic obstruction for each
candidate block and the Vandermonde termination theorem.

Degree conclusions for the original matching polynomial are deliberately not
asserted here until the reversal interface to that polynomial is banked.
-/

namespace Erdos686
namespace Erdos686Variant

open scoped BigOperators
open Polynomial

variable {R : Type*} [CommRing R]
variable {α : Type*} [DecidableEq α]

/-- The `q`-th weighted node moment. -/
def mu (S : Finset α) (j w : α → R) (q : ℕ) : R :=
  ∑ e ∈ S, w e * j e ^ q

/-- The `q`-th offset-weighted node moment. -/
def nu (S : Finset α) (j rho w : α → R) (q : ℕ) : R :=
  ∑ e ∈ S, w e * rho e * j e ^ q

noncomputable def reverseFactor (j : α → R) (e : α) : Polynomial R :=
  1 - C (j e) * X

noncomputable def reverseW (S : Finset α) (j : α → R) : Polynomial R :=
  ∏ e ∈ S, reverseFactor j e

noncomputable def reverseWexcept (S : Finset α) (j : α → R) (e : α) : Polynomial R :=
  ∏ l ∈ S.erase e, reverseFactor j l

/-- The finite numerator whose quotient by `reverseW` expands as
`sum_q mu_q X^q` at the origin. -/
noncomputable def momentNumerator
    (S : Finset α) (j w : α → R) (q : ℕ) : Polynomial R :=
  ∑ e ∈ S, C (w e * j e ^ q) * reverseWexcept S j e

lemma reverseW_eq_factor_mul_except {S : Finset α} {j : α → R} {e : α}
    (he : e ∈ S) :
    reverseW S j = reverseFactor j e * reverseWexcept S j e := by
  rw [reverseW, reverseWexcept, ← Finset.mul_prod_erase _ _ he]

lemma reverseFactor_mul_except {S : Finset α} {j : α → R} {e : α}
    (he : e ∈ S) :
    reverseFactor j e * reverseWexcept S j e = reverseW S j := by
  exact (reverseW_eq_factor_mul_except he).symm

/-- Exact finite generating-series recurrence:
`G_q = mu_q Wbar + X G_(q+1)`. -/
theorem momentNumerator_recurrence
    (S : Finset α) (j w : α → R) (q : ℕ) :
    momentNumerator S j w q =
      C (mu S j w q) * reverseW S j +
        X * momentNumerator S j w (q + 1) := by
  rw [momentNumerator, momentNumerator, mu]
  simp only [map_sum, map_mul, map_pow]
  rw [Finset.sum_mul, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  rw [reverseW_eq_factor_mul_except he]
  simp only [reverseFactor]
  ring

lemma momentNumerator_coeff_zero
    (S : Finset α) (j w : α → R) (q : ℕ) :
    (momentNumerator S j w q).coeff 0 = mu S j w q := by
  rw [coeff_zero_eq_eval_zero, momentNumerator,
    Polynomial.eval_finset_sum, mu]
  apply Finset.sum_congr rfl
  intro e he
  simp [reverseWexcept, reverseFactor, Polynomial.eval_prod]

/-- If the moments below `q` vanish, the complete numerator has an exact
factor `X^q`. -/
theorem momentNumerator_eq_X_pow_of_lower_moments
    (S : Finset α) (j w : α → R) (q : ℕ)
    (hzero : ∀ p < q, mu S j w p = 0) :
    momentNumerator S j w 0 = X ^ q * momentNumerator S j w q := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [ih (fun p hp => hzero p (by omega))]
      rw [momentNumerator_recurrence]
      rw [hzero q (by omega), map_zero, zero_mul, zero_add]
      ring

/-- The first uncancelled coefficient of the finite numerator is the first
uncancelled moment. -/
theorem momentNumerator_coeff_of_lower_moments
    (S : Finset α) (j w : α → R) (q : ℕ)
    (hzero : ∀ p < q, mu S j w p = 0) :
    (momentNumerator S j w 0).coeff q = mu S j w q := by
  rw [momentNumerator_eq_X_pow_of_lower_moments S j w q hzero]
  calc
    (X ^ q * momentNumerator S j w q).coeff q =
        (momentNumerator S j w q).coeff 0 := by
      simpa using Polynomial.coeff_X_pow_mul (momentNumerator S j w q) q 0
    _ = mu S j w q := momentNumerator_coeff_zero S j w q

/-- The candidate coefficient in the next matching block. -/
def momentDelta (k : ℕ) (muq nuPred : R) : R :=
  (muq + nuPred) ^ k - 4 * muq ^ k

def offsetWeights (rho w : α → R) : α → R := fun e => w e * rho e

lemma mu_offsetWeights_eq_nu
    (S : Finset α) (j rho w : α → R) (q : ℕ) :
    mu S j (offsetWeights rho w) q = nu S j rho w q := by
  rw [mu, nu]
  apply Finset.sum_congr rfl
  intro e he
  simp only [offsetWeights]

/-- Clearing both rational denominators reduces the rational obstruction to
the integral two-adic theorem. -/
theorem rational_pow_eq_four_mul_pow_zero {x y : ℚ} {k : ℕ} (hk : 3 ≤ k)
    (h : x ^ k = 4 * y ^ k) : x = 0 ∧ y = 0 := by
  let X0 : ℤ := x.num * y.den
  let Y0 : ℤ := y.num * x.den
  have hxnum : (x.num : ℚ) = x * x.den := by
    calc
      (x.num : ℚ) = ((x.num : ℚ) / x.den) * x.den := by field_simp
      _ = x * x.den := by rw [Rat.num_div_den]
  have hynum : (y.num : ℚ) = y * y.den := by
    calc
      (y.num : ℚ) = ((y.num : ℚ) / y.den) * y.den := by field_simp
      _ = y * y.den := by rw [Rat.num_div_den]
  have hxy : (X0 : ℚ) ^ k = 4 * (Y0 : ℚ) ^ k := by
    rw [show (X0 : ℚ) = x * x.den * y.den by
      dsimp [X0]
      push_cast
      rw [hxnum],
      show (Y0 : ℚ) = y * y.den * x.den by
        dsimp [Y0]
        push_cast
        rw [hynum]]
    rw [mul_pow, mul_pow, h]
    ring
  have hXY : X0 ^ k = 4 * Y0 ^ k := by exact_mod_cast hxy
  obtain ⟨hX, hY⟩ := pow_eq_four_mul_pow_zero hk hXY
  have hxnum0 : x.num = 0 := by
    have : x.num * (y.den : ℤ) = 0 := hX
    exact (mul_eq_zero.mp this).resolve_right (by exact_mod_cast y.den_nz)
  have hynum0 : y.num = 0 := by
    have : y.num * (x.den : ℤ) = 0 := hY
    exact (mul_eq_zero.mp this).resolve_right (by exact_mod_cast x.den_nz)
  exact ⟨Rat.num_eq_zero.mp hxnum0, Rat.num_eq_zero.mp hynum0⟩

/-- Over the rationals the next candidate block vanishes exactly when both
new moments vanish. -/
theorem rational_momentDelta_eq_zero_iff {muq nuPred : ℚ} {k : ℕ}
    (hk : 3 ≤ k) :
    momentDelta k muq nuPred = 0 ↔ muq = 0 ∧ nuPred = 0 := by
  constructor
  · intro h
    have hp : (muq + nuPred) ^ k = 4 * muq ^ k := sub_eq_zero.mp h
    obtain ⟨hsum, hmu⟩ := rational_pow_eq_four_mul_pow_zero hk hp
    exact ⟨hmu, by linarith⟩
  · rintro ⟨rfl, rfl⟩
    simp [momentDelta, show k ≠ 0 by omega]

/-- Vandermonde termination for a support indexed by `Fin m`: if all first
`m` weighted moments vanish at distinct rational nodes, every weight is zero. -/
theorem mu_vandermonde_termination {m : ℕ} {j w : Fin m → ℚ}
    (hj : Function.Injective j)
    (hmu : ∀ q < m, mu Finset.univ j w q = 0) :
    w = 0 := by
  apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hj
  intro q
  simpa [mu] using hmu q.val q.isLt

#print axioms momentNumerator_recurrence
#print axioms momentNumerator_eq_X_pow_of_lower_moments
#print axioms momentNumerator_coeff_of_lower_moments
#print axioms rational_momentDelta_eq_zero_iff
#print axioms mu_vandermonde_termination

end Erdos686Variant
end Erdos686
