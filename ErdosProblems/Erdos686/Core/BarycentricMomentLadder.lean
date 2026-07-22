/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.Core.BarycentricMatching
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Erdős 686: barycentric moment-block cancellation ladder

This module isolates the exact expansion at infinity used by the repaired
barycentric matching argument.  The recurrence for `momentNumerator` is a
finite polynomial identity; no formal Laurent-series division is hidden in
the statement.  We also record the rational two-adic obstruction for each
candidate block and the Vandermonde termination theorem.

The reflection interface then transports the first nonzero moment block to an
exact degree formula for the original matching polynomial and for its
canonical square quotient.
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

/-- Integral version of the same two-adic block obstruction. -/
theorem integer_momentDelta_eq_zero_iff {muq nuPred : ℤ} {k : ℕ}
    (hk : 3 ≤ k) :
    momentDelta k muq nuPred = 0 ↔ muq = 0 ∧ nuPred = 0 := by
  constructor
  · intro h
    have hp : (muq + nuPred) ^ k = 4 * muq ^ k := sub_eq_zero.mp h
    obtain ⟨hsum, hmu⟩ := pow_eq_four_mul_pow_zero hk hp
    exact ⟨hmu, by linarith⟩
  · rintro ⟨rfl, rfl⟩
    simp [momentDelta, show k ≠ 0 by omega]

/-- Vandermonde termination over any domain. -/
theorem mu_vandermonde_termination_domain [IsDomain R] {m : ℕ}
    {j w : Fin m → R}
    (hj : Function.Injective j)
    (hmu : ∀ q < m, mu Finset.univ j w q = 0) :
    w = 0 := by
  apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hj
  intro q
  simpa [mu] using hmu q.val q.isLt

/-- Vandermonde termination for a support indexed by `Fin m`: if all first
`m` weighted moments vanish at distinct rational nodes, every weight is zero. -/
theorem mu_vandermonde_termination {m : ℕ} {j w : Fin m → ℚ}
    (hj : Function.Injective j)
    (hmu : ∀ q < m, mu Finset.univ j w q = 0) :
    w = 0 := by
  apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hj
  intro q
  simpa [mu] using hmu q.val q.isLt

/-- On the zero branch `mu_0 = 0`, nonzero weights force at least one of the
next `m` moment pairs `(mu_q, nu_(q-1))` to be nonzero.  The `mu_0`
hypothesis is essential when a support node can be zero. -/
theorem exists_nonzero_integral_moment_pair {m : ℕ}
    {j rho w : Fin m → ℤ}
    (hj : Function.Injective j) (hw : w ≠ 0)
    (hmu0 : mu Finset.univ j w 0 = 0) :
    ∃ q, 1 ≤ q ∧ q ≤ m ∧
      (mu Finset.univ j w q ≠ 0 ∨
        nu Finset.univ j rho w (q - 1) ≠ 0) := by
  by_contra hex
  have hpairs : ∀ q, 1 ≤ q → q ≤ m →
      mu Finset.univ j w q = 0 ∧
        nu Finset.univ j rho w (q - 1) = 0 := by
    intro q hq hqm
    have hn : ¬ (mu Finset.univ j w q ≠ 0 ∨
        nu Finset.univ j rho w (q - 1) ≠ 0) := by
      intro hpair
      exact hex ⟨q, hq, hqm, hpair⟩
    exact ⟨not_ne_iff.mp (not_or.mp hn).1, not_ne_iff.mp (not_or.mp hn).2⟩
  apply hw
  apply mu_vandermonde_termination_domain hj
  intro q hqm
  by_cases hq : q = 0
  · simpa [hq] using hmu0
  · exact (hpairs q (Nat.one_le_iff_ne_zero.mpr hq) (by omega)).1

/-- Choose the least nonzero integral moment pair.  All lower `mu` moments
and all preceding `nu` moments then vanish, while its `momentDelta` is
nonzero for every exponent `k ≥ 3`. -/
theorem exists_first_nonzero_integral_moment_block {m : ℕ}
    {j rho w : Fin m → ℤ}
    (hj : Function.Injective j) (hw : w ≠ 0)
    (hmu0 : mu Finset.univ j w 0 = 0) {k : ℕ} (hk : 3 ≤ k) :
    ∃ q, 1 ≤ q ∧ q ≤ m ∧
      (∀ p < q, mu Finset.univ j w p = 0) ∧
      (∀ p < q - 1, nu Finset.univ j rho w p = 0) ∧
      momentDelta k (mu Finset.univ j w q)
        (nu Finset.univ j rho w (q - 1)) ≠ 0 := by
  let P : ℕ → Prop := fun q =>
    1 ≤ q ∧ q ≤ m ∧
      (mu Finset.univ j w q ≠ 0 ∨
        nu Finset.univ j rho w (q - 1) ≠ 0)
  have hex : ∃ q, P q := exists_nonzero_integral_moment_pair hj hw hmu0
  let q := Nat.find hex
  have hqP : P q := Nat.find_spec hex
  have hlowerPair : ∀ p, 1 ≤ p → p < q →
      mu Finset.univ j w p = 0 ∧
        nu Finset.univ j rho w (p - 1) = 0 := by
    intro p hp hpq
    have hpm : p ≤ m := le_trans (Nat.le_of_lt hpq) hqP.2.1
    have hn : ¬ (mu Finset.univ j w p ≠ 0 ∨
        nu Finset.univ j rho w (p - 1) ≠ 0) := by
      intro hpair
      have hfind : q ≤ p := Nat.find_min' hex ⟨hp, hpm, hpair⟩
      omega
    exact ⟨not_ne_iff.mp (not_or.mp hn).1, not_ne_iff.mp (not_or.mp hn).2⟩
  refine ⟨q, hqP.1, hqP.2.1, ?_, ?_, ?_⟩
  · intro p hpq
    by_cases hp : p = 0
    · simpa [hp] using hmu0
    · exact (hlowerPair p (Nat.one_le_iff_ne_zero.mpr hp) hpq).1
  · intro p hpq
    have hpq' : p + 1 < q := by omega
    have hpair := hlowerPair (p + 1) (by omega) hpq'
    simpa using hpair.2
  · intro hdelta
    have hzero := (integer_momentDelta_eq_zero_iff hk).mp hdelta
    exact hqP.2.2.elim (fun hmu => hmu hzero.1) (fun hnu => hnu hzero.2)

section ReflectionBridge

variable {S : Finset α} {j rho w : α → ℤ} {c : ℤ}

lemma reflect_factor (j : α → ℤ) (e : α) :
    (factor j e).reflect 1 = reverseFactor j e := by
  rw [factor, Polynomial.reflect_sub, Polynomial.reflect_one_X,
    Polynomial.reflect_C]
  simp [reverseFactor]

lemma reflect_fixed_succ {p : Polynomial ℤ} {N : ℕ}
    (hp : p.natDegree ≤ N) :
    p.reflect (N + 1) = X * p.reflect N := by
  conv_lhs => rw [← one_mul p]
  rw [show N + 1 = 1 + N by omega]
  rw [Polynomial.reflect_mul (1 : Polynomial ℤ) p (by simp) hp]
  simp [Polynomial.reflect_one]

lemma reflect_W (S : Finset α) (j : α → ℤ) :
    (W S j).reflect S.card = reverseW S j := by
  induction S using Finset.induction_on with
  | empty => simp [W, reverseW, Polynomial.reflect_one]
  | @insert e S he ih =>
      have hfac : (factor j e).natDegree ≤ 1 := by
        rw [factor]
        rw [Polynomial.natDegree_X_sub_C]
      have hW : (W S j).natDegree ≤ S.card := (W_natDegree S j).le
      rw [Finset.card_insert_of_notMem he, W, reverseW]
      simp only [Finset.prod_insert, he, not_false_eq_true]
      change (factor j e * W S j).reflect (S.card + 1) =
        reverseFactor j e * reverseW S j
      rw [show S.card + 1 = 1 + S.card by omega]
      rw [Polynomial.reflect_mul (factor j e) (W S j) hfac hW]
      rw [reflect_factor, ih]

lemma reflect_Wexcept {e : α} (he : e ∈ S) :
    (Wexcept S j e).reflect (S.card - 1) = reverseWexcept S j e := by
  rw [show S.card - 1 = (S.erase e).card by
    rw [Finset.card_erase_of_mem he]]
  exact reflect_W (S.erase e) j

lemma reflect_finset_sum (T : Finset α) (f : α → Polynomial ℤ) (N : ℕ) :
    (∑ e ∈ T, f e).reflect N = ∑ e ∈ T, (f e).reflect N := by
  induction T using Finset.induction_on with
  | empty => simp [Polynomial.reflect_zero]
  | @insert e T he ih =>
      simp only [Finset.sum_insert, he, not_false_eq_true]
      rw [Polynomial.reflect_add, ih]

lemma reflect_V :
    (V S j w).reflect (S.card - 1) = momentNumerator S j w 0 := by
  rw [V, momentNumerator]
  simp only [pow_zero, mul_one]
  rw [reflect_finset_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [Polynomial.reflect_C_mul, reflect_Wexcept he]

noncomputable def reverseV (S : Finset α) (j w : α → ℤ) : Polynomial ℤ :=
  momentNumerator S j w 0

noncomputable def reverseU (S : Finset α) (j rho w : α → ℤ) (c : ℤ) : Polynomial ℤ :=
  C c * reverseW S j + X * momentNumerator S j (offsetWeights rho w) 0

lemma U_eq_C_mul_W_add_V_offset :
    U S j rho w c = C c * W S j + V S j (offsetWeights rho w) := by
  rw [U, V]
  congr 1

lemma reflect_U (hS : S.Nonempty) :
    (U S j rho w c).reflect S.card = reverseU S j rho w c := by
  rw [U_eq_C_mul_W_add_V_offset, Polynomial.reflect_add,
    Polynomial.reflect_C_mul, reflect_W]
  have hcard : S.card = (S.card - 1) + 1 := by
    have : 0 < S.card := Finset.card_pos.mpr hS
    omega
  have hV : (V S j (offsetWeights rho w)).natDegree ≤ S.card - 1 :=
    V_natDegree_le_card_sub_one hS j (offsetWeights rho w)
  rw [hcard, reflect_fixed_succ hV, reflect_V]
  rfl

lemma reflect_affine (a : ℤ) :
    (X + C a).reflect 1 = 1 + C a * X := by
  rw [Polynomial.reflect_add, Polynomial.reflect_one_X,
    Polynomial.reflect_C]
  simp

lemma reflect_affine_mul_V (hS : S.Nonempty) (a : ℤ) :
    ((X + C a) * V S j w).reflect S.card =
      (1 + C a * X) * reverseV S j w := by
  have hcard : S.card = 1 + (S.card - 1) := by
    have : 0 < S.card := Finset.card_pos.mpr hS
    omega
  have ha : (X + C a : Polynomial ℤ).natDegree ≤ 1 := by
    rw [Polynomial.natDegree_X_add_C]
  have hV : (V S j w).natDegree ≤ S.card - 1 :=
    V_natDegree_le_card_sub_one hS j w
  rw [hcard, Polynomial.reflect_mul (X + C a) (V S j w) ha hV,
    reflect_affine, reverseV, reflect_V]

lemma reflect_finset_prod_fixed (T : Finset α) (f : α → Polynomial ℤ) (N : ℕ)
    (hdeg : ∀ e ∈ T, (f e).natDegree ≤ N) :
    (∏ e ∈ T, f e).reflect (T.card * N) =
      ∏ e ∈ T, (f e).reflect N := by
  induction T using Finset.induction_on with
  | empty => simp [Polynomial.reflect_one]
  | @insert e T he ih =>
      have hedeg : (f e).natDegree ≤ N := hdeg e (Finset.mem_insert_self e T)
      have hprod : (∏ x ∈ T, f x).natDegree ≤ T.card * N := by
        refine (Polynomial.natDegree_prod_le T f).trans ?_
        calc
          (∑ x ∈ T, (f x).natDegree) ≤ ∑ x ∈ T, N := by
            apply Finset.sum_le_sum
            intro x hx
            exact hdeg x (Finset.mem_insert_of_mem hx)
          _ = T.card * N := by simp
      rw [Finset.card_insert_of_notMem he]
      simp only [Finset.prod_insert, he, not_false_eq_true]
      rw [Nat.add_mul]
      rw [show T.card * N + 1 * N = N + T.card * N by omega]
      rw [Polynomial.reflect_mul (f e) (∏ x ∈ T, f x) hedeg hprod]
      rw [ih (fun x hx => hdeg x (Finset.mem_insert_of_mem hx))]

noncomputable def reverseMatchingPhi
    (k : ℕ) (S : Finset α) (j rho w : α → ℤ) (c : ℤ) : Polynomial ℤ :=
  (Finset.univ : Finset (Fin k)).prod
      (fun h => reverseU S j rho w c +
        (1 + C (finNode h) * X) * reverseV S j w) -
    C 4 * (Finset.univ : Finset (Fin k)).prod
      (fun h => (1 + C (finNode h) * X) * reverseV S j w)

theorem reflect_matchingPhi (hS : S.Nonempty) (k : ℕ) :
    (matchingPhi k (U S j rho w c) (V S j w)).reflect (k * S.card) =
      reverseMatchingPhi k S j rho w c := by
  let A : Fin k → Polynomial ℤ := fun h =>
    U S j rho w c + (X + C (finNode h)) * V S j w
  let B : Fin k → Polynomial ℤ := fun h =>
    (X + C (finNode h)) * V S j w
  have hcard : (S.card - 1) + 1 = S.card := by
    have : 0 < S.card := Finset.card_pos.mpr hS
    omega
  have hAdeg : ∀ h : Fin k, (A h).natDegree ≤ S.card := by
    intro h
    apply Polynomial.natDegree_add_le_of_degree_le
      (U_natDegree_le_card S j rho w c)
    simpa [hcard] using affine_mul_natDegree_le_succ
      (V_natDegree_le_card_sub_one hS j w) (finNode h)
  have hBdeg : ∀ h : Fin k, (B h).natDegree ≤ S.card := by
    intro h
    simpa [hcard] using affine_mul_natDegree_le_succ
      (V_natDegree_le_card_sub_one hS j w) (finNode h)
  rw [matchingPhi, Polynomial.reflect_sub, Polynomial.reflect_C_mul]
  change ((Finset.univ : Finset (Fin k)).prod A).reflect (k * S.card) -
      C 4 * ((Finset.univ : Finset (Fin k)).prod B).reflect (k * S.card) = _
  rw [show k * S.card = (Finset.univ : Finset (Fin k)).card * S.card by simp]
  rw [reflect_finset_prod_fixed _ A S.card (by simpa using hAdeg),
    reflect_finset_prod_fixed _ B S.card (by simpa using hBdeg)]
  unfold A B reverseMatchingPhi
  simp_rw [Polynomial.reflect_add, reflect_U hS, reflect_affine_mul_V hS]

noncomputable def nextMomentBlock
    (k : ℕ) (S : Finset α) (j rho w : α → ℤ) (q : ℕ) : Polynomial ℤ :=
  (Finset.univ : Finset (Fin k)).prod
      (fun h => momentNumerator S j (offsetWeights rho w) (q - 1) +
        (1 + C (finNode h) * X) * momentNumerator S j w q) -
    C 4 * (Finset.univ : Finset (Fin k)).prod
      (fun h => (1 + C (finNode h) * X) * momentNumerator S j w q)

lemma reverseV_eq_X_pow_of_lower_moments (q : ℕ)
    (hmu : ∀ p < q, mu S j w p = 0) :
    reverseV S j w = X ^ q * momentNumerator S j w q := by
  exact momentNumerator_eq_X_pow_of_lower_moments S j w q hmu

lemma reverseU_zero_eq_X_pow_of_lower_moments {q : ℕ} (hq : 1 ≤ q)
    (hnu : ∀ p < q - 1, nu S j rho w p = 0) :
    reverseU S j rho w 0 =
      X ^ q * momentNumerator S j (offsetWeights rho w) (q - 1) := by
  rw [reverseU]
  simp only [map_zero, zero_mul, zero_add]
  rw [momentNumerator_eq_X_pow_of_lower_moments S j
    (offsetWeights rho w) (q - 1)]
  · calc
      X * (X ^ (q - 1) * momentNumerator S j (offsetWeights rho w) (q - 1)) =
          (X * X ^ (q - 1)) * momentNumerator S j (offsetWeights rho w) (q - 1) := by
            ring
      _ = X ^ q * momentNumerator S j (offsetWeights rho w) (q - 1) := by
        rw [← pow_succ']
        congr 2
        omega
  · intro p hp
    rw [mu_offsetWeights_eq_nu]
    exact hnu p hp

theorem reverseMatchingPhi_moment_factorization {q : ℕ} (hq : 1 ≤ q)
    (hmu : ∀ p < q, mu S j w p = 0)
    (hnu : ∀ p < q - 1, nu S j rho w p = 0) :
    reverseMatchingPhi k S j rho w 0 =
      X ^ (q * k) * nextMomentBlock k S j rho w q := by
  rw [reverseMatchingPhi, nextMomentBlock,
    reverseV_eq_X_pow_of_lower_moments q hmu,
    reverseU_zero_eq_X_pow_of_lower_moments hq hnu]
  let A : Fin k → Polynomial ℤ := fun h =>
    momentNumerator S j (offsetWeights rho w) (q - 1) +
      (1 + C (finNode h) * X) * momentNumerator S j w q
  let B : Fin k → Polynomial ℤ := fun h =>
    (1 + C (finNode h) * X) * momentNumerator S j w q
  have hA : ∀ h : Fin k,
      X ^ q * momentNumerator S j (offsetWeights rho w) (q - 1) +
          (1 + C (finNode h) * X) *
            (X ^ q * momentNumerator S j w q) = X ^ q * A h := by
    intro h
    unfold A
    ring
  have hB : ∀ h : Fin k,
      (1 + C (finNode h) * X) *
        (X ^ q * momentNumerator S j w q) = X ^ q * B h := by
    intro h
    unfold B
    ring
  simp_rw [hA, hB]
  change (∏ h : Fin k, X ^ q * A h) -
      C 4 * (∏ h : Fin k, X ^ q * B h) =
    X ^ (q * k) * ((∏ h : Fin k, A h) - C 4 * (∏ h : Fin k, B h))
  simp_rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [pow_mul]
  ring

lemma nextMomentBlock_coeff_zero (k : ℕ) (q : ℕ) :
    (nextMomentBlock k S j rho w q).coeff 0 =
      momentDelta k (mu S j w q) (nu S j rho w (q - 1)) := by
  rw [coeff_zero_eq_eval_zero, nextMomentBlock, eval_sub, eval_mul, eval_C]
  simp only [Polynomial.eval_prod, eval_add, eval_mul, eval_one, eval_X,
    eval_C, mul_zero, add_zero, one_mul]
  simp_rw [← coeff_zero_eq_eval_zero, momentNumerator_coeff_zero,
    mu_offsetWeights_eq_nu]
  simp [momentDelta, add_comm]

theorem reverseMatchingPhi_coeff_momentDelta {q : ℕ} (hq : 1 ≤ q)
    (hmu : ∀ p < q, mu S j w p = 0)
    (hnu : ∀ p < q - 1, nu S j rho w p = 0) :
    (reverseMatchingPhi k S j rho w 0).coeff (q * k) =
      momentDelta k (mu S j w q) (nu S j rho w (q - 1)) := by
  rw [reverseMatchingPhi_moment_factorization hq hmu hnu]
  calc
    (X ^ (q * k) * nextMomentBlock k S j rho w q).coeff (q * k) =
        (nextMomentBlock k S j rho w q).coeff 0 := by
      simpa using Polynomial.coeff_X_pow_mul
        (nextMomentBlock k S j rho w q) (q * k) 0
    _ = _ := nextMomentBlock_coeff_zero k q

theorem matchingPhi_coeff_momentDelta (hS : S.Nonempty) {q k : ℕ}
    (hq : 1 ≤ q) (hqcard : q ≤ S.card)
    (hmu : ∀ p < q, mu S j w p = 0)
    (hnu : ∀ p < q - 1, nu S j rho w p = 0) :
    (matchingPhi k (U S j rho w 0) (V S j w)).coeff (k * (S.card - q)) =
      momentDelta k (mu S j w q) (nu S j rho w (q - 1)) := by
  have href := congrArg (fun P : Polynomial ℤ => P.coeff (q * k))
    (reflect_matchingPhi (S := S) (j := j) (rho := rho) (w := w)
      (c := 0) hS k)
  change ((matchingPhi k (U S j rho w 0) (V S j w)).reflect
      (k * S.card)).coeff (q * k) =
    (reverseMatchingPhi k S j rho w 0).coeff (q * k) at href
  rw [Polynomial.coeff_reflect] at href
  have hqk : q * k ≤ k * S.card := by
    calc q * k = k * q := Nat.mul_comm _ _
      _ ≤ k * S.card := Nat.mul_le_mul_left k hqcard
  rw [Polynomial.revAt_le hqk] at href
  have hindex : k * S.card - q * k = k * (S.card - q) := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_comm q k]
  rw [hindex] at href
  calc
    (matchingPhi k (U S j rho w 0) (V S j w)).coeff (k * (S.card - q)) =
        (reverseMatchingPhi k S j rho w 0).coeff (q * k) := href
    _ = _ := reverseMatchingPhi_coeff_momentDelta hq hmu hnu

/-- If reflection in degree `N` has a zero of order at least `r` at the
origin, then the original polynomial has degree at most `N-r`.  This form is
useful here because it does not require the reflected cofactor to be
nonzero. -/
lemma natDegree_le_sub_of_reflect_eq_X_pow_mul
    {p A : Polynomial ℤ} {N r : ℕ}
    (hp : p.natDegree ≤ N) (hr : r ≤ N)
    (href : p.reflect N = X ^ r * A) :
    p.natDegree ≤ N - r := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro i hi
  by_cases hiN : i ≤ N
  · have hir : N - i < r := by omega
    have hcoeff : (p.reflect N).coeff (N - i) = 0 := by
      rw [href, Polynomial.coeff_X_pow_mul']
      simp [not_le.mpr hir]
    rw [Polynomial.coeff_reflect, Polynomial.revAt_le (Nat.sub_le N i)] at hcoeff
    have hrev : N - (N - i) = i := Nat.sub_sub_self hiN
    simpa [hrev] using hcoeff
  · exact Polynomial.natDegree_le_iff_coeff_eq_zero.mp hp i (by omega)

/-- Vanishing of the lower moment blocks gives the sharp degree upper bound
for the original matching polynomial. -/
theorem matchingPhi_natDegree_le_first_moment_block
    (hS : S.Nonempty) {q k : ℕ}
    (hq : 1 ≤ q) (hqcard : q ≤ S.card)
    (hmu : ∀ p < q, mu S j w p = 0)
    (hnu : ∀ p < q - 1, nu S j rho w p = 0) :
    (matchingPhi k (U S j rho w 0) (V S j w)).natDegree ≤
      k * (S.card - q) := by
  let Phi := matchingPhi k (U S j rho w 0) (V S j w)
  have hdeg : Phi.natDegree ≤ k * S.card :=
    barycentric_matchingPhi_natDegree_le hS j rho w 0 k
  have hr : q * k ≤ k * S.card := by
    calc
      q * k = k * q := Nat.mul_comm _ _
      _ ≤ k * S.card := Nat.mul_le_mul_left k hqcard
  have href : Phi.reflect (k * S.card) =
      X ^ (q * k) * nextMomentBlock k S j rho w q := by
    calc
      Phi.reflect (k * S.card) = reverseMatchingPhi k S j rho w 0 :=
        reflect_matchingPhi hS k
      _ = X ^ (q * k) * nextMomentBlock k S j rho w q :=
        reverseMatchingPhi_moment_factorization hq hmu hnu
  have hle := natDegree_le_sub_of_reflect_eq_X_pow_mul hdeg hr href
  have hsub : k * S.card - q * k = k * (S.card - q) := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_comm q k]
  simpa [Phi, hsub] using hle

/-- If the first candidate moment block is nonzero, its coefficient and the
reflection factorization determine the exact degree of the matching
polynomial. -/
theorem matchingPhi_natDegree_eq_first_nonzero_moment_block
    (hS : S.Nonempty) {q k : ℕ}
    (hq : 1 ≤ q) (hqcard : q ≤ S.card)
    (hmu : ∀ p < q, mu S j w p = 0)
    (hnu : ∀ p < q - 1, nu S j rho w p = 0)
    (hdelta : momentDelta k (mu S j w q) (nu S j rho w (q - 1)) ≠ 0) :
    (matchingPhi k (U S j rho w 0) (V S j w)).natDegree =
      k * (S.card - q) := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (matchingPhi_natDegree_le_first_moment_block hS hq hqcard hmu hnu)
  rw [matchingPhi_coeff_momentDelta hS hq hqcard hmu hnu]
  exact hdelta

/-- `degree` version of the exact first-nonzero-block theorem. -/
theorem matchingPhi_degree_eq_first_nonzero_moment_block
    (hS : S.Nonempty) {q k : ℕ}
    (hq : 1 ≤ q) (hqcard : q ≤ S.card)
    (hmu : ∀ p < q, mu S j w p = 0)
    (hnu : ∀ p < q - 1, nu S j rho w p = 0)
    (hdelta : momentDelta k (mu S j w q) (nu S j rho w (q - 1)) ≠ 0) :
    (matchingPhi k (U S j rho w 0) (V S j w)).degree =
      (↑(k * (S.card - q)) : WithBot ℕ) := by
  let Phi := matchingPhi k (U S j rho w 0) (V S j w)
  have hPhi : Phi ≠ 0 := by
    intro hz
    have hcoeff := matchingPhi_coeff_momentDelta (k := k) hS hq hqcard hmu hnu
    rw [show matchingPhi k (U S j rho w 0) (V S j w) = Phi by rfl, hz] at hcoeff
    simp at hcoeff
    exact hdelta hcoeff.symm
  rw [show matchingPhi k (U S j rho w 0) (V S j w) = Phi by rfl,
    Polynomial.degree_eq_natDegree hPhi,
    matchingPhi_natDegree_eq_first_nonzero_moment_block
      hS hq hqcard hmu hnu hdelta]

/-- Exact quotient degree after removing the canonical square `W^2` from a
matching polynomial whose first nonzero moment block is `q`. -/
theorem matchingPhi_quotient_natDegree_eq_first_nonzero_moment_block
    (hS : S.Nonempty) {q k : ℕ}
    (hq : 1 ≤ q) (hqcard : q ≤ S.card)
    (hmu : ∀ p < q, mu S j w p = 0)
    (hnu : ∀ p < q - 1, nu S j rho w p = 0)
    (hdelta : momentDelta k (mu S j w q) (nu S j rho w (q - 1)) ≠ 0)
    (Q : Polynomial ℤ)
    (hfactor : matchingPhi k (U S j rho w 0) (V S j w) = (W S j) ^ 2 * Q) :
    Q.natDegree = k * (S.card - q) - 2 * S.card := by
  let Phi := matchingPhi k (U S j rho w 0) (V S j w)
  have hPhiDeg : Phi.natDegree = k * (S.card - q) :=
    matchingPhi_natDegree_eq_first_nonzero_moment_block
      hS hq hqcard hmu hnu hdelta
  have hPhi : Phi ≠ 0 := by
    intro hz
    have hcoeff := matchingPhi_coeff_momentDelta (k := k) hS hq hqcard hmu hnu
    rw [show matchingPhi k (U S j rho w 0) (V S j w) = Phi by rfl, hz] at hcoeff
    simp at hcoeff
    exact hdelta hcoeff.symm
  have hWne : W S j ≠ 0 := (W_monic S j).ne_zero
  have hQne : Q ≠ 0 := by
    intro hQ
    rw [show matchingPhi k (U S j rho w 0) (V S j w) = Phi by rfl,
      hQ, mul_zero] at hfactor
    exact hPhi hfactor
  have heq : k * (S.card - q) = 2 * S.card + Q.natDegree := by
    rw [← hPhiDeg]
    dsimp [Phi]
    rw [hfactor, Polynomial.natDegree_mul (pow_ne_zero 2 hWne) hQne,
      Polynomial.natDegree_pow, W_natDegree]
  omega

/-- For a finite, distinctly supported integral zero branch with nonzero
weights, the least moment block supplies both a nonzero coefficient and the
exact matching-polynomial degree. -/
theorem fin_matchingPhi_exists_first_nonzero_block_and_exact_degree
    {m : ℕ} {j rho w : Fin m → ℤ}
    (hj : Function.Injective j) (hw : w ≠ 0)
    (hmu0 : mu Finset.univ j w 0 = 0) {k : ℕ} (hk : 3 ≤ k) :
    ∃ q, 1 ≤ q ∧ q ≤ m ∧
      (∀ p < q, mu Finset.univ j w p = 0) ∧
      (∀ p < q - 1, nu Finset.univ j rho w p = 0) ∧
      momentDelta k (mu Finset.univ j w q)
        (nu Finset.univ j rho w (q - 1)) ≠ 0 ∧
      matchingPhi k (U Finset.univ j rho w 0) (V Finset.univ j w) ≠ 0 ∧
      (matchingPhi k (U Finset.univ j rho w 0)
        (V Finset.univ j w)).natDegree = k * (m - q) := by
  obtain ⟨q, hq, hqm, hmu, hnu, hdelta⟩ :=
    exists_first_nonzero_integral_moment_block hj hw hmu0 hk
  have hm : 1 ≤ m := le_trans hq hqm
  have hS : (Finset.univ : Finset (Fin m)).Nonempty := by
    exact ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have hqcard : q ≤ (Finset.univ : Finset (Fin m)).card := by
    simpa using hqm
  have hcoeff :
      (matchingPhi k (U Finset.univ j rho w 0)
        (V Finset.univ j w)).coeff
          (k * ((Finset.univ : Finset (Fin m)).card - q)) ≠ 0 := by
    rw [matchingPhi_coeff_momentDelta hS hq hqcard hmu hnu]
    exact hdelta
  have hne : matchingPhi k (U Finset.univ j rho w 0)
      (V Finset.univ j w) ≠ 0 := by
    intro hz
    rw [hz] at hcoeff
    exact hcoeff (by simp)
  have hdeg := matchingPhi_natDegree_eq_first_nonzero_moment_block
    hS hq hqcard hmu hnu hdelta
  refine ⟨q, hq, hqm, hmu, hnu, hdelta, hne, ?_⟩
  simpa using hdeg

/-- Nonvanishing-only corollary of finite moment termination. -/
theorem fin_matchingPhi_ne_zero_of_injective_nonzero_weights
    {m : ℕ} {j rho w : Fin m → ℤ}
    (hj : Function.Injective j) (hw : w ≠ 0)
    (hmu0 : mu Finset.univ j w 0 = 0) {k : ℕ} (hk : 3 ≤ k) :
    matchingPhi k (U Finset.univ j rho w 0) (V Finset.univ j w) ≠ 0 := by
  obtain ⟨q, hq, hqm, hmu, hnu, hdelta, hne, hdeg⟩ :=
    fin_matchingPhi_exists_first_nonzero_block_and_exact_degree
      hj hw hmu0 hk
  exact hne

end ReflectionBridge

#print axioms momentNumerator_recurrence
#print axioms momentNumerator_eq_X_pow_of_lower_moments
#print axioms momentNumerator_coeff_of_lower_moments
#print axioms rational_momentDelta_eq_zero_iff
#print axioms integer_momentDelta_eq_zero_iff
#print axioms mu_vandermonde_termination_domain
#print axioms mu_vandermonde_termination
#print axioms exists_nonzero_integral_moment_pair
#print axioms exists_first_nonzero_integral_moment_block
#print axioms reflect_matchingPhi
#print axioms reverseMatchingPhi_moment_factorization
#print axioms reverseMatchingPhi_coeff_momentDelta
#print axioms matchingPhi_coeff_momentDelta
#print axioms matchingPhi_natDegree_le_first_moment_block
#print axioms matchingPhi_natDegree_eq_first_nonzero_moment_block
#print axioms matchingPhi_degree_eq_first_nonzero_moment_block
#print axioms matchingPhi_quotient_natDegree_eq_first_nonzero_moment_block
#print axioms fin_matchingPhi_exists_first_nonzero_block_and_exact_degree
#print axioms fin_matchingPhi_ne_zero_of_injective_nonzero_weights

end Erdos686Variant
end Erdos686
