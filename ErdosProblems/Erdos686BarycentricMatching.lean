/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import Mathlib

/-!
# Erdős 686: repaired barycentric matching interpolation

This module audits the old square-Hermite pair in its barycentric form.  The
central correction is that `(c+v)^k - 4v^k` is the coefficient of degree
`k * |S|`; it need not be the leading coefficient in the cancellation branch.

The formulas below are entirely integral.  In particular the displayed
directional-derivative identity is the denominator-cleared form of the usual
barycentric system, so it does not silently divide at a support node.
-/

namespace Erdos686
namespace Erdos686Variant

open scoped BigOperators
open Polynomial

/-- The two-adic obstruction to `x^k = 4y^k` for `k >= 3`. -/
theorem pow_eq_four_mul_pow_zero {x y : ℤ} {k : ℕ} (hk : 3 ≤ k)
    (h : x ^ k = 4 * y ^ k) : x = 0 ∧ y = 0 := by
  have hnat : x.natAbs ^ k = 4 * y.natAbs ^ k := by
    simpa [Int.natAbs_pow, Int.natAbs_mul] using congrArg Int.natAbs h
  by_cases hy : y.natAbs = 0
  · have hyz : y = 0 := Int.natAbs_eq_zero.mp hy
    subst y
    have hk0 : k ≠ 0 := by omega
    have hxpow : x ^ k = 0 := by simpa [hk0] using h
    have hx : x = 0 := eq_zero_of_pow_eq_zero hxpow
    exact ⟨hx, rfl⟩
  have hx : x.natAbs ≠ 0 := by
    intro hx
    have hk0 : k ≠ 0 := by omega
    have hypos : 0 < y.natAbs ^ k := pow_pos (Nat.pos_of_ne_zero hy) k
    rw [hx, zero_pow hk0] at hnat
    omega
  have hval := congrArg (padicValNat 2) hnat
  have hyPow : y.natAbs ^ k ≠ 0 := pow_ne_zero _ hy
  have hfour : (4 : ℕ) = 2 ^ 2 := by norm_num
  rw [padicValNat.pow k hx, hfour,
    padicValNat.mul (pow_ne_zero _ (by norm_num)) hyPow,
    padicValNat_base_pow (by norm_num) 2,
    padicValNat.pow k hy] at hval
  have hdvdInt : (k : ℤ) ∣ (2 : ℤ) := by
    have hvalZ : (k : ℤ) * (padicValNat 2 x.natAbs : ℤ) =
        2 + (k : ℤ) * (padicValNat 2 y.natAbs : ℤ) := by
      exact_mod_cast hval
    refine ⟨(padicValNat 2 x.natAbs : ℤ) -
      (padicValNat 2 y.natAbs : ℤ), ?_⟩
    rw [mul_sub]
    linarith
  have hdvdNat : k ∣ 2 := Int.natCast_dvd_natCast.mp hdvdInt
  have hk_le : k ≤ 2 := Nat.le_of_dvd (by norm_num) hdvdNat
  omega

variable {α : Type*} [DecidableEq α]

noncomputable def factor (j : α → ℤ) (e : α) : Polynomial ℤ := X - C (j e)

noncomputable def W (S : Finset α) (j : α → ℤ) : Polynomial ℤ :=
  ∏ e ∈ S, factor j e

noncomputable def Wexcept (S : Finset α) (j : α → ℤ) (e : α) : Polynomial ℤ :=
  ∏ l ∈ S.erase e, factor j l

def D (S : Finset α) (j : α → ℤ) (e : α) : ℤ :=
  ∏ l ∈ S.erase e, (j e - j l)

lemma eval_factor (j : α → ℤ) (e l : α) :
    (factor j l).eval (j e) = j e - j l := by simp [factor]

lemma W_eq_factor_mul_except {S : Finset α} {j : α → ℤ} {e : α}
    (he : e ∈ S) : W S j = factor j e * Wexcept S j e := by
  rw [W, Wexcept, ← Finset.mul_prod_erase _ _ he]

lemma derivative_eval_W {S : Finset α} {j : α → ℤ} {e : α}
    (he : e ∈ S) : (W S j).derivative.eval (j e) = D S j e := by
  rw [W_eq_factor_mul_except he, derivative_mul, eval_add, eval_mul, eval_mul]
  simp [factor, Wexcept, D, Polynomial.eval_prod, eval_factor]

lemma derivative_eval_except {S : Finset α} {j : α → ℤ} {e l : α}
    (he : e ∈ S) (hl : l ∈ S) (hne : l ≠ e) :
    (Wexcept S j l).derivative.eval (j e) =
      ∏ q ∈ (S.erase l).erase e, (j e - j q) := by
  have he' : e ∈ S.erase l := Finset.mem_erase.mpr ⟨hne.symm, he⟩
  change (derivative (∏ q ∈ S.erase l, factor j q)).eval (j e) = _
  rw [← Finset.mul_prod_erase (S.erase l) (fun q => factor j q) he']
  rw [derivative_mul, eval_add, eval_mul, eval_mul]
  simp [factor, Polynomial.eval_prod, eval_factor]

noncomputable def V (S : Finset α) (j : α → ℤ) (w : α → ℤ) : Polynomial ℤ :=
  ∑ e ∈ S, C (w e) * Wexcept S j e

noncomputable def U (S : Finset α) (j rho w : α → ℤ) (c : ℤ) : Polynomial ℤ :=
  C c * W S j + ∑ e ∈ S, C (w e * rho e) * Wexcept S j e

lemma eval_W_at_node {S : Finset α} {j : α → ℤ} {e : α} (he : e ∈ S) :
    (W S j).eval (j e) = 0 := by
  rw [W_eq_factor_mul_except he, eval_mul]
  simp [factor]

lemma eval_Wexcept_other {S : Finset α} {j : α → ℤ} {e l : α}
    (he : e ∈ S) (hne : e ≠ l) :
    (Wexcept S j l).eval (j e) = 0 := by
  have he' : e ∈ S.erase l := Finset.mem_erase.mpr ⟨hne, he⟩
  rw [Wexcept, Polynomial.eval_prod]
  apply Finset.prod_eq_zero he'
  simp [factor]

lemma eval_V_at_node {S : Finset α} {j : α → ℤ} {w : α → ℤ} {e : α}
    (he : e ∈ S) : (V S j w).eval (j e) = w e * D S j e := by
  rw [V, Polynomial.eval_finset_sum]
  rw [Finset.sum_eq_single e]
  · simp [Wexcept, D, Polynomial.eval_prod, factor]
  · intro l hl hle
    simp [eval_Wexcept_other he hle.symm]
  · simp [he]

lemma eval_U_at_node {S : Finset α} {j rho w : α → ℤ} {c : ℤ} {e : α}
    (he : e ∈ S) : (U S j rho w c).eval (j e) = rho e * (V S j w).eval (j e) := by
  rw [eval_V_at_node he]
  rw [U, eval_add, eval_mul, Polynomial.eval_finset_sum, eval_W_at_node he]
  simp only [eval_C, zero_mul, zero_add]
  rw [Finset.sum_eq_single e]
  · simp [Wexcept, D, Polynomial.eval_prod, factor]
    ring
  · intro l hl hle
    simp [eval_Wexcept_other he hle.symm]
  · simp [he]

def pairDerivativeProduct (S : Finset α) (j : α → ℤ) (e l : α) : ℤ :=
  ∏ q ∈ (S.erase l).erase e, (j e - j q)

/-- Clearing the denominator `j_e-j_l` in the barycentric derivative formula
produces exactly `pairDerivativeProduct`. -/
lemma nodeDifference_mul_pairDerivativeProduct {S : Finset α} {j : α → ℤ}
    {e l : α} (he : e ∈ S) (hl : l ∈ S) (hne : l ≠ e) :
    (j e - j l) * pairDerivativeProduct S j e l = D S j e := by
  have hl' : l ∈ S.erase e := Finset.mem_erase.mpr ⟨hne, hl⟩
  rw [D, ← Finset.mul_prod_erase (S.erase e) (fun q => j e - j q) hl']
  congr 1
  unfold pairDerivativeProduct
  apply congrArg (fun T : Finset α => ∏ q ∈ T, (j e - j q))
  ext q
  simp only [Finset.mem_erase]
  aesop

lemma factor_monic (j : α → ℤ) (e : α) : (factor j e).Monic := by
  exact Polynomial.monic_X_sub_C (j e)

lemma W_monic (S : Finset α) (j : α → ℤ) : (W S j).Monic := by
  apply Polynomial.monic_prod_of_monic
  intro e he
  exact factor_monic j e

lemma W_natDegree (S : Finset α) (j : α → ℤ) :
    (W S j).natDegree = S.card := by
  rw [W, Polynomial.natDegree_prod_of_monic]
  · calc
      (∑ e ∈ S, (factor j e).natDegree) = ∑ e ∈ S, 1 := by
        apply Finset.sum_congr rfl
        intro e he
        exact Polynomial.natDegree_X_sub_C (j e)
      _ = S.card := by simp
  · intro e he
    exact factor_monic j e

lemma Wexcept_monic (S : Finset α) (j : α → ℤ) (e : α) :
    (Wexcept S j e).Monic := by
  apply Polynomial.monic_prod_of_monic
  intro l hl
  exact factor_monic j l

lemma Wexcept_natDegree (S : Finset α) (j : α → ℤ) (e : α) :
    (Wexcept S j e).natDegree = (S.erase e).card := by
  rw [Wexcept, Polynomial.natDegree_prod_of_monic]
  · calc
      (∑ l ∈ S.erase e, (factor j l).natDegree) = ∑ l ∈ S.erase e, 1 := by
        apply Finset.sum_congr rfl
        intro l hl
        exact Polynomial.natDegree_X_sub_C (j l)
      _ = (S.erase e).card := by simp
  · intro l hl
    exact factor_monic j l

lemma V_natDegree_le_card_sub_one {S : Finset α} (hS : S.Nonempty)
    (j w : α → ℤ) : (V S j w).natDegree ≤ S.card - 1 := by
  rw [V]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro e he
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  rw [Wexcept_natDegree, Finset.card_erase_of_mem he]

lemma U_natDegree_le_card (S : Finset α) (j rho w : α → ℤ) (c : ℤ) :
    (U S j rho w c).natDegree ≤ S.card := by
  rw [U]
  apply Polynomial.natDegree_add_le_of_degree_le
  · exact (Polynomial.natDegree_C_mul_le _ _).trans_eq (W_natDegree S j)
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro e he
    refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    rw [Wexcept_natDegree, Finset.card_erase_of_mem he]
    omega

lemma W_coeff_card (S : Finset α) (j : α → ℤ) :
    (W S j).coeff S.card = 1 := by
  rw [← W_natDegree S j]
  exact (W_monic S j).coeff_natDegree

lemma Wexcept_coeff_card_sub_one {S : Finset α} {e : α} (he : e ∈ S)
    (j : α → ℤ) : (Wexcept S j e).coeff (S.card - 1) = 1 := by
  rw [← Finset.card_erase_of_mem he, ← Wexcept_natDegree]
  exact (Wexcept_monic S j e).coeff_natDegree

lemma coeff_finset_sum (S : Finset α) (f : α → Polynomial ℤ) (n : ℕ) :
    (∑ e ∈ S, f e).coeff n = ∑ e ∈ S, (f e).coeff n := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert e S he ih => simp [he, ih]

lemma U_coeff_card (S : Finset α) (j rho w : α → ℤ) (c : ℤ) :
    (U S j rho w c).coeff S.card = c := by
  rw [U, coeff_add, coeff_C_mul, W_coeff_card]
  simp only [mul_one]
  have hzero :
      (∑ e ∈ S, C (w e * rho e) * Wexcept S j e).coeff S.card = 0 := by
    rw [coeff_finset_sum]
    apply Finset.sum_eq_zero
    intro e he
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    refine (Polynomial.natDegree_C_mul_le _ _).trans_lt ?_
    rw [Wexcept_natDegree, Finset.card_erase_of_mem he]
    exact Nat.sub_lt (Finset.card_pos.mpr ⟨e, he⟩) (by norm_num)
  rw [hzero, add_zero]

lemma V_coeff_card_sub_one {S : Finset α} (hS : S.Nonempty)
    (j w : α → ℤ) :
    (V S j w).coeff (S.card - 1) = ∑ e ∈ S, w e := by
  rw [V, coeff_finset_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [coeff_C_mul, Wexcept_coeff_card_sub_one he]
  simp

def finNode {k : ℕ} (h : Fin k) : ℤ := (h.val : ℤ) + 1

noncomputable def matchingPhi (k : ℕ) (U V : Polynomial ℤ) : Polynomial ℤ :=
  (Finset.univ : Finset (Fin k)).prod
      (fun h => U + (X + C (finNode h)) * V) -
    C 4 * (Finset.univ : Finset (Fin k)).prod
      (fun h => (X + C (finNode h)) * V)

lemma affine_mul_coeff_succ {P : Polynomial ℤ} {m : ℕ} (hdeg : P.natDegree ≤ m) (a : ℤ) :
    ((X + C a) * P).coeff (m + 1) = P.coeff m := by
  rw [add_mul, coeff_add, Polynomial.coeff_X_mul, coeff_C_mul]
  have hz : P.coeff (m + 1) = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg (Nat.lt_succ_self m))
  rw [hz]
  simp

lemma affine_mul_natDegree_le_succ {P : Polynomial ℤ} {m : ℕ} (hdeg : P.natDegree ≤ m)
    (a : ℤ) : ((X + C a) * P).natDegree ≤ m + 1 := by
  refine Polynomial.natDegree_mul_le.trans ?_
  rw [Polynomial.natDegree_X_add_C]
  omega

lemma matchingPhi_coeff_mul {k m : ℕ} {U V : Polynomial ℤ}
    (hm : 1 ≤ m) (hU : U.natDegree ≤ m) (hV : V.natDegree ≤ m - 1) :
    (matchingPhi k U V).coeff (k * m) =
      (U.coeff m + V.coeff (m - 1)) ^ k - 4 * (V.coeff (m - 1)) ^ k := by
  let A : Fin k → Polynomial ℤ := fun h => U + (X + C (finNode h)) * V
  let B : Fin k → Polynomial ℤ := fun h => (X + C (finNode h)) * V
  have hVm : V.natDegree ≤ m - 1 := hV
  have hmEq : (m - 1) + 1 = m := by omega
  have hBdeg : ∀ h : Fin k, (B h).natDegree ≤ m := by
    intro h
    unfold B
    simpa [hmEq] using affine_mul_natDegree_le_succ hVm (finNode h)
  have hAdeg : ∀ h : Fin k, (A h).natDegree ≤ m := by
    intro h
    unfold A
    exact Polynomial.natDegree_add_le_of_degree_le hU (hBdeg h)
  have hBcoeff : ∀ h : Fin k, (B h).coeff m = V.coeff (m - 1) := by
    intro h
    unfold B
    simpa [hmEq] using affine_mul_coeff_succ hVm (finNode h)
  have hAcoeff : ∀ h : Fin k,
      (A h).coeff m = U.coeff m + V.coeff (m - 1) := by
    intro h
    unfold A
    rw [coeff_add, hBcoeff]
  have hprodA := Polynomial.coeff_prod_of_natDegree_le
    (s := (Finset.univ : Finset (Fin k))) A m (by simpa using hAdeg)
  have hprodB := Polynomial.coeff_prod_of_natDegree_le
    (s := (Finset.univ : Finset (Fin k))) B m (by simpa using hBdeg)
  simp only [Finset.card_univ, Fintype.card_fin] at hprodA hprodB
  rw [matchingPhi, coeff_sub, coeff_C_mul]
  change ((Finset.univ : Finset (Fin k)).prod A).coeff (k * m) -
      4 * ((Finset.univ : Finset (Fin k)).prod B).coeff (k * m) = _
  rw [hprodA, hprodB]
  simp [hAcoeff, hBcoeff]

lemma matchingPhi_natDegree_le_mul {k m : ℕ} {U V : Polynomial ℤ}
    (hm : 1 ≤ m) (hU : U.natDegree ≤ m) (hV : V.natDegree ≤ m - 1) :
    (matchingPhi k U V).natDegree ≤ k * m := by
  let A : Fin k → Polynomial ℤ := fun h => U + (X + C (finNode h)) * V
  let B : Fin k → Polynomial ℤ := fun h => (X + C (finNode h)) * V
  have hmEq : (m - 1) + 1 = m := by omega
  have hBdeg : ∀ h : Fin k, (B h).natDegree ≤ m := by
    intro h
    unfold B
    simpa [hmEq] using affine_mul_natDegree_le_succ hV (finNode h)
  have hAdeg : ∀ h : Fin k, (A h).natDegree ≤ m := by
    intro h
    unfold A
    exact Polynomial.natDegree_add_le_of_degree_le hU (hBdeg h)
  have hprodA : ((Finset.univ : Finset (Fin k)).prod A).natDegree ≤ k * m := by
    refine (Polynomial.natDegree_prod_le (Finset.univ : Finset (Fin k)) A).trans ?_
    calc
      (∑ h ∈ (Finset.univ : Finset (Fin k)), (A h).natDegree) ≤
          ∑ h ∈ (Finset.univ : Finset (Fin k)), m := by
            apply Finset.sum_le_sum
            intro h hh
            exact hAdeg h
      _ = k * m := by simp
  have hprodB : ((Finset.univ : Finset (Fin k)).prod B).natDegree ≤ k * m := by
    refine (Polynomial.natDegree_prod_le (Finset.univ : Finset (Fin k)) B).trans ?_
    calc
      (∑ h ∈ (Finset.univ : Finset (Fin k)), (B h).natDegree) ≤
          ∑ h ∈ (Finset.univ : Finset (Fin k)), m := by
            apply Finset.sum_le_sum
            intro h hh
            exact hBdeg h
      _ = k * m := by simp
  have hsub := Polynomial.natDegree_sub_le_of_le hprodA
    ((Polynomial.natDegree_C_mul_le (4 : ℤ) _).trans hprodB)
  change ((Finset.univ : Finset (Fin k)).prod A -
    C 4 * (Finset.univ : Finset (Fin k)).prod B).natDegree ≤ k * m
  simpa using hsub

lemma pow_sub_four_pow_eq_zero_iff {c v : ℤ} {k : ℕ} (hk : 3 ≤ k) :
    (c + v) ^ k - 4 * v ^ k = 0 ↔ c = 0 ∧ v = 0 := by
  constructor
  · intro h
    have hp : (c + v) ^ k = 4 * v ^ k := sub_eq_zero.mp h
    obtain ⟨hcv, hv⟩ := pow_eq_four_mul_pow_zero hk hp
    constructor
    · linarith
    · exact hv
  · rintro ⟨rfl, rfl⟩
    simp [show k ≠ 0 by omega]

lemma barycentric_matchingPhi_coeff {S : Finset α} (hS : S.Nonempty)
    (j rho w : α → ℤ) (c : ℤ) (k : ℕ) :
    (matchingPhi k (U S j rho w c) (V S j w)).coeff (k * S.card) =
      (c + ∑ e ∈ S, w e) ^ k - 4 * (∑ e ∈ S, w e) ^ k := by
  have hm : 1 ≤ S.card := Finset.one_le_card.mpr hS
  rw [matchingPhi_coeff_mul hm (U_natDegree_le_card S j rho w c)
      (V_natDegree_le_card_sub_one hS j w),
    U_coeff_card, V_coeff_card_sub_one hS]

lemma barycentric_matchingPhi_coeff_eq_zero_iff {S : Finset α} (hS : S.Nonempty)
    (j rho w : α → ℤ) (c : ℤ) {k : ℕ} (hk : 3 ≤ k) :
    (matchingPhi k (U S j rho w c) (V S j w)).coeff (k * S.card) = 0 ↔
      c = 0 ∧ (∑ e ∈ S, w e) = 0 := by
  rw [barycentric_matchingPhi_coeff hS, pow_sub_four_pow_eq_zero_iff hk]

lemma U_zero_natDegree_le_card_sub_one {S : Finset α} (hS : S.Nonempty)
    (j rho w : α → ℤ) : (U S j rho w 0).natDegree ≤ S.card - 1 := by
  rw [U]
  simp only [map_zero, zero_mul, zero_add]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro e he
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  rw [Wexcept_natDegree, Finset.card_erase_of_mem he]

lemma V_natDegree_le_card_sub_two {S : Finset α} (hcard : 2 ≤ S.card)
    (j w : α → ℤ) (hv : (∑ e ∈ S, w e) = 0) :
    (V S j w).natDegree ≤ S.card - 2 := by
  have hS : S.Nonempty := Finset.card_pos.mp (by omega)
  have htop : (V S j w).coeff (S.card - 1) = 0 := by
    rw [V_coeff_card_sub_one hS, hv]
  have hpred := Polynomial.natDegree_le_pred
    (V_natDegree_le_card_sub_one hS j w) htop
  convert hpred using 1 <;> omega

lemma barycentric_matchingPhi_natDegree_le {S : Finset α} (hS : S.Nonempty)
    (j rho w : α → ℤ) (c : ℤ) (k : ℕ) :
    (matchingPhi k (U S j rho w c) (V S j w)).natDegree ≤ k * S.card := by
  exact matchingPhi_natDegree_le_mul (Finset.one_le_card.mpr hS)
    (U_natDegree_le_card S j rho w c) (V_natDegree_le_card_sub_one hS j w)

lemma barycentric_matchingPhi_zero_branch_natDegree_le {S : Finset α}
    (hcard : 2 ≤ S.card) (j rho w : α → ℤ)
    (hv : (∑ e ∈ S, w e) = 0) (k : ℕ) :
    (matchingPhi k (U S j rho w 0) (V S j w)).natDegree ≤ k * (S.card - 1) := by
  have hS : S.Nonempty := Finset.card_pos.mp (by omega)
  have hm : 1 ≤ S.card - 1 := by omega
  apply matchingPhi_natDegree_le_mul hm
  · exact U_zero_natDegree_le_card_sub_one hS j rho w
  · convert V_natDegree_le_card_sub_two hcard j w hv using 1 <;> omega

lemma barycentric_quotient_natDegree_nonzero_branch {S : Finset α} (hS : S.Nonempty)
    (j rho w : α → ℤ) (c : ℤ) {k : ℕ} (hk : 3 ≤ k) (Q : Polynomial ℤ)
    (hcv : c ≠ 0 ∨ (∑ e ∈ S, w e) ≠ 0)
    (hfactor : matchingPhi k (U S j rho w c) (V S j w) = (W S j) ^ 2 * Q) :
    Q.natDegree = S.card * (k - 2) := by
  let Phi := matchingPhi k (U S j rho w c) (V S j w)
  have hcoef : Phi.coeff (k * S.card) ≠ 0 := by
    intro hz
    have hz' := (barycentric_matchingPhi_coeff_eq_zero_iff hS j rho w c hk).mp hz
    exact hcv.elim (fun hc => hc hz'.1) (fun hv => hv hz'.2)
  have hPhiDeg : Phi.natDegree = k * S.card :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
      (barycentric_matchingPhi_natDegree_le hS j rho w c k) hcoef
  have hWne : W S j ≠ 0 := (W_monic S j).ne_zero
  have hQne : Q ≠ 0 := by
    intro hQ
    subst Q
    rw [mul_zero] at hfactor
    have hPhiZero : Phi = 0 := by
      dsimp [Phi]
      exact hfactor
    rw [hPhiZero] at hcoef
    exact hcoef (by simp)
  have hdegFactor : Phi.natDegree = 2 * S.card + Q.natDegree := by
    dsimp [Phi]
    rw [hfactor, Polynomial.natDegree_mul (pow_ne_zero 2 hWne) hQne,
      Polynomial.natDegree_pow, W_natDegree]
  have heq : k * S.card = 2 * S.card + Q.natDegree := by
    rw [← hPhiDeg, hdegFactor]
  have hsub : Q.natDegree = (k - 2) * S.card := by
    have hsum : Q.natDegree + 2 * S.card = k * S.card := by omega
    calc
      Q.natDegree = k * S.card - 2 * S.card := Nat.eq_sub_of_add_eq hsum
      _ = (k - 2) * S.card := (Nat.sub_mul k 2 S.card).symm
  simpa [Nat.mul_comm] using hsub

lemma zero_branch_degree_arithmetic {q m k : ℕ} (hm : 2 ≤ m) (hk : 4 ≤ k)
    (h : q + 2 * m ≤ k * (m - 1)) : q ≤ m * (k - 2) - k := by
  apply Nat.le_sub_of_add_le
  have hmEq : m - 1 + 1 = m := by omega
  have hkEq : k - 2 + 2 = k := by omega
  have hleft : q + k + 2 * m ≤ k * m := by
    calc
      q + k + 2 * m = q + 2 * m + k := by omega
      _ ≤ k * (m - 1) + k := Nat.add_le_add_right h k
      _ = k * (m - 1) + k * 1 := by simp
      _ = k * ((m - 1) + 1) := (Nat.mul_add _ _ _).symm
      _ = k * m := by rw [hmEq]
  have hright : m * (k - 2) + 2 * m = k * m := by
    calc
      m * (k - 2) + 2 * m = m * ((k - 2) + 2) := by ring
      _ = m * k := by rw [hkEq]
      _ = k * m := Nat.mul_comm _ _
  apply Nat.le_of_add_le_add_right (b := 2 * m)
  rw [hright]
  exact hleft

lemma barycentric_quotient_natDegree_zero_branch {S : Finset α}
    (hcard : 2 ≤ S.card) (j rho w : α → ℤ) {k : ℕ} (hk : 4 ≤ k)
    (hv : (∑ e ∈ S, w e) = 0) (Q : Polynomial ℤ)
    (hfactor : matchingPhi k (U S j rho w 0) (V S j w) = (W S j) ^ 2 * Q) :
    Q.natDegree ≤ S.card * (k - 2) - k := by
  by_cases hQ : Q = 0
  · subst Q
    simp
  have hWne : W S j ≠ 0 := (W_monic S j).ne_zero
  have hdegree : 2 * S.card + Q.natDegree ≤ k * (S.card - 1) := by
    have hPhi := barycentric_matchingPhi_zero_branch_natDegree_le
      hcard j rho w hv k
    rw [hfactor, Polynomial.natDegree_mul (pow_ne_zero 2 hWne) hQ,
      Polynomial.natDegree_pow, W_natDegree] at hPhi
    exact hPhi
  apply zero_branch_degree_arithmetic hcard hk
  omega

lemma derivative_defect_at_node {S : Finset α} {j rho w : α → ℤ} {c : ℤ} {e : α}
    (he : e ∈ S) :
    ((U S j rho w c).derivative - C (rho e) * (V S j w).derivative).eval (j e) =
      c * D S j e +
        ∑ l ∈ S.erase e, w l * (rho l - rho e) * pairDerivativeProduct S j e l := by
  have hpoly :
      U S j rho w c - C (rho e) * V S j w =
        C c * W S j +
          ∑ l ∈ S, C (w l * (rho l - rho e)) * Wexcept S j l := by
    simp [U, V, Finset.mul_sum]
    rw [add_sub_assoc, ← Finset.sum_sub_distrib]
    apply congrArg (fun z => C c * W S j + z)
    apply Finset.sum_congr rfl
    intro l hl
    push_cast
    ring
  have hderiv :
      (U S j rho w c).derivative - C (rho e) * (V S j w).derivative =
        (U S j rho w c - C (rho e) * V S j w).derivative := by
    simp
  rw [hderiv, hpoly]
  simp only [derivative_add, derivative_mul, derivative_C, zero_mul, add_zero,
    derivative_sum, eval_add, eval_mul, Polynomial.eval_finset_sum, eval_C]
  rw [derivative_eval_W he]
  rw [Finset.sum_eq_add_sum_diff_singleton e _ (by simp [he])]
  simp only [Finset.sdiff_singleton_eq_erase]
  simp only [eval_zero, zero_add]
  have hself : w e * (rho e - rho e) *
      (Wexcept S j e).derivative.eval (j e) = 0 := by ring
  rw [hself, zero_add]
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  have hlS : l ∈ S := Finset.mem_of_mem_erase hl
  have hle : l ≠ e := Finset.ne_of_mem_erase hl
  rw [derivative_eval_except he hlS hle]
  simp [pairDerivativeProduct]

/-- Exact denominator-cleared form of the imported derivative system.  If
`D_j` is subsequently inverted, this is
`b_j(c + sum_{l != j} w_l(rho_l-rho_j)/(j-l)) = A_j w_j`. -/
theorem barycentric_derivative_system_iff {S : Finset α} {j rho w : α → ℤ}
    {c b A : ℤ} {e : α} (he : e ∈ S) :
    b * ((U S j rho w c).derivative -
        C (rho e) * (V S j w).derivative).eval (j e) =
          A * (V S j w).eval (j e) ↔
      b * (c * D S j e +
        ∑ l ∈ S.erase e,
          w l * (rho l - rho e) * pairDerivativeProduct S j e l) =
        A * w e * D S j e := by
  rw [derivative_defect_at_node he, eval_V_at_node he]
  ring_nf

/-! ## The root identity

The next theorem is the exact rational identity obtained from a root of
`U(T) + d V(T)`.  Distinctness of the interpolation nodes is relevant to the
barycentric construction, but no division by a node difference occurs here:
the only denominators are `n + j_e`.
-/

theorem barycentric_root_identity {S : Finset α} {j rho w : α → ℤ}
    {c d n : ℤ}
    (hden : ∀ e ∈ S, n + j e ≠ 0)
    (hroot : (U S j rho w c).eval (-n) +
      d * (V S j w).eval (-n) = 0) :
    (c : ℚ) = ∑ e ∈ S,
      ((w e : ℚ) * ((d : ℚ) + rho e)) / ((n : ℚ) + j e) := by
  have hWne : (W S j).eval (-n) ≠ 0 := by
    rw [W, Polynomial.eval_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro e he
    simp only [factor, eval_sub, eval_X, eval_C]
    intro hz
    apply hden e he
    omega
  have hroot' :
      c * (W S j).eval (-n) +
        ∑ e ∈ S, w e * (rho e + d) * (Wexcept S j e).eval (-n) = 0 := by
    rw [U, V] at hroot
    simp only [eval_add, eval_mul, eval_C, Polynomial.eval_finset_sum] at hroot
    rw [Finset.mul_sum] at hroot
    calc
      c * (W S j).eval (-n) +
          ∑ e ∈ S, w e * (rho e + d) * (Wexcept S j e).eval (-n) =
          c * (W S j).eval (-n) +
            ((∑ e ∈ S, w e * rho e * (Wexcept S j e).eval (-n)) +
             ∑ e ∈ S, d * (w e * (Wexcept S j e).eval (-n))) := by
              congr 1
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro e he
              ring
      _ = (c * (W S j).eval (-n) +
            ∑ e ∈ S, w e * rho e * (Wexcept S j e).eval (-n)) +
             ∑ e ∈ S, d * (w e * (Wexcept S j e).eval (-n)) := by ring
      _ = 0 := hroot
  have hterm : ∀ e ∈ S,
      (w e : ℚ) * ((rho e : ℚ) + d) *
          (((Wexcept S j e).eval (-n) : ℤ) : ℚ) /
          (((W S j).eval (-n) : ℤ) : ℚ) =
        -(((w e : ℚ) * ((d : ℚ) + rho e)) / ((n : ℚ) + j e)) := by
    intro e he
    have hfactorRaw := congrArg (fun P : Polynomial ℤ => P.eval (-n))
      (W_eq_factor_mul_except (j := j) he)
    have hfactor : (W S j).eval (-n) =
        (factor j e).eval (-n) * (Wexcept S j e).eval (-n) := by
      simpa only [eval_mul] using hfactorRaw
    simp only [eval_mul, factor, eval_sub, eval_X, eval_C] at hfactor
    have hExceptNe : (Wexcept S j e).eval (-n) ≠ 0 := by
      intro hz
      rw [hfactor, hz, mul_zero] at hWne
      exact hWne rfl
    have hdenQ : (n : ℚ) + j e ≠ 0 := by
      exact_mod_cast hden e he
    rw [hfactor]
    push_cast
    rw [show -(n : ℚ) - (j e : ℚ) = -((n : ℚ) + j e) by ring]
    field_simp [hExceptNe, hdenQ]
    ring
  have hrootQ := congrArg (fun z : ℤ => (z : ℚ)) hroot'
  push_cast at hrootQ
  have hWneQ : (((W S j).eval (-n) : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hWne
  have hdiv := congrArg
    (fun z : ℚ => z / (((W S j).eval (-n) : ℤ) : ℚ)) hrootQ
  simp only [zero_div] at hdiv
  rw [add_div, mul_div_cancel_right₀ _ hWneQ, Finset.sum_div] at hdiv
  have hsum :
      (∑ e ∈ S, (w e : ℚ) * ((rho e : ℚ) + d) *
          (((Wexcept S j e).eval (-n) : ℤ) : ℚ) /
            (((W S j).eval (-n) : ℤ) : ℚ)) =
        ∑ e ∈ S, -(((w e : ℚ) * ((d : ℚ) + rho e)) /
          ((n : ℚ) + j e)) := by
    apply Finset.sum_congr rfl
    intro e he
    exact hterm e he
  rw [hsum] at hdiv
  rw [Finset.sum_neg_distrib] at hdiv
  linarith

/-- A single support fraction differs from `d/n` by less than the uniform
`(2k-1)/(n+1)` envelope.  This is the exact estimate behind both root
bounds; it uses only `0 ≤ d < n`, `1 ≤ j ≤ k`, and `|rho| ≤ k-1`. -/
lemma support_fraction_deviation_bound {n d j rho k : ℚ}
    (hn : 0 < n) (hd : 0 ≤ d) (hdn : d < n)
    (hj1 : 1 ≤ j) (hjk : j ≤ k) (hrho : |rho| ≤ k - 1) :
    |(d + rho) / (n + j) - d / n| < (2 * k - 1) / (n + 1) := by
  have hk : 0 < k := lt_of_lt_of_le (by norm_num) (hj1.trans hjk)
  have hj : 0 < j := lt_of_lt_of_le (by norm_num) hj1
  have hnp1 : 0 < n + 1 := by linarith
  have hnj : 0 < n + j := by linarith
  have hden : 0 < n * (n + j) := mul_pos hn hnj
  have hid : (d + rho) / (n + j) - d / n =
      (n * rho - d * j) / (n * (n + j)) := by
    field_simp
    ring
  rw [hid, abs_div, abs_of_pos hden]
  rw [div_lt_div_iff₀ hden hnp1]
  have habs : |n * rho - d * j| < n * (2 * k - 1) := by
    calc
      |n * rho - d * j| ≤ |n * rho| + |d * j| := abs_sub _ _
      _ = n * |rho| + d * j := by
        rw [abs_mul, abs_mul, abs_of_pos hn, abs_of_nonneg hd, abs_of_pos hj]
      _ ≤ n * (k - 1) + d * k := by
        gcongr
      _ < n * (k - 1) + n * k := by
        gcongr
      _ = n * (2 * k - 1) := by ring
  calc
    |n * rho - d * j| * (n + 1) <
        (n * (2 * k - 1)) * (n + 1) := by
          gcongr
    _ = (2 * k - 1) * (n * (n + 1)) := by ring
    _ ≤ (2 * k - 1) * (n * (n + j)) := by
      have hA : 0 ≤ 2 * k - 1 := by linarith
      apply mul_le_mul_of_nonneg_left _ hA
      apply mul_le_mul_of_nonneg_left _ hn.le
      linarith

/-- The barycentric root is within the weighted support envelope of `d/n`.
The explicit nonzero-weight witness is what makes the conclusion strict. -/
theorem barycentric_weighted_root_deviation {S : Finset α}
    {j rho w : α → ℤ} {c d n k : ℤ}
    (hn : (0 : ℚ) < n) (hd : (0 : ℚ) ≤ d) (hdn : (d : ℚ) < n)
    (hj1 : ∀ e ∈ S, (1 : ℚ) ≤ j e)
    (hjk : ∀ e ∈ S, (j e : ℚ) ≤ k)
    (hrho : ∀ e ∈ S, |(rho e : ℚ)| ≤ (k : ℚ) - 1)
    (hweight : ∃ e ∈ S, w e ≠ 0)
    (hroot : (U S j rho w c).eval (-n) +
      d * (V S j w).eval (-n) = 0) :
    |(c : ℚ) - ((∑ e ∈ S, w e : ℤ) : ℚ) * ((d : ℚ) / n)| <
      ((2 * (k : ℚ) - 1) / ((n : ℚ) + 1)) *
        ∑ e ∈ S, |(w e : ℚ)| := by
  have hden : ∀ e ∈ S, n + j e ≠ 0 := by
    intro e he
    have : (0 : ℚ) < (n : ℚ) + j e := by linarith [hj1 e he]
    exact_mod_cast this.ne'
  have hid := barycentric_root_identity (S := S) (j := j) (rho := rho)
    (w := w) (c := c) (d := d) (n := n) hden hroot
  let f : α → ℚ := fun e =>
    ((d : ℚ) + rho e) / ((n : ℚ) + j e)
  let B : ℚ := (2 * (k : ℚ) - 1) / ((n : ℚ) + 1)
  have hrewrite :
      (c : ℚ) - ((∑ e ∈ S, w e : ℤ) : ℚ) * ((d : ℚ) / n) =
        ∑ e ∈ S, (w e : ℚ) * (f e - (d : ℚ) / n) := by
    rw [hid]
    push_cast
    rw [Finset.sum_mul]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro e he
    dsimp [f]
    ring
  rw [hrewrite]
  calc
    |∑ e ∈ S, (w e : ℚ) * (f e - (d : ℚ) / n)| ≤
        ∑ e ∈ S, |(w e : ℚ) * (f e - (d : ℚ) / n)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ e ∈ S, |(w e : ℚ)| * |f e - (d : ℚ) / n| := by
      apply Finset.sum_congr rfl
      intro e he
      rw [abs_mul]
    _ < ∑ e ∈ S, |(w e : ℚ)| * B := by
      apply Finset.sum_lt_sum
      · intro e he
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        exact (support_fraction_deviation_bound hn hd hdn
          (hj1 e he) (hjk e he) (hrho e he)).le
      · obtain ⟨e, he, hwe⟩ := hweight
        refine ⟨e, he, ?_⟩
        apply mul_lt_mul_of_pos_left _ (abs_pos.mpr ?_)
        · exact support_fraction_deviation_bound hn hd hdn
            (hj1 e he) (hjk e he) (hrho e he)
        · exact_mod_cast hwe
    _ = B * ∑ e ∈ S, |(w e : ℚ)| := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      ring

/-- If the total barycentric weight vanishes but `c` does not, the root is
uniformly bounded.  This is the exact support-dependent alternative requested
in the imported package. -/
theorem barycentric_zero_total_weight_root_bound {S : Finset α}
    {j rho w : α → ℤ} {c d n k : ℤ}
    (hn : (0 : ℚ) < n) (hd : (0 : ℚ) ≤ d) (hdn : (d : ℚ) < n)
    (hj1 : ∀ e ∈ S, (1 : ℚ) ≤ j e)
    (hjk : ∀ e ∈ S, (j e : ℚ) ≤ k)
    (hrho : ∀ e ∈ S, |(rho e : ℚ)| ≤ (k : ℚ) - 1)
    (hv : (∑ e ∈ S, w e) = 0) (hc : c ≠ 0)
    (hroot : (U S j rho w c).eval (-n) +
      d * (V S j w).eval (-n) = 0) :
    (n : ℚ) + 1 <
      ((2 * (k : ℚ) - 1) * ∑ e ∈ S, |(w e : ℚ)|) / |(c : ℚ)| := by
  have hden : ∀ e ∈ S, n + j e ≠ 0 := by
    intro e he
    have : (0 : ℚ) < (n : ℚ) + j e := by linarith [hj1 e he]
    exact_mod_cast this.ne'
  have hid := barycentric_root_identity (S := S) (j := j) (rho := rho)
    (w := w) (c := c) (d := d) (n := n) hden hroot
  have hweight : ∃ e ∈ S, w e ≠ 0 := by
    by_contra hex
    simp only [not_exists, not_and] at hex
    have hall : ∀ e ∈ S, w e = 0 := by
      intro e he
      exact not_ne_iff.mp (hex e he)
    have hsumzero : (∑ e ∈ S,
        ((w e : ℚ) * ((d : ℚ) + rho e)) / ((n : ℚ) + j e)) = 0 := by
      apply Finset.sum_eq_zero
      intro e he
      rw [hall e he]
      simp
    rw [hsumzero] at hid
    exact hc (by exact_mod_cast hid)
  have hdev := barycentric_weighted_root_deviation
    (S := S) (j := j) (rho := rho) (w := w)
    (c := c) (d := d) (n := n) (k := k)
    hn hd hdn hj1 hjk hrho hweight hroot
  rw [hv] at hdev
  norm_num at hdev
  have hnp1 : (0 : ℚ) < (n : ℚ) + 1 := by linarith
  have hcabs : (0 : ℚ) < |(c : ℚ)| := abs_pos.mpr (by exact_mod_cast hc)
  rw [lt_div_iff₀ hcabs]
  have hmul := mul_lt_mul_of_pos_left hdev hnp1
  calc
    ((n : ℚ) + 1) * |(c : ℚ)| <
        ((n : ℚ) + 1) *
          (((2 * (k : ℚ) - 1) / ((n : ℚ) + 1)) *
            ∑ e ∈ S, |(w e : ℚ)|) := hmul
    _ = (2 * (k : ℚ) - 1) * ∑ e ∈ S, |(w e : ℚ)| := by
      field_simp

/-- The rational slope singled out by a nonzero total barycentric weight. -/
def barycentricMu (S : Finset α) (w : α → ℤ) (c : ℤ) : ℚ :=
  (c : ℚ) / ((∑ e ∈ S, w e : ℤ) : ℚ)

/-- The normalized `l¹` weight entering the support-dependent root bound. -/
def barycentricKappa (S : Finset α) (w : α → ℤ) : ℚ :=
  (∑ e ∈ S, |(w e : ℚ)|) / |((∑ e ∈ S, w e : ℤ) : ℚ)|

#print axioms derivative_defect_at_node
#print axioms barycentric_derivative_system_iff
#print axioms barycentric_matchingPhi_coeff_eq_zero_iff
#print axioms barycentric_quotient_natDegree_nonzero_branch
#print axioms barycentric_quotient_natDegree_zero_branch
#print axioms barycentric_root_identity
#print axioms support_fraction_deviation_bound
#print axioms barycentric_weighted_root_deviation
#print axioms barycentric_zero_total_weight_root_bound

end Erdos686Variant
end Erdos686
