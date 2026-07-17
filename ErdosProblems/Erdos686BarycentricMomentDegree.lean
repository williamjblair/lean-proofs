/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686BarycentricMomentBlock
import Mathlib.Algebra.Polynomial.Reverse

/-!
# Erdős 686: exact moment reversal and degree ladder

This module closes the reversal interface left abstract in the first corrected
moment package.  It defines the rational barycentric matching polynomial,
uses `Polynomial.reflect` at the declared support degree, and proves that the
first nonzero moment pair gives the exact degrees

`deg Phi = k * (m - q)`

and, after division by the square support polynomial,

`deg Q = m * (k - 2) - q * k`.

The coefficient in total degree `m*k` is not called the leading coefficient.
The proof follows the first nonzero reflected block and therefore remains
valid through every degree-drop branch.
-/

namespace Erdos686
namespace Erdos686Variant

open scoped BigOperators
open Polynomial

variable {α : Type*} [DecidableEq α]

/-! ## Rational forward barycentric polynomials -/

noncomputable def momentForwardFactor (j : α → ℚ) (e : α) : Polynomial ℚ :=
  X - C (j e)

noncomputable def momentForwardW (S : Finset α) (j : α → ℚ) : Polynomial ℚ :=
  ∏ e ∈ S, momentForwardFactor j e

noncomputable def momentForwardWexcept
    (S : Finset α) (j : α → ℚ) (e : α) : Polynomial ℚ :=
  ∏ l ∈ S.erase e, momentForwardFactor j l

noncomputable def momentForwardV
    (S : Finset α) (j w : α → ℚ) : Polynomial ℚ :=
  ∑ e ∈ S, C (w e) * momentForwardWexcept S j e

noncomputable def momentForwardU
    (S : Finset α) (j rho w : α → ℚ) (c : ℚ) : Polynomial ℚ :=
  C c * momentForwardW S j +
    ∑ e ∈ S, C (w e * rho e) * momentForwardWexcept S j e

noncomputable def momentForwardLeftFactor
    (S : Finset α) (j rho w : α → ℚ) (c h : ℚ) : Polynomial ℚ :=
  momentForwardU S j rho w c +
    (X + C h) * momentForwardV S j w

noncomputable def momentForwardRightFactor
    (S : Finset α) (j w : α → ℚ) (h : ℚ) : Polynomial ℚ :=
  (X + C h) * momentForwardV S j w

noncomputable def momentMatchingPhi
    {k : ℕ} (S : Finset α) (j rho w : α → ℚ) (c : ℚ)
    (h : Fin k → ℚ) : Polynomial ℚ :=
  (∏ i : Fin k, momentForwardLeftFactor S j rho w c (h i)) -
    C 4 * (∏ i : Fin k, momentForwardRightFactor S j w (h i))

lemma momentForwardFactor_monic (j : α → ℚ) (e : α) :
    (momentForwardFactor j e).Monic := by
  exact Polynomial.monic_X_sub_C (j e)

lemma momentForwardW_monic (S : Finset α) (j : α → ℚ) :
    (momentForwardW S j).Monic := by
  apply Polynomial.monic_prod_of_monic
  intro e he
  exact momentForwardFactor_monic j e

lemma momentForwardW_natDegree (S : Finset α) (j : α → ℚ) :
    (momentForwardW S j).natDegree = S.card := by
  rw [momentForwardW, Polynomial.natDegree_prod_of_monic]
  · calc
      (∑ e ∈ S, (momentForwardFactor j e).natDegree) =
          ∑ _e ∈ S, 1 := by
        apply Finset.sum_congr rfl
        intro e he
        exact Polynomial.natDegree_X_sub_C (j e)
      _ = S.card := by simp
  · intro e he
    exact momentForwardFactor_monic j e

lemma momentForwardWexcept_monic
    (S : Finset α) (j : α → ℚ) (e : α) :
    (momentForwardWexcept S j e).Monic := by
  apply Polynomial.monic_prod_of_monic
  intro l hl
  exact momentForwardFactor_monic j l

lemma momentForwardWexcept_natDegree
    (S : Finset α) (j : α → ℚ) (e : α) :
    (momentForwardWexcept S j e).natDegree = (S.erase e).card := by
  rw [momentForwardWexcept, Polynomial.natDegree_prod_of_monic]
  · calc
      (∑ l ∈ S.erase e, (momentForwardFactor j l).natDegree) =
          ∑ _l ∈ S.erase e, 1 := by
        apply Finset.sum_congr rfl
        intro l hl
        exact Polynomial.natDegree_X_sub_C (j l)
      _ = (S.erase e).card := by simp
  · intro l hl
    exact momentForwardFactor_monic j l

lemma momentForwardV_natDegree_le_card_sub_one
    {S : Finset α} (hS : S.Nonempty) (j w : α → ℚ) :
    (momentForwardV S j w).natDegree ≤ S.card - 1 := by
  rw [momentForwardV]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro e he
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  rw [momentForwardWexcept_natDegree, Finset.card_erase_of_mem he]

lemma momentForwardU_natDegree_le_card
    (S : Finset α) (j rho w : α → ℚ) (c : ℚ) :
    (momentForwardU S j rho w c).natDegree ≤ S.card := by
  rw [momentForwardU]
  apply Polynomial.natDegree_add_le_of_degree_le
  · exact (Polynomial.natDegree_C_mul_le _ _).trans_eq
      (momentForwardW_natDegree S j)
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro e he
    refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    rw [momentForwardWexcept_natDegree, Finset.card_erase_of_mem he]
    omega

lemma momentForwardRightFactor_natDegree_le_card
    {S : Finset α} (hS : S.Nonempty)
    (j w : α → ℚ) (h : ℚ) :
    (momentForwardRightFactor S j w h).natDegree ≤ S.card := by
  rw [momentForwardRightFactor]
  refine Polynomial.natDegree_mul_le.trans ?_
  rw [Polynomial.natDegree_X_add_C]
  exact Nat.add_le_of_le_sub
    (Finset.one_le_card.mpr hS)
    (momentForwardV_natDegree_le_card_sub_one hS j w)

lemma momentForwardLeftFactor_natDegree_le_card
    {S : Finset α} (hS : S.Nonempty)
    (j rho w : α → ℚ) (c h : ℚ) :
    (momentForwardLeftFactor S j rho w c h).natDegree ≤ S.card := by
  rw [momentForwardLeftFactor]
  exact Polynomial.natDegree_add_le_of_degree_le
    (momentForwardU_natDegree_le_card S j rho w c)
    (momentForwardRightFactor_natDegree_le_card hS j w h)

/-! ## Exact fixed-degree reversal -/

lemma reflect_finset_sum
    (S : Finset α) (f : α → Polynomial ℚ) (N : ℕ) :
    (∑ e ∈ S, f e).reflect N = ∑ e ∈ S, (f e).reflect N := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert e S he ih =>
      simp [he, ih, Polynomial.reflect_add]

lemma momentForwardFactor_reflect (j : α → ℚ) (e : α) :
    (momentForwardFactor j e).reflect 1 = reverseFactor j e := by
  have hneg : -(C (j e)) = C (-j e) := by simp
  rw [momentForwardFactor, sub_eq_add_neg, hneg, Polynomial.reflect_add]
  simp [reverseFactor, sub_eq_add_neg]
  ring

lemma momentForwardW_reflect (S : Finset α) (j : α → ℚ) :
    (momentForwardW S j).reflect S.card = reverseW S j := by
  induction S using Finset.induction_on with
  | empty => simp [momentForwardW, reverseW]
  | @insert e S he ih =>
      have hmul := Polynomial.reflect_mul
        (momentForwardFactor j e) (momentForwardW S j)
        (F := 1) (G := S.card)
        (by rw [momentForwardFactor, Polynomial.natDegree_X_sub_C])
        (by rw [momentForwardW_natDegree])
      simpa [momentForwardW, reverseW, he, Nat.add_comm,
        momentForwardFactor_reflect, ih] using hmul

lemma momentForwardWexcept_reflect
    (S : Finset α) (j : α → ℚ) (e : α) :
    (momentForwardWexcept S j e).reflect (S.erase e).card =
      reverseWexcept S j e := by
  simpa [momentForwardWexcept, reverseWexcept, momentForwardW, reverseW]
    using momentForwardW_reflect (S.erase e) j

lemma momentForwardWexcept_reflect_full
    {S : Finset α} {e : α} (he : e ∈ S) (j : α → ℚ) :
    (momentForwardWexcept S j e).reflect S.card =
      X * reverseWexcept S j e := by
  have hmul := Polynomial.reflect_mul
    (momentForwardWexcept S j e) (1 : Polynomial ℚ)
    (F := (S.erase e).card) (G := 1)
    (by rw [momentForwardWexcept_natDegree])
    (by simp)
  have hcard : S.card = (S.erase e).card + 1 := by
    rw [Finset.card_erase_of_mem he]
    omega
  calc
    (momentForwardWexcept S j e).reflect S.card =
        (momentForwardWexcept S j e * 1).reflect
          ((S.erase e).card + 1) := by rw [hcard, mul_one]
    _ = (momentForwardWexcept S j e).reflect (S.erase e).card *
          (1 : Polynomial ℚ).reflect 1 := hmul
    _ = reverseWexcept S j e * X := by
      rw [momentForwardWexcept_reflect]
      simp
    _ = X * reverseWexcept S j e := by ring

lemma momentForwardV_reflect
    {S : Finset α} (hS : S.Nonempty) (j w : α → ℚ) :
    (momentForwardV S j w).reflect (S.card - 1) =
      momentNumerator S j w 0 := by
  rw [momentForwardV, momentNumerator, reflect_finset_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [Polynomial.reflect_C_mul]
  have hcard : S.card - 1 = (S.erase e).card := by
    rw [Finset.card_erase_of_mem he]
  rw [hcard, momentForwardWexcept_reflect]
  simp

lemma momentForwardRhoSum_reflect
    (S : Finset α) (j rho w : α → ℚ) :
    (∑ e ∈ S, C (w e * rho e) * momentForwardWexcept S j e).reflect S.card =
      X * momentNumerator S j (offsetWeights rho w) 0 := by
  rw [reflect_finset_sum, momentNumerator, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [Polynomial.reflect_C_mul, momentForwardWexcept_reflect_full he]
  simp [offsetWeights]
  ring

lemma momentForwardU_reflect
    (S : Finset α) (j rho w : α → ℚ) (c : ℚ) :
    (momentForwardU S j rho w c).reflect S.card =
      C c * reverseW S j +
        X * momentNumerator S j (offsetWeights rho w) 0 := by
  rw [momentForwardU, Polynomial.reflect_add,
    Polynomial.reflect_C_mul, momentForwardW_reflect,
    momentForwardRhoSum_reflect]

lemma affine_reflect (h : ℚ) :
    ((X + C h : Polynomial ℚ).reflect 1) = 1 + C h * X := by
  rw [Polynomial.reflect_add]
  simp

/-- The exact reflected right factor. -/
noncomputable def actualReverseRightFactor
    (S : Finset α) (j w : α → ℚ) (h : ℚ) : Polynomial ℚ :=
  (1 + C h * X) * momentNumerator S j w 0

/-- The exact reflected left factor. -/
noncomputable def actualReverseLeftFactor
    (S : Finset α) (j rho w : α → ℚ) (c h : ℚ) : Polynomial ℚ :=
  C c * reverseW S j +
    X * momentNumerator S j (offsetWeights rho w) 0 +
    (1 + C h * X) * momentNumerator S j w 0

lemma momentForwardRightFactor_reflect
    {S : Finset α} (hS : S.Nonempty)
    (j w : α → ℚ) (h : ℚ) :
    (momentForwardRightFactor S j w h).reflect S.card =
      actualReverseRightFactor S j w h := by
  have hmul := Polynomial.reflect_mul
    (X + C h : Polynomial ℚ) (momentForwardV S j w)
    (F := 1) (G := S.card - 1)
    (by rw [Polynomial.natDegree_X_add_C])
    (momentForwardV_natDegree_le_card_sub_one hS j w)
  have hcard : S.card = 1 + (S.card - 1) := by
    have := Finset.one_le_card.mpr hS
    omega
  rw [momentForwardRightFactor, hcard, hmul,
    affine_reflect, momentForwardV_reflect hS]
  rfl

lemma momentForwardLeftFactor_reflect
    {S : Finset α} (hS : S.Nonempty)
    (j rho w : α → ℚ) (c h : ℚ) :
    (momentForwardLeftFactor S j rho w c h).reflect S.card =
      actualReverseLeftFactor S j rho w c h := by
  rw [momentForwardLeftFactor, Polynomial.reflect_add,
    momentForwardU_reflect, momentForwardRightFactor_reflect hS]
  rfl

/-! ## The first nonzero reflected moment block -/

lemma actualReverseRightFactor_eq_X_pow_mul
    {S : Finset α} {j w : α → ℚ} {h : ℚ} {q : ℕ}
    (hmu : ∀ p < q, mu S j w p = 0) :
    actualReverseRightFactor S j w h =
      X ^ q * ((1 + C h * X) * momentNumerator S j w q) := by
  have hM := momentNumerator_eq_X_pow_of_lower_moments S j w q hmu
  rw [actualReverseRightFactor, hM]
  ring

lemma actualReverseLeftFactor_eq_X_pow_mul
    {S : Finset α} {j rho w : α → ℚ} {c h : ℚ} {q : ℕ}
    (hqpos : 1 ≤ q) (hc : c = 0)
    (hmu : ∀ p < q, mu S j w p = 0)
    (hnu : ∀ p, p + 1 < q → nu S j rho w p = 0) :
    actualReverseLeftFactor S j rho w c h =
      X ^ q *
        (momentNumerator S j (offsetWeights rho w) (q - 1) +
          (1 + C h * X) * momentNumerator S j w q) := by
  have hnu' : ∀ p < q - 1,
      mu S j (offsetWeights rho w) p = 0 := by
    intro p hp
    rw [mu_offsetWeights_eq_nu]
    exact hnu p (by omega)
  have hM := momentNumerator_eq_X_pow_of_lower_moments S j w q hmu
  have hN := momentNumerator_eq_X_pow_of_lower_moments
    S j (offsetWeights rho w) (q - 1) hnu'
  have hXpred :
      (X : Polynomial ℚ) * X ^ (q - 1) = X ^ q := by
    calc
      (X : Polynomial ℚ) * X ^ (q - 1) = X ^ ((q - 1) + 1) :=
        (pow_succ' X (q - 1)).symm
      _ = X ^ q := by congr 1 <;> omega
  rw [actualReverseLeftFactor, hc]
  simp only [map_zero, zero_mul, zero_add]
  rw [hM, hN, hXpred]
  ring

lemma actualReverseRightFactor_coeff_lt
    {S : Finset α} {j w : α → ℚ} {h : ℚ} {q t : ℕ}
    (hmu : ∀ p < q, mu S j w p = 0)
    (ht : t < q) :
    (actualReverseRightFactor S j w h).coeff t = 0 := by
  have hdvd : X ^ q ∣ actualReverseRightFactor S j w h :=
    ⟨(1 + C h * X) * momentNumerator S j w q,
      actualReverseRightFactor_eq_X_pow_mul hmu⟩
  exact (Polynomial.X_pow_dvd_iff.mp hdvd) t ht

lemma actualReverseLeftFactor_coeff_lt
    {S : Finset α} {j rho w : α → ℚ} {c h : ℚ} {q t : ℕ}
    (hqpos : 1 ≤ q) (hc : c = 0)
    (hmu : ∀ p < q, mu S j w p = 0)
    (hnu : ∀ p, p + 1 < q → nu S j rho w p = 0)
    (ht : t < q) :
    (actualReverseLeftFactor S j rho w c h).coeff t = 0 := by
  have hdvd : X ^ q ∣ actualReverseLeftFactor S j rho w c h :=
    ⟨momentNumerator S j (offsetWeights rho w) (q - 1) +
        (1 + C h * X) * momentNumerator S j w q,
      actualReverseLeftFactor_eq_X_pow_mul hqpos hc hmu hnu⟩
  exact (Polynomial.X_pow_dvd_iff.mp hdvd) t ht

lemma actualReverseRightFactor_coeff_eq
    {S : Finset α} {j w : α → ℚ} {h : ℚ} {q : ℕ}
    (hmu : ∀ p < q, mu S j w p = 0) :
    (actualReverseRightFactor S j w h).coeff q = mu S j w q := by
  rw [actualReverseRightFactor_eq_X_pow_mul hmu,
    Polynomial.coeff_X_pow_mul']
  simp [momentNumerator_coeff_zero]

lemma actualReverseLeftFactor_coeff_eq
    {S : Finset α} {j rho w : α → ℚ} {c h : ℚ} {q : ℕ}
    (hqpos : 1 ≤ q) (hc : c = 0)
    (hmu : ∀ p < q, mu S j w p = 0)
    (hnu : ∀ p, p + 1 < q → nu S j rho w p = 0) :
    (actualReverseLeftFactor S j rho w c h).coeff q =
      mu S j w q + nu S j rho w (q - 1) := by
  rw [actualReverseLeftFactor_eq_X_pow_mul hqpos hc hmu hnu,
    Polynomial.coeff_X_pow_mul']
  simp [momentNumerator_coeff_zero, mu_offsetWeights_eq_nu]
  ring

/-! ## Transfer from reflected order to exact forward degree -/

theorem natDegree_le_sub_of_reflect_low_coeff_zero
    {P : Polynomial ℚ} {N q : ℕ}
    (hdeg : P.natDegree ≤ N) (hq : q ≤ N)
    (hzero : ∀ t < q, (P.reflect N).coeff t = 0) :
    P.natDegree ≤ N - q := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  by_cases hiN : i ≤ N
  · let t := N - i
    have ht : t < q := by
      dsimp [t]
      omega
    have href := Polynomial.coeff_reflect N P t
    have htN : t ≤ N := Nat.sub_le N i
    rw [Polynomial.revAt_le htN] at href
    have hback : N - t = i := by
      dsimp [t]
      omega
    rw [hback] at href
    rw [← href, hzero t ht]
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt hdeg (by omega))

lemma momentForwardRightFactor_natDegree_le_sub
    {S : Finset α} {j w : α → ℚ} {h : ℚ} {q : ℕ}
    (hqpos : 1 ≤ q) (hq : q ≤ S.card)
    (hmu : ∀ p < q, mu S j w p = 0) :
    (momentForwardRightFactor S j w h).natDegree ≤ S.card - q := by
  have hS : S.Nonempty := Finset.card_pos.mp (by omega)
  apply natDegree_le_sub_of_reflect_low_coeff_zero
    (momentForwardRightFactor_natDegree_le_card hS j w h) hq
  intro t ht
  rw [momentForwardRightFactor_reflect hS]
  exact actualReverseRightFactor_coeff_lt hmu ht

lemma momentForwardLeftFactor_natDegree_le_sub
    {S : Finset α} {j rho w : α → ℚ} {c h : ℚ} {q : ℕ}
    (hqpos : 1 ≤ q) (hq : q ≤ S.card) (hc : c = 0)
    (hmu : ∀ p < q, mu S j w p = 0)
    (hnu : ∀ p, p + 1 < q → nu S j rho w p = 0) :
    (momentForwardLeftFactor S j rho w c h).natDegree ≤ S.card - q := by
  have hS : S.Nonempty := Finset.card_pos.mp (by omega)
  apply natDegree_le_sub_of_reflect_low_coeff_zero
    (momentForwardLeftFactor_natDegree_le_card hS j rho w c h) hq
  intro t ht
  rw [momentForwardLeftFactor_reflect hS]
  exact actualReverseLeftFactor_coeff_lt hqpos hc hmu hnu ht

lemma momentForwardRightFactor_coeff_sub
    {S : Finset α} {j w : α → ℚ} {h : ℚ} {q : ℕ}
    (hqpos : 1 ≤ q) (hq : q ≤ S.card)
    (hmu : ∀ p < q, mu S j w p = 0) :
    (momentForwardRightFactor S j w h).coeff (S.card - q) =
      mu S j w q := by
  have hS : S.Nonempty := Finset.card_pos.mp (by omega)
  have href := Polynomial.coeff_reflect S.card
    (momentForwardRightFactor S j w h) q
  rw [Polynomial.revAt_le hq] at href
  calc
    (momentForwardRightFactor S j w h).coeff (S.card - q) =
        ((momentForwardRightFactor S j w h).reflect S.card).coeff q :=
      href.symm
    _ = (actualReverseRightFactor S j w h).coeff q := by
      rw [momentForwardRightFactor_reflect hS]
    _ = mu S j w q := actualReverseRightFactor_coeff_eq hmu

lemma momentForwardLeftFactor_coeff_sub
    {S : Finset α} {j rho w : α → ℚ} {c h : ℚ} {q : ℕ}
    (hqpos : 1 ≤ q) (hq : q ≤ S.card) (hc : c = 0)
    (hmu : ∀ p < q, mu S j w p = 0)
    (hnu : ∀ p, p + 1 < q → nu S j rho w p = 0) :
    (momentForwardLeftFactor S j rho w c h).coeff (S.card - q) =
      mu S j w q + nu S j rho w (q - 1) := by
  have hS : S.Nonempty := Finset.card_pos.mp (by omega)
  have href := Polynomial.coeff_reflect S.card
    (momentForwardLeftFactor S j rho w c h) q
  rw [Polynomial.revAt_le hq] at href
  calc
    (momentForwardLeftFactor S j rho w c h).coeff (S.card - q) =
        ((momentForwardLeftFactor S j rho w c h).reflect S.card).coeff q :=
      href.symm
    _ = (actualReverseLeftFactor S j rho w c h).coeff q := by
      rw [momentForwardLeftFactor_reflect hS]
    _ = mu S j w q + nu S j rho w (q - 1) :=
      actualReverseLeftFactor_coeff_eq hqpos hc hmu hnu

lemma fin_prod_natDegree_le
    {k d : ℕ} (F : Fin k → Polynomial ℚ)
    (hF : ∀ i : Fin k, (F i).natDegree ≤ d) :
    (∏ i : Fin k, F i).natDegree ≤ k * d := by
  refine (Polynomial.natDegree_prod_le (Finset.univ : Finset (Fin k)) F).trans ?_
  calc
    (∑ i ∈ (Finset.univ : Finset (Fin k)), (F i).natDegree) ≤
        ∑ _i ∈ (Finset.univ : Finset (Fin k)), d := by
      apply Finset.sum_le_sum
      intro i hi
      exact hF i
    _ = k * d := by simp

/-- Exact coefficient of the first nonzero reflected product block. -/
theorem momentMatchingPhi_coeff_first_nonzero
    {S : Finset α} {j rho w : α → ℚ} {c : ℚ}
    {k q : ℕ} (h : Fin k → ℚ)
    (hqpos : 1 ≤ q) (hq : q ≤ S.card) (hc : c = 0)
    (hmu : ∀ p < q, mu S j w p = 0)
    (hnu : ∀ p, p + 1 < q → nu S j rho w p = 0) :
    (momentMatchingPhi S j rho w c h).coeff (k * (S.card - q)) =
      momentDelta k (mu S j w q) (nu S j rho w (q - 1)) := by
  let L : Fin k → Polynomial ℚ := fun i =>
    momentForwardLeftFactor S j rho w c (h i)
  let R : Fin k → Polynomial ℚ := fun i =>
    momentForwardRightFactor S j w (h i)
  have hLdeg : ∀ i : Fin k, (L i).natDegree ≤ S.card - q := by
    intro i
    exact momentForwardLeftFactor_natDegree_le_sub
      hqpos hq hc hmu hnu
  have hRdeg : ∀ i : Fin k, (R i).natDegree ≤ S.card - q := by
    intro i
    exact momentForwardRightFactor_natDegree_le_sub hqpos hq hmu
  have hLcoeff : ∀ i : Fin k,
      (L i).coeff (S.card - q) =
        mu S j w q + nu S j rho w (q - 1) := by
    intro i
    exact momentForwardLeftFactor_coeff_sub hqpos hq hc hmu hnu
  have hRcoeff : ∀ i : Fin k,
      (R i).coeff (S.card - q) = mu S j w q := by
    intro i
    exact momentForwardRightFactor_coeff_sub hqpos hq hmu
  have hprodL := Polynomial.coeff_prod_of_natDegree_le
    (s := (Finset.univ : Finset (Fin k))) L (S.card - q)
    (by simpa using hLdeg)
  have hprodR := Polynomial.coeff_prod_of_natDegree_le
    (s := (Finset.univ : Finset (Fin k))) R (S.card - q)
    (by simpa using hRdeg)
  simp only [Finset.card_univ, Fintype.card_fin] at hprodL hprodR
  rw [momentMatchingPhi, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
  change ((Finset.univ : Finset (Fin k)).prod L).coeff
      (k * (S.card - q)) -
    4 * ((Finset.univ : Finset (Fin k)).prod R).coeff
      (k * (S.card - q)) = _
  rw [hprodL, hprodR]
  simp [hLcoeff, hRcoeff, momentDelta]

lemma momentMatchingPhi_natDegree_le_first_nonzero
    {S : Finset α} {j rho w : α → ℚ} {c : ℚ}
    {k q : ℕ} (h : Fin k → ℚ)
    (hqpos : 1 ≤ q) (hq : q ≤ S.card) (hc : c = 0)
    (hmu : ∀ p < q, mu S j w p = 0)
    (hnu : ∀ p, p + 1 < q → nu S j rho w p = 0) :
    (momentMatchingPhi S j rho w c h).natDegree ≤
      k * (S.card - q) := by
  let L : Fin k → Polynomial ℚ := fun i =>
    momentForwardLeftFactor S j rho w c (h i)
  let R : Fin k → Polynomial ℚ := fun i =>
    momentForwardRightFactor S j w (h i)
  have hLdeg : ∀ i : Fin k, (L i).natDegree ≤ S.card - q := by
    intro i
    exact momentForwardLeftFactor_natDegree_le_sub
      hqpos hq hc hmu hnu
  have hRdeg : ∀ i : Fin k, (R i).natDegree ≤ S.card - q := by
    intro i
    exact momentForwardRightFactor_natDegree_le_sub hqpos hq hmu
  have hprodL := fin_prod_natDegree_le L hLdeg
  have hprodR := fin_prod_natDegree_le R hRdeg
  rw [momentMatchingPhi]
  exact Polynomial.natDegree_sub_le_of_le hprodL
    ((Polynomial.natDegree_C_mul_le (4 : ℚ) _).trans hprodR)

/-- Exact moment-ladder degree of the rational matching polynomial. -/
theorem momentMatchingPhi_natDegree_first_nonzero
    {S : Finset α} {j rho w : α → ℚ} {c : ℚ}
    {k q : ℕ} (h : Fin k → ℚ)
    (hk : 3 ≤ k) (hqpos : 1 ≤ q) (hq : q ≤ S.card) (hc : c = 0)
    (hmu : ∀ p < q, mu S j w p = 0)
    (hnu : ∀ p, p + 1 < q → nu S j rho w p = 0)
    (hpair : mu S j w q ≠ 0 ∨ nu S j rho w (q - 1) ≠ 0) :
    (momentMatchingPhi S j rho w c h).natDegree =
      k * (S.card - q) := by
  have hcoeff := momentMatchingPhi_coeff_first_nonzero
    h hqpos hq hc hmu hnu
  have hdelta :
      momentDelta k (mu S j w q) (nu S j rho w (q - 1)) ≠ 0 :=
    momentDelta_ne_zero_of_first_nonzero hk hpair
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (momentMatchingPhi_natDegree_le_first_nonzero
      h hqpos hq hc hmu hnu)
  simpa [hcoeff] using hdelta

/-- Exact quotient degree after the square support divisor is removed. -/
theorem momentMatchingQuotient_natDegree_first_nonzero
    {S : Finset α} {j rho w : α → ℚ} {c : ℚ}
    {k q : ℕ} (h : Fin k → ℚ)
    (hk : 3 ≤ k) (hqpos : 1 ≤ q) (hq : q ≤ S.card) (hc : c = 0)
    (hmu : ∀ p < q, mu S j w p = 0)
    (hnu : ∀ p, p + 1 < q → nu S j rho w p = 0)
    (hpair : mu S j w q ≠ 0 ∨ nu S j rho w (q - 1) ≠ 0)
    (Q : Polynomial ℚ)
    (hfactor : momentMatchingPhi S j rho w c h =
      momentForwardW S j ^ 2 * Q) :
    Q.natDegree = S.card * (k - 2) - q * k := by
  let Phi := momentMatchingPhi S j rho w c h
  have hPhi : Phi.natDegree = k * (S.card - q) := by
    dsimp [Phi]
    exact momentMatchingPhi_natDegree_first_nonzero
      h hk hqpos hq hc hmu hnu hpair
  have hcoef : Phi.coeff (k * (S.card - q)) ≠ 0 := by
    dsimp [Phi]
    rw [momentMatchingPhi_coeff_first_nonzero h hqpos hq hc hmu hnu]
    exact momentDelta_ne_zero_of_first_nonzero hk hpair
  have hWne : momentForwardW S j ≠ 0 :=
    (momentForwardW_monic S j).ne_zero
  have hQne : Q ≠ 0 := by
    intro hQ
    subst Q
    have hPhi0 : Phi = 0 := by
      dsimp [Phi]
      simpa using hfactor
    rw [hPhi0] at hcoef
    exact hcoef (by simp)
  have hdegree : k * (S.card - q) = 2 * S.card + Q.natDegree := by
    rw [← hPhi]
    dsimp [Phi]
    rw [hfactor, Polynomial.natDegree_mul (pow_ne_zero 2 hWne) hQne,
      Polynomial.natDegree_pow, momentForwardW_natDegree]
  have htwo : 2 * S.card ≤ k * (S.card - q) := by omega
  have hsum :
      k * (S.card - q) + q * k = S.card * k := by
    calc
      k * (S.card - q) + q * k =
          k * (S.card - q) + k * q := by rw [Nat.mul_comm q k]
      _ = k * ((S.card - q) + q) := (Nat.mul_add _ _ _).symm
      _ = k * S.card := by rw [Nat.sub_add_cancel hq]
      _ = S.card * k := Nat.mul_comm _ _
  have hk2 : 2 ≤ k := by omega
  have hdecomp : S.card * k = 2 * S.card + S.card * (k - 2) := by
    have hkEq : (k - 2) + 2 = k := by omega
    calc
      S.card * k = S.card * ((k - 2) + 2) := by rw [hkEq]
      _ = 2 * S.card + S.card * (k - 2) := by ring
  have hfeasible : q * k ≤ S.card * (k - 2) := by
    have hadd :
        2 * S.card + q * k ≤ 2 * S.card + S.card * (k - 2) := by
      rw [← hdecomp, ← hsum]
      exact Nat.add_le_add_right htwo (q * k)
    exact Nat.le_of_add_le_add_left hadd
  exact momentQuotient_natDegree hPhi
    (momentForwardW_natDegree S j) hWne hQne hfactor hq hk2 hfeasible

#print axioms momentForwardW_reflect
#print axioms momentForwardLeftFactor_reflect
#print axioms actualReverseLeftFactor_eq_X_pow_mul
#print axioms momentMatchingPhi_coeff_first_nonzero
#print axioms momentMatchingPhi_natDegree_first_nonzero
#print axioms momentMatchingQuotient_natDegree_first_nonzero

end Erdos686Variant
end Erdos686
