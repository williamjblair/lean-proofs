import Research.RootCountMeasurable
import Mathlib.Algebra.Polynomial.RuleOfSigns
import Mathlib.Tactic

open Set
open scoped BigOperators

namespace Erdos521

noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Polynomial obtained from `f_n` by the positive-axis Möbius substitution `x=t/(1+t)`. -/
noncomputable def mobiusPolynomial (ω : ℕ → Bool) (n : ℕ) : Polynomial ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    Polynomial.C (sign (ω i)) * Polynomial.X ^ i *
      (1 + Polynomial.X) ^ (n - i)

lemma pow_mul_div_pow {t : ℝ} {i n : ℕ} (hi : i ≤ n) (h : 1 + t ≠ 0) :
    (1 + t) ^ n * (t / (1 + t)) ^ i = t ^ i * (1 + t) ^ (n - i) := by
  rw [div_pow]
  field_simp
  rw [show (1 + t) ^ n = (1 + t) ^ (n - i) * (1 + t) ^ i by
    rw [← pow_add, Nat.sub_add_cancel hi]]
  ring

lemma mobiusPolynomial_eval (ω : ℕ → Bool) (n : ℕ) (t : ℝ) :
    (mobiusPolynomial ω n).eval t =
      ∑ i ∈ Finset.range (n + 1),
        sign (ω i) * t ^ i * (1 + t) ^ (n - i) := by
  rw [mobiusPolynomial, Polynomial.eval_finset_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp

lemma mobiusPolynomial_eval_eq (ω : ℕ → Bool) (n : ℕ) {t : ℝ} (h : 1 + t ≠ 0) :
    (mobiusPolynomial ω n).eval t =
      (1 + t) ^ n * (littlewoodPolynomial ω n).eval (t / (1 + t)) := by
  rw [mobiusPolynomial_eval, littlewoodPolynomial_eval, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i ≤ n := by
    have := Finset.mem_range.mp hi
    omega
  calc
    sign (ω i) * t ^ i * (1 + t) ^ (n - i) =
        sign (ω i) * (t ^ i * (1 + t) ^ (n - i)) := by ring
    _ = sign (ω i) * ((1 + t) ^ n * (t / (1 + t)) ^ i) := by
      rw [pow_mul_div_pow hin h]
    _ = (1 + t) ^ n * (sign (ω i) * (t / (1 + t)) ^ i) := by ring

lemma mobiusPolynomial_ne_zero (ω : ℕ → Bool) (n : ℕ) : mobiusPolynomial ω n ≠ 0 := by
  intro hzero
  have heval := mobiusPolynomial_eval_eq ω n (t := 0) (by norm_num)
  rw [hzero, Polynomial.eval_zero] at heval
  have hp := littlewoodPolynomial_ne_zero_of_abs_le_half ω n 0 (by norm_num)
  norm_num at heval
  exact hp heval.symm

/-- Möbius coordinate carrying `(0,1)` bijectively to the positive half-line. -/
noncomputable def positiveMobius (x : ℝ) : ℝ := x / (1 - x)

lemma positiveMobius_pos {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    0 < positiveMobius x := div_pos hx0 (sub_pos.mpr hx1)

lemma positiveMobius_back {x : ℝ} (hx1 : x < 1) :
    positiveMobius x / (1 + positiveMobius x) = x := by
  unfold positiveMobius
  field_simp [ne_of_gt (sub_pos.mpr hx1)]
  ring

lemma one_add_positiveMobius_ne_zero {x : ℝ} (hx1 : x < 1) :
    1 + positiveMobius x ≠ 0 := by
  have : 0 < 1 + positiveMobius x := by
    unfold positiveMobius
    rw [show 1 + x / (1 - x) = 1 / (1 - x) by
      field_simp [ne_of_gt (sub_pos.mpr hx1)] <;> ring]
    positivity
  exact ne_of_gt this

lemma positiveMobius_injective_on_Iio_one :
    Set.InjOn positiveMobius (Set.Iio (1 : ℝ)) := by
  intro x hx y hy heq
  unfold positiveMobius at heq
  have hxne : 1 - x ≠ 0 := ne_of_gt (sub_pos.mpr hx)
  have hyne : 1 - y ≠ 0 := ne_of_gt (sub_pos.mpr hy)
  field_simp [hxne, hyne] at heq
  linarith

lemma positiveMobius_maps_root {ω : ℕ → Bool} {n : ℕ} {x : ℝ}
    (hroot : x ∈ (littlewoodPolynomial ω n).rootSet ℝ) (hx1 : x < 1) :
    positiveMobius x ∈ (mobiusPolynomial ω n).rootSet ℝ := by
  rw [mem_littlewood_rootSet_iff_eval_eq_zero] at hroot
  rw [Polynomial.mem_rootSet]
  constructor
  · exact mobiusPolynomial_ne_zero ω n
  · have heval : (mobiusPolynomial ω n).eval (positiveMobius x) = 0 := by
      rw [mobiusPolynomial_eval_eq ω n (one_add_positiveMobius_ne_zero hx1),
        positiveMobius_back hx1, hroot]
      simp
    simpa [Polynomial.aeval_def] using heval

/-- The number of distinct positive roots is bounded by the multiplicity-counted positive roots. -/
lemma ncard_positive_rootSet_le_countP (P : Polynomial ℝ) :
    Set.ncard (P.rootSet ℝ ∩ Set.Ioi 0) ≤ P.roots.countP (0 < ·) := by
  by_cases hP : P = 0
  · simp [hP]
  · let M := P.roots.filter (0 < ·)
    have hset : P.rootSet ℝ ∩ Set.Ioi 0 = (M.toFinset : Set ℝ) := by
      ext x
      simp [M, Polynomial.mem_rootSet, Polynomial.mem_roots hP, hP,
        Polynomial.IsRoot, Polynomial.aeval_def]
    rw [hset, Set.ncard_coe_finset, Multiset.countP_eq_card_filter]
    exact Multiset.toFinset_card_le M

/-- Distinct roots of `f_n` in `(1/2,1)` inject under the Möbius map into positive roots of the
transformed polynomial, hence are bounded by its coefficient sign variations. -/
lemma ncard_roots_Ioo_half_one_le_signVariations (ω : ℕ → Bool) (n : ℕ) :
    Set.ncard ((littlewoodPolynomial ω n).rootSet ℝ ∩ Set.Ioo (1 / 2 : ℝ) 1) ≤
      (mobiusPolynomial ω n).signVariations := by
  let A := (littlewoodPolynomial ω n).rootSet ℝ ∩ Set.Ioo (1 / 2 : ℝ) 1
  let B := (mobiusPolynomial ω n).rootSet ℝ ∩ Set.Ioi 0
  have hmap : positiveMobius '' A ⊆ B := by
    rintro y ⟨x, hx, rfl⟩
    exact ⟨positiveMobius_maps_root hx.1 hx.2.2,
      positiveMobius_pos (by linarith [hx.2.1]) hx.2.2⟩
  have hinj : Set.InjOn positiveMobius A :=
    positiveMobius_injective_on_Iio_one.mono (by
      intro x hx
      exact hx.2.2)
  calc
    A.ncard = (positiveMobius '' A).ncard := hinj.ncard_image.symm
    _ ≤ B.ncard := Set.ncard_le_ncard hmap (Set.toFinite B)
    _ ≤ (mobiusPolynomial ω n).roots.countP (0 < ·) :=
      ncard_positive_rootSet_le_countP _
    _ ≤ (mobiusPolynomial ω n).signVariations :=
      Polynomial.roots_countP_pos_le_signVariations _

end Erdos521
