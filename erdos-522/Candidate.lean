import Erdos522Statement


/-! ===== amalgamated from Research.SparseFrequencyMatrix ===== -/

section AmalgamatedModule0


open scoped BigOperators ComplexConjugate

namespace Erdos522

noncomputable def complexFrequency (m : ℤ) : ℂ := (m : ℂ) * Complex.I

noncomputable def frequencyDerivativeMatrix
    {h : ℕ} (m : Fin h → ℤ) : Matrix (Fin h) (Fin h) ℂ :=
  fun i j => complexFrequency (m j) ^ (i.val + 2)

lemma frequencyDerivativeMatrix_eq
    {h : ℕ} (m : Fin h → ℤ) :
    frequencyDerivativeMatrix m =
      (Matrix.vandermonde (fun j => complexFrequency (m j))).transpose *
        Matrix.diagonal (fun j => complexFrequency (m j) ^ 2) := by
  ext i j
  rw [Matrix.mul_diagonal]
  simp only [Matrix.transpose_apply, Matrix.vandermonde_apply]
  unfold frequencyDerivativeMatrix
  rw [← pow_add]

lemma complexFrequency_injective {h : ℕ} {m : Fin h → ℤ}
    (hm : Function.Injective m) :
    Function.Injective (fun j => complexFrequency (m j)) := by
  intro i j hij
  have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  unfold complexFrequency at hij
  have hc : (m i : ℂ) = (m j : ℂ) := mul_right_cancel₀ hI hij
  apply hm
  exact_mod_cast hc

lemma one_le_norm_complexFrequency {m : ℤ} (hm : m ≠ 0) :
    1 ≤ ‖complexFrequency m‖ := by
  unfold complexFrequency
  rw [Complex.norm_mul, Complex.norm_I]
  simp only [mul_one, Complex.norm_intCast]
  have hpos : (0 : ℤ) < |m| := abs_pos.mpr hm
  have hone : (1 : ℤ) ≤ |m| := by omega
  exact_mod_cast hone

lemma one_le_norm_complexFrequency_sub {m₁ m₂ : ℤ} (h : m₁ ≠ m₂) :
    1 ≤ ‖complexFrequency m₁ - complexFrequency m₂‖ := by
  rw [show complexFrequency m₁ - complexFrequency m₂ =
      complexFrequency (m₁ - m₂) by
    unfold complexFrequency
    push_cast
    ring]
  exact one_le_norm_complexFrequency (sub_ne_zero.mpr h)

/-- The derivative Vandermonde determinant has norm at least one for distinct
nonzero integer frequencies. -/
lemma one_le_norm_frequencyDerivativeMatrix_det
    {h : ℕ} (m : Fin h → ℤ) (hinj : Function.Injective m)
    (hne : ∀ j, m j ≠ 0) :
    1 ≤ ‖(frequencyDerivativeMatrix m).det‖ := by
  rw [frequencyDerivativeMatrix_eq, Matrix.det_mul, Matrix.det_transpose,
    Matrix.det_vandermonde, Matrix.det_diagonal, norm_mul]
  have hV : 1 ≤ ‖∏ i : Fin h, ∏ j ∈ Finset.Ioi i,
      (complexFrequency (m j) - complexFrequency (m i))‖ := by
    rw [norm_prod]
    apply Finset.one_le_prod
    intro i hi
    rw [norm_prod]
    apply Finset.one_le_prod
    intro j hj
    exact one_le_norm_complexFrequency_sub (hinj.ne (Finset.mem_Ioi.mp hj).ne')
  have hD : 1 ≤ ‖∏ j : Fin h, complexFrequency (m j) ^ 2‖ := by
    rw [norm_prod]
    apply Finset.one_le_prod
    intro j hj
    rw [norm_pow]
    exact one_le_pow₀ (one_le_norm_complexFrequency (hne j))
  nlinarith [mul_le_mul hV hD (by positivity) (by positivity)]

lemma norm_frequencyDerivativeMatrix_entry_le
    {h n : ℕ} (m : Fin h → ℤ) (hm : ∀ j, (m j).natAbs ≤ n)
    (i j : Fin h) :
    ‖frequencyDerivativeMatrix m i j‖ ≤ (n + 1 : ℝ) ^ (h + 1) := by
  unfold frequencyDerivativeMatrix complexFrequency
  rw [norm_pow, Complex.norm_mul, Complex.norm_I, mul_one,
    Complex.norm_intCast]
  rw [← Int.cast_abs, ← Nat.cast_natAbs]
  have habs : (m j).natAbs ≤ n + 1 := (hm j).trans (Nat.le_succ n)
  have hexp : i.val + 2 ≤ h + 1 := by omega
  calc
    ((m j).natAbs : ℝ) ^ (i.val + 2) ≤ (n + 1 : ℝ) ^ (i.val + 2) := by
      gcongr
      exact_mod_cast habs
    _ ≤ (n + 1 : ℝ) ^ (h + 1) := by
      exact pow_le_pow_right₀ (by norm_num) hexp


lemma norm_frequencyDerivativeMatrix_adjugate_entry_le
    {h n : ℕ} (m : Fin h → ℤ) (hm : ∀ j, (m j).natAbs ≤ n)
    (i j : Fin h) :
    ‖(frequencyDerivativeMatrix m).adjugate i j‖ ≤
      h.factorial * ((n + 1 : ℝ) ^ (h + 1)) ^ h := by
  rw [Matrix.adjugate_apply]
  have hd := Matrix.det_le
    (A := (frequencyDerivativeMatrix m).updateRow j (Pi.single i 1))
    (abv := IsAbsoluteValue.toAbsoluteValue (norm : ℂ → ℝ))
    (x := ((n + 1 : ℝ) ^ (h + 1))) (by
      intro r c
      rw [Matrix.updateRow_apply]
      split_ifs with hrow
      · rw [Pi.single_apply]
        split_ifs
        · simp
          exact one_le_pow₀ (by norm_num)
        · simp
          positivity
      · exact norm_frequencyDerivativeMatrix_entry_le m hm r c)
  simpa using hd

/-- Quantitative pointwise finite-type estimate: among derivative orders
`2,...,h+1`, one detects any chosen coefficient of a distinct nonzero integer
frequency exponential sum. -/
theorem exists_frequencyDerivativeMatrix_mulVec_large
    {h n : ℕ} (m : Fin h → ℤ) (hinj : Function.Injective m)
    (hne : ∀ j, m j ≠ 0) (hm : ∀ j, (m j).natAbs ≤ n)
    (v : Fin h → ℂ) (j₀ : Fin h) (a : ℝ) (ha : 0 < a)
    (hv : a ≤ ‖v j₀‖) :
    ∃ i : Fin h,
      a / ((h : ℝ) * (h.factorial : ℝ) *
        ((n + 1 : ℝ) ^ (h + 1)) ^ h) ≤
      ‖∑ j : Fin h, frequencyDerivativeMatrix m i j * v j‖ := by
  let A := frequencyDerivativeMatrix m
  let y : Fin h → ℂ := A.mulVec v
  let D : ℝ := (h.factorial : ℝ) * ((n + 1 : ℝ) ^ (h + 1)) ^ h
  have hh : 0 < h := Fin.pos_iff_nonempty.mpr ⟨j₀⟩
  have hD : 0 < D := by
    dsimp [D]
    positivity
  have hdet := one_le_norm_frequencyDerivativeMatrix_det m hinj hne
  have hcramer : A.cramer y = A.det • v := by
    rw [Matrix.cramer_eq_adjugate_mulVec]
    dsimp [y]
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul,
      Matrix.smul_mulVec, Matrix.one_mulVec]
  by_contra hnone
  push Not at hnone
  have hy (i : Fin h) : ‖y i‖ < a / ((h : ℝ) * D) := by
    change ‖∑ j : Fin h, frequencyDerivativeMatrix m i j * v j‖ < _
    rw [show (h : ℝ) * D = (h : ℝ) * (h.factorial : ℝ) *
        ((n + 1 : ℝ) ^ (h + 1)) ^ h by
      dsimp [D]
      ring]
    exact hnone i
  have hadj (i j : Fin h) : ‖A.adjugate i j‖ ≤ D := by
    dsimp [A, D]
    exact norm_frequencyDerivativeMatrix_adjugate_entry_le m hm i j
  have hupper : ‖A.cramer y j₀‖ < a := by
    rw [Matrix.cramer_eq_adjugate_mulVec, Matrix.mulVec]
    calc
      ‖∑ i : Fin h, A.adjugate j₀ i * y i‖ ≤
          ∑ i : Fin h, ‖A.adjugate j₀ i * y i‖ := norm_sum_le _ _
      _ < ∑ _i : Fin h, D * (a / ((h : ℝ) * D)) := by
        apply Finset.sum_lt_sum_of_nonempty
        · exact ⟨j₀, Finset.mem_univ _⟩
        · intro i hi
          rw [norm_mul]
          exact lt_of_le_of_lt
            (mul_le_mul_of_nonneg_right (hadj j₀ i) (norm_nonneg _))
            (mul_lt_mul_of_pos_left (hy i) hD)
      _ = a := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        field_simp
  have hlower : a ≤ ‖A.cramer y j₀‖ := by
    rw [hcramer]
    simp only [Pi.smul_apply, norm_smul]
    nlinarith [mul_le_mul hdet hv ha.le (by positivity : (0 : ℝ) ≤ ‖A.det‖)]
  linarith

end Erdos522

end AmalgamatedModule0


/-! ===== amalgamated from Research.SparseExponentialDerivatives ===== -/

section AmalgamatedModule1


open scoped BigOperators ComplexConjugate

namespace Erdos522

noncomputable def complexExponentialSumOrder
    {h : ℕ} (r : ℕ) (m : Fin h → ℤ) (c : Fin h → ℂ) (z : ℂ) : ℂ :=
  ∑ j : Fin h, complexFrequency (m j) ^ r * c j *
    Complex.exp (complexFrequency (m j) * z)

noncomputable def realExponentialSum
    {h : ℕ} (m : Fin h → ℤ) (c : Fin h → ℂ) (x : ℝ) : ℝ :=
  (complexExponentialSumOrder 0 m c x).re

lemma hasDerivAt_complexExponentialTerm
    (m : ℤ) (c : ℂ) (z : ℂ) :
    HasDerivAt (fun w : ℂ => c * Complex.exp (complexFrequency m * w))
      (complexFrequency m * (c * Complex.exp (complexFrequency m * z))) z := by
  have hi : HasDerivAt (fun w : ℂ => complexFrequency m * w)
      (complexFrequency m) z := by
    simpa using (hasDerivAt_id z).const_mul (complexFrequency m)
  have he := (Complex.hasDerivAt_exp (complexFrequency m * z)).comp z hi
  have hc := he.const_mul c
  simpa only [Function.comp_apply, mul_assoc, mul_comm, mul_left_comm] using hc

lemma hasDerivAt_complexExponentialSumOrder
    {h : ℕ} (r : ℕ) (m : Fin h → ℤ) (c : Fin h → ℂ) (z : ℂ) :
    HasDerivAt (complexExponentialSumOrder r m c)
      (complexExponentialSumOrder (r + 1) m c z) z := by
  unfold complexExponentialSumOrder
  apply HasDerivAt.fun_sum
  intro j hj
  simpa only [pow_succ, mul_assoc, mul_comm, mul_left_comm] using
    (hasDerivAt_complexExponentialTerm (m j)
      (complexFrequency (m j) ^ r * c j) z)

lemma hasDerivAt_realExponentialSumOrder
    {h : ℕ} (r : ℕ) (m : Fin h → ℤ) (c : Fin h → ℂ) (x : ℝ) :
    HasDerivAt
      (fun y : ℝ => (complexExponentialSumOrder r m c (y : ℂ)).re)
      (complexExponentialSumOrder (r + 1) m c (x : ℂ)).re x := by
  exact (hasDerivAt_complexExponentialSumOrder r m c (x : ℂ)).real_of_complex

lemma iteratedDeriv_realExponentialSum
    {h : ℕ} (r : ℕ) (m : Fin h → ℤ) (c : Fin h → ℂ) (x : ℝ) :
    iteratedDeriv r (realExponentialSum m c) x =
      (complexExponentialSumOrder r m c (x : ℂ)).re := by
  induction r generalizing x with
  | zero => rfl
  | succ r ih =>
      rw [iteratedDeriv_succ]
      rw [show iteratedDeriv r (realExponentialSum m c) =
          fun y : ℝ => (complexExponentialSumOrder r m c (y : ℂ)).re by
        funext y
        exact ih y]
      exact (hasDerivAt_realExponentialSumOrder r m c x).deriv

lemma contDiff_realExponentialSum
    {h : ℕ} (m : Fin h → ℤ) (c : Fin h → ℂ) (r : WithTop ℕ∞) :
    ContDiff ℝ r (realExponentialSum m c) := by
  apply ContDiff.real_of_complex
  unfold complexExponentialSumOrder
  fun_prop

lemma norm_complexExponentialSumOrder_le
    {h n : ℕ} (r : ℕ) (m : Fin h → ℤ) (hm : ∀ j, (m j).natAbs ≤ n)
    (c : Fin h → ℂ) (x : ℝ) :
    ‖complexExponentialSumOrder r m c x‖ ≤
      ∑ j : Fin h, (n : ℝ) ^ r * ‖c j‖ := by
  unfold complexExponentialSumOrder
  calc
    ‖∑ j : Fin h, complexFrequency (m j) ^ r * c j *
        Complex.exp (complexFrequency (m j) * (x : ℂ))‖ ≤
        ∑ j : Fin h, ‖complexFrequency (m j) ^ r * c j *
          Complex.exp (complexFrequency (m j) * (x : ℂ))‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin h, (n : ℝ) ^ r * ‖c j‖ := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul, norm_mul, norm_pow, Complex.norm_exp]
      have hre : (complexFrequency (m j) * (x : ℂ)).re = 0 := by
        unfold complexFrequency
        simp
      rw [hre, Real.exp_zero, mul_one]
      have hfreq : ‖complexFrequency (m j)‖ ≤ n := by
        unfold complexFrequency
        rw [Complex.norm_mul, Complex.norm_I, mul_one, Complex.norm_intCast,
          ← Int.cast_abs, ← Nat.cast_natAbs]
        exact_mod_cast hm j
      gcongr


lemma abs_iteratedDeriv_realExponentialSum_le
    {h n : ℕ} (r : ℕ) (m : Fin h → ℤ) (hm : ∀ j, (m j).natAbs ≤ n)
    (c : Fin h → ℂ) (x : ℝ) :
    |iteratedDeriv r (realExponentialSum m c) x| ≤
      ∑ j : Fin h, (n : ℝ) ^ r * ‖c j‖ := by
  rw [iteratedDeriv_realExponentialSum]
  exact (Complex.abs_re_le_norm _).trans
    (norm_complexExponentialSumOrder_le r m hm c x)

lemma iteratedDeriv_realExponentialSum_sub_le
    {h n : ℕ} (r : ℕ) (m : Fin h → ℤ) (hm : ∀ j, (m j).natAbs ≤ n)
    (c : Fin h → ℂ) (x y : ℝ) :
    |iteratedDeriv r (realExponentialSum m c) y -
        iteratedDeriv r (realExponentialSum m c) x| ≤
      (∑ j : Fin h, (n : ℝ) ^ (r + 1) * ‖c j‖) * |y - x| := by
  let f : ℝ → ℝ := fun z => iteratedDeriv r (realExponentialSum m c) z
  let f' : ℝ → ℝ := fun z =>
    (complexExponentialSumOrder (r + 1) m c (z : ℂ)).re
  have hf (z : ℝ) : HasDerivAt f (f' z) z := by
    dsimp [f, f']
    rw [show (fun w : ℝ => iteratedDeriv r (realExponentialSum m c) w) =
        fun w : ℝ => (complexExponentialSumOrder r m c (w : ℂ)).re by
      funext w
      exact iteratedDeriv_realExponentialSum r m c w]
    exact hasDerivAt_realExponentialSumOrder r m c z
  have hb (z : ℝ) : ‖f' z‖ ≤
      ∑ j : Fin h, (n : ℝ) ^ (r + 1) * ‖c j‖ := by
    rw [Real.norm_eq_abs]
    exact (Complex.abs_re_le_norm _).trans
      (norm_complexExponentialSumOrder_le (r + 1) m hm c z)
  have hmvt := convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z hz => (hf z).hasDerivWithinAt) (fun z hz => hb z)
    (Set.mem_univ x) (Set.mem_univ y)
  simpa [f, Real.norm_eq_abs] using hmvt

/-- Finite-type consequence for a real-valued conjugate-symmetric exponential
sum. -/
theorem exists_iteratedDeriv_realExponentialSum_large
    {h n : ℕ} (m : Fin h → ℤ) (hinj : Function.Injective m)
    (hne : ∀ j, m j ≠ 0) (hm : ∀ j, (m j).natAbs ≤ n)
    (c : Fin h → ℂ) (j₀ : Fin h) (a : ℝ) (ha : 0 < a)
    (hc : a ≤ ‖c j₀‖)
    (hreal : ∀ (r : ℕ) (x : ℝ),
      (complexExponentialSumOrder r m c (x : ℂ)).im = 0)
    (x : ℝ) :
    ∃ r : ℕ, 2 ≤ r ∧ r ≤ h + 1 ∧
      a / ((h : ℝ) * (h.factorial : ℝ) *
        ((n + 1 : ℝ) ^ (h + 1)) ^ h) ≤
        |iteratedDeriv r (realExponentialSum m c) x| := by
  let v : Fin h → ℂ := fun j =>
    c j * Complex.exp (complexFrequency (m j) * (x : ℂ))
  have hv : a ≤ ‖v j₀‖ := by
    dsimp [v]
    rw [norm_mul, Complex.norm_exp]
    have hre : (complexFrequency (m j₀) * (x : ℂ)).re = 0 := by
      unfold complexFrequency
      simp
    rw [hre, Real.exp_zero, mul_one]
    exact hc
  obtain ⟨i, hi⟩ := exists_frequencyDerivativeMatrix_mulVec_large
    m hinj hne hm v j₀ a ha hv
  refine ⟨i.val + 2, by omega, by omega, ?_⟩
  rw [iteratedDeriv_realExponentialSum]
  have heq : (∑ j : Fin h, frequencyDerivativeMatrix m i j * v j) =
      complexExponentialSumOrder (i.val + 2) m c (x : ℂ) := by
    unfold frequencyDerivativeMatrix v complexExponentialSumOrder
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [heq] at hi
  have hz := hreal (i.val + 2) x
  have hcomplex : complexExponentialSumOrder (i.val + 2) m c (x : ℂ) =
      ((complexExponentialSumOrder (i.val + 2) m c (x : ℂ)).re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using hz
  rw [hcomplex, Complex.norm_real, Real.norm_eq_abs] at hi
  exact hi

end Erdos522

end AmalgamatedModule1


/-! ===== amalgamated from LeanOscillatory.Mathlib.Analysis.Complex.Trigonometric ===== -/

section AmalgamatedModule2

open CauSeq Finset IsAbsoluteValue
open scoped ComplexConjugate

namespace Complex

variable (x y : ℂ)

theorem conj_exp_ofReal_mul_I (x : ℝ) : conj (exp (x * I)) = exp (-(x * I)) := by simp [← exp_conj]

end Complex

end AmalgamatedModule2


/-! ===== amalgamated from LeanOscillatory.Mathlib.Analysis.Calculus.TangentCone.Real ===== -/

section AmalgamatedModule3

open Filter Set
open scoped Topology NNReal

section Real

-- theorem uniqueDiffOn_uIcc {a b : ℝ} (hab : a ≠ b) : UniqueDiffOn ℝ (uIcc a b) :=
--   uniqueDiffOn_Icc <| min_lt_max.mpr hab

-- -- maybe not needed
-- theorem uniqueDiffOn_uIoo (a b : ℝ) : UniqueDiffOn ℝ (uIoo a b) := uniqueDiffOn_Ioo _ _

-- -- maybe not needed
-- theorem uniqueDiffOn_uIoc (a b : ℝ) : UniqueDiffOn ℝ (uIoc a b) := uniqueDiffOn_Ioc _ _

end Real

end AmalgamatedModule3


/-! ===== amalgamated from LeanOscillatory.Mathlib.Analysis.Calculus.Deriv.Inv' ===== -/

section AmalgamatedModule4

/-!
# Derivatives of `x ↦ x⁻¹` and `f x / g x`

In this file we prove `(x⁻¹)' = -1 / x ^ 2`, `((f x)⁻¹)' = -f' x / (f x) ^ 2`, and
`(f x / g x)' = (f' x * g x - f x * g' x) / (g x) ^ 2` for different notions of derivative.

For a more detailed overview of one-dimensional derivatives in mathlib, see the module docstring of
`Analysis/Calculus/Deriv/Basic`.

## Keywords

derivative
-/
universe u

open scoped Topology
open Filter Asymptotics Set

open ContinuousLinearMap (toSpanSingleton)

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] {x : 𝕜} {s : Set 𝕜}
variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
variable {c : 𝕜 → 𝕜'} {c' : 𝕜'}

section Inverse

@[to_fun]
theorem HasDerivWithinAt.inv' (hc : HasDerivWithinAt c c' s x) (hx : c x ≠ 0) :
    HasDerivWithinAt (c⁻¹) (-c' / c x ^ 2) s x := by
  convert! (hasDerivAt_inv hx).comp_hasDerivWithinAt x hc using 1
  ring

@[to_fun]
theorem HasDerivAt.inv' (hc : HasDerivAt c c' x) (hx : c x ≠ 0) :
    HasDerivAt (c⁻¹) (-c' / c x ^ 2) x := by
  rw [← hasDerivWithinAt_univ] at *
  exact hc.inv' hx

theorem derivWithin_fun_inv'' (hc : DifferentiableWithinAt 𝕜 c s x) (hx : c x ≠ 0) :
    derivWithin (fun x => (c x)⁻¹) s x = -derivWithin c s x / c x ^ 2 := by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (hc.hasDerivWithinAt.inv' hx).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

theorem derivWithin_inv'' (hc : DifferentiableWithinAt 𝕜 c s x) (hx : c x ≠ 0) :
    derivWithin (c⁻¹) s x = -derivWithin c s x / c x ^ 2 :=
  derivWithin_fun_inv'' hc hx

@[simp]
theorem deriv_fun_inv''' (hc : DifferentiableAt 𝕜 c x) (hx : c x ≠ 0) :
    deriv (fun x => (c x)⁻¹) x = -deriv c x / c x ^ 2 :=
  (hc.hasDerivAt.inv' hx).deriv

@[simp]
theorem deriv_inv''' (hc : DifferentiableAt 𝕜 c x) (hx : c x ≠ 0) :
    deriv (c⁻¹) x = -deriv c x / c x ^ 2 :=
  (hc.hasDerivAt.inv' hx).deriv

end Inverse

end AmalgamatedModule4


/-! ===== amalgamated from LeanOscillatory.VanDerCorput ===== -/

section AmalgamatedModule5

/-
Copyright (c) 2025 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos, Manasa Praveen
-/
-- public import LeanOscillatory.Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Van der Corput's lemma

We prove van der Corput's lemma for oscillatory integrals of the first kind
in one real variable, following Stein.

## Main definitions

* `Oscillatory.VanDerCorput.c`: the constant `5 * 2 ^ (k - 1) - 2` appearing in the bound.

## Main statements

* `Oscillatory.norm_integral_exp_mul_I_le_of_order_one`:
  Vector-valued amplitude, first order case
* `Oscillatory.norm_integral_exp_mul_I_le_of_order_one'`:
  Scalar constant amplitude version, first order case
* `Oscillatory.norm_integral_exp_mul_I_le_of_order_ge_two`:
  Vector-valued amplitude, higher-order case
* `Oscillatory.norm_integral_exp_mul_I_le_of_order_ge_two'`:
  Scalar constant amplitude version, higher-order case

## Notes

Following the standard argument, we first prove the constant amplitude cases
and then extend to arbitrary amplitudes.

## References

* E. M. Stein, *Harmonic Analysis: Real-Variable Methods, Orthogonality and Oscillatory
  Integrals*, Ch. VIII.1, Prop. 2, pp. 332–334.

-/
namespace Oscillatory

open Set Complex Real Function intervalIntegral Interval

/-- Compatibility lemma for Mathlib versions predating `uniqueDiffOn_uIcc`. -/
theorem uniqueDiffOn_uIcc {a b : ℝ} (h : a ≠ b) :
    UniqueDiffOn ℝ [[a, b]] := by
  rcases lt_or_gt_of_ne h with hab | hba
  · rw [uIcc_of_le hab.le]
    exact uniqueDiffOn_Icc hab
  · rw [uIcc_of_ge hba.le]
    exact uniqueDiffOn_Icc hba

open scoped ComplexConjugate

namespace VanDerCorput

/-- The constant appearing in van der Corput's lemma. Note: `c 0` is a junk value. -/
protected abbrev c (k : ℕ) : ℝ := 5 * 2 ^ (k - 1) - 2

open VanDerCorput (c)

protected theorem c_rec {k : ℕ} (hk : k ≠ 0) : c (k + 1) = 2 * c k + 2 := by
  simp only [c, add_tsub_cancel_right]
  conv_lhs => rw [show k = (k - 1) + 1 by lia]
  ring

protected theorem c_pos : ∀ k : ℕ, 0 < c k
| 0 => by norm_num
| 1 => by norm_num
| k + 2 => by rw [VanDerCorput.c_rec (by lia)]; positivity [VanDerCorput.c_pos (k + 1)]

end VanDerCorput

open VanDerCorput (c c_pos c_rec)

variable {a b : ℝ} {L : ℝ}
variable {φ : ℝ → ℝ}
variable {k : ℕ}

section GeneralLemma

variable {α β : Type*}
variable [TopologicalSpace α] [LinearOrder β] [TopologicalSpace β] [OrderClosedTopology β]

variable [Group β] [MulLeftMono β]

-- Find correct file. `Topology/Connected/Basic.lean` does not import absolute value
@[to_additive]
theorem _root_.IsPreconnected.forall_le_or_forall_le_of_forall_le_mabs {s : Set α}
    (hs : IsPreconnected s) {L : β} (hL : 1 < L) {f : α → β}
    (hfcont : ContinuousOn f s) (hf : ∀ x ∈ s, L ≤ |f x|ₘ) :
    (∀ x ∈ s, L ≤ f x) ∨ (∀ x ∈ s, L ≤ (f x)⁻¹) := by
  obtain (h | h) := hs.mapsTo_Ioi_or_Iio (b := 1) hfcont (fun x hx h ↦
    not_le_of_gt hL <| by simpa [mabs_one, h] using hf x hx)
  · grind [MapsTo, mabs_of_one_lt]
  · grind [MapsTo, mabs_of_lt_one]

-- #find_home! IsPreconnected.forall_le_or_forall_le_of_forall_le_mabs

end GeneralLemma

/-- Auxiliary lemma used in the higher-order proof -/
private theorem exists_le_abs_of_le_derivWithin
    {L : ℝ} (hL : 0 < L) (hφ : ContDiffOn ℝ 1 φ [[a, b]])
    (h : ∀ x ∈ [[a, b]], L ≤ derivWithin φ [[a, b]] x) :
    ∃ c ∈ [[a, b]], ∀ x ∈ [[a, b]], L * |x - c| ≤ |φ x| := by
  obtain (rfl | hab) := eq_or_ne a b
  · simp
  have hφ' := hφ.continuousOn
  have hmvt : ∀ x ∈ [[a, b]], ∀ y ∈ [[a, b]], x ≤ y → L * (y - x) ≤ φ y - φ x := by
    suffices hg : MonotoneOn (fun x ↦ φ x - L * x) [[a, b]] by
      intro x hx y hy hxy; linarith only [hg hx hy hxy]
    have := (hφ.differentiableOn one_ne_zero).mono interior_subset
    refine monotoneOn_of_deriv_nonneg (convex_uIcc ..) (by fun_prop) (by fun_prop) fun x hx ↦ ?_
    have hdx := this.differentiableAt <| isOpen_interior.mem_nhds hx
    have hx' := interior_subset hx
    rw [deriv_fun_sub hdx (by fun_prop), deriv_const_mul L differentiableAt_fun_id,
      deriv_id'', ← hdx.derivWithin (uniqueDiffOn_uIcc hab x hx')]
    simpa using h x hx'
  have hmon : MonotoneOn φ [[a, b]] := fun x hx y hy hxy ↦
    le_add_neg_iff_le.mp <| le_trans (by positivity) <| hmvt _ hx _ hy hxy
  have hmin : min a b ∈ [[a, b]] := ⟨le_rfl, min_le_max⟩
  have hmax : max a b ∈ [[a, b]] := ⟨min_le_max, le_rfl⟩
  -- If `φ` is non-neg. at left endpoint, take `c` to be left endpoint
  rcases le_or_gt 0 (φ (min a b)) with hm | hm
  · refine ⟨min a b, hmin, fun x hx ↦ ?_⟩
    rw [abs_of_nonneg (sub_nonneg.mpr hx.1), abs_of_nonneg (le_trans hm <| hmon hmin hx hx.1)]
    linarith [hmvt _ hmin _ hx hx.1, hx.1]
  -- If `φ` is non-pos. at right endpoint, take `c` to be right endpoint
  rcases le_or_gt (φ (max a b)) 0 with hM | hM
  · refine ⟨max a b, hmax, fun x hx ↦ ?_⟩
    rw [abs_of_nonpos (sub_nonpos.mpr hx.2), abs_of_nonpos (le_trans (hmon hx hmax hx.2) hM)]
    linarith [hmvt _ hx _ hmax hx.2, hx.2]
  -- Otherwise, `φ` has a zero. Take `c` so that `φ c = 0`
  have h0 : 0 ∈ [[φ (min a b), φ (max a b)]] := by grind [uIcc_of_le <| le_of_lt <| lt_trans hm hM]
  obtain ⟨c, hc, hfc⟩ := intermediate_value_uIcc
    (hφ.continuousOn.mono (uIcc_subset_uIcc hmin hmax)) h0
  have hc' := uIcc_subset_uIcc hmin hmax hc
  refine ⟨c, hc', fun x hx ↦ ?_⟩
  rcases le_or_gt c x with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr h), abs_of_nonneg (by linarith only [hmon hc' hx h, hfc])]
    linarith only [hmvt _ hc' _ hx h, hfc]
  · rw [abs_of_neg (sub_neg.mpr h), abs_of_nonpos (by linarith only [hmon hx hc' h.le, h, hfc])]
    linarith only [hmvt _ hx _ hc' h.le, hfc]

section SpecialCase

/-- **Van der Corput's lemma**. Special case of `norm_integral_exp_mul_I_le_of_order_one`
  where the amplitude function is constant and scalar. -/
theorem norm_integral_exp_mul_I_le_of_order_one'
    (hφ : ContDiffOn ℝ 2 φ [[a, b]]) (h : ∀ x ∈ [[a, b]], L ≤ |derivWithin φ [[a, b]] x|)
    (hφ'_mono : MonotoneOn (derivWithin φ [[a, b]]) [[a, b]]) (hL : 0 < L) :
    ‖∫ x in a..b, exp (φ x * I)‖ ≤ c 1 * L⁻¹ := by
  wlog! hab : a ≠ b
  · simp only [hab, integral_same, norm_zero]; positivity
  have hud := uniqueDiffOn_uIcc hab
  /- `φ` is smooth of order `2` on `[[a, b]]`, hence continuous there, and its derivative within
  `[[a, b]]`, denoted by `φ'`, is continuous on `[[a, b]]`. -/
  have _ := hφ.continuousOn
  let φ' := fun x ↦ derivWithin φ [[a, b]] x
  have hasDerivAt_φ : ∀ x ∈ [[a, b]], HasDerivWithinAt φ (φ' x) [[a, b]] x := fun x hx ↦
    ((hφ.contDiffWithinAt hx).differentiableWithinAt (by norm_num)).hasDerivWithinAt
  have hφ'_cont := hφ.continuousOn_derivWithin hud (by norm_num)
  /- Since `[[a, b]]` is connected and `L ≤ |φ'|` on `[[a, b]]`, either `φ' ≥ L` or `φ' ≤ -L`
  everywhere on this set, so `L ≤ ‖φ' x‖` for all `x ∈ [[a, b]]`. The second derivative of `φ`,
  denoted `φ''`, is also continuous on `[[a, b]]`. -/
  have h' := isPreconnected_uIcc.forall_le_or_forall_le_of_forall_le_abs hL hφ'_cont h
  have hφ'_norm {x : ℝ} (hx : x ∈ [[a, b]]) : L ≤ ‖φ' x‖ := by simpa using h x hx
  let φ'' := fun x ↦ derivWithin φ' [[a, b]] x
  have hasDerivAt_φ' : ∀ x ∈ [[a, b]], HasDerivWithinAt φ' (φ'' x) [[a, b]] x :=
    fun x hx ↦ (hφ.contDiffWithinAt hx).derivWithin (m := 1) hud (by norm_num) hx |>
      fun h ↦ (h.differentiableWithinAt <| by norm_num).hasDerivWithinAt
  have hφ''_cont : ContinuousOn φ'' [[a, b]] := by
    simpa [φ'', iteratedDerivWithin_succ, iteratedDerivWithin_one] using
      hφ.continuousOn_iteratedDerivWithin (m := 2) (by norm_num) hud
  /- The rough idea is just to integrate by parts to gain the factor `L⁻¹`, where we
  express the integrand `exp (φ x * I)` as `u * v'` with `u := (φ' x * I)⁻¹` and
  `v' := φ' x * I * exp (φ x * I)`. -/
  let u := fun x ↦ (φ' x * I)⁻¹
  let v := fun x ↦ exp (φ x * I)
  let u' := fun x ↦ (φ'' x) * I / (φ' x) ^ 2
  let v' := fun x ↦ φ' x * I * exp (φ x * I)
  /- These help automation to succeed later -/
  have hφ'_nz {x : ℝ} (hx : x ∈ [[a, b]]) : φ' x ≠ 0 := by grind
  have hnz1 {x : ℝ} (hx : x ∈ [[a, b]]) : φ' x * I ≠ 0 := by simp [hφ'_nz hx]
  have hnz2 {x : ℝ} (hx : x ∈ [[a, b]]) : ((φ' x) ^ 2 : ℂ) ≠ 0 := by simp [hφ'_nz hx]
  /- The derivatives of `u` and `v` are `u'` and `v'`, respectively. -/
  have hasDerivAt_u : ∀ x ∈ [[a, b]], HasDerivWithinAt u (u' x) [[a, b]] x := fun x hx ↦ by
    convert! HasDerivWithinAt.inv' (.mul (.ofReal_comp <| hasDerivAt_φ' _ hx)
        (hasDerivWithinAt_const _ _ I)) (hnz1 hx) using 1
    simp [mul_pow, u']
  have hasDerivAt_v : ∀ x ∈ [[a, b]], HasDerivWithinAt v (v' x) [[a, b]] x := fun x hx ↦ by
    convert! HasDerivWithinAt.cexp (.mul (.ofReal_comp <| hasDerivAt_φ _ hx)
      (hasDerivWithinAt_const _ _ I)) using 1
    simp [v']; ring
  have h1 : ∫ x in a..b, exp (φ x * I) = u b * v b - u a * v a - ∫ x in a..b, u' x * v x := by
    suffices h'' : ∀ x ∈ [[a, b]], exp (φ x * I) = u x * v' x by
      rw [integral_congr h'']
      refine integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt hasDerivAt_u hasDerivAt_v ?_ ?_
        <;> exact ContinuousOn.intervalIntegrable (by fun_prop)
    grind only
  -- The boundary terms are each bounded by `L⁻¹`
  have h2 {x : ℝ} (hx : x ∈ [[a, b]]) : ‖u x * v x‖ ≤ L⁻¹ := by
    simpa [u, v, field, hL.trans_le (h x hx), φ'] using h x hx
  /- We want to estimate the integral `∫ x in a..b, u' x * v x`. We first recognize that
  `‖u' x‖` is the derivative of `fun y ↦ -(φ' y)⁻¹` evaluated at `x`. -/
  have hasDerivAt_φ'_int : ∀ x ∈ uIoo a b, HasDerivWithinAt (fun x ↦ -(φ' x)⁻¹)
      (φ'' x / (φ' x) ^ 2) (Ioi x) x := fun x hx ↦ by
    have hx' := uIoo_subset_uIcc_self hx
    have := hasDerivAt_φ' x hx' |>.mono uIoo_subset_uIcc_self |>.hasDerivAt (isOpen_Ioo.mem_nhds hx)
    simpa [neg_div] using! this.inv (hφ'_nz hx') |>.neg.hasDerivWithinAt
  have hnorm_u'_eq : ∀ x ∈ [[a, b]], ‖u' x‖ = φ'' x / (φ' x) ^ 2 := fun x hx ↦ by
    simp_all [u', φ'', φ', hφ'_mono.derivWithin_nonneg (x := x)]
  /- This is the key estimate, independent of `a, b`. We realize the integrand as the derivative of
  `fun x ↦ (φ' x)⁻¹` and apply the fundamental theorem of calculus. Since `|φ'| ≥ L > 0` and `φ'`
  is continuous (therefore always positive or always negative), `|(φ' b)⁻¹ - (φ' a)⁻¹| ≤ L⁻¹`. -/
  have h3 : ‖∫ x in a..b, u' x * v x‖ ≤ L⁻¹ := calc
    ‖∫ x in a..b, u' x * v x‖ ≤ |∫ x in a..b, ‖u' x * v x‖| := norm_integral_le_abs_integral_norm
    _ = |∫ x in a..b, φ'' x / (φ' x) ^ 2| := by simp [v, integral_congr hnorm_u'_eq]
    _ = |(φ' b)⁻¹ - (φ' a)⁻¹| := by
      rw [integral_eq_sub_of_hasDeriv_right ?cont hasDerivAt_φ'_int ?int]
      case int => exact ContinuousOn.intervalIntegrable <| by fun_prop (discharger := grind)
      case cont => fun_prop (discharger := grind)
      grind
    _ ≤ L⁻¹ := by
      -- To get the right constant, want `≤ L⁻¹`, not `2 * L⁻¹` here,
      -- so we can't just use the triangle inequality.
      suffices hrange : (∀ x ∈ [[a, b]], (φ' x)⁻¹ ≤ L⁻¹ ∧ 0 ≤ (φ' x)⁻¹) ∨
          (∀ x ∈ [[a, b]], (φ' x)⁻¹ ≤ 0 ∧ -L⁻¹ ≤ (φ' x)⁻¹) by
        rcases hrange with h | h <;> grind [h a left_mem_uIcc, h b right_mem_uIcc]
      refine h'.imp ?_ ?_ <;> refine forall₂_imp fun x hx hφL ↦ ?_
      · have : 0 < φ' x := by linarith only [hL, hφL]
        field_simp
        simpa using hφL
      · have : (φ' x)⁻¹ < 0 := by rw [inv_neg'']; linarith only [hL, hφL]
        exact ⟨this.le, by rwa [neg_le, neg_inv, inv_le_inv₀ (by simpa) ‹_›]⟩
  calc
    _ ≤ ‖∫ x in a..b, u' x * v x‖ + ‖u b * v b - u a * v a‖ := by
      rw [h1, sub_eq_neg_add]
      conv_rhs => rw [← norm_neg]
      exact norm_add_le ..
    _ ≤ L⁻¹ + 2 * L⁻¹ := by
      gcongr
      apply le_trans (norm_sub_le ..) (by linarith only [h2 left_mem_uIcc, h2 right_mem_uIcc])
    _ = _ := by ring

/-- **Van der Corput's lemma**. Special case of `norm_integral_exp_mul_I_le_of_order_ge_two`
  where the amplitude function is constant and scalar. -/
theorem norm_integral_exp_mul_I_le_of_order_ge_two' {k : ℕ} (hk : 2 ≤ k)
    (hφc : ContDiffOn ℝ k φ [[a, b]])
    (hφ : ∀ x ∈ [[a, b]], L ≤ |iteratedDerivWithin k φ [[a, b]] x|) (hL : 0 < L) :
    ‖∫ x in a..b, exp (φ x * I)‖ ≤ c k * L ^ (-(1 : ℝ) / k) := by
  wlog! hab : a < b generalizing a b
  · rcases hab.eq_or_lt with rfl | hba
    · rw [integral_same, norm_zero]
      have := c_pos k; positivity
    · convert this (by rwa [uIcc_comm]) (by rwa [uIcc_comm]) hba using 1
      rw [integral_symm, norm_neg]
  revert hk hL
  -- The idea is induction on the order `k`.
  -- If `k = 2` we use the order one theorem and show the monotonicity condition.
  induction k generalizing a b L φ with
  | zero => intro hk; contradiction
  | succ k ih =>
  intro hk hL
  have hφc' := hφc.continuousOn_iteratedDerivWithin (m := k + 1) (by rfl) (uniqueDiffOn_uIcc hab.ne)
  wlog hφ' : ∀ x ∈ [[a, b]], L ≤ iteratedDerivWithin (k + 1) φ [[a, b]] x generalizing φ L
  · rcases isPreconnected_uIcc.forall_le_or_forall_le_of_forall_le_abs hL hφc' hφ with _ | hφ'
    · contradiction
    convert! this (φ := -φ) hφc.neg (by simpa) hL ?_
        (fun x hx ↦ by rw [iteratedDerivWithin_neg]; linarith only [hφ' x hx]) using 1
    · simp [← conj_exp_ofReal_mul_I, intervalIntegral_conj]
    · convert hφc'.neg using 2
      exact iteratedDerivWithin_neg _
  -- Main idea: split the integral into three pieces: `[a, d - δ]`, `[d - δ, d + δ]`, `[d + δ, b]`
  -- `δ` is small and carefully chosen, `d` is argmin of `|φ^(k) x|`,
  -- so that `δ`-away from `d` we have a good lower bound on `|φ^(k) x|` which allows us
  -- to use the inductive hypothesis (or the order one theorem).
  let δ := L ^ (-(1 : ℝ) / (k + 1))
  obtain ⟨d, hd, hd'⟩ := exists_le_abs_of_le_derivWithin (L := L) (hL := hL)
    ((contDiffOn_nat_succ_iff_contDiffOn_one_iteratedDerivWithin
      <| uniqueDiffOn_uIcc hab.ne).mp hφc |>.2)
    (by rwa [iteratedDerivWithin_succ] at hφ')
  let c₁ := max a (d - δ)
  let c₂ := min b (d + δ)
  have hδ_pos : 0 < δ := by positivity
  have ⟨had, hdb⟩ : a ≤ d ∧ d ≤ b := by rwa [uIcc_of_le hab.le] at hd
  have hδ : |c₂ - c₁| ≤ 2 * δ := by
    grind [max_le had (sub_le_self d hδ_pos.le), le_min hdb (le_add_of_nonneg_right hδ_pos.le)]
  have hc₁_mem : c₁ ∈ [[a, b]] :=
    ⟨le_trans (min_le_left a b) (le_max_left a (d - δ)),
     max_le (le_max_left a b) (le_trans (sub_le_self d hδ_pos.le) hd.2)⟩
  have hc₂_mem : c₂ ∈ [[a, b]] :=
    ⟨le_min (min_le_right a b) (le_trans hd.1 (le_add_of_nonneg_right hδ_pos.le)),
     le_trans (min_le_left b (d + δ)) (le_max_right a b)⟩
  have hac₁ : [[a, c₁]] ⊆ [[a, b]] := uIcc_subset_uIcc left_mem_uIcc hc₁_mem
  have hc₁b : [[c₁, b]] ⊆ [[a, b]] := uIcc_subset_uIcc hc₁_mem right_mem_uIcc
  have hc₁c₂ : [[c₁, c₂]] ⊆ [[a, b]] := uIcc_subset_uIcc hc₁_mem hc₂_mem
  have hc₂b : [[c₂, b]] ⊆ [[a, b]] := uIcc_subset_uIcc hc₂_mem right_mem_uIcc
  have hud := uniqueDiffOn_uIcc hab.ne
  replace hk : 1 ≤ k := by omega
  -- If `k = 1` we will need the monotonicity condition of the order one theorem.
  have hmono_ab (hk : k = 1) : MonotoneOn (derivWithin φ [[a, b]]) [[a, b]] := by
    subst hk
    have hC1 := contDiffOn_nat_succ_iff_contDiffOn_one_iteratedDerivWithin hud |>.mp hφc |>.2
    suffices MonotoneOn (iteratedDerivWithin 1 φ [[a, b]]) [[a, b]] from
      fun x hx y hy hxy ↦ by simpa [iteratedDerivWithin_one] using this hx hy hxy
    refine monotoneOn_of_deriv_nonneg (convex_uIcc (r := a) (s := b)) hC1.continuousOn
      ((hC1.differentiableOn (by norm_num)).mono interior_subset) fun x hx ↦ ?_
    have hx' := interior_subset hx
    have hda := ((hC1.differentiableOn (by norm_num)) x hx').differentiableAt
      (Filter.mem_of_superset (isOpen_interior.mem_nhds hx) interior_subset)
    rw [← hda.derivWithin (hud x hx'), ← iteratedDerivWithin_succ]
    exact le_trans hL.le <| hφ' x hx'
  -- This is the main estimate for the outer two pieces, unified to avoid duplication.
  have haux {α β : ℝ} (hαβ : [[α, β]] ⊆ [[a, b]])
      (hest : α ≠ β → ∀ x ∈ [[α, β]], L * δ ≤ |iteratedDerivWithin k φ [[a, b]] x|) :
      ‖∫ x in α..β, exp (φ x * I)‖ ≤ c k * (L * δ) ^ (-(1 : ℝ) / k) := by
    by_cases hαβ' : α = β
    · simp only [hαβ', integral_same, norm_zero]; have := c_pos k; positivity
    have hud_αβ := uniqueDiffOn_uIcc hαβ'
    have deriv_eq (x : ℝ) (hx : x ∈ [[α, β]]) :
        iteratedDerivWithin k φ [[α, β]] x = iteratedDerivWithin k φ [[a, b]] x := by
      simp only [iteratedDerivWithin]; congr 1
      exact iteratedFDerivWithin_subset hαβ hud_αβ hud (hφc.of_le (by norm_cast; omega)) hx
    have hψ_bd (x : ℝ) (hx : x ∈ [[α, β]]) : L * δ ≤ |iteratedDerivWithin k φ [[α, β]] x| := by
      simpa [deriv_eq x hx] using hest hαβ' x hx
    rcases eq_or_lt_of_le hk with rfl | hk'
    · -- This is the `k = 1` case: use the order one theorem
      have deq1 : ∀ z ∈ [[α, β]], derivWithin φ [[α, β]] z = derivWithin φ [[a, b]] z :=
        fun z hz ↦ by simpa only [iteratedDerivWithin_one] using deriv_eq z hz
      have hmono : MonotoneOn (derivWithin φ [[α, β]]) [[α, β]] := fun x hx y hy hxy ↦ by
        rw [deq1 x hx, deq1 y hy]
        exact hmono_ab rfl (hαβ hx) (hαβ hy) hxy
      calc _ ≤ c 1 * (L * δ)⁻¹ := norm_integral_exp_mul_I_le_of_order_one'
              (hφc.mono hαβ)
              (fun x hx ↦ by simpa only [iteratedDerivWithin_one] using hψ_bd x hx)
              hmono (by positivity)
        _ = _ := by norm_num [rpow_neg_one]
    · -- This is the `k ≥ 2` case: use inductive hypothesis
      have hψc : ContDiffOn ℝ (k : ℕ∞) φ [[α, β]] := (hφc.mono hαβ).of_le (by norm_cast; simp)
      rcases lt_or_gt_of_ne hαβ' with h | h
      · simpa [mul_comm] using ih hψc hψ_bd h hk' (by positivity)
      · rw [integral_symm, norm_neg]
        simpa [mul_comm] using ih (by rwa [uIcc_comm]) (by rwa [uIcc_comm]) h hk' (by positivity)
  -- Auxiliaries for verifying the hypothesis of `haux`.
  have hest_sub {α β : ℝ} (hαβ : [[α, β]] ⊆ [[a, b]])
      (hle : ∀ x ∈ [[α, β]], δ ≤ |x - d|) :
      ∀ x ∈ [[α, β]], L * δ ≤ |iteratedDerivWithin k φ [[a, b]] x| := fun x hx ↦ by
    have h1 : L * |x - d| ≤ |iteratedDerivWithin k φ [[a, b]] x| := by simpa using hd' x (hαβ hx)
    exact le_trans (by have := hle x hx; gcongr) h1
  have hφcont : ContinuousOn φ [[a, b]] := hφc.continuousOn
  have hf : ContinuousOn (fun x : ℝ ↦ exp (φ x * I)) [[a, b]] := by fun_prop
  have hLδ : (L * δ) ^ (-(1 : ℝ) / k) = δ := by
    rw [mul_rpow (by positivity) (by positivity), ← rpow_mul (by positivity),
      ← rpow_add (by positivity)]
    congr; field_simp; simp
  have hac₁_est : a ≠ c₁ → ∀ x ∈ [[a, c₁]], δ ≤ |x - d| := fun hne x hx ↦ by
    rw [uIcc_of_le (le_max_left a (d - δ))] at hx
    have : a < d - δ := by by_contra! hle; exact hne (max_eq_left hle).symm
    rw [abs_sub_comm, abs_of_nonneg (by linarith only [hδ_pos, hx.2, max_eq_right this.le])]
    linarith [hx.2, (max_eq_right this.le : c₁ = d - δ)]
  have hc₂b_est : c₂ ≠ b → ∀ x ∈ [[c₂, b]], δ ≤ |x - d| := fun hne x hx ↦ by
    rw [uIcc_of_le (min_le_left b (d + δ))] at hx
    have : d + δ < b := by by_contra! hle; exact hne (min_eq_left hle)
    rw [abs_of_nonneg (by linarith only [hδ_pos, hx.1, min_eq_right this.le])]
    linarith only [hδ_pos, hx.1, min_eq_right this.le]
  -- Finally we are ready to put the pieces together
  rw [← integral_add_adjacent_intervals (hf.mono hac₁ |>.intervalIntegrable)
      (hf.mono hc₁b |>.intervalIntegrable),
    ← integral_add_adjacent_intervals (hf.mono hc₁c₂ |>.intervalIntegrable)
      (hf.mono hc₂b |>.intervalIntegrable)]
  calc
    _ ≤ ‖∫ x in a..c₁, exp (φ x * I)‖ + ‖∫ x in c₁..c₂, exp (φ x * I)‖ +
        ‖∫ x in c₂..b, exp (φ x * I)‖ := by grind only [add_assoc, norm_add_le]
    _ ≤ c k * (L * δ) ^ (-(1 : ℝ) / k) + 2 * δ + c k * (L * δ) ^ (-(1 : ℝ) / k) := by
      gcongr
      · exact haux hac₁ fun hne ↦ hest_sub hac₁ (hac₁_est hne)
      · exact le_trans (norm_integral_le_of_norm_le_const fun x _ ↦
          le_of_eq <| norm_exp_ofReal_mul_I _) (by simpa using hδ)
      · exact haux hc₂b fun hne ↦ hest_sub hc₂b (hc₂b_est hne)
    _ = _ := by grind only [c_rec <|ne_zero_of_lt hk]

end SpecialCase

section GeneralCase

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [CompleteSpace E] [IsScalarTower ℝ ℂ E]
variable {ψ : ℝ → E}

/-- Auxiliary lemma for proving vector-valued amplitude versions of Van der Corput's lemma
from constant amplitude versions. -/
private theorem norm_integral_exp_mul_I_smul_le_of_norm_integral_exp_mul_I {A : ℝ} (hA : 0 < A)
    (hest : ∀ y ∈ [[a, b]], ‖∫ x in a..y, exp (φ x * I)‖ ≤ A)
    (hφ_cont : ContinuousOn φ [[a, b]]) (hψ : ContDiffOn ℝ 1 ψ [[a, b]]) :
    ‖∫ x in a..b, exp (φ x * I) • ψ x‖ ≤
      A * (‖ψ b‖ + |∫ x in a..b, ‖derivWithin ψ [[a, b]] x‖|) := by
  by_cases hab : a = b
  · simp only [hab, integral_same, norm_zero, Std.le_refl, uIcc_of_le, Icc_self, abs_zero,
    add_zero]; positivity
  have hψ'_cont := hψ.continuousOn_derivWithin (uniqueDiffOn_uIcc hab) (by norm_num)
  let F := fun x ↦ ∫ t in a..x, exp (φ t * I)
  let F' := fun x ↦ exp (φ x * I)
  let ψ' := fun x ↦ derivWithin ψ [[a, b]] x
  have hasDeriv_ψ := fun x (hx : x ∈ [[a, b]]) ↦
    (hψ.contDiffWithinAt hx).differentiableWithinAt (by norm_num) |>.hasDerivWithinAt
  have cont_F' : ContinuousOn F' [[a, b]] := by fun_prop
  have hasDeriv_F : ∀ x ∈ [[a, b]], HasDerivWithinAt F (F' x) [[a, b]] x := fun x hx ↦ by
    have := FTCFilter.nhdsUIcc (h := ⟨hx⟩)
    apply integral_hasDerivWithinAt_right (t := [[a, b]])
    · exact cont_F'.mono (uIcc_subset_uIcc_left hx) |>.intervalIntegrable
    · exact cont_F'.stronglyMeasurableAtFilter_nhdsWithin measurableSet_uIcc _
    · exact cont_F'.continuousWithinAt hx
  have h1 : ∫ x in a..b, F x • ψ' x = F b • ψ b - F a • ψ a - ∫ x in a..b, F' x • ψ x := by
    apply integral_smul_deriv_eq_deriv_smul_of_hasDerivWithinAt hasDeriv_F hasDeriv_ψ
      <;> { apply ContinuousOn.intervalIntegrable; fun_prop }
  -- The main point is to integrate by parts to reduce to the constant amplitude case.
  calc
    _ = ‖F b • ψ b - F a • ψ a - ∫ x in a..b, F x • ψ' x‖ := by simp only [h1, sub_sub_cancel, F']
    _ ≤ ‖F b‖ * ‖ψ b‖ + |∫ x in a..b, A * ‖ψ' x‖| := by
      rw [show F a = 0 from integral_same, zero_smul, sub_zero]
      apply le_trans <| norm_sub_le ..
      apply add_le_add (le_of_eq <| norm_smul ..)
      apply norm_integral_le_abs_of_norm_le
      · apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_uIoc
        intro x hx; rw [norm_smul]; gcongr
        exact hest _ <| uIoc_subset_uIcc hx
      · apply ContinuousOn.intervalIntegrable; fun_prop
    _ ≤ A * ‖ψ b‖ + A * |∫ x in a..b, ‖ψ' x‖| := by
      gcongr
      · exact hest _ right_mem_uIcc
      · simp [integral_const_mul, abs_of_pos hA]
    _ = _ := by ring

/-- **Van der Corput's lemma** for vector-valued amplitude functions, first order case.
For second and higher order see `norm_integral_exp_mul_I_le_of_order_ge_two`. -/
theorem norm_integral_exp_mul_I_le_of_order_one
    (hφ : ContDiffOn ℝ 2 φ [[a, b]]) (hψ : ContDiffOn ℝ 1 ψ [[a, b]])
    (h : ∀ x ∈ [[a, b]], L ≤ |derivWithin φ [[a, b]] x|)
    (hφ'_mono : MonotoneOn (derivWithin φ [[a, b]]) [[a, b]])
    (hL : 0 < L) :
    ‖∫ x in a..b, exp (φ x * I) • ψ x‖ ≤
      c 1 * L⁻¹ *
        (‖ψ b‖ + |∫ x in a..b, ‖derivWithin ψ [[a, b]] x‖|) := by
  refine norm_integral_exp_mul_I_smul_le_of_norm_integral_exp_mul_I
    (by positivity) ?_ hφ.continuousOn hψ
  intro x hx
  wlog hxa : x ≠ a
  · simp only [not_not.mp hxa, integral_same, norm_zero]; positivity
  have hsubset := uIcc_subset_uIcc_left hx
  have haux : ∀ y ∈ [[a, x]], derivWithin φ [[a, x]] y = derivWithin φ [[a, b]] y := by
    intro y hy
    refine ((hφ.contDiffWithinAt <| hsubset hy).differentiableWithinAt
      (by norm_num)).hasDerivWithinAt |>.mono hsubset |>.derivWithin ?_
    exact uniqueDiffOn_uIcc hxa.symm _ hy
  exact norm_integral_exp_mul_I_le_of_order_one' (hφ.mono hsubset)
    (fun y hy ↦ haux y hy ▸ h y (hsubset hy))
    ((hφ'_mono.mono hsubset).congr <| fun y hy ↦ (haux y hy).symm) hL

/-- **Van der Corput's lemma** for vector-valued amplitude functions, case `k ≥ 2`.
For `k = 1` see `norm_integral_exp_mul_I_le_of_order_one`. -/
theorem norm_integral_exp_mul_I_le_of_order_ge_two {k : ℕ} (hk : 2 ≤ k)
    (hφ : ContDiffOn ℝ k φ [[a, b]]) (hψ : ContDiffOn ℝ 1 ψ [[a, b]])
    (h : ∀ x ∈ [[a, b]], L ≤ |iteratedDerivWithin k φ [[a, b]] x|)
    (hL : 0 < L) :
    ‖∫ x in a..b, exp (φ x * I) • ψ x‖ ≤
      c k * L ^ ((-1 : ℝ) / k) *
        (‖ψ b‖ + |∫ x in a..b, ‖derivWithin ψ [[a, b]] x‖|) := by
  refine norm_integral_exp_mul_I_smul_le_of_norm_integral_exp_mul_I
    (by have := c_pos k; positivity) ?_ hφ.continuousOn hψ
  intro x hx
  have hsubset := uIcc_subset_uIcc_left hx
  wlog hxa : x ≠ a
  · rw [not_not.mp hxa, integral_same, norm_zero]; have := c_pos k; positivity
  have hud_ax := uniqueDiffOn_uIcc (Ne.symm hxa)
  have hab : a ≠ b := by rintro rfl; exact hxa (mem_singleton_iff.mp (by simpa using hx))
  refine norm_integral_exp_mul_I_le_of_order_ge_two' hk (hφ.mono hsubset)
    (fun y hy ↦ ?deriv_est) hL
  rw [show iteratedDerivWithin k φ [[a, x]] y = iteratedDerivWithin k φ [[a, b]] y by
    simp only [iteratedDerivWithin]; congr 1
    exact iteratedFDerivWithin_subset hsubset hud_ax (uniqueDiffOn_uIcc hab)
      (hφ.of_le (by norm_cast)) hy]
  exact h y (hsubset hy)

end GeneralCase

end Oscillatory

end AmalgamatedModule5


/-! ===== amalgamated from Research.PiecewiseVanDerCorput ===== -/

section AmalgamatedModule6


open MeasureTheory Set Complex Real Function intervalIntegral
open scoped BigOperators ComplexConjugate

namespace Erdos522

/-- Sum van der Corput over a finite interval partition, allowing a different
derivative order on each cell. -/
theorem norm_intervalIntegral_cexp_le_piecewise_vanDerCorput
    (H J : ℕ) (hH : 2 ≤ H) (L : ℝ) (hL : 1 ≤ L)
    (x : ℕ → ℝ) (φ : ℝ → ℝ)
    (hφ : ContDiff ℝ H φ)
    (hcell : ∀ j < J, ∃ r : ℕ, 2 ≤ r ∧ r ≤ H ∧
      ∀ y ∈ Set.uIcc (x j) (x (j + 1)),
        L ≤ |iteratedDerivWithin r φ (Set.uIcc (x j) (x (j + 1))) y|) :
    ‖∫ y in x 0..x J, Complex.exp (φ y * Complex.I)‖ ≤
      (J : ℝ) * (5 * 2 ^ H) * L ^ (-(1 : ℝ) / H) := by
  have hHpos : (0 : ℝ) < H := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hH)
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hrpow0 : 0 ≤ L ^ (-(1 : ℝ) / H) := Real.rpow_nonneg (le_trans zero_le_one hL) _
  have hpiece (j : ℕ) (hj : j < J) :
      ‖∫ y in x j..x (j + 1), Complex.exp (φ y * Complex.I)‖ ≤
        (5 * 2 ^ H) * L ^ (-(1 : ℝ) / H) := by
    obtain ⟨r, hr2, hrH, hr⟩ := hcell j hj
    have hHr : (0 : ℝ) < r := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hr2)
    have hvdc := Oscillatory.norm_integral_exp_mul_I_le_of_order_ge_two'
      hr2 (hφ.contDiffOn.of_le (by exact_mod_cast hrH)) hr hLpos
    refine hvdc.trans ?_
    have hc : Oscillatory.VanDerCorput.c r ≤ (5 : ℝ) * 2 ^ H := by
      unfold Oscillatory.VanDerCorput.c
      have hp : (2 : ℝ) ^ (r - 1) ≤ 2 ^ H := by
        exact pow_le_pow_right₀ (by norm_num) (by omega)
      nlinarith [show (0 : ℝ) ≤ 2 ^ (r - 1) by positivity]
    have hexp : -(1 : ℝ) / r ≤ -(1 : ℝ) / H := by
      have hrle : (r : ℝ) ≤ H := by exact_mod_cast hrH
      have hinv : (H : ℝ)⁻¹ ≤ (r : ℝ)⁻¹ :=
        (inv_le_inv₀ hHpos hHr).2 hrle
      simpa [div_eq_mul_inv] using neg_le_neg hinv
    have hpow : L ^ (-(1 : ℝ) / r) ≤ L ^ (-(1 : ℝ) / H) :=
      Real.rpow_le_rpow_of_exponent_le hL hexp
    exact mul_le_mul hc hpow (Real.rpow_nonneg hLpos.le _) (by positivity)
  have hint (j : ℕ) (hj : j < J) : IntervalIntegrable
      (fun y => Complex.exp (φ y * Complex.I)) volume (x j) (x (j + 1)) := by
    have hc : Continuous (fun y => Complex.exp (φ y * Complex.I)) := by
      fun_prop
    exact hc.intervalIntegrable (x j) (x (j + 1))
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hint
  rw [← hsum]
  calc
    ‖∑ j ∈ Finset.range J,
        ∫ y in x j..x (j + 1), Complex.exp (φ y * Complex.I)‖ ≤
        ∑ j ∈ Finset.range J,
          ‖∫ y in x j..x (j + 1), Complex.exp (φ y * Complex.I)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range J,
        ((5 : ℝ) * 2 ^ H) * L ^ (-(1 : ℝ) / H) := by
      exact Finset.sum_le_sum fun j hj => hpiece j (Finset.mem_range.mp hj)
    _ = (J : ℝ) * (5 * 2 ^ H) * L ^ (-(1 : ℝ) / H) := by
      simp
      ring

end Erdos522

end AmalgamatedModule6


/-! ===== amalgamated from Research.UniformGridVanDerCorput ===== -/

section AmalgamatedModule7


open MeasureTheory Set Complex Real Function intervalIntegral
open scoped BigOperators ComplexConjugate

namespace Erdos522

noncomputable def circleGridPoint (J j : ℕ) : ℝ :=
  -Real.pi + (j : ℝ) * (2 * Real.pi / J)

lemma circleGridPoint_zero (J : ℕ) : circleGridPoint J 0 = -Real.pi := by
  simp [circleGridPoint]

lemma circleGridPoint_self (J : ℕ) (hJ : 0 < J) :
    circleGridPoint J J = Real.pi := by
  unfold circleGridPoint
  field_simp
  ring

lemma circleGridPoint_succ_sub (J j : ℕ) :
    circleGridPoint J (j + 1) - circleGridPoint J j = 2 * Real.pi / J := by
  unfold circleGridPoint
  push_cast
  ring

/-- A uniform-grid finite-type criterion for an oscillatory integral. -/
theorem norm_intervalIntegral_cexp_le_of_uniform_finiteType
    (H J : ℕ) (hH : 2 ≤ H) (hJ : 0 < J)
    (δ M : ℝ) (hδ : 2 ≤ δ) (hM : 0 ≤ M)
    (hmesh : M * (2 * Real.pi / J) ≤ δ / 2)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ H φ)
    (hfinite : ∀ x : ℝ, ∃ r : ℕ, 2 ≤ r ∧ r ≤ H ∧
      δ ≤ |iteratedDeriv r φ x|)
    (hlip : ∀ r : ℕ, r ≤ H → ∀ x y : ℝ,
      |iteratedDeriv r φ y - iteratedDeriv r φ x| ≤ M * |y - x|) :
    ‖∫ y in -Real.pi..Real.pi, Complex.exp (φ y * Complex.I)‖ ≤
      (J : ℝ) * (5 * 2 ^ H) * (δ / 2) ^ (-(1 : ℝ) / H) := by
  let x : ℕ → ℝ := circleGridPoint J
  have hstep : 0 < 2 * Real.pi / (J : ℝ) := by positivity
  have hmono (j : ℕ) : x j < x (j + 1) := by
    have hs := circleGridPoint_succ_sub J j
    dsimp [x]
    linarith
  have hcell : ∀ j < J, ∃ r : ℕ, 2 ≤ r ∧ r ≤ H ∧
      ∀ y ∈ Set.uIcc (x j) (x (j + 1)),
        δ / 2 ≤ |iteratedDerivWithin r φ
          (Set.uIcc (x j) (x (j + 1))) y| := by
    intro j hj
    obtain ⟨r, hr2, hrH, hr⟩ := hfinite (x j)
    refine ⟨r, hr2, hrH, ?_⟩
    intro y hy
    have hxy : x j ≤ y ∧ y ≤ x (j + 1) := by
      rw [Set.uIcc_of_le (hmono j).le] at hy
      exact hy
    have hydist : |y - x j| ≤ 2 * Real.pi / J := by
      rw [abs_of_nonneg (sub_nonneg.mpr hxy.1)]
      have hs := circleGridPoint_succ_sub J j
      linarith
    have hdiff := (hlip r hrH (x j) y).trans
      (mul_le_mul_of_nonneg_left hydist hM)
    have hdiff' :
        |iteratedDeriv r φ y - iteratedDeriv r φ (x j)| ≤ δ / 2 :=
      hdiff.trans hmesh
    have hlower : δ / 2 ≤ |iteratedDeriv r φ y| := by
      have habs := abs_sub_abs_le_abs_sub
        (iteratedDeriv r φ (x j)) (iteratedDeriv r φ y)
      rw [abs_sub_comm] at habs
      linarith
    have hud : UniqueDiffOn ℝ (Set.uIcc (x j) (x (j + 1))) := by
      rw [Set.uIcc_of_le (hmono j).le]
      exact uniqueDiffOn_Icc (hmono j)
    rw [iteratedDerivWithin_eq_iteratedDeriv hud
      (hφ.contDiffAt.of_le (by exact_mod_cast hrH)) hy]
    exact hlower
  have hvdc := norm_intervalIntegral_cexp_le_piecewise_vanDerCorput
    H J hH (δ / 2) (by linarith) x φ hφ hcell
  dsimp [x] at hvdc
  rw [circleGridPoint_zero, circleGridPoint_self J hJ] at hvdc
  exact hvdc

end Erdos522

end AmalgamatedModule7


/-! ===== amalgamated from Research.CircleCauchySchwarz ===== -/

section AmalgamatedModule8


open MeasureTheory
open scoped Interval

namespace Erdos522

/-- The probability measure in the angular parameter underlying unit-circle
averages. -/
noncomputable def circleParameterMeasure : Measure ℝ :=
  let μI := volume.restrict (Set.uIoc 0 (2 * Real.pi))
  (μI Set.univ)⁻¹ • μI

instance circleParameterMeasure_isProbability :
    IsProbabilityMeasure circleParameterMeasure := by
  rw [isProbabilityMeasure_iff]
  unfold circleParameterMeasure
  simp only [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ,
    Real.volume_uIoc, sub_zero]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr (by positivity)).ne'
    ENNReal.ofReal_ne_top

/-- Pull a planar test back to the standard unit-circle parameter. -/
noncomputable def circleParameterFunction (f : ℂ → ℝ) (θ : ℝ) : ℝ :=
  f (circleMap 0 1 θ)

lemma circleAverage_eq_integral_circleParameterMeasure (f : ℂ → ℝ) :
    Real.circleAverage f 0 1 =
      ∫ θ, circleParameterFunction f θ ∂circleParameterMeasure := by
  rw [Real.circleAverage_eq_intervalAverage]
  rfl

/-- Cauchy--Schwarz for nonnegative real functions in integral form. -/
theorem integral_mul_nonneg_le_sqrt_mul_sqrt
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ}
    (hf0 : 0 ≤ᵐ[μ] f) (hg0 : 0 ≤ᵐ[μ] g)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, f x * g x ∂μ) ≤
      √(∫ x, f x ^ 2 ∂μ) * √(∫ x, g x ^ 2 ∂μ) := by
  have hpq : (2 : ℝ).HolderConjugate 2 :=
    ⟨by norm_num, by norm_num, by norm_num⟩
  have hf' : MemLp f (ENNReal.ofReal 2) μ := by simpa using hf
  have hg' : MemLp g (ENNReal.ofReal 2) μ := by simpa using hg
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hpq hf0 hg0 hf' hg'
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  convert h using 1 <;> norm_num [Real.rpow_two]

/-- Cauchy--Schwarz for an arbitrary normalized average measure. -/
theorem average_mul_le_sqrt_mul_sqrt
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {f g : α → ℝ}
    (hf0 : 0 ≤ᵐ[(μ Set.univ)⁻¹ • μ] f)
    (hg0 : 0 ≤ᵐ[(μ Set.univ)⁻¹ • μ] g)
    (hf : MemLp f 2 ((μ Set.univ)⁻¹ • μ))
    (hg : MemLp g 2 ((μ Set.univ)⁻¹ • μ)) :
    (⨍ x, f x * g x ∂μ) ≤
      √(⨍ x, f x ^ 2 ∂μ) * √(⨍ x, g x ^ 2 ∂μ) := by
  unfold average
  have hpq : (2 : ℝ).HolderConjugate 2 :=
    ⟨by norm_num, by norm_num, by norm_num⟩
  have hf' : MemLp f (ENNReal.ofReal 2) ((μ Set.univ)⁻¹ • μ) := by
    simpa using hf
  have hg' : MemLp g (ENNReal.ofReal 2) ((μ Set.univ)⁻¹ • μ) := by
    simpa using hg
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hpq hf0 hg0 hf' hg'
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  convert h using 1 <;> norm_num [Real.rpow_two]

/-- Cauchy--Schwarz in exactly the normalization used by `circleAverage`. -/
theorem circleAverage_mul_le_sqrt_mul_sqrt
    {f g : ℂ → ℝ}
    (hf0 : ∀ z, 0 ≤ f z) (hg0 : ∀ z, 0 ≤ g z)
    (hf : MemLp (circleParameterFunction f) 2 circleParameterMeasure)
    (hg : MemLp (circleParameterFunction g) 2 circleParameterMeasure) :
    Real.circleAverage (fun z => f z * g z) 0 1 ≤
      √(Real.circleAverage (fun z => f z ^ 2) 0 1) *
        √(Real.circleAverage (fun z => g z ^ 2) 0 1) := by
  let μI := volume.restrict (Set.uIoc 0 (2 * Real.pi))
  have hμ : circleParameterMeasure = (μI Set.univ)⁻¹ • μI := rfl
  have hf0ae : 0 ≤ᵐ[circleParameterMeasure] circleParameterFunction f :=
    Filter.Eventually.of_forall fun θ => hf0 _
  have hg0ae : 0 ≤ᵐ[circleParameterMeasure] circleParameterFunction g :=
    Filter.Eventually.of_forall fun θ => hg0 _
  have h := average_mul_le_sqrt_mul_sqrt μI
    (hμ ▸ hf0ae) (hμ ▸ hg0ae) (hμ ▸ hf) (hμ ▸ hg)
  rw [Real.circleAverage_eq_intervalAverage,
    Real.circleAverage_eq_intervalAverage,
    Real.circleAverage_eq_intervalAverage]
  simpa [circleParameterFunction] using h

end Erdos522

end AmalgamatedModule8


/-! ===== amalgamated from Research.SparseExponentialOscillation ===== -/

section AmalgamatedModule9


open MeasureTheory Set Complex Real Function intervalIntegral
open scoped BigOperators ComplexConjugate

namespace Erdos522

lemma periodic_complexExponentialSumOrder_zero
    {h : ℕ} (m : Fin h → ℤ) (c : Fin h → ℂ) :
    Function.Periodic (complexExponentialSumOrder 0 m c) (2 * (Real.pi : ℂ)) := by
  intro x
  unfold complexExponentialSumOrder
  apply Finset.sum_congr rfl
  intro j hj
  simp only [pow_zero, one_mul]
  rw [mul_add, Complex.exp_add]
  have hper : Complex.exp (complexFrequency (m j) * (2 * Real.pi : ℂ)) = 1 := by
    unfold complexFrequency
    rw [show (m j : ℂ) * Complex.I * (2 * (Real.pi : ℂ)) =
        (m j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by ring]
    exact Complex.exp_int_mul_two_pi_mul_I (m j)
  rw [hper, mul_one]

lemma periodic_realExponentialSum
    {h : ℕ} (m : Fin h → ℤ) (c : Fin h → ℂ) :
    Function.Periodic (realExponentialSum m c) (2 * Real.pi) := by
  intro x
  unfold realExponentialSum
  change (complexExponentialSumOrder 0 m c
      ((x + 2 * Real.pi : ℝ) : ℂ)).re = _
  rw [show (((x + 2 * Real.pi : ℝ) : ℂ)) =
      (x : ℂ) + 2 * (Real.pi : ℂ) by push_cast; rfl]
  rw [periodic_complexExponentialSumOrder_zero m c (x : ℂ)]

/-- Sparse finite type plus a sufficiently fine uniform mesh gives fractional
oscillatory decay. -/
theorem norm_intervalIntegral_realExponentialSum_le
    (H J : ℕ) (hH : 2 ≤ H) (hJ : 0 < J)
    {h n : ℕ} (hhH : h + 1 ≤ H)
    (m : Fin h → ℤ) (hinj : Function.Injective m)
    (hne : ∀ j, m j ≠ 0) (hm : ∀ j, (m j).natAbs ≤ n)
    (c : Fin h → ℂ) (j₀ : Fin h) (a : ℝ) (ha : 0 < a)
    (hc : a ≤ ‖c j₀‖)
    (hreal : ∀ (r : ℕ) (x : ℝ),
      (complexExponentialSumOrder r m c (x : ℂ)).im = 0)
    (M : ℝ) (hM : 0 ≤ M)
    (hMbound : ∀ r : ℕ, r ≤ H →
      (∑ j : Fin h, (n : ℝ) ^ (r + 1) * ‖c j‖) ≤ M)
    (hdelta : 2 ≤ a / ((h : ℝ) * (h.factorial : ℝ) *
      ((n + 1 : ℝ) ^ (h + 1)) ^ h))
    (hmesh : M * (2 * Real.pi / J) ≤
      (a / ((h : ℝ) * (h.factorial : ℝ) *
        ((n + 1 : ℝ) ^ (h + 1)) ^ h)) / 2) :
    ‖∫ x in -Real.pi..Real.pi,
        Complex.exp (realExponentialSum m c x * Complex.I)‖ ≤
      (J : ℝ) * (5 * 2 ^ H) *
        ((a / ((h : ℝ) * (h.factorial : ℝ) *
          ((n + 1 : ℝ) ^ (h + 1)) ^ h)) / 2) ^
            (-(1 : ℝ) / H) := by
  let δ : ℝ := a / ((h : ℝ) * (h.factorial : ℝ) *
    ((n + 1 : ℝ) ^ (h + 1)) ^ h)
  let φ := realExponentialSum m c
  have hfinite (x : ℝ) : ∃ r : ℕ, 2 ≤ r ∧ r ≤ H ∧
      δ ≤ |iteratedDeriv r φ x| := by
    obtain ⟨r, hr2, hrh, hr⟩ := exists_iteratedDeriv_realExponentialSum_large
      m hinj hne hm c j₀ a ha hc hreal x
    exact ⟨r, hr2, hrh.trans hhH, hr⟩
  have hlip (r : ℕ) (hr : r ≤ H) (x y : ℝ) :
      |iteratedDeriv r φ y - iteratedDeriv r φ x| ≤ M * |y - x| := by
    exact (iteratedDeriv_realExponentialSum_sub_le r m hm c x y).trans
      (mul_le_mul_of_nonneg_right (hMbound r hr) (abs_nonneg _))
  exact norm_intervalIntegral_cexp_le_of_uniform_finiteType
    H J hH hJ δ M hdelta hM hmesh φ
      (contDiff_realExponentialSum m c H) hfinite hlip

/-- The corresponding normalized integral over the angular parameter measure
has the same bound (in fact a factor `1/(2π)` smaller). -/
theorem norm_integral_circleParameterMeasure_realExponentialSum_le
    (H J : ℕ) (hH : 2 ≤ H) (hJ : 0 < J)
    {h n : ℕ} (hhH : h + 1 ≤ H)
    (m : Fin h → ℤ) (hinj : Function.Injective m)
    (hne : ∀ j, m j ≠ 0) (hm : ∀ j, (m j).natAbs ≤ n)
    (c : Fin h → ℂ) (j₀ : Fin h) (a : ℝ) (ha : 0 < a)
    (hc : a ≤ ‖c j₀‖)
    (hreal : ∀ (r : ℕ) (x : ℝ),
      (complexExponentialSumOrder r m c (x : ℂ)).im = 0)
    (M : ℝ) (hM : 0 ≤ M)
    (hMbound : ∀ r : ℕ, r ≤ H →
      (∑ j : Fin h, (n : ℝ) ^ (r + 1) * ‖c j‖) ≤ M)
    (hdelta : 2 ≤ a / ((h : ℝ) * (h.factorial : ℝ) *
      ((n + 1 : ℝ) ^ (h + 1)) ^ h))
    (hmesh : M * (2 * Real.pi / J) ≤
      (a / ((h : ℝ) * (h.factorial : ℝ) *
        ((n + 1 : ℝ) ^ (h + 1)) ^ h)) / 2) :
    ‖∫ x, Complex.exp (realExponentialSum m c x * Complex.I)
        ∂circleParameterMeasure‖ ≤
      (J : ℝ) * (5 * 2 ^ H) *
        ((a / ((h : ℝ) * (h.factorial : ℝ) *
          ((n + 1 : ℝ) ^ (h + 1)) ^ h)) / 2) ^
            (-(1 : ℝ) / H) := by
  let f : ℝ → ℂ := fun x =>
    Complex.exp (realExponentialSum m c x * Complex.I)
  have hcp : (∫ x, f x ∂circleParameterMeasure) =
      (2 * Real.pi)⁻¹ • (∫ x in 0..2 * Real.pi, f x) := by
    unfold circleParameterMeasure
    rw [MeasureTheory.integral_smul_measure]
    simp only [Measure.restrict_apply_univ, Real.volume_uIoc, sub_zero,
      ENNReal.toReal_inv]
    rw [abs_of_pos (by positivity : 0 < 2 * Real.pi),
      ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * Real.pi)]
    rw [Set.uIoc_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
    rw [intervalIntegral.integral_of_le (by positivity)]
  have hfper : Function.Periodic f (2 * Real.pi) := by
    intro x
    dsimp [f]
    rw [periodic_realExponentialSum m c x]
  have hperiod : (∫ x in 0..2 * Real.pi, f x) =
      ∫ x in -Real.pi..Real.pi, f x := by
    have hp := hfper.intervalIntegral_add_eq 0 (-Real.pi)
    calc
      (∫ x in 0..2 * Real.pi, f x) =
          ∫ x in 0..0 + 2 * Real.pi, f x := by congr 2 <;> ring
      _ = ∫ x in -Real.pi..-Real.pi + 2 * Real.pi, f x := hp
      _ = ∫ x in -Real.pi..Real.pi, f x := by congr 2 <;> ring
  have hvdc := norm_intervalIntegral_realExponentialSum_le
    H J hH hJ hhH m hinj hne hm c j₀ a ha hc hreal M hM hMbound hdelta hmesh
  dsimp [f] at hcp hperiod
  rw [hcp, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (by positivity : 0 < 2 * Real.pi)), hperiod]
  calc
    (2 * Real.pi)⁻¹ *
        ‖∫ x in -Real.pi..Real.pi,
          Complex.exp (realExponentialSum m c x * Complex.I)‖ ≤
        1 * ‖∫ x in -Real.pi..Real.pi,
          Complex.exp (realExponentialSum m c x * Complex.I)‖ := by
      gcongr
      apply (inv_le_one₀ (by positivity : 0 < 2 * Real.pi)).mpr
      nlinarith [Real.pi_gt_three]
    _ ≤ _ := by simpa using hvdc

end Erdos522

end AmalgamatedModule9


/-! ===== amalgamated from Research.AutomaticMeshOscillation ===== -/

section AmalgamatedModule10


open MeasureTheory
open scoped BigOperators

namespace Erdos522

/-- Choose the uniform van der Corput mesh automatically by a natural ceiling.
This removes the mesh side condition at the cost of the explicit factor
`4π M / δ + 2`. -/
theorem norm_integral_circleParameterMeasure_realExponentialSum_le_autoMesh
    (H : ℕ) (hH : 2 ≤ H)
    {h n : ℕ} (hhH : h + 1 ≤ H)
    (m : Fin h → ℤ) (hinj : Function.Injective m)
    (hne : ∀ j, m j ≠ 0) (hm : ∀ j, (m j).natAbs ≤ n)
    (c : Fin h → ℂ) (j₀ : Fin h) (a : ℝ) (ha : 0 < a)
    (hc : a ≤ ‖c j₀‖)
    (hreal : ∀ (r : ℕ) (x : ℝ),
      (complexExponentialSumOrder r m c (x : ℂ)).im = 0)
    (M : ℝ) (hM : 0 ≤ M)
    (hMbound : ∀ r : ℕ, r ≤ H →
      (∑ j : Fin h, (n : ℝ) ^ (r + 1) * ‖c j‖) ≤ M)
    (hdelta : 2 ≤ a / ((h : ℝ) * (h.factorial : ℝ) *
      ((n + 1 : ℝ) ^ (h + 1)) ^ h)) :
    ‖∫ x, Complex.exp (realExponentialSum m c x * Complex.I)
        ∂circleParameterMeasure‖ ≤
      (4 * Real.pi * M /
          (a / ((h : ℝ) * (h.factorial : ℝ) *
            ((n + 1 : ℝ) ^ (h + 1)) ^ h)) + 2) *
        (5 * 2 ^ H) *
        ((a / ((h : ℝ) * (h.factorial : ℝ) *
          ((n + 1 : ℝ) ^ (h + 1)) ^ h)) / 2) ^
            (-(1 : ℝ) / H) := by
  let δ : ℝ := a / ((h : ℝ) * (h.factorial : ℝ) *
    ((n + 1 : ℝ) ^ (h + 1)) ^ h)
  let x : ℝ := 4 * Real.pi * M / δ
  let J : ℕ := ⌈x⌉₊ + 1
  have hδ : 0 < δ := lt_of_lt_of_le (by norm_num) hdelta
  have hx : 0 ≤ x := by
    dsimp [x]
    positivity
  have hJ : 0 < J := by dsimp [J]; omega
  have hJreal : x ≤ (J : ℝ) := by
    calc
      x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
      _ ≤ (J : ℝ) := by dsimp [J]; norm_num
  have hcore : 4 * Real.pi * M ≤ (J : ℝ) * δ := by
    apply (div_le_iff₀ hδ).mp
    simpa [x] using hJreal
  have hmesh : M * (2 * Real.pi / J) ≤ δ / 2 := by
    rw [show M * (2 * Real.pi / (J : ℝ)) =
      (M * (2 * Real.pi)) / (J : ℝ) by ring]
    apply (div_le_iff₀ (by exact_mod_cast hJ)).2
    nlinarith [Real.pi_pos]
  have hvdc := norm_integral_circleParameterMeasure_realExponentialSum_le
    H J hH hJ hhH m hinj hne hm c j₀ a ha hc hreal M hM hMbound
      (by simpa [δ] using hdelta) (by simpa [δ] using hmesh)
  have hJupper : (J : ℝ) ≤ x + 2 := by
    have hc := Nat.ceil_lt_add_one hx
    dsimp [J]
    push_cast
    linarith
  calc
    _ ≤ (J : ℝ) * (5 * 2 ^ H) * (δ / 2) ^ (-(1 : ℝ) / H) := by
      simpa [δ] using hvdc
    _ ≤ (x + 2) * (5 * 2 ^ H) * (δ / 2) ^ (-(1 : ℝ) / H) := by
      gcongr
    _ = _ := by rfl

end Erdos522

end AmalgamatedModule10


/-! ===== amalgamated from Research.LowRangeTupleCount ===== -/

section AmalgamatedModule11


open scoped BigOperators

namespace Erdos522

noncomputable def tupleRange {m N : ℕ} (f : Fin m → Fin N) : Finset (Fin N) :=
  Finset.univ.image f

noncomputable def lowRangeTuples (m N q : ℕ) : Finset (Fin m → Fin N) :=
  Finset.univ.filter (fun f => (tupleRange f).card ≤ q)

noncomputable def supportedTuples {m N : ℕ} (S : Finset (Fin N)) :
    Finset (Fin m → Fin N) :=
  Finset.univ.filter (fun f => ∀ i, f i ∈ S)

lemma mem_tupleRange {m N : ℕ} (f : Fin m → Fin N) (x : Fin N) :
    x ∈ tupleRange f ↔ ∃ i, f i = x := by
  simp [tupleRange]

lemma card_supportedTuples {m N : ℕ} (S : Finset (Fin N)) :
    (supportedTuples (m := m) S).card = S.card ^ m := by
  let e : {f // f ∈ supportedTuples (m := m) S} ≃ (Fin m → S) :=
    { toFun := fun f i => ⟨f.1 i, by
        have hf := (Finset.mem_filter.mp f.2).2
        exact hf i⟩
      invFun := fun g => ⟨fun i => (g i).1, by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, fun i => (g i).2⟩⟩
      left_inv := by intro f; ext i; rfl
      right_inv := by intro g; funext i; apply Subtype.ext; rfl }
  calc
    (supportedTuples (m := m) S).card =
        Fintype.card {f // f ∈ supportedTuples (m := m) S} :=
      (Fintype.card_coe _).symm
    _ = Fintype.card (Fin m → S) := Fintype.card_congr e
    _ = S.card ^ m := by simp

lemma lowRangeTuples_subset_biUnion (m N q : ℕ) :
    lowRangeTuples m N q ⊆
      (Finset.univ.powerset.filter (fun S => S.card ≤ q)).biUnion
        (fun S => supportedTuples (m := m) S) := by
  intro f hf
  have hfr := (Finset.mem_filter.mp hf).2
  let R := tupleRange f
  apply Finset.mem_biUnion.mpr
  refine ⟨R, ?_, ?_⟩
  · apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), hfr⟩
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro i
    exact (mem_tupleRange f (f i)).mpr ⟨i, rfl⟩

lemma card_subsets_card_le (N q : ℕ) (hN : 0 < N) :
    (Finset.univ.powerset.filter (fun S : Finset (Fin N) => S.card ≤ q)).card ≤
      (q + 1) * N ^ q := by
  let P : Finset (Finset (Fin N)) :=
    (Finset.range (q + 1)).biUnion (fun j => Finset.univ.powersetCard j)
  have hsub :
      Finset.univ.powerset.filter (fun S : Finset (Fin N) => S.card ≤ q) ⊆ P := by
    intro S hS
    have hs := Finset.mem_filter.mp hS
    apply Finset.mem_biUnion.mpr
    refine ⟨S.card, Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hs.2), ?_⟩
    exact Finset.mem_powersetCard.mpr
      ⟨Finset.mem_powerset.mp hs.1, rfl⟩
  calc
    (Finset.univ.powerset.filter (fun S : Finset (Fin N) => S.card ≤ q)).card ≤
        P.card := Finset.card_le_card hsub
    _ ≤ ∑ j ∈ Finset.range (q + 1),
        (Finset.univ.powersetCard j : Finset (Finset (Fin N))).card :=
      Finset.card_biUnion_le
    _ = ∑ j ∈ Finset.range (q + 1), Nat.choose N j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    _ ≤ ∑ _j ∈ Finset.range (q + 1), N ^ q := by
      apply Finset.sum_le_sum
      intro j hj
      exact (Nat.choose_le_pow N j).trans
        (Nat.pow_le_pow_right hN
          (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
    _ = (q + 1) * N ^ q := by simp

/-- The number of length-`m` tuples over `N` symbols using at most `q`
distinct symbols is polynomial of degree `q` in `N`. -/
theorem card_lowRangeTuples_le (m N q : ℕ) (hN : 0 < N) :
    (lowRangeTuples m N q).card ≤
      ((q + 1) * q ^ m) * N ^ q := by
  have hsub := lowRangeTuples_subset_biUnion m N q
  calc
    (lowRangeTuples m N q).card ≤
        ((Finset.univ.powerset.filter
          (fun S : Finset (Fin N) => S.card ≤ q)).biUnion
            (fun S => supportedTuples (m := m) S)).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ S ∈ Finset.univ.powerset.filter
          (fun S : Finset (Fin N) => S.card ≤ q),
        (supportedTuples (m := m) S).card := Finset.card_biUnion_le
    _ ≤ ∑ _S ∈ Finset.univ.powerset.filter
          (fun S : Finset (Fin N) => S.card ≤ q), q ^ m := by
      apply Finset.sum_le_sum
      intro S hS
      rw [card_supportedTuples]
      exact Nat.pow_le_pow_left (Finset.mem_filter.mp hS).2 m
    _ = (Finset.univ.powerset.filter
          (fun S : Finset (Fin N) => S.card ≤ q)).card * q ^ m := by simp
    _ ≤ ((q + 1) * N ^ q) * q ^ m := by
      gcongr
      exact card_subsets_card_le N q hN
    _ = ((q + 1) * q ^ m) * N ^ q := by ring


noncomputable def evenFiberTuples (q N : ℕ) :
    Finset (Fin (2 * q) → Fin N) :=
  Finset.univ.filter (fun f => ∀ k ∈ tupleRange f,
    Even ((Finset.univ.filter (fun i => f i = k)).card))

lemma evenFiberTuple_range_card_le (q N : ℕ)
    (f : Fin (2 * q) → Fin N)
    (hf : ∀ k ∈ tupleRange f,
      Even ((Finset.univ.filter (fun i => f i = k)).card)) :
    (tupleRange f).card ≤ q := by
  let R := tupleRange f
  have hmaps : Set.MapsTo f
      (↑(Finset.univ : Finset (Fin (2 * q))) : Set (Fin (2 * q))) ↑R := by
    intro i hi
    exact (mem_tupleRange f (f i)).mpr ⟨i, rfl⟩
  have hsum : 2 * q = ∑ k ∈ R,
      (Finset.univ.filter (fun i => f i = k)).card := by
    simpa [R] using (Finset.card_eq_sum_card_fiberwise hmaps)
  have htwo : ∀ k ∈ R, 2 ≤
      (Finset.univ.filter (fun i => f i = k)).card := by
    intro k hk
    apply Nat.le_of_dvd
    · rw [Finset.card_pos]
      obtain ⟨i, hi⟩ := (mem_tupleRange f k).mp (by simpa [R] using hk)
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
    · exact even_iff_two_dvd.mp (hf k (by simpa [R] using hk))
  have hcard : 2 * R.card ≤ 2 * q := by
    calc
      2 * R.card = ∑ _k ∈ R, 2 := by simp [Nat.mul_comm]
      _ ≤ ∑ k ∈ R, (Finset.univ.filter (fun i => f i = k)).card := by
        exact Finset.sum_le_sum fun k hk => htwo k hk
      _ = 2 * q := hsum.symm
  dsimp [R] at hcard
  omega

lemma evenFiberTuples_subset_lowRange (q N : ℕ) :
    evenFiberTuples q N ⊆ lowRangeTuples (2 * q) N q := by
  intro f hf
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, evenFiberTuple_range_card_le q N f ?_⟩
  exact (Finset.mem_filter.mp hf).2

/-- Tuples of length `2q` for which every occupied symbol has even
multiplicity number only `O_q(N^q)`. -/
theorem card_evenFiberTuples_le (q N : ℕ) (hN : 0 < N) :
    (evenFiberTuples q N).card ≤
      ((q + 1) * q ^ (2 * q)) * N ^ q :=
  (Finset.card_le_card (evenFiberTuples_subset_lowRange q N)).trans
    (card_lowRangeTuples_le (2 * q) N q hN)

end Erdos522

end AmalgamatedModule11


/-! ===== amalgamated from Research.PositiveEvenFiberTupleCount ===== -/

section AmalgamatedModule12


open scoped BigOperators

namespace Erdos522

noncomputable def positiveTupleRange {m N : ℕ} (f : Fin m → Fin N) :
    Finset (Fin N) :=
  (tupleRange f).filter (fun k => k.val ≠ 0)

noncomputable def positiveEvenFiberTuples (q N : ℕ) :
    Finset (Fin (2 * q) → Fin N) :=
  Finset.univ.filter (fun f => ∀ k ∈ tupleRange f, k.val ≠ 0 →
    Even ((Finset.univ.filter (fun i => f i = k)).card))

lemma positiveEvenFiberTuple_positiveRange_card_le
    (q N : ℕ) (f : Fin (2 * q) → Fin N)
    (hf : ∀ k ∈ tupleRange f, k.val ≠ 0 →
      Even ((Finset.univ.filter (fun i => f i = k)).card)) :
    (positiveTupleRange f).card ≤ q := by
  let R := positiveTupleRange f
  have htwo : ∀ k ∈ R, 2 ≤
      (Finset.univ.filter (fun i => f i = k)).card := by
    intro k hk
    change k ∈ positiveTupleRange f at hk
    have hkr := Finset.mem_filter.mp hk
    apply Nat.le_of_dvd
    · rw [Finset.card_pos]
      obtain ⟨i, hi⟩ := (mem_tupleRange f k).mp hkr.1
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
    · exact even_iff_two_dvd.mp (hf k hkr.1 hkr.2)
  have hsumle : ∑ k ∈ R,
      (Finset.univ.filter (fun i => f i = k)).card ≤ 2 * q := by
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    calc
      (Finset.univ.filter (fun i => f i ∈ R)).card ≤
          (Finset.univ : Finset (Fin (2 * q))).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = 2 * q := Fintype.card_fin _
  have hcard : 2 * R.card ≤ 2 * q := by
    calc
      2 * R.card = ∑ _k ∈ R, 2 := by simp [Nat.mul_comm]
      _ ≤ ∑ k ∈ R, (Finset.univ.filter (fun i => f i = k)).card :=
        Finset.sum_le_sum fun k hk => htwo k hk
      _ ≤ 2 * q := hsumle
  dsimp [R] at hcard
  omega

lemma positiveEvenFiberTuples_subset_supportUnion (q N : ℕ) [NeZero N] :
    positiveEvenFiberTuples q N ⊆
      (Finset.univ.powerset.filter (fun S : Finset (Fin N) => S.card ≤ q)).biUnion
        (fun S => supportedTuples (m := 2 * q) (insert 0 S)) := by
  intro f hf
  have hfpar := (Finset.mem_filter.mp hf).2
  let R := positiveTupleRange f
  apply Finset.mem_biUnion.mpr
  refine ⟨R, ?_, ?_⟩
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), ?_⟩
    exact positiveEvenFiberTuple_positiveRange_card_le q N f hfpar
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro i
    by_cases hi : f i = 0
    · simp [hi]
    · apply Finset.mem_insert_of_mem
      apply Finset.mem_filter.mpr
      refine ⟨(mem_tupleRange f (f i)).mpr ⟨i, rfl⟩, ?_⟩
      intro hv
      apply hi
      apply Fin.ext
      simpa using hv

/-- Allowing the zero frequency arbitrary multiplicity does not increase the
polynomial degree: positive frequencies with even multiplicity still give only
`O_q(N^q)` tuples. -/
theorem card_positiveEvenFiberTuples_le (q N : ℕ) (hN : 0 < N) :
    (positiveEvenFiberTuples q N).card ≤
      ((q + 1) ^ (2 * q + 1)) * N ^ q := by
  letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  have hsub := positiveEvenFiberTuples_subset_supportUnion q N
  calc
    (positiveEvenFiberTuples q N).card ≤
        ((Finset.univ.powerset.filter
          (fun S : Finset (Fin N) => S.card ≤ q)).biUnion
            (fun S => supportedTuples (m := 2 * q) (insert 0 S))).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ S ∈ Finset.univ.powerset.filter
          (fun S : Finset (Fin N) => S.card ≤ q),
        (supportedTuples (m := 2 * q) (insert 0 S)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _S ∈ Finset.univ.powerset.filter
          (fun S : Finset (Fin N) => S.card ≤ q), (q + 1) ^ (2 * q) := by
      apply Finset.sum_le_sum
      intro S hS
      rw [card_supportedTuples]
      apply Nat.pow_le_pow_left
      exact (Finset.card_insert_le _ _).trans (by
        simpa [Nat.add_comm] using
          (Nat.add_le_add_left (Finset.mem_filter.mp hS).2 1))
    _ = (Finset.univ.powerset.filter
          (fun S : Finset (Fin N) => S.card ≤ q)).card *
          (q + 1) ^ (2 * q) := by simp
    _ ≤ ((q + 1) * N ^ q) * (q + 1) ^ (2 * q) := by
      gcongr
      exact card_subsets_card_le N q hN
    _ = ((q + 1) ^ (2 * q + 1)) * N ^ q := by ring


def intBoolSign (b : Bool) : ℤ := if b then 1 else -1

lemma intBoolSign_sum_ne_zero_of_odd
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (b : ι → Bool)
    (hodd : S.card % 2 = 1) :
    (∑ i ∈ S, intBoolSign (b i)) ≠ 0 := by
  intro hz
  have hc : ((∑ i ∈ S, intBoolSign (b i) : ℤ) : ZMod 2) =
      (S.card : ZMod 2) := by
    push_cast
    simp [intBoolSign]
  rw [hz] at hc
  simp only [Int.cast_zero] at hc
  have hmod : (S.card : ZMod 2) = (S.card % 2 : ℕ) := by norm_num
  rw [hmod, hodd] at hc
  norm_num at hc

noncomputable def signedTupleMultiplicity
    {q N : ℕ} (K : Fin (2 * q) → Fin N) (σ : Fin (2 * q) → Bool)
    (k : Fin N) : ℤ :=
  ∑ j ∈ Finset.univ.filter (fun j => K j = k), intBoolSign (σ j)

/-- Outside the enlarged exceptional class there is a genuinely nonzero
positive-frequency coefficient, for every sign choice. -/
lemma exists_positive_signedTupleMultiplicity_ne_zero
    (q N : ℕ) (K : Fin (2 * q) → Fin N)
    (hK : K ∉ positiveEvenFiberTuples q N)
    (σ : Fin (2 * q) → Bool) :
    ∃ k : Fin N, k.val ≠ 0 ∧ signedTupleMultiplicity K σ k ≠ 0 := by
  have hpar : ¬(∀ k ∈ tupleRange K, k.val ≠ 0 →
      Even ((Finset.univ.filter (fun i => K i = k)).card)) := by
    intro h
    apply hK
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, h⟩
  push_neg at hpar
  obtain ⟨k, hkRange, hkpos, hkodd⟩ := hpar
  refine ⟨k, hkpos, ?_⟩
  unfold signedTupleMultiplicity
  apply intBoolSign_sum_ne_zero_of_odd
  exact Nat.not_even_iff.mp hkodd

end Erdos522

end AmalgamatedModule12


/-! ===== amalgamated from Research.SigmaBounds ===== -/

section AmalgamatedModule13


open scoped BigOperators

namespace Erdos522

/-- The exponential lies below the chord joining its endpoint values on a
unit interval. -/
lemma exp_mul_unitInterval_le_chord (a x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp (a * x) ≤ (1 - x) + x * Real.exp a := by
  have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ a)
    (sub_nonneg.mpr hx1) hx0 (by ring : (1 - x) + x = 1)
  simpa [smul_eq_mul, Real.exp_zero, mul_comm, mul_left_comm, mul_assoc] using h

lemma two_mul_sum_range_cast (n : ℕ) :
    2 * (∑ k ∈ Finset.range (n + 1), (k : ℝ)) = (n : ℝ) * (n + 1) := by
  have hnat : 2 * (∑ k ∈ Finset.range (n + 1), k) = n * (n + 1) := by
    rw [mul_comm, Finset.sum_range_id_mul_two]
    simp [Nat.mul_comm]
  have hreal := congrArg (fun m : ℕ => (m : ℝ)) hnat
  push_cast at hreal
  exact hreal

/-- Uniform chord bound for the exponential variance sum used in the radial
normalization. -/
theorem two_mul_sum_exp_range_div_le (n : ℕ) (hn : 0 < n) (a : ℝ) :
    2 * (∑ k ∈ Finset.range (n + 1), Real.exp (a * ((k : ℝ) / n))) ≤
      (n + 1 : ℝ) * (1 + Real.exp a) := by
  have hterm : ∀ k ∈ Finset.range (n + 1),
      Real.exp (a * ((k : ℝ) / n)) ≤
        (1 - (k : ℝ) / n) + ((k : ℝ) / n) * Real.exp a := by
    intro k hk
    have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    apply exp_mul_unitInterval_le_chord
    · positivity
    · exact (div_le_one (by positivity)).mpr (by exact_mod_cast hkn)
  have hsum := Finset.sum_le_sum hterm
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hid := two_mul_sum_range_cast n
  calc
    2 * (∑ k ∈ Finset.range (n + 1), Real.exp (a * ((k : ℝ) / n)))
        ≤ 2 * (∑ k ∈ Finset.range (n + 1),
            ((1 - (k : ℝ) / n) + ((k : ℝ) / n) * Real.exp a)) :=
          mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = (n + 1 : ℝ) * (1 + Real.exp a) := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      simp_rw [div_eq_mul_inv]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul]
      norm_num [Nat.cast_add, Nat.cast_one] at hid ⊢
      field_simp
      linear_combination (Real.exp a - 1) * hid

/-- Squared `L²` normalization of the radially evaluated degree-`n` Littlewood
coefficient vector. -/
noncomputable def radialVariance (n : ℕ) (s : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), Real.exp (2 * s * ((k : ℝ) / n))

lemma radialVariance_pos (n : ℕ) (s : ℝ) : 0 < radialVariance n s := by
  unfold radialVariance
  apply Finset.sum_pos
  · intro k hk
    positivity
  · simp

/-- A uniform-in-degree upper bound for the radial variance ratio. -/
theorem radialVariance_le_chord (n : ℕ) (hn : 0 < n) (s : ℝ) :
    radialVariance n s ≤
      (n + 1 : ℝ) * ((1 + Real.exp (2 * s)) / 2) := by
  have h := two_mul_sum_exp_range_div_le n hn (2 * s)
  unfold radialVariance
  norm_num [Nat.cast_add, Nat.cast_one] at h ⊢
  nlinarith

/-- Logarithmic form of the uniform radial variance bound. -/
theorem half_log_radialVariance_ratio_le_chord
    (n : ℕ) (hn : 0 < n) (s : ℝ) :
    (Real.log (radialVariance n s) - Real.log (n + 1 : ℝ)) / 2 ≤
      Real.log ((1 + Real.exp (2 * s)) / 2) / 2 := by
  have hvpos := radialVariance_pos n s
  have hcpos : 0 < (1 + Real.exp (2 * s)) / 2 := by positivity
  have hnpos : 0 < (n + 1 : ℝ) := by positivity
  have hv := radialVariance_le_chord n hn s
  have hlog := Real.log_le_log hvpos hv
  rw [Real.log_mul (ne_of_gt hnpos) (ne_of_gt hcpos)] at hlog
  linarith

lemma hasDerivAt_log_exp_chord :
    HasDerivAt (fun s : ℝ => Real.log ((1 + Real.exp (2 * s)) / 2)) 1 0 := by
  have hlin : HasDerivAt (fun s : ℝ => 2 * s) 2 0 := by
    simpa using (hasDerivAt_id (𝕜 := ℝ) 0).const_mul 2
  have hexp := (Real.hasDerivAt_exp (2 * 0)).comp 0 hlin
  have hinner := (hexp.const_add 1).div_const 2
  have hlog := (Real.hasDerivAt_log
    (by norm_num : ((1 + Real.exp (2 * (0 : ℝ))) / 2) ≠ 0)).comp 0 hinner
  norm_num [Function.comp_apply] at hlog
  exact hlog

/-- The chord error has the sharp first-order constant needed when the radial
shift is sent to zero. -/
theorem tendsto_log_exp_chord_div : Filter.Tendsto
    (fun s : ℝ => Real.log ((1 + Real.exp (2 * s)) / 2) / s)
    (nhdsWithin 0 {0}ᶜ) (nhds 1) := by
  have ht := hasDerivAt_log_exp_chord.tendsto_slope_zero
  simp only [Function.comp_apply, zero_add, smul_eq_mul] at ht
  norm_num at ht
  simpa [div_eq_mul_inv, mul_comm] using ht

 theorem tendsto_log_exp_chord_div_right : Filter.Tendsto
    (fun s : ℝ => Real.log ((1 + Real.exp (2 * s)) / 2) / s)
    (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have ht := hasDerivAt_log_exp_chord.tendsto_slope_zero_right
  simp only [Function.comp_apply, zero_add, smul_eq_mul] at ht
  norm_num at ht
  simpa [div_eq_mul_inv, mul_comm] using ht

/-- The analogous inward chord quotient also tends to one from positive
shifts. -/
theorem tendsto_neg_log_exp_neg_chord_div_right : Filter.Tendsto
    (fun s : ℝ => -Real.log ((1 + Real.exp (-2 * s)) / 2) / s)
    (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have hneg := (hasDerivAt_id (𝕜 := ℝ) 0).neg
  have hout : HasDerivAt
      (fun s : ℝ => Real.log ((1 + Real.exp (2 * s)) / 2)) 1 ((-id) 0) := by
    simpa using hasDerivAt_log_exp_chord
  have hcomp := hout.comp 0 hneg
  have hderiv := hcomp.neg
  have ht := hderiv.tendsto_slope_zero_right
  simp only [Function.comp_apply, zero_add, smul_eq_mul] at ht
  norm_num at ht
  simpa [div_eq_mul_inv, mul_comm] using ht

end Erdos522

end AmalgamatedModule13


/-! ===== amalgamated from Research.RadialWeights ===== -/

section AmalgamatedModule14


open scoped BigOperators

namespace Erdos522

/-- Squared normalized coefficient at radial shift `s`. -/
noncomputable def radialWeight (n : ℕ) (s : ℝ) (k : ℕ) : ℝ :=
  Real.exp (2 * s * ((k : ℝ) / n)) / radialVariance n s

lemma radialWeight_nonneg (n : ℕ) (s : ℝ) (k : ℕ) :
    0 ≤ radialWeight n s k := by
  unfold radialWeight
  exact div_nonneg (Real.exp_nonneg _) (radialVariance_pos n s).le

lemma sum_radialWeight (n : ℕ) (s : ℝ) :
    ∑ k ∈ Finset.range (n + 1), radialWeight n s k = 1 := by
  unfold radialWeight radialVariance
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (by
    apply Finset.sum_pos
    · intro k hk
      positivity
    · simp))

lemma mul_div_mem_unitInterval {n k : ℕ} (hn : 0 < n) (hk : k ≤ n) :
    (0 : ℝ) ≤ (k : ℝ) / n ∧ (k : ℝ) / n ≤ 1 := by
  constructor
  · positivity
  · apply (div_le_one (by positivity)).mpr
    exact_mod_cast hk

lemma abs_bound_mul_unitInterval (s x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    -|s| ≤ s * x ∧ s * x ≤ |s| := by
  constructor
  · calc
      -|s| ≤ -|s| * x := by
        have := mul_le_mul_of_nonpos_left hx1 (neg_nonpos.mpr (abs_nonneg s))
        simpa using this
      _ ≤ s * x := mul_le_mul_of_nonneg_right (neg_abs_le s) hx0
  · calc
      s * x ≤ |s| * x := mul_le_mul_of_nonneg_right (le_abs_self s) hx0
      _ ≤ |s| := by
        simpa using mul_le_of_le_one_right (abs_nonneg s) hx1

lemma radialVariance_lower_bound (n : ℕ) (hn : 0 < n) (s : ℝ) :
    (n + 1 : ℝ) * Real.exp (-2 * |s|) ≤ radialVariance n s := by
  unfold radialVariance
  calc
    (n + 1 : ℝ) * Real.exp (-2 * |s|) =
        ∑ k ∈ Finset.range (n + 1), Real.exp (-2 * |s|) := by simp
    _ ≤ ∑ k ∈ Finset.range (n + 1), Real.exp (2 * s * ((k : ℝ) / n)) := by
      apply Finset.sum_le_sum
      intro k hk
      apply Real.exp_le_exp.mpr
      have hunit := mul_div_mem_unitInterval hn
        (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
      have h := (abs_bound_mul_unitInterval s ((k : ℝ) / n) hunit.1 hunit.2).1
      linarith

lemma radialWeight_numerator_upper {n k : ℕ} (hn : 0 < n) (hk : k ≤ n)
    (s : ℝ) :
    Real.exp (2 * s * ((k : ℝ) / n)) ≤ Real.exp (2 * |s|) := by
  apply Real.exp_le_exp.mpr
  have hunit := mul_div_mem_unitInterval hn hk
  have h := (abs_bound_mul_unitInterval s ((k : ℝ) / n) hunit.1 hunit.2).2
  linarith

/-- Every squared normalized radial coefficient is `O_s(1/n)`, with an
explicit uniform constant. -/
theorem radialWeight_le (n : ℕ) (hn : 0 < n) (s : ℝ)
    {k : ℕ} (hk : k ∈ Finset.range (n + 1)) :
    radialWeight n s k ≤ Real.exp (4 * |s|) / (n + 1 : ℝ) := by
  have hk' : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hnum := radialWeight_numerator_upper hn hk' s
  have hden := radialVariance_lower_bound n hn s
  have hvar := radialVariance_pos n s
  have hnpos : (0 : ℝ) < n + 1 := by positivity
  have hexp : 0 < Real.exp (-2 * |s|) := Real.exp_pos _
  unfold radialWeight
  apply (div_le_iff₀ hvar).mpr
  calc
    Real.exp (2 * s * ((k : ℝ) / n)) ≤ Real.exp (2 * |s|) := hnum
    _ = (Real.exp (4 * |s|) / (n + 1 : ℝ)) *
          ((n + 1 : ℝ) * Real.exp (-2 * |s|)) := by
        rw [show -2 * |s| = -(2 * |s|) by ring, Real.exp_neg]
        field_simp
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
    _ ≤ (Real.exp (4 * |s|) / (n + 1 : ℝ)) * radialVariance n s :=
      mul_le_mul_of_nonneg_left hden (by positivity)

end Erdos522

end AmalgamatedModule14


/-! ===== amalgamated from Research.RadialWeightLowerBound ===== -/

section AmalgamatedModule15


open scoped BigOperators

namespace Erdos522

lemma radialVariance_upper_bound (n : ℕ) (hn : 0 < n) (s : ℝ) :
    radialVariance n s ≤ (n + 1 : ℝ) * Real.exp (2 * |s|) := by
  unfold radialVariance
  calc
    (∑ k ∈ Finset.range (n + 1),
        Real.exp (2 * s * ((k : ℝ) / n))) ≤
        ∑ _k ∈ Finset.range (n + 1), Real.exp (2 * |s|) := by
      apply Finset.sum_le_sum
      intro k hk
      exact radialWeight_numerator_upper hn
        (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) s
    _ = (n + 1 : ℝ) * Real.exp (2 * |s|) := by simp

lemma radialWeight_numerator_lower {n k : ℕ} (hn : 0 < n) (hk : k ≤ n)
    (s : ℝ) :
    Real.exp (-2 * |s|) ≤ Real.exp (2 * s * ((k : ℝ) / n)) := by
  apply Real.exp_le_exp.mpr
  have hunit := mul_div_mem_unitInterval hn hk
  have h := (abs_bound_mul_unitInterval s ((k : ℝ) / n) hunit.1 hunit.2).1
  linarith

/-- Every normalized squared radial coefficient is also bounded below by a
shift-dependent multiple of `1/(n+1)`. -/
theorem radialWeight_lower (n : ℕ) (hn : 0 < n) (s : ℝ)
    {k : ℕ} (hk : k ∈ Finset.range (n + 1)) :
    Real.exp (-4 * |s|) / (n + 1 : ℝ) ≤ radialWeight n s k := by
  have hk' : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hnum := radialWeight_numerator_lower hn hk' s
  have hden := radialVariance_upper_bound n hn s
  have hvar := radialVariance_pos n s
  have hnpos : (0 : ℝ) < n + 1 := by positivity
  unfold radialWeight
  apply (le_div_iff₀ hvar).mpr
  calc
    (Real.exp (-4 * |s|) / (n + 1 : ℝ)) * radialVariance n s ≤
        (Real.exp (-4 * |s|) / (n + 1 : ℝ)) *
          ((n + 1 : ℝ) * Real.exp (2 * |s|)) :=
      mul_le_mul_of_nonneg_left hden (by positivity)
    _ = Real.exp (-2 * |s|) := by
      field_simp
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (2 * s * ((k : ℝ) / n)) := hnum

lemma sqrt_radialWeight_lower (n : ℕ) (hn : 0 < n) (s : ℝ)
    {k : ℕ} (hk : k ∈ Finset.range (n + 1)) :
    Real.exp (-2 * |s|) / Real.sqrt (n + 1 : ℝ) ≤
      Real.sqrt (radialWeight n s k) := by
  have h := Real.sqrt_le_sqrt (radialWeight_lower n hn s hk)
  have hN : (0 : ℝ) ≤ n + 1 := by positivity
  have hNpos : (0 : ℝ) < n + 1 := by positivity
  calc
    Real.exp (-2 * |s|) / Real.sqrt (n + 1 : ℝ) =
        Real.sqrt (Real.exp (-4 * |s|) / (n + 1 : ℝ)) := by
      rw [Real.sqrt_div (by positivity)]
      have hsq : Real.exp (-4 * |s|) = (Real.exp (-2 * |s|)) ^ 2 := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
      rw [hsq, Real.sqrt_sq_eq_abs, abs_of_pos (Real.exp_pos _)]
    _ ≤ Real.sqrt (radialWeight n s k) := h

end Erdos522

end AmalgamatedModule15


/-! ===== amalgamated from Research.RadialTupleFrequencySupport ===== -/

section AmalgamatedModule16


open scoped BigOperators ComplexConjugate

namespace Erdos522

noncomputable def activeTupleIndices
    {q N : ℕ} (K : Fin (2 * q) → Fin N) (σ : Fin (2 * q) → Bool) :
    Finset (Fin N) :=
  (tupleRange K).filter (fun k => k.val ≠ 0 ∧ signedTupleMultiplicity K σ k ≠ 0)

noncomputable def radialTupleFrequencySupport
    {q N : ℕ} (K : Fin (2 * q) → Fin N) (σ : Fin (2 * q) → Bool) :
    Finset ℤ :=
  (activeTupleIndices K σ).biUnion fun k => {(k.val : ℤ), -(k.val : ℤ)}

noncomputable def radialTupleFrequencyEnumeration
    {q N : ℕ} (K : Fin (2 * q) → Fin N) (σ : Fin (2 * q) → Bool) :
    Fin (radialTupleFrequencySupport K σ).card → ℤ :=
  fun i => ((radialTupleFrequencySupport K σ).equivFin.symm i).1

lemma activeTupleIndices_subset_tupleRange
    {q N : ℕ} (K : Fin (2 * q) → Fin N) (σ : Fin (2 * q) → Bool) :
    activeTupleIndices K σ ⊆ tupleRange K := by
  intro k hk
  exact (Finset.mem_filter.mp hk).1

lemma card_tupleRange_le {m N : ℕ} (K : Fin m → Fin N) :
    (tupleRange K).card ≤ m := by
  unfold tupleRange
  exact (Finset.card_image_le.trans_eq (Finset.card_univ.trans (Fintype.card_fin m)))

lemma card_activeTupleIndices_le
    {q N : ℕ} (K : Fin (2 * q) → Fin N) (σ : Fin (2 * q) → Bool) :
    (activeTupleIndices K σ).card ≤ 2 * q :=
  (Finset.card_le_card (activeTupleIndices_subset_tupleRange K σ)).trans
    (card_tupleRange_le K)

lemma card_radialTupleFrequencySupport_le
    {q N : ℕ} (K : Fin (2 * q) → Fin N) (σ : Fin (2 * q) → Bool) :
    (radialTupleFrequencySupport K σ).card ≤ 4 * q := by
  calc
    (radialTupleFrequencySupport K σ).card ≤
        ∑ _k ∈ activeTupleIndices K σ, 2 := by
      unfold radialTupleFrequencySupport
      refine Finset.card_biUnion_le.trans ?_
      apply Finset.sum_le_sum
      intro k hk
      exact Finset.card_le_two
    _ = 2 * (activeTupleIndices K σ).card := by simp [mul_comm]
    _ ≤ 2 * (2 * q) := Nat.mul_le_mul_left 2 (card_activeTupleIndices_le K σ)
    _ = 4 * q := by ring

lemma mem_radialTupleFrequencySupport_iff
    {q N : ℕ} (K : Fin (2 * q) → Fin N) (σ : Fin (2 * q) → Bool)
    (z : ℤ) :
    z ∈ radialTupleFrequencySupport K σ ↔
      ∃ k ∈ activeTupleIndices K σ, z = k.val ∨ z = -(k.val : ℤ) := by
  simp [radialTupleFrequencySupport]

lemma radialTupleFrequencyEnumeration_injective
    {q N : ℕ} (K : Fin (2 * q) → Fin N) (σ : Fin (2 * q) → Bool) :
    Function.Injective (radialTupleFrequencyEnumeration K σ) := by
  intro i j hij
  unfold radialTupleFrequencyEnumeration at hij
  apply (radialTupleFrequencySupport K σ).equivFin.symm.injective
  apply Subtype.ext
  exact hij

lemma radialTupleFrequencyEnumeration_ne_zero
    {q N : ℕ} (K : Fin (2 * q) → Fin N) (σ : Fin (2 * q) → Bool)
    (i : Fin (radialTupleFrequencySupport K σ).card) :
    radialTupleFrequencyEnumeration K σ i ≠ 0 := by
  have hi := ((radialTupleFrequencySupport K σ).equivFin.symm i).2
  obtain ⟨k, hk, hpos⟩ := (mem_radialTupleFrequencySupport_iff K σ _).mp hi
  change (((radialTupleFrequencySupport K σ).equivFin.symm i).1 : ℤ) ≠ 0
  rcases hpos with hpos | hneg
  · rw [hpos]
    exact_mod_cast (Finset.mem_filter.mp hk).2.1
  · rw [hneg]
    exact neg_ne_zero.mpr (by exact_mod_cast (Finset.mem_filter.mp hk).2.1)

lemma radialTupleFrequencyEnumeration_natAbs_le
    {q n : ℕ} (K : Fin (2 * q) → Fin (n + 1))
    (σ : Fin (2 * q) → Bool)
    (i : Fin (radialTupleFrequencySupport K σ).card) :
    (radialTupleFrequencyEnumeration K σ i).natAbs ≤ n := by
  have hi := ((radialTupleFrequencySupport K σ).equivFin.symm i).2
  obtain ⟨k, hk, hpos⟩ := (mem_radialTupleFrequencySupport_iff K σ _).mp hi
  have hkval : k.val ≤ n := Nat.le_of_lt_succ k.isLt
  change (((radialTupleFrequencySupport K σ).equivFin.symm i).1 : ℤ).natAbs ≤ n
  rcases hpos with hpos | hneg
  · rw [hpos]
    simpa using hkval
  · rw [hneg, Int.natAbs_neg]
    simpa using hkval

lemma exists_activeTupleIndex_of_not_positiveEven
    (q N : ℕ) (K : Fin (2 * q) → Fin N)
    (hK : K ∉ positiveEvenFiberTuples q N)
    (σ : Fin (2 * q) → Bool) :
    ∃ k ∈ activeTupleIndices K σ, True := by
  obtain ⟨k, hkpos, hksigned⟩ :=
    exists_positive_signedTupleMultiplicity_ne_zero q N K hK σ
  refine ⟨k, ?_, trivial⟩
  apply Finset.mem_filter.mpr
  refine ⟨?_, hkpos, hksigned⟩
  have hfiber : (Finset.univ.filter (fun j => K j = k)).Nonempty := by
    by_contra hempty
    have heq := Finset.not_nonempty_iff_eq_empty.mp hempty
    unfold signedTupleMultiplicity at hksigned
    rw [heq] at hksigned
    simp at hksigned
  obtain ⟨j, hj⟩ := hfiber
  exact (mem_tupleRange K k).mpr ⟨j, (Finset.mem_filter.mp hj).2⟩

end Erdos522

end AmalgamatedModule16


/-! ===== amalgamated from Research.CosineProductExponential ===== -/

section AmalgamatedModule17


open scoped BigOperators

namespace Erdos522

lemma abs_cos_le_exp_cos_two (x : ℝ) :
    |Real.cos x| ≤ Real.exp ((-1 + Real.cos (2 * x)) / 4) := by
  have htrig : (Real.cos x) ^ 2 = 1 - (Real.sin x) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq x]
  have hexp : 1 - (Real.sin x) ^ 2 ≤ Real.exp (-(Real.sin x) ^ 2) := by
    have h := Real.add_one_le_exp (-(Real.sin x) ^ 2)
    linarith
  have hsq : |Real.cos x| ^ 2 ≤
      (Real.exp (-(Real.sin x) ^ 2 / 2)) ^ 2 := by
    rw [sq_abs, htrig]
    simp only [pow_two]
    rw [← Real.exp_add]
    convert hexp using 1 <;> ring
  have hleft : 0 ≤ |Real.cos x| := abs_nonneg _
  have hright : 0 ≤ Real.exp (-(Real.sin x) ^ 2 / 2) := (Real.exp_pos _).le
  have hroot : |Real.cos x| ≤ Real.exp (-(Real.sin x) ^ 2 / 2) := by
    nlinarith [sq_nonneg (|Real.cos x| - Real.exp (-(Real.sin x) ^ 2 / 2))]
  calc
    |Real.cos x| ≤ Real.exp (-(Real.sin x) ^ 2 / 2) := hroot
    _ = Real.exp ((-1 + Real.cos (2 * x)) / 4) := by
      congr 1
      rw [Real.cos_two_mul]
      nlinarith [Real.sin_sq_add_cos_sq x]

lemma abs_finset_prod_cos_le_exp_sum_cos_two
    {ι : Type*} (s : Finset ι) (a : ι → ℝ) :
    |∏ i ∈ s, Real.cos (a i)| ≤
      Real.exp (-(s.card : ℝ) / 4 +
        (1 / 4 : ℝ) * ∑ i ∈ s, Real.cos (2 * a i)) := by
  rw [Finset.abs_prod]
  calc
    ∏ i ∈ s, |Real.cos (a i)| ≤
        ∏ i ∈ s, Real.exp ((-1 + Real.cos (2 * a i)) / 4) := by
      gcongr with i hi
      exact abs_cos_le_exp_cos_two (a i)
    _ = Real.exp (∑ i ∈ s, ((-1 + Real.cos (2 * a i)) / 4)) := by
      rw [← Real.exp_sum]
    _ = Real.exp (-(s.card : ℝ) / 4 +
        (1 / 4 : ℝ) * ∑ i ∈ s, Real.cos (2 * a i)) := by
      congr 1
      simp_rw [add_div]
      rw [Finset.sum_add_distrib]
      simp
      simp_rw [div_eq_mul_inv]
      rw [← Finset.sum_mul]
      ring

lemma abs_fin_prod_cos_le_of_sum_cos_two
    {N : ℕ} (a : Fin N → ℝ)
    (h : ∑ i : Fin N, Real.cos (2 * a i) ≤ (N : ℝ) / 2) :
    |∏ i : Fin N, Real.cos (a i)| ≤ Real.exp (-(N : ℝ) / 8) := by
  calc
    |∏ i : Fin N, Real.cos (a i)| ≤
        Real.exp (-(N : ℝ) / 4 +
          (1 / 4 : ℝ) * ∑ i : Fin N, Real.cos (2 * a i)) := by
      simpa using abs_finset_prod_cos_le_exp_sum_cos_two Finset.univ a
    _ ≤ Real.exp (-(N : ℝ) / 8) := by
      apply Real.exp_le_exp.mpr
      linarith

end Erdos522

end AmalgamatedModule17


/-! ===== amalgamated from Research.CosineProductMomentBound ===== -/

section AmalgamatedModule18


open MeasureTheory
open scoped BigOperators

namespace Erdos522

lemma measure_cosineSum_gt_half_le_moment
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (N q : ℕ) (hN : 0 < N) (hq : 0 < q) (a : Fin N → α → ℝ)
    (hmeas : ∀ i, Measurable (a i))
    (hint : Integrable
      (fun x => |∑ i : Fin N, Real.cos (2 * a i x)| ^ (2 * q)) μ) :
    μ.real {x | (N : ℝ) / 2 < ∑ i : Fin N, Real.cos (2 * a i x)} ≤
      (2 / N : ℝ) ^ (2 * q) *
        ∫ x, |∑ i : Fin N, Real.cos (2 * a i x)| ^ (2 * q) ∂μ := by
  let S : α → ℝ := fun x => ∑ i : Fin N, Real.cos (2 * a i x)
  have hSmeas : Measurable S := by
    dsimp [S]
    fun_prop
  have hthreshold : 0 < (N : ℝ) / 2 := by positivity
  let F : α → ℝ := fun x => |S x| ^ (2 * q)
  have hF0 : 0 ≤ᵐ[μ] F := by
    filter_upwards with x
    exact pow_nonneg (abs_nonneg _) _
  have hFint : Integrable F μ := by simpa [F, S] using hint
  have hmarkov := mul_meas_ge_le_integral_of_nonneg hF0 hFint
    (((N : ℝ) / 2) ^ (2 * q))
  let P : Set α := {x | ((N : ℝ) / 2) ^ (2 * q) ≤ F x}
  have hset : {x | (N : ℝ) / 2 < S x} ⊆ P := by
    intro x hx
    dsimp [P, F]
    apply pow_le_pow_left₀ (by positivity) (le_trans (le_of_lt hx) (le_abs_self _))
  have hm := measureReal_mono (μ := μ) hset (by finiteness)
  have hmul : ((N : ℝ) / 2) ^ (2 * q) *
      μ.real {x | (N : ℝ) / 2 < S x} ≤ ∫ x, F x ∂μ := by
    exact (mul_le_mul_of_nonneg_left hm (pow_nonneg hthreshold.le _)).trans
      (by simpa [P] using hmarkov)
  calc
    μ.real {x | (N : ℝ) / 2 < S x} ≤
        (∫ x, F x ∂μ) / (((N : ℝ) / 2) ^ (2 * q)) :=
      (le_div_iff₀ (pow_pos hthreshold _)).2 (by simpa [mul_comm] using hmul)
    _ = (2 / N : ℝ) ^ (2 * q) *
        ∫ x, |S x| ^ (2 * q) ∂μ := by
      dsimp [F]
      have hNc : ((N : ℝ)) ≠ 0 := by positivity
      have hh : (N : ℝ) ^ (2 * q) * (2 / N : ℝ) ^ (2 * q) =
          2 ^ (2 * q) := by
        rw [← mul_pow]
        field_simp
      rw [div_pow]
      field_simp
      calc
        (∫ x, |S x| ^ (2 * q) ∂μ) * 2 ^ (2 * q) =
            (∫ x, |S x| ^ (2 * q) ∂μ) *
              ((N : ℝ) ^ (2 * q) * (2 / N : ℝ) ^ (2 * q)) := by rw [hh]
        _ = (∫ x, |S x| ^ (2 * q) ∂μ) * (N : ℝ) ^ (2 * q) *
              (2 / N : ℝ) ^ (2 * q) := by ring
    _ = _ := by rfl

/-- A high even moment of the doubled-phase cosine sum controls the mean
absolute Rademacher characteristic product. -/
theorem integral_abs_cosineProduct_le_exp_add_moment
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (N q : ℕ) (hN : 0 < N) (hq : 0 < q) (a : Fin N → α → ℝ)
    (hmeas : ∀ i, Measurable (a i))
    (hprodInt : Integrable (fun x => |∏ i : Fin N, Real.cos (a i x)|) μ)
    (hmomentInt : Integrable
      (fun x => |∑ i : Fin N, Real.cos (2 * a i x)| ^ (2 * q)) μ) :
    (∫ x, |∏ i : Fin N, Real.cos (a i x)| ∂μ) ≤
      Real.exp (-(N : ℝ) / 8) +
        (2 / N : ℝ) ^ (2 * q) *
          ∫ x, |∑ i : Fin N, Real.cos (2 * a i x)| ^ (2 * q) ∂μ := by
  let B : Set α := {x | (N : ℝ) / 2 < ∑ i : Fin N, Real.cos (2 * a i x)}
  have hBmeas : MeasurableSet B := by
    dsimp [B]
    exact measurableSet_lt measurable_const (by fun_prop)
  have honeInt : Integrable (fun _ : α => (1 : ℝ)) μ := integrable_const 1
  have hbound : ∀ x,
      |∏ i : Fin N, Real.cos (a i x)| ≤
        B.indicator (fun _ => (1 : ℝ)) x +
          Bᶜ.indicator (fun _ => Real.exp (-(N : ℝ) / 8)) x := by
    intro x
    by_cases hx : x ∈ B
    · simp [B, hx]
      have hp : |∏ i : Fin N, Real.cos (a i x)| ≤ 1 := by
        rw [Finset.abs_prod]
        calc
          (∏ i : Fin N, |Real.cos (a i x)|) ≤ ∏ _i : Fin N, (1 : ℝ) := by
            gcongr with i
            exact Real.abs_cos_le_one _
          _ = 1 := by simp
      simpa using hp
    · have hs : ∑ i : Fin N, Real.cos (2 * a i x) ≤ (N : ℝ) / 2 := by
        simpa [B] using hx
      simp [B, hx]
      exact abs_fin_prod_cos_le_of_sum_cos_two (fun i => a i x) hs
  have hrightInt : Integrable
      (fun x => B.indicator (fun _ => (1 : ℝ)) x +
        Bᶜ.indicator (fun _ => Real.exp (-(N : ℝ) / 8)) x) μ :=
    (honeInt.indicator hBmeas).add
      ((integrable_const (Real.exp (-(N : ℝ) / 8))).indicator hBmeas.compl)
  calc
    (∫ x, |∏ i : Fin N, Real.cos (a i x)| ∂μ) ≤
        ∫ x, (B.indicator (fun _ => (1 : ℝ)) x +
          Bᶜ.indicator (fun _ => Real.exp (-(N : ℝ) / 8)) x) ∂μ :=
      integral_mono hprodInt hrightInt hbound
    _ = μ.real B + Real.exp (-(N : ℝ) / 8) * μ.real Bᶜ := by
      rw [integral_add, integral_indicator_const (1 : ℝ) hBmeas,
        integral_indicator_const (Real.exp (-(N : ℝ) / 8)) hBmeas.compl]
      · simp only [smul_eq_mul]
        ring
      · exact honeInt.indicator hBmeas
      · exact (integrable_const (Real.exp (-(N : ℝ) / 8))).indicator hBmeas.compl
    _ ≤ Real.exp (-(N : ℝ) / 8) + μ.real B := by
      have hcomp : μ.real Bᶜ ≤ 1 := measureReal_le_one
      have he0 : 0 ≤ Real.exp (-(N : ℝ) / 8) := (Real.exp_pos _).le
      nlinarith [(measureReal_nonneg : 0 ≤ μ.real B)]
    _ ≤ Real.exp (-(N : ℝ) / 8) +
        (2 / N : ℝ) ^ (2 * q) *
          ∫ x, |∑ i : Fin N, Real.cos (2 * a i x)| ^ (2 * q) ∂μ := by
      gcongr
      exact measure_cosineSum_gt_half_le_moment μ N q hN hq a hmeas hmomentInt

end Erdos522

end AmalgamatedModule18


/-! ===== amalgamated from Research.CovarianceQuadratic ===== -/

section AmalgamatedModule19


open scoped ComplexConjugate

namespace Erdos522

/-- Quadratic form of the real covariance matrix of a normalized complex
Rademacher sum with pseudocorrelation `ρ`. -/
noncomputable def covarianceQuadratic (ρ : ℂ) (x y : ℝ) : ℝ :=
  ((1 + ρ.re) * x ^ 2 + 2 * ρ.im * x * y + (1 - ρ.re) * y ^ 2) / 2

lemma covarianceQuadratic_perturbation_identity (ρ : ℂ) (x y : ℝ) :
    2 * covarianceQuadratic ρ x y - (x ^ 2 + y ^ 2) =
      (conj ρ * (((x : ℂ) + (y : ℂ) * Complex.I) ^ 2)).re := by
  have hzre : ((((x : ℂ) + (y : ℂ) * Complex.I) ^ 2).re) = x ^ 2 - y ^ 2 := by
    simp [pow_two, Complex.mul_re]
  have hzim : ((((x : ℂ) + (y : ℂ) * Complex.I) ^ 2).im) = 2 * x * y := by
    simp [pow_two, Complex.mul_im]
    ring
  unfold covarianceQuadratic
  rw [Complex.mul_re, Complex.conj_re, Complex.conj_im, hzre, hzim]
  ring

/-- The pseudocorrelation norm exactly controls the departure from circular
covariance in every direction. -/
theorem abs_two_covarianceQuadratic_sub_le (ρ : ℂ) (x y : ℝ) :
    |2 * covarianceQuadratic ρ x y - (x ^ 2 + y ^ 2)| ≤
      ‖ρ‖ * (x ^ 2 + y ^ 2) := by
  rw [covarianceQuadratic_perturbation_identity]
  calc
    |(conj ρ * (((x : ℂ) + (y : ℂ) * Complex.I) ^ 2)).re| ≤
        ‖conj ρ * (((x : ℂ) + (y : ℂ) * Complex.I) ^ 2)‖ :=
      Complex.abs_re_le_norm _
    _ = ‖ρ‖ * (x ^ 2 + y ^ 2) := by
      rw [norm_mul, Complex.norm_conj, norm_pow]
      have hnorm : ‖(x : ℂ) + (y : ℂ) * Complex.I‖ ^ 2 = x ^ 2 + y ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        simp
        ring
      exact congrArg (fun t : ℝ => ‖ρ‖ * t) hnorm

/-- If `‖ρ‖≤η`, all covariance eigenvalues lie between
`(1-η)/2` and `(1+η)/2`, expressed without matrix machinery. -/
theorem covarianceQuadratic_between {ρ : ℂ} {η : ℝ} (hρ : ‖ρ‖ ≤ η)
    (x y : ℝ) :
    (1 - η) / 2 * (x ^ 2 + y ^ 2) ≤ covarianceQuadratic ρ x y ∧
      covarianceQuadratic ρ x y ≤ (1 + η) / 2 * (x ^ 2 + y ^ 2) := by
  have hsquares : 0 ≤ x ^ 2 + y ^ 2 := by positivity
  have hpert := abs_two_covarianceQuadratic_sub_le ρ x y
  have hbound :
      |2 * covarianceQuadratic ρ x y - (x ^ 2 + y ^ 2)| ≤
        η * (x ^ 2 + y ^ 2) :=
    hpert.trans (mul_le_mul_of_nonneg_right hρ hsquares)
  constructor <;> rw [abs_le] at hbound <;> nlinarith [hbound.1, hbound.2]

end Erdos522

end AmalgamatedModule19


/-! ===== amalgamated from Research.CubeAverage ===== -/

section AmalgamatedModule20


open scoped BigOperators

namespace Erdos522

/-- Uniform average over the Boolean cube of dimension `N`. -/
noncomputable def cubeAverage {N : ℕ} (F : (Fin N → Bool) → ℝ) : ℝ :=
  (∑ x : Fin N → Bool, F x) / (2 : ℝ) ^ N

@[simp] lemma cubeAverage_zero (F : (Fin 0 → Bool) → ℝ) :
    cubeAverage F = F (fun i => Fin.elim0 i) := by
  unfold cubeAverage
  simp
  congr 1

lemma cube_sum_succ (N : ℕ) (F : (Fin (N + 1) → Bool) → ℝ) :
    (∑ x : Fin (N + 1) → Bool, F x) =
      (∑ y : Fin N → Bool, F (Fin.cons true y)) +
      (∑ y : Fin N → Bool, F (Fin.cons false y)) := by
  let e := Fin.consEquiv (fun _ : Fin (N + 1) => Bool)
  calc
    (∑ x : Fin (N + 1) → Bool, F x) =
        ∑ p : Bool × (Fin N → Bool), F (e p) := by
      apply Fintype.sum_equiv e.symm
      intro x
      exact congrArg F (e.apply_symm_apply x).symm
    _ = ∑ b : Bool, ∑ y : Fin N → Bool, F (e (b, y)) :=
      Fintype.sum_prod_type _
    _ = _ := by
      rw [Fintype.sum_bool]
      change (∑ x, F (Fin.cons true x)) + (∑ x, F (Fin.cons false x)) = _
      rfl

/-- Iterated averaging: a cube average is the mean of the two head slices. -/
theorem cubeAverage_succ (N : ℕ) (F : (Fin (N + 1) → Bool) → ℝ) :
    cubeAverage F =
      (cubeAverage (fun y : Fin N → Bool => F (Fin.cons true y)) +
        cubeAverage (fun y : Fin N → Bool => F (Fin.cons false y))) / 2 := by
  unfold cubeAverage
  rw [cube_sum_succ]
  rw [show (2 : ℝ) ^ (N + 1) = 2 ^ N * 2 by ring]
  field_simp

lemma cubeAverage_mono {N : ℕ} {F G : (Fin N → Bool) → ℝ}
    (h : ∀ x, F x ≤ G x) : cubeAverage F ≤ cubeAverage G := by
  unfold cubeAverage
  apply div_le_div_of_nonneg_right
  · exact Finset.sum_le_sum fun x hx => h x
  · positivity

lemma cubeAverage_neg {N : ℕ} (F : (Fin N → Bool) → ℝ) :
    cubeAverage (fun x => -F x) = -cubeAverage F := by
  unfold cubeAverage
  simp
  ring

lemma cubeAverage_const_mul {N : ℕ} (a : ℝ) (F : (Fin N → Bool) → ℝ) :
    cubeAverage (fun x => a * F x) = a * cubeAverage F := by
  unfold cubeAverage
  rw [← Finset.mul_sum]
  ring

@[simp] lemma cubeAverage_const {N : ℕ} (c : ℝ) :
    cubeAverage (fun _ : Fin N → Bool => c) = c := by
  unfold cubeAverage
  simp [Fintype.card_bool, Fintype.card_fin]

lemma abs_cubeAverage_le {N : ℕ} (F : (Fin N → Bool) → ℝ) :
    |cubeAverage F| ≤ cubeAverage (fun x => |F x|) := by
  unfold cubeAverage
  rw [abs_div, abs_of_pos (by positivity : 0 < (2 : ℝ) ^ N)]
  apply div_le_div_of_nonneg_right
  · exact Finset.abs_sum_le_sum_abs _ _
  · positivity

lemma abs_cubeAverage_sub_le_of_pointwise {N : ℕ}
    (F G : (Fin N → Bool) → ℝ) {c : ℝ}
    (h : ∀ x, |F x - G x| ≤ c) :
    |cubeAverage F - cubeAverage G| ≤ c := by
  have havgsub : cubeAverage F - cubeAverage G =
      cubeAverage (fun x => F x - G x) := by
    unfold cubeAverage
    rw [Finset.sum_sub_distrib]
    ring
  rw [havgsub]
  calc
    |cubeAverage (fun x => F x - G x)| ≤
        cubeAverage (fun x => |F x - G x|) := abs_cubeAverage_le _
    _ ≤ cubeAverage (fun _ => c) := cubeAverage_mono h
    _ = c := cubeAverage_const c

end Erdos522

end AmalgamatedModule20


/-! ===== amalgamated from Research.JensenSqueeze ===== -/

section AmalgamatedModule21


open scoped BigOperators

namespace Erdos522

/-- Positive part of a real number, used after taking logarithms of root moduli. -/
def hinge (x : ℝ) : ℝ := max 0 x

/-- Contribution of one logarithmic root radius to the outward Mahler increment. -/
def outwardContribution (δ x : ℝ) : ℝ := δ + hinge (x - δ) - hinge x

/-- Contribution of one logarithmic root radius to the inward Mahler decrement. -/
def inwardContribution (δ x : ℝ) : ℝ := δ + hinge x - hinge (x + δ)

lemma outwardContribution_eq_of_nonpos {δ x : ℝ} (hδ : 0 ≤ δ) (hx : x ≤ 0) :
    outwardContribution δ x = δ := by
  simp [outwardContribution, hinge, max_eq_left, hx, sub_nonpos.mpr (hx.trans hδ)]

lemma outwardContribution_nonneg {δ x : ℝ} (hδ : 0 ≤ δ) :
    0 ≤ outwardContribution δ x := by
  unfold outwardContribution hinge
  rcases le_total x 0 with hx | hx
  · rw [max_eq_left hx]
    rw [max_eq_left (sub_nonpos.mpr (hx.trans hδ))]
    simpa using hδ
  rcases le_total x δ with hxd | hdx
  · rw [max_eq_right hx]
    rw [max_eq_left (sub_nonpos.mpr hxd)]
    linarith
  · rw [max_eq_right hx]
    rw [max_eq_right (sub_nonneg.mpr hdx)]
    ring_nf
    exact le_rfl

lemma inwardContribution_eq_of_nonneg {δ x : ℝ} (hδ : 0 ≤ δ) (hx : 0 ≤ x) :
    inwardContribution δ x = 0 := by
  simp [inwardContribution, hinge, hx, add_nonneg hx hδ]
  ring

lemma inwardContribution_le_delta {δ x : ℝ} (hδ : 0 ≤ δ) :
    inwardContribution δ x ≤ δ := by
  unfold inwardContribution hinge
  have hmax : max 0 x ≤ max 0 (x + δ) :=
    max_le_max_left 0 (le_add_of_nonneg_right hδ)
  linarith

/-- The logarithmic Mahler expression after shifting every logarithmic root
radius inward by `δ` while multiplying the leading coefficient by
`exp(card * δ)`. -/
def radialLogMahler (rootsLog : Multiset ℝ) (δ : ℝ) : ℝ :=
  (rootsLog.card : ℝ) * δ + (rootsLog.map fun x => hinge (x - δ)).sum

lemma radialLogMahler_sub_zero (rootsLog : Multiset ℝ) (δ : ℝ) :
    radialLogMahler rootsLog δ - radialLogMahler rootsLog 0 =
      (rootsLog.map fun x => outwardContribution δ x).sum := by
  induction rootsLog using Multiset.induction_on with
  | empty => simp [radialLogMahler]
  | @cons x roots ih =>
      simp only [radialLogMahler, Multiset.card_cons, Nat.cast_add, Nat.cast_one,
        Multiset.map_cons, Multiset.sum_cons] at ih ⊢
      simp [outwardContribution]
      linarith

lemma radialLogMahler_zero_sub_neg (rootsLog : Multiset ℝ) (δ : ℝ) :
    radialLogMahler rootsLog 0 - radialLogMahler rootsLog (-δ) =
      (rootsLog.map fun x => inwardContribution δ x).sum := by
  induction rootsLog using Multiset.induction_on with
  | empty => simp [radialLogMahler]
  | @cons x roots ih =>
      simp only [radialLogMahler, Multiset.card_cons, Nat.cast_add, Nat.cast_one,
        Multiset.map_cons, Multiset.sum_cons] at ih ⊢
      simp [inwardContribution]
      linarith

lemma sum_indicator_nonpos (rootsLog : Multiset ℝ) (δ : ℝ) :
    (rootsLog.map fun x => if x ≤ 0 then δ else 0).sum =
      (rootsLog.filter (· ≤ 0)).card * δ := by
  induction rootsLog using Multiset.induction_on with
  | empty => simp
  | @cons x roots ih =>
      by_cases hx : x ≤ 0 <;> simp [hx, ih, Nat.cast_add] <;> ring

lemma sum_indicator_neg (rootsLog : Multiset ℝ) (δ : ℝ) :
    (rootsLog.map fun x => if x < 0 then δ else 0).sum =
      (rootsLog.filter (· < 0)).card * δ := by
  induction rootsLog using Multiset.induction_on with
  | empty => simp
  | @cons x roots ih =>
      by_cases hx : x < 0 <;> simp [hx, ih, Nat.cast_add] <;> ring

/-- Outward Jensen increments count every nonpositive logarithmic root radius
(the closed unit disk) with full weight `δ`. -/
theorem sum_closed_indicator_le_outward (rootsLog : Multiset ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    (rootsLog.map fun x => if x ≤ 0 then δ else 0).sum ≤
      (rootsLog.map fun x => outwardContribution δ x).sum := by
  apply Multiset.sum_map_le_sum_map
  intro x hx
  by_cases h : x ≤ 0
  · simp [h, outwardContribution_eq_of_nonpos hδ h]
  · simp [h, outwardContribution_nonneg hδ]

/-- Inward Jensen decrements receive no contribution from nonnegative
logarithmic root radii and at most `δ` from each strictly negative one. -/
theorem sum_inward_le_open_indicator (rootsLog : Multiset ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    (rootsLog.map fun x => inwardContribution δ x).sum ≤
      (rootsLog.map fun x => if x < 0 then δ else 0).sum := by
  apply Multiset.sum_map_le_sum_map
  intro x hx
  by_cases h : x < 0
  · simp [h, inwardContribution_le_delta hδ]
  · have hx0 : 0 ≤ x := le_of_not_gt h
    simp [h, inwardContribution_eq_of_nonneg hδ hx0]

/-- Abstract outward Jensen inequality: the closed-disk count times the radial
logarithmic increment is bounded by the Mahler increment. -/
theorem closed_count_mul_le_radialLogMahler_sub (rootsLog : Multiset ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    (rootsLog.filter (· ≤ 0)).card * δ ≤
      radialLogMahler rootsLog δ - radialLogMahler rootsLog 0 := by
  rw [← sum_indicator_nonpos]
  rw [radialLogMahler_sub_zero]
  exact sum_closed_indicator_le_outward rootsLog hδ

/-- Abstract inward Jensen inequality: the Mahler decrement is bounded by the
open-disk count times the radial logarithmic increment. -/
theorem radialLogMahler_sub_le_open_count_mul (rootsLog : Multiset ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    radialLogMahler rootsLog 0 - radialLogMahler rootsLog (-δ) ≤
      (rootsLog.filter (· < 0)).card * δ := by
  rw [radialLogMahler_zero_sub_neg]
  rw [← sum_indicator_neg]
  exact sum_inward_le_open_indicator rootsLog hδ

end Erdos522

end AmalgamatedModule21


/-! ===== amalgamated from Research.PolynomialJensen ===== -/

section AmalgamatedModule22


namespace Erdos522

/-- Closed-unit-disk root count, with algebraic multiplicity. -/
noncomputable def polynomialClosedRootCount (p : Polynomial ℂ) : ℕ :=
  (p.roots.filter fun z => ‖z‖ ≤ 1).card

/-- Open-unit-disk root count, with algebraic multiplicity. -/
noncomputable def polynomialOpenRootCount (p : Polynomial ℂ) : ℕ :=
  (p.roots.filter fun z => ‖z‖ < 1).card

/-- Root-form radial logarithmic Mahler expression. -/
noncomputable def polynomialRadialLogMahler (p : Polynomial ℂ) (δ : ℝ) : ℝ :=
  radialLogMahler (p.roots.map fun z => Real.log ‖z‖) δ

lemma polynomial_ne_zero_of_coeff_zero_ne {p : Polynomial ℂ} (h0 : p.coeff 0 ≠ 0) :
    p ≠ 0 := by
  intro hp
  simp [hp] at h0

lemma root_ne_zero_of_coeff_zero_ne {p : Polynomial ℂ} (h0 : p.coeff 0 ≠ 0)
    {z : ℂ} (hz : z ∈ p.roots) : z ≠ 0 := by
  have hp : p ≠ 0 := polynomial_ne_zero_of_coeff_zero_ne h0
  have hroot := (Polynomial.mem_roots hp).mp hz
  intro hz0
  subst z
  apply h0
  rw [Polynomial.coeff_zero_eq_eval_zero]
  simpa [Polynomial.IsRoot.def] using hroot

lemma closed_log_filter_card (p : Polynomial ℂ) :
    ((p.roots.map fun z => Real.log ‖z‖).filter (· ≤ 0)).card =
      polynomialClosedRootCount p := by
  classical
  unfold polynomialClosedRootCount
  rw [Multiset.filter_map, Multiset.card_map]
  congr 1
  apply Multiset.filter_congr
  intro z hz
  exact Real.log_nonpos_iff (norm_nonneg z)

lemma open_log_filter_card {p : Polynomial ℂ} (h0 : p.coeff 0 ≠ 0) :
    ((p.roots.map fun z => Real.log ‖z‖).filter (· < 0)).card =
      polynomialOpenRootCount p := by
  classical
  unfold polynomialOpenRootCount
  rw [Multiset.filter_map, Multiset.card_map]
  congr 1
  apply Multiset.filter_congr
  intro z hz
  exact Real.log_neg_iff (norm_pos_iff.mpr (root_ne_zero_of_coeff_zero_ne h0 hz))

/-- Polynomial outward Jensen inequality in root form. -/
theorem polynomial_closed_count_mul_le_radial_sub (p : Polynomial ℂ)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    (polynomialClosedRootCount p : ℝ) * δ ≤
      polynomialRadialLogMahler p δ - polynomialRadialLogMahler p 0 := by
  unfold polynomialRadialLogMahler
  rw [← closed_log_filter_card]
  exact closed_count_mul_le_radialLogMahler_sub _ hδ

/-- Polynomial inward Jensen inequality in root form. -/
theorem polynomial_radial_sub_le_open_count_mul {p : Polynomial ℂ}
    (h0 : p.coeff 0 ≠ 0) {δ : ℝ} (hδ : 0 ≤ δ) :
    polynomialRadialLogMahler p 0 - polynomialRadialLogMahler p (-δ) ≤
      (polynomialOpenRootCount p : ℝ) * δ := by
  unfold polynomialRadialLogMahler
  rw [← open_log_filter_card h0]
  exact radialLogMahler_sub_le_open_count_mul _ hδ

end Erdos522

end AmalgamatedModule22


/-! ===== amalgamated from Research.MahlerRadial ===== -/

section AmalgamatedModule23


open scoped Real

namespace Erdos522

lemma norm_real_exp_complex (δ : ℝ) : ‖((Real.exp δ : ℝ) : ℂ)‖ = Real.exp δ := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos δ)]

lemma posLog_norm_exp_inv_mul (δ : ℝ) {z : ℂ} (hz : z ≠ 0) :
    log⁺ ‖(((Real.exp δ : ℝ) : ℂ)⁻¹ * z)‖ =
      hinge (Real.log ‖z‖ - δ) := by
  rw [Real.posLog_apply]
  unfold hinge
  congr 1
  rw [norm_mul, norm_inv, norm_real_exp_complex]
  rw [Real.log_mul]
  · rw [Real.log_inv, Real.log_exp]
    ring
  · exact inv_ne_zero (ne_of_gt (Real.exp_pos δ))
  · exact norm_ne_zero_iff.mpr hz

lemma leadingCoeff_radial_comp {p : Polynomial ℂ} (δ : ℝ) :
    (p.comp (Polynomial.C (((Real.exp δ : ℝ) : ℂ)) * Polynomial.X)).leadingCoeff =
      p.leadingCoeff * (((Real.exp δ : ℝ) : ℂ) ^ p.natDegree) := by
  rw [Polynomial.leadingCoeff_comp (by simp)]
  simp

lemma roots_radial_comp (p : Polynomial ℂ) (δ : ℝ) :
    (p.comp (Polynomial.C (((Real.exp δ : ℝ) : ℂ)) * Polynomial.X)).roots =
      p.roots.map fun z => (((Real.exp δ : ℝ) : ℂ)⁻¹ * z) := by
  have hu : IsUnit (((Real.exp δ : ℝ) : ℂ)) :=
    isUnit_iff_ne_zero.mpr (by exact_mod_cast (ne_of_gt (Real.exp_pos δ)))
  simpa using Polynomial.roots_comp_C_mul_X_add_C p
    (((Real.exp δ : ℝ) : ℂ)) 0 hu

/-- The root-form radial expression from F-004 is exactly Mathlib's logarithmic
Mahler measure after composing with the radial dilation `z ↦ exp(δ) z`. -/
theorem polynomialRadialLogMahler_eq_logMahlerMeasure_comp
    {p : Polynomial ℂ} (h0 : p.coeff 0 ≠ 0) (hlc : ‖p.leadingCoeff‖ = 1)
    (δ : ℝ) :
    polynomialRadialLogMahler p δ =
      (p.comp (Polynomial.C (((Real.exp δ : ℝ) : ℂ)) * Polynomial.X)).logMahlerMeasure := by
  rw [Polynomial.logMahlerMeasure_eq_log_leadingCoeff_add_sum_log_roots]
  rw [leadingCoeff_radial_comp, roots_radial_comp]
  unfold polynomialRadialLogMahler radialLogMahler
  simp only [Multiset.card_map, Multiset.map_map, Function.comp_apply]
  have hroot : ∀ z ∈ p.roots, z ≠ 0 := fun z hz =>
    root_ne_zero_of_coeff_zero_ne h0 hz
  have hmaps :
      (p.roots.map fun z => log⁺ ‖(((Real.exp δ : ℝ) : ℂ)⁻¹ * z)‖).sum =
      (p.roots.map fun z => hinge (Real.log ‖z‖ - δ)).sum := by
    apply congrArg Multiset.sum
    apply Multiset.map_congr rfl
    intro z hz
    exact posLog_norm_exp_inv_mul δ (hroot z hz)
  rw [hmaps]
  rw [norm_mul, norm_pow, norm_real_exp_complex, hlc, one_mul]
  rw [Real.log_pow, Real.log_exp]
  rw [(IsAlgClosed.splits p).natDegree_eq_card_roots]

/-- Outward Jensen inequality stated directly with Mathlib's circle-average
logarithmic Mahler measure. -/
theorem polynomial_closed_count_mul_le_logMahler_comp_sub
    {p : Polynomial ℂ} (h0 : p.coeff 0 ≠ 0) (hlc : ‖p.leadingCoeff‖ = 1)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    (polynomialClosedRootCount p : ℝ) * δ ≤
      (p.comp (Polynomial.C (((Real.exp δ : ℝ) : ℂ)) * Polynomial.X)).logMahlerMeasure -
      p.logMahlerMeasure := by
  rw [← polynomialRadialLogMahler_eq_logMahlerMeasure_comp h0 hlc δ]
  have hzero : polynomialRadialLogMahler p 0 = p.logMahlerMeasure := by
    simpa using polynomialRadialLogMahler_eq_logMahlerMeasure_comp h0 hlc 0
  rw [← hzero]
  simpa using polynomial_closed_count_mul_le_radial_sub p hδ

/-- Inward Jensen inequality stated directly with Mathlib's circle-average
logarithmic Mahler measure. -/
theorem logMahler_sub_comp_le_polynomial_open_count_mul
    {p : Polynomial ℂ} (h0 : p.coeff 0 ≠ 0) (hlc : ‖p.leadingCoeff‖ = 1)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    p.logMahlerMeasure -
      (p.comp (Polynomial.C (((Real.exp (-δ) : ℝ) : ℂ)) * Polynomial.X)).logMahlerMeasure ≤
      (polynomialOpenRootCount p : ℝ) * δ := by
  rw [← polynomialRadialLogMahler_eq_logMahlerMeasure_comp h0 hlc (-δ)]
  have hzero : polynomialRadialLogMahler p 0 = p.logMahlerMeasure := by
    simpa using polynomialRadialLogMahler_eq_logMahlerMeasure_comp h0 hlc 0
  rw [← hzero]
  simpa using polynomial_radial_sub_le_open_count_mul h0 hδ

end Erdos522

end AmalgamatedModule23


/-! ===== amalgamated from Research.DeterministicReduction ===== -/

section AmalgamatedModule24


open scoped BigOperators Real

namespace Erdos522

lemma radialVariance_zero (n : ℕ) : radialVariance n 0 = (n + 1 : ℝ) := by
  simp [radialVariance]

/-- The radially evaluated log-Mahler measure after subtracting its natural
coefficient `L²` normalization. -/
noncomputable def centeredRadialLogMahler (p : Polynomial ℂ) (n : ℕ) (s : ℝ) : ℝ :=
  (p.comp (Polynomial.C (((Real.exp (s / n) : ℝ) : ℂ)) * Polynomial.X)).logMahlerMeasure -
    Real.log (radialVariance n s) / 2

lemma centeredRadialLogMahler_zero (p : Polynomial ℂ) (n : ℕ) :
    centeredRadialLogMahler p n 0 =
      p.logMahlerMeasure - Real.log (n + 1 : ℝ) / 2 := by
  simp [centeredRadialLogMahler, radialVariance_zero]

lemma polynomialOpenRootCount_le_closedRootCount (p : Polynomial ℂ) :
    polynomialOpenRootCount p ≤ polynomialClosedRootCount p := by
  classical
  unfold polynomialOpenRootCount polynomialClosedRootCount
  apply Multiset.card_le_card
  rw [Multiset.le_filter]
  constructor
  · exact Multiset.filter_le _ _
  · intro z hz
    exact le_of_lt (Multiset.mem_filter.mp hz).2

/-- The outward Jensen bound after separating the centered random term from the
explicit deterministic coefficient variance. -/
theorem closed_root_ratio_le_centered_add_chord
    {p : Polynomial ℂ} (h0 : p.coeff 0 ≠ 0) (hlc : ‖p.leadingCoeff‖ = 1)
    {n : ℕ} (hn : 0 < n) {s : ℝ} (hs : 0 < s) :
    (polynomialClosedRootCount p : ℝ) / n ≤
      (centeredRadialLogMahler p n s - centeredRadialLogMahler p n 0) / s +
      Real.log ((1 + Real.exp (2 * s)) / 2) / (2 * s) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hδ : 0 ≤ s / (n : ℝ) := div_nonneg hs.le hnR.le
  have hj := polynomial_closed_count_mul_le_logMahler_comp_sub h0 hlc hδ
  have hv := half_log_radialVariance_ratio_le_chord n hn s
  have hid :
      (p.comp (Polynomial.C (((Real.exp (s / n) : ℝ) : ℂ)) * Polynomial.X)).logMahlerMeasure -
          p.logMahlerMeasure =
        (centeredRadialLogMahler p n s - centeredRadialLogMahler p n 0) +
          (Real.log (radialVariance n s) - Real.log (n + 1 : ℝ)) / 2 := by
    rw [centeredRadialLogMahler_zero]
    unfold centeredRadialLogMahler
    ring
  rw [hid] at hj
  calc
    (polynomialClosedRootCount p : ℝ) / n =
        ((polynomialClosedRootCount p : ℝ) * (s / n)) / s := by
          field_simp
    _ ≤ ((centeredRadialLogMahler p n s - centeredRadialLogMahler p n 0) +
          (Real.log (radialVariance n s) - Real.log (n + 1 : ℝ)) / 2) / s :=
        div_le_div_of_nonneg_right hj hs.le
    _ ≤ (centeredRadialLogMahler p n s - centeredRadialLogMahler p n 0) / s +
          Real.log ((1 + Real.exp (2 * s)) / 2) / (2 * s) := by
        have hvs := div_le_div_of_nonneg_right hv hs.le
        calc
          ((centeredRadialLogMahler p n s - centeredRadialLogMahler p n 0) +
              (Real.log (radialVariance n s) - Real.log (n + 1 : ℝ)) / 2) / s =
            (centeredRadialLogMahler p n s - centeredRadialLogMahler p n 0) / s +
              ((Real.log (radialVariance n s) - Real.log (n + 1 : ℝ)) / 2) / s := by ring
          _ ≤ (centeredRadialLogMahler p n s - centeredRadialLogMahler p n 0) / s +
              (Real.log ((1 + Real.exp (2 * s)) / 2) / 2) / s := by gcongr
          _ = _ := by ring

/-- The inward Jensen bound after separating the centered random term from the
explicit deterministic coefficient variance. -/
theorem neg_chord_add_centered_le_closed_root_ratio
    {p : Polynomial ℂ} (h0 : p.coeff 0 ≠ 0) (hlc : ‖p.leadingCoeff‖ = 1)
    {n : ℕ} (hn : 0 < n) {s : ℝ} (hs : 0 < s) :
    -Real.log ((1 + Real.exp (-2 * s)) / 2) / (2 * s) +
        (centeredRadialLogMahler p n 0 - centeredRadialLogMahler p n (-s)) / s ≤
      (polynomialClosedRootCount p : ℝ) / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hδ : 0 ≤ s / (n : ℝ) := div_nonneg hs.le hnR.le
  have hj := logMahler_sub_comp_le_polynomial_open_count_mul h0 hlc hδ
  have hopen := polynomialOpenRootCount_le_closedRootCount p
  have hopenR : (polynomialOpenRootCount p : ℝ) ≤ polynomialClosedRootCount p := by
    exact_mod_cast hopen
  have hjclosed :
      p.logMahlerMeasure -
          (p.comp (Polynomial.C (((Real.exp (-(s / n)) : ℝ) : ℂ)) * Polynomial.X)).logMahlerMeasure ≤
        (polynomialClosedRootCount p : ℝ) * (s / n) :=
    hj.trans (mul_le_mul_of_nonneg_right hopenR hδ)
  have hv := half_log_radialVariance_ratio_le_chord n hn (-s)
  have hid :
      p.logMahlerMeasure -
          (p.comp (Polynomial.C (((Real.exp (-(s / n)) : ℝ) : ℂ)) * Polynomial.X)).logMahlerMeasure =
        (centeredRadialLogMahler p n 0 - centeredRadialLogMahler p n (-s)) +
          (Real.log (n + 1 : ℝ) - Real.log (radialVariance n (-s))) / 2 := by
    rw [centeredRadialLogMahler_zero]
    unfold centeredRadialLogMahler
    rw [show (-s) / (n : ℝ) = -(s / n) by ring]
    ring
  rw [hid] at hjclosed
  have hv' :
      (Real.log (radialVariance n (-s)) - Real.log (n + 1 : ℝ)) / 2 ≤
        Real.log ((1 + Real.exp (-2 * s)) / 2) / 2 := by
    simpa [show 2 * (-s) = -2 * s by ring] using hv
  have hvneg :
      -Real.log ((1 + Real.exp (-2 * s)) / 2) / 2 ≤
        (Real.log (n + 1 : ℝ) - Real.log (radialVariance n (-s))) / 2 := by
    linarith
  have hvs := div_le_div_of_nonneg_right hvneg hs.le
  calc
    -Real.log ((1 + Real.exp (-2 * s)) / 2) / (2 * s) +
        (centeredRadialLogMahler p n 0 - centeredRadialLogMahler p n (-s)) / s =
      (-Real.log ((1 + Real.exp (-2 * s)) / 2) / 2) / s +
        (centeredRadialLogMahler p n 0 - centeredRadialLogMahler p n (-s)) / s := by ring
    _ ≤ ((Real.log (n + 1 : ℝ) - Real.log (radialVariance n (-s))) / 2) / s +
        (centeredRadialLogMahler p n 0 - centeredRadialLogMahler p n (-s)) / s :=
      by simpa [add_comm] using
        add_le_add_right hvs
          ((centeredRadialLogMahler p n 0 - centeredRadialLogMahler p n (-s)) / s)
    _ = ((centeredRadialLogMahler p n 0 - centeredRadialLogMahler p n (-s)) +
          (Real.log (n + 1 : ℝ) - Real.log (radialVariance n (-s))) / 2) / s := by ring
    _ ≤ ((polynomialClosedRootCount p : ℝ) * (s / n)) / s :=
      div_le_div_of_nonneg_right hjclosed hs.le
    _ = (polynomialClosedRootCount p : ℝ) / n := by field_simp

/-- Complete deterministic reduction: convergence of the centered radial
log-Mahler increments at every fixed shift forces half of the roots into the
closed unit disk.  No rate and no uniformity in the shift are assumed. -/
theorem tendsto_closed_root_ratio_of_centered_radial_increments
    (p : ℕ → Polynomial ℂ)
    (h0 : ∀ m, (p m).coeff 0 ≠ 0)
    (hlc : ∀ m, ‖(p m).leadingCoeff‖ = 1)
    (hcenter : ∀ s : ℝ, Filter.Tendsto
      (fun m => centeredRadialLogMahler (p m) (m + 1) s -
        centeredRadialLogMahler (p m) (m + 1) 0)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun m => (polynomialClosedRootCount (p m) : ℝ) / (m + 1 : ℝ))
      Filter.atTop (nhds (1 / 2 : ℝ)) := by
  have hU : Filter.Tendsto
      (fun s : ℝ => Real.log ((1 + Real.exp (2 * s)) / 2) / (2 * s))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 / 2 : ℝ)) := by
    convert tendsto_log_exp_chord_div_right.div_const 2 using 1 <;> ring
  have hL : Filter.Tendsto
      (fun s : ℝ => -Real.log ((1 + Real.exp (-2 * s)) / 2) / (2 * s))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 / 2 : ℝ)) := by
    convert tendsto_neg_log_exp_neg_chord_div_right.div_const 2 using 1 <;> ring
  rw [tendsto_order]
  constructor
  · intro a ha
    have heventL := (tendsto_order.mp hL).1 a ha
    have hpos : ∀ᶠ s : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < s :=
      self_mem_nhdsWithin
    obtain ⟨s, hs, has⟩ := (hpos.and heventL).exists
    have herr0 : Filter.Tendsto
        (fun m => (centeredRadialLogMahler (p m) (m + 1) 0 -
          centeredRadialLogMahler (p m) (m + 1) (-s)) / s)
        Filter.atTop (nhds 0) := by
      have h := (hcenter (-s)).neg.div_const s
      simpa using h
    have herr := (tendsto_order.mp herr0).1 (a -
      (-Real.log ((1 + Real.exp (-2 * s)) / 2) / (2 * s))) (by linarith)
    filter_upwards [herr] with m hm
    have hpoint := neg_chord_add_centered_le_closed_root_ratio
      (h0 m) (hlc m) (Nat.zero_lt_succ m) hs
    norm_num [Nat.cast_add, Nat.cast_one] at hpoint
    rw [show -(2 * s) = -2 * s by ring] at hpoint
    linarith
  · intro a ha
    have heventU := (tendsto_order.mp hU).2 a ha
    have hpos : ∀ᶠ s : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < s :=
      self_mem_nhdsWithin
    obtain ⟨s, hs, hsa⟩ := (hpos.and heventU).exists
    have herr0 : Filter.Tendsto
        (fun m => (centeredRadialLogMahler (p m) (m + 1) s -
          centeredRadialLogMahler (p m) (m + 1) 0) / s)
        Filter.atTop (nhds 0) := by
      simpa [ne_of_gt hs] using (hcenter s).div_const s
    have herr := (tendsto_order.mp herr0).2 (a -
      Real.log ((1 + Real.exp (2 * s)) / 2) / (2 * s)) (by linarith)
    filter_upwards [herr] with m hm
    have hpoint := closed_root_ratio_le_centered_add_chord
      (h0 m) (hlc m) (Nat.zero_lt_succ m) hs
    norm_num [Nat.cast_add, Nat.cast_one] at hpoint
    linarith

/-- Countable-shift version of the reduction, suited to taking one
probability-one intersection. -/
theorem tendsto_closed_root_ratio_of_countable_centered_increments
    (p : ℕ → Polynomial ℂ) (shift : ℕ → ℝ)
    (hshiftPos : ∀ j, 0 < shift j)
    (hshift : Filter.Tendsto shift Filter.atTop (nhdsWithin 0 (Set.Ioi 0)))
    (h0 : ∀ m, (p m).coeff 0 ≠ 0)
    (hlc : ∀ m, ‖(p m).leadingCoeff‖ = 1)
    (hcenterPos : ∀ j, Filter.Tendsto
      (fun m => centeredRadialLogMahler (p m) (m + 1) (shift j) -
        centeredRadialLogMahler (p m) (m + 1) 0)
      Filter.atTop (nhds 0))
    (hcenterNeg : ∀ j, Filter.Tendsto
      (fun m => centeredRadialLogMahler (p m) (m + 1) (-shift j) -
        centeredRadialLogMahler (p m) (m + 1) 0)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun m => (polynomialClosedRootCount (p m) : ℝ) / (m + 1 : ℝ))
      Filter.atTop (nhds (1 / 2 : ℝ)) := by
  have hU : Filter.Tendsto
      (fun s : ℝ => Real.log ((1 + Real.exp (2 * s)) / 2) / (2 * s))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 / 2 : ℝ)) := by
    convert tendsto_log_exp_chord_div_right.div_const 2 using 1 <;> ring
  have hL : Filter.Tendsto
      (fun s : ℝ => -Real.log ((1 + Real.exp (-2 * s)) / 2) / (2 * s))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 / 2 : ℝ)) := by
    convert tendsto_neg_log_exp_neg_chord_div_right.div_const 2 using 1 <;> ring
  have hUseq := hU.comp hshift
  have hLseq := hL.comp hshift
  rw [tendsto_order]
  constructor
  · intro a ha
    obtain ⟨j, haj⟩ := ((tendsto_order.mp hLseq).1 a ha).exists
    change a < -Real.log ((1 + Real.exp (-2 * shift j)) / 2) / (2 * shift j) at haj
    have hs := hshiftPos j
    have herr0 : Filter.Tendsto
        (fun m => (centeredRadialLogMahler (p m) (m + 1) 0 -
          centeredRadialLogMahler (p m) (m + 1) (-shift j)) / shift j)
        Filter.atTop (nhds 0) := by
      have h := (hcenterNeg j).neg.div_const (shift j)
      simpa using h
    have herr := (tendsto_order.mp herr0).1 (a -
      (-Real.log ((1 + Real.exp (-2 * shift j)) / 2) / (2 * shift j))) (by linarith)
    filter_upwards [herr] with m hm
    have hpoint := neg_chord_add_centered_le_closed_root_ratio
      (h0 m) (hlc m) (Nat.zero_lt_succ m) hs
    norm_num [Nat.cast_add, Nat.cast_one] at hpoint
    rw [show -(2 * shift j) = -2 * shift j by ring] at hpoint
    linarith
  · intro a ha
    obtain ⟨j, hja⟩ := ((tendsto_order.mp hUseq).2 a ha).exists
    change Real.log ((1 + Real.exp (2 * shift j)) / 2) / (2 * shift j) < a at hja
    have hs := hshiftPos j
    have herr0 : Filter.Tendsto
        (fun m => (centeredRadialLogMahler (p m) (m + 1) (shift j) -
          centeredRadialLogMahler (p m) (m + 1) 0) / shift j)
        Filter.atTop (nhds 0) := by
      simpa [ne_of_gt hs] using (hcenterPos j).div_const (shift j)
    have herr := (tendsto_order.mp herr0).2 (a -
      Real.log ((1 + Real.exp (2 * shift j)) / 2) / (2 * shift j)) (by linarith)
    filter_upwards [herr] with m hm
    have hpoint := closed_root_ratio_le_centered_add_chord
      (h0 m) (hlc m) (Nat.zero_lt_succ m) hs
    norm_num [Nat.cast_add, Nat.cast_one] at hpoint
    linarith

/-- Specialization to the reciprocal shifts `1/(j+1)`. -/
theorem tendsto_closed_root_ratio_of_reciprocal_centered_increments
    (p : ℕ → Polynomial ℂ)
    (h0 : ∀ m, (p m).coeff 0 ≠ 0)
    (hlc : ∀ m, ‖(p m).leadingCoeff‖ = 1)
    (hcenterPos : ∀ j : ℕ, Filter.Tendsto
      (fun m => centeredRadialLogMahler (p m) (m + 1) ((1 : ℝ) / ((j : ℝ) + 1)) -
        centeredRadialLogMahler (p m) (m + 1) 0)
      Filter.atTop (nhds 0))
    (hcenterNeg : ∀ j : ℕ, Filter.Tendsto
      (fun m => centeredRadialLogMahler (p m) (m + 1) (-((1 : ℝ) / ((j : ℝ) + 1))) -
        centeredRadialLogMahler (p m) (m + 1) 0)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun m => (polynomialClosedRootCount (p m) : ℝ) / (m + 1 : ℝ))
      Filter.atTop (nhds (1 / 2 : ℝ)) := by
  apply tendsto_closed_root_ratio_of_countable_centered_increments p
    (fun j => (1 : ℝ) / (j + 1))
  · intro j
    positivity
  · rw [tendsto_nhdsWithin_iff]
    constructor
    · simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    · filter_upwards [] with j
      change 0 < (1 : ℝ) / (j + 1)
      positivity
  · exact h0
  · exact hlc
  · exact hcenterPos
  · exact hcenterNeg

end Erdos522

end AmalgamatedModule24


/-! ===== amalgamated from Research.NormalizedRadialPolynomial ===== -/

section AmalgamatedModule25


namespace Erdos522

/-- The radially evaluated polynomial divided by its coefficient `L²` norm. -/
noncomputable def normalizedRadialPolynomial (p : Polynomial ℂ)
    (n : ℕ) (s : ℝ) : Polynomial ℂ :=
  Polynomial.C ((((√(radialVariance n s) : ℝ) : ℂ))⁻¹) *
    p.comp (Polynomial.C (((Real.exp (s / n) : ℝ) : ℂ)) * Polynomial.X)

lemma radial_comp_ne_zero {p : Polynomial ℂ} (hp : p ≠ 0) (δ : ℝ) :
    p.comp (Polynomial.C (((Real.exp δ : ℝ) : ℂ)) * Polynomial.X) ≠ 0 := by
  intro hzero
  have hlead := congrArg Polynomial.leadingCoeff hzero
  rw [leadingCoeff_radial_comp] at hlead
  simp only [Polynomial.leadingCoeff_zero] at hlead
  exact (mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hp)
    (pow_ne_zero _ (by exact_mod_cast (Real.exp_pos δ).ne'))) hlead

lemma normalizedRadialPolynomial_ne_zero {p : Polynomial ℂ} (hp : p ≠ 0)
    (n : ℕ) (s : ℝ) : normalizedRadialPolynomial p n s ≠ 0 := by
  unfold normalizedRadialPolynomial
  apply mul_ne_zero
  · rw [map_ne_zero]
    exact inv_ne_zero (by
      exact_mod_cast (Real.sqrt_pos.mpr (radialVariance_pos n s)).ne')
  · exact radial_comp_ne_zero hp _

/-- The centered observable is exactly the logarithmic Mahler measure of the
unit-variance normalized radial polynomial. -/
theorem normalizedRadialPolynomial_logMahlerMeasure
    {p : Polynomial ℂ} (hp : p ≠ 0) (n : ℕ) (s : ℝ) :
    (normalizedRadialPolynomial p n s).logMahlerMeasure =
      centeredRadialLogMahler p n s := by
  have hvpos := radialVariance_pos n s
  have hsqrt : 0 < √(radialVariance n s) := Real.sqrt_pos.mpr hvpos
  unfold normalizedRadialPolynomial centeredRadialLogMahler
  rw [Polynomial.logMahlerMeasure_C_mul]
  · rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsqrt,
      Real.log_inv, Real.log_sqrt hvpos.le]
    ring
  · exact inv_ne_zero (by exact_mod_cast hsqrt.ne')
  · exact radial_comp_ne_zero hp _

/-- Pointwise evaluation has the expected normalized random Fourier-sum form. -/
theorem normalizedRadialPolynomial_eval (p : Polynomial ℂ)
    (n : ℕ) (s : ℝ) (z : ℂ) :
    (normalizedRadialPolynomial p n s).eval z =
      (((√(radialVariance n s) : ℝ) : ℂ))⁻¹ *
        p.eval ((((Real.exp (s / n) : ℝ) : ℂ)) * z) := by
  unfold normalizedRadialPolynomial
  simp [Polynomial.eval_comp]

end Erdos522

end AmalgamatedModule25


/-! ===== amalgamated from Research.AngularLipschitz ===== -/

section AmalgamatedModule26


open scoped BigOperators
open MeasureTheory

namespace Erdos522

/-- Angular average of a real statistic of a complex polynomial on the unit
circle. -/
noncomputable def angularStatistic (h : ℂ → ℝ) (p : Polynomial ℂ) : ℝ :=
  Real.circleAverage (fun z => h (p.eval z)) 0 1

lemma circleIntegrable_norm_eval (p : Polynomial ℂ) :
    CircleIntegrable (fun z => ‖p.eval z‖) 0 1 := by
  apply ContinuousOn.circleIntegrable (by norm_num)
  fun_prop

lemma circleIntegrable_sq_norm_eval (p : Polynomial ℂ) :
    CircleIntegrable (fun z => ‖p.eval z‖ ^ 2) 0 1 := by
  apply ContinuousOn.circleIntegrable (by norm_num)
  fun_prop

/-- `L¹≤L²` on the normalized circle, followed by polynomial Parseval. -/
theorem circleAverage_norm_eval_le_sqrt_sum_sq (p : Polynomial ℂ) :
    Real.circleAverage (fun z => ‖p.eval z‖) 0 1 ≤
      √(∑ i ∈ p.support, ‖p.coeff i‖ ^ 2) := by
  have : IsFiniteMeasure (volume.restrict (Set.uIoc 0 (2 * Real.pi))) := by
    rw [Set.uIoc_of_le (by positivity)]
    infer_instance
  have : NeZero (volume (Set.uIoc 0 (2 * Real.pi))) := ⟨by simp⟩
  have hnonneg : 0 ≤ Real.circleAverage (fun z => ‖p.eval z‖) 0 1 :=
    Real.circleAverage_nonneg_of_nonneg (fun z hz => norm_nonneg _)
  calc
    Real.circleAverage (fun z => ‖p.eval z‖) 0 1 =
        √((Real.circleAverage (fun z => ‖p.eval z‖) 0 1) ^ 2) := by
      rw [Real.sqrt_sq hnonneg]
    _ ≤ √(Real.circleAverage (fun z => ‖p.eval z‖ ^ 2) 0 1) := by
      gcongr
      rw [Real.circleAverage_eq_intervalAverage, Real.circleAverage_eq_intervalAverage]
      refine (convexOn_pow 2).map_average_le (continuousOn_pow 2)
        isClosed_Ici (by filter_upwards; simp) ?_ ?_
      · exact ((by fun_prop : Continuous (fun θ : ℝ =>
          ‖p.eval (circleMap 0 1 θ)‖))).integrableOn_Icc.mono_set
            Set.Ioc_subset_Icc_self
      · exact ((by fun_prop : Continuous (fun θ : ℝ =>
          ‖p.eval (circleMap 0 1 θ)‖ ^ 2))).integrableOn_Icc.mono_set
            Set.Ioc_subset_Icc_self
    _ = √(∑ i ∈ p.support, ‖p.coeff i‖ ^ 2) := by
      rw [← p.sum_sq_norm_coeff_eq_circleAverage]

/-- Parseval gives the sharp Euclidean coefficient Lipschitz constant for every
angular Lipschitz statistic. -/
theorem abs_angularStatistic_sub_le
    {K : NNReal} {h : ℂ → ℝ} (hh : LipschitzWith K h)
    (p q : Polynomial ℂ) :
    |angularStatistic h p - angularStatistic h q| ≤
      (K : ℝ) * √(∑ i ∈ (p - q).support, ‖(p - q).coeff i‖ ^ 2) := by
  have hp : CircleIntegrable (fun z => h (p.eval z)) 0 1 := by
    apply ContinuousOn.circleIntegrable (by norm_num)
    exact (hh.continuous.comp
      (Polynomial.continuous_eval₂ p (RingHom.id ℂ))).continuousOn
  have hq : CircleIntegrable (fun z => h (q.eval z)) 0 1 := by
    apply ContinuousOn.circleIntegrable (by norm_num)
    exact (hh.continuous.comp
      (Polynomial.continuous_eval₂ q (RingHom.id ℂ))).continuousOn
  have habs : CircleIntegrable (fun z => |h (p.eval z) - h (q.eval z)|) 0 1 := by
    change CircleIntegrable
      |(fun z => h (p.eval z)) - fun z => h (q.eval z)| 0 1
    exact (hp.sub hq).abs
  have hscaled : CircleIntegrable (fun z => (K : ℝ) * ‖(p - q).eval z‖) 0 1 := by
    apply ContinuousOn.circleIntegrable (by norm_num)
    fun_prop
  unfold angularStatistic
  rw [← Real.circleAverage_sub hp hq]
  calc
    |Real.circleAverage
        ((fun z => h (p.eval z)) - fun z => h (q.eval z)) 0 1| ≤
      Real.circleAverage
        (fun z => |h (p.eval z) - h (q.eval z)|) 0 1 := by
        change |Real.circleAverage
          ((fun z => h (p.eval z)) - fun z => h (q.eval z)) 0 1| ≤
            Real.circleAverage
              |(fun z => h (p.eval z)) - fun z => h (q.eval z)| 0 1
        exact Real.abs_circleAverage_le_circleAverage_abs
    _ ≤ Real.circleAverage
        (fun z => (K : ℝ) * ‖(p - q).eval z‖) 0 1 := by
      apply Real.circleAverage_mono habs
      · exact hscaled
      · intro z hz
        simpa [Polynomial.eval_sub, dist_eq_norm] using
          hh.dist_le_mul (p.eval z) (q.eval z)
    _ = (K : ℝ) * Real.circleAverage (fun z => ‖(p - q).eval z‖) 0 1 := by
      change Real.circleAverage
        ((K : ℝ) • (fun z => ‖(p - q).eval z‖)) 0 1 = _
      simpa [smul_eq_mul] using
        (Real.circleAverage_smul (f := fun z => ‖(p - q).eval z‖)
          (c := 0) (R := 1) (a := (K : ℝ)))
    _ ≤ (K : ℝ) * √(∑ i ∈ (p - q).support, ‖(p - q).coeff i‖ ^ 2) := by
      gcongr
      exact circleAverage_norm_eval_le_sqrt_sum_sq (p - q)

end Erdos522

end AmalgamatedModule26


/-! ===== amalgamated from Research.ClippedLog ===== -/

section AmalgamatedModule27


open Set

namespace Erdos522

/-- Clamp a nonnegative radius to `[1/M,M]`. -/
noncomputable def clippedRadius (M : NNReal) (x : ℝ) : ℝ :=
  min (M : ℝ) (max (1 / (M : ℝ)) x)

/-- Symmetrically clipped logarithmic modulus. -/
noncomputable def clippedLog (M : NNReal) (z : ℂ) : ℝ :=
  Real.log (clippedRadius M ‖z‖)

lemma log_lipschitzOn_Ici_inv (M : NNReal) (hM : 1 ≤ M) :
    LipschitzOnWith M Real.log (Ici (1 / (M : ℝ))) := by
  have hMp : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one (by exact_mod_cast hM)
  apply Convex.lipschitzOnWith_of_nnnorm_deriv_le
  · intro x hx
    exact Real.differentiableAt_log
      (lt_of_lt_of_le (one_div_pos.mpr hMp) hx).ne'
  · intro x hx
    rw [Real.deriv_log]
    apply (NNReal.coe_le_coe).mp
    rw [coe_nnnorm]
    have hxpos : 0 < x := lt_of_lt_of_le (one_div_pos.mpr hMp) hx
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hxpos)]
    exact (inv_le_comm₀ hxpos hMp).mpr (by simpa [one_div] using hx)
  · exact convex_Ici _

lemma clippedRadius_lipschitz (M : NNReal) :
    LipschitzWith 1 (clippedRadius M) := by
  have hmax : LipschitzWith 1 (fun x : ℝ => max (1 / (M : ℝ)) x) := by
    simpa using
      (LipschitzWith.const (α := ℝ) (1 / (M : ℝ))).max LipschitzWith.id
  unfold clippedRadius
  simpa using (LipschitzWith.const (α := ℝ) (M : ℝ)).min hmax

lemma norm_lipschitz_complex : LipschitzWith 1 (fun z : ℂ => ‖z‖) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simpa [Real.dist_eq, dist_eq_norm] using abs_norm_sub_norm_le z w

lemma clippedRadius_lower (M : NNReal) (hM : 1 ≤ M) (x : ℝ) :
    1 / (M : ℝ) ≤ clippedRadius M x := by
  have hMp : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one (by exact_mod_cast hM)
  have hone : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have haM : 1 / (M : ℝ) ≤ (M : ℝ) :=
    ((div_le_one hMp).mpr hone).trans hone
  exact le_min haM (le_max_left _ _)

lemma clippedRadius_upper (M : NNReal) (x : ℝ) :
    clippedRadius M x ≤ (M : ℝ) := min_le_left _ _

/-- The clipped logarithm has global Lipschitz constant `M`. -/
theorem clippedLog_lipschitz (M : NNReal) (hM : 1 ≤ M) :
    LipschitzWith M (clippedLog M) := by
  have hlog := log_lipschitzOn_Ici_inv M hM
  have hcn : LipschitzWith 1 (fun z : ℂ => clippedRadius M ‖z‖) := by
    simpa [Function.comp_def] using (clippedRadius_lipschitz M).comp norm_lipschitz_complex
  have hmaps : MapsTo (fun z : ℂ => clippedRadius M ‖z‖) univ
      (Ici (1 / (M : ℝ))) := fun z hz => clippedRadius_lower M hM _
  have hout := hlog.comp (lipschitzOnWith_univ.mpr hcn) hmaps
  rw [lipschitzOnWith_univ] at hout
  change LipschitzWith M (fun z : ℂ => Real.log (clippedRadius M ‖z‖))
  simpa [Function.comp_def] using hout

/-- The clipping really stays between `-log M` and `log M`. -/
theorem abs_clippedLog_le_log (M : NNReal) (hM : 1 ≤ M) (z : ℂ) :
    |clippedLog M z| ≤ Real.log (M : ℝ) := by
  have hMp : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one (by exact_mod_cast hM)
  have hcpos : 0 < clippedRadius M ‖z‖ :=
    lt_of_lt_of_le (one_div_pos.mpr hMp) (clippedRadius_lower M hM _)
  rw [abs_le]
  constructor
  · have hlog := (Real.strictMonoOn_log.le_iff_le
      (one_div_pos.mpr hMp) hcpos).mpr (clippedRadius_lower M hM _)
    rw [show Real.log (1 / (M : ℝ)) = -Real.log (M : ℝ) by
      rw [one_div, Real.log_inv]] at hlog
    exact hlog
  · exact (Real.strictMonoOn_log.le_iff_le hcpos hMp).mpr
      (clippedRadius_upper M _)

/-- On the unclipped annulus the clipped statistic is the ordinary logarithm. -/
theorem clippedLog_eq_log_norm (M : NNReal) {z : ℂ}
    (hlow : 1 / (M : ℝ) ≤ ‖z‖) (hupp : ‖z‖ ≤ (M : ℝ)) :
    clippedLog M z = Real.log ‖z‖ := by
  unfold clippedLog clippedRadius
  rw [max_eq_right hlow, min_eq_right hupp]

end Erdos522

end AmalgamatedModule27


/-! ===== amalgamated from Research.WeightedAngularLipschitz ===== -/

section AmalgamatedModule28


open scoped BigOperators

namespace Erdos522

/-- A finite real coefficient vector, weighted by square roots of `w`, viewed
as a complex polynomial. -/
noncomputable def weightedVectorPolynomial {N : ℕ} (w x : Fin N → ℝ) :
    Polynomial ℂ :=
  ∑ k : Fin N,
    Polynomial.monomial (k : ℕ) (((√(w k) * x k : ℝ) : ℂ))

lemma coeff_weightedVectorPolynomial {N : ℕ} (w x : Fin N → ℝ) (j : Fin N) :
    (weightedVectorPolynomial w x).coeff j = (((√(w j) * x j : ℝ) : ℂ)) := by
  classical
  unfold weightedVectorPolynomial
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b hb hbj
    have hv : (b : ℕ) ≠ (j : ℕ) := fun h => hbj (Fin.ext h)
    simp [hv]
  · simp

lemma coeff_weightedVectorPolynomial_eq_zero_of_ge {N : ℕ}
    (w x : Fin N → ℝ) {j : ℕ} (hj : N ≤ j) :
    (weightedVectorPolynomial w x).coeff j = 0 := by
  classical
  unfold weightedVectorPolynomial
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro k hk
  rw [Polynomial.coeff_monomial, if_neg]
  exact fun h => by omega

lemma support_weightedVectorPolynomial_sub_subset_range {N : ℕ}
    (w x y : Fin N → ℝ) :
    (weightedVectorPolynomial w x - weightedVectorPolynomial w y).support ⊆
      Finset.range N := by
  intro j hj
  rw [Finset.mem_range]
  by_contra hnot
  have hge : N ≤ j := Nat.le_of_not_gt hnot
  have hx := coeff_weightedVectorPolynomial_eq_zero_of_ge w x hge
  have hy := coeff_weightedVectorPolynomial_eq_zero_of_ge w y hge
  rw [Polynomial.mem_support_iff, Polynomial.coeff_sub, hx, hy, sub_zero] at hj
  exact hj rfl

lemma coeff_sub_weightedVectorPolynomial {N : ℕ} (w x y : Fin N → ℝ)
    (j : Fin N) :
    (weightedVectorPolynomial w x - weightedVectorPolynomial w y).coeff j =
      (((√(w j) * (x j - y j) : ℝ) : ℂ)) := by
  rw [Polynomial.coeff_sub, coeff_weightedVectorPolynomial,
    coeff_weightedVectorPolynomial]
  push_cast
  ring

/-- The coefficient `ℓ²` distance is bounded by flatness times Euclidean
vector distance. -/
theorem weightedVectorPolynomial_coeff_distance_le {N : ℕ}
    (w x y : Fin N → ℝ) (B : ℝ)
    (hw0 : ∀ j, 0 ≤ w j) (hwB : ∀ j, w j ≤ B) :
    ∑ i ∈ (weightedVectorPolynomial w x - weightedVectorPolynomial w y).support,
        ‖(weightedVectorPolynomial w x - weightedVectorPolynomial w y).coeff i‖ ^ 2 ≤
      B * ∑ j : Fin N, (x j - y j) ^ 2 := by
  classical
  calc
    ∑ i ∈ (weightedVectorPolynomial w x - weightedVectorPolynomial w y).support,
        ‖(weightedVectorPolynomial w x - weightedVectorPolynomial w y).coeff i‖ ^ 2 ≤
      ∑ i ∈ Finset.range N,
        ‖(weightedVectorPolynomial w x - weightedVectorPolynomial w y).coeff i‖ ^ 2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
            (support_weightedVectorPolynomial_sub_subset_range w x y)
          intro i hi his
          positivity
    _ = ∑ j : Fin N, w j * (x j - y j) ^ 2 := by
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro j hj
      rw [coeff_sub_weightedVectorPolynomial]
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_mul]
      rw [abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
        Real.sq_sqrt (hw0 j), sq_abs]
    _ ≤ ∑ j : Fin N, B * (x j - y j) ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_right (hwB j) (sq_nonneg _)
    _ = B * ∑ j : Fin N, (x j - y j) ^ 2 := by
      rw [Finset.mul_sum]

/-- Angular Parseval for an arbitrary Lipschitz test: coefficient flatness
turns a `K`-Lipschitz planar test into a `K√B` coefficient modulus. -/
theorem weightedVectorPolynomial_angular_lipschitz
    {N : ℕ} (h : ℂ → ℝ) {K : NNReal} (hK : LipschitzWith K h)
    (w x y : Fin N → ℝ) (B : ℝ)
    (hw0 : ∀ j, 0 ≤ w j) (hwB : ∀ j, w j ≤ B) :
    |angularStatistic h (weightedVectorPolynomial w x) -
      angularStatistic h (weightedVectorPolynomial w y)| ≤
      (K : ℝ) * √(B * ∑ j : Fin N, (x j - y j) ^ 2) := by
  calc
    |angularStatistic h (weightedVectorPolynomial w x) -
      angularStatistic h (weightedVectorPolynomial w y)| ≤
      (K : ℝ) * √(∑ i ∈
        (weightedVectorPolynomial w x - weightedVectorPolynomial w y).support,
          ‖(weightedVectorPolynomial w x - weightedVectorPolynomial w y).coeff i‖ ^ 2) :=
      abs_angularStatistic_sub_le hK _ _
    _ ≤ (K : ℝ) * √(B * ∑ j : Fin N, (x j - y j) ^ 2) := by
      gcongr
      exact weightedVectorPolynomial_coeff_distance_le w x y B hw0 hwB

/-- Combining clipping with angular Parseval: for a coefficient probability
vector bounded by `B`, the clipped logarithmic angular statistic is
`M√B`-Lipschitz in Euclidean coordinates (in squared form). -/
theorem clippedLog_weightedVectorPolynomial_lipschitz
    {N : ℕ} (w x y : Fin N → ℝ) (B : ℝ) (M : NNReal)
    (hM : 1 ≤ M) (hw0 : ∀ j, 0 ≤ w j) (hwB : ∀ j, w j ≤ B) :
    |angularStatistic (clippedLog M) (weightedVectorPolynomial w x) -
      angularStatistic (clippedLog M) (weightedVectorPolynomial w y)| ≤
      (M : ℝ) * √(B * ∑ j : Fin N, (x j - y j) ^ 2) := by
  calc
    |angularStatistic (clippedLog M) (weightedVectorPolynomial w x) -
      angularStatistic (clippedLog M) (weightedVectorPolynomial w y)| ≤
      (M : ℝ) * √(∑ i ∈
        (weightedVectorPolynomial w x - weightedVectorPolynomial w y).support,
          ‖(weightedVectorPolynomial w x - weightedVectorPolynomial w y).coeff i‖ ^ 2) :=
      abs_angularStatistic_sub_le (clippedLog_lipschitz M hM) _ _
    _ ≤ (M : ℝ) * √(B * ∑ j : Fin N, (x j - y j) ^ 2) := by
      gcongr
      exact weightedVectorPolynomial_coeff_distance_le w x y B hw0 hwB

end Erdos522

end AmalgamatedModule28


/-! ===== amalgamated from Research.LittlewoodFourierIdentification ===== -/

section AmalgamatedModule29


open scoped BigOperators

namespace Erdos522

/-- Real version of the Boolean Rademacher sign. -/
def realRademacherSign (b : Bool) : ℝ := if b then 1 else -1

lemma coe_realRademacherSign (b : Bool) :
    ((realRademacherSign b : ℝ) : ℂ) = rademacherSign b := by
  cases b <;> simp [realRademacherSign, rademacherSign]

lemma sqrt_radialWeight (n : ℕ) (s : ℝ) (k : ℕ) :
    √(radialWeight n s k) =
      Real.exp (s * ((k : ℝ) / n)) / √(radialVariance n s) := by
  unfold radialWeight
  rw [Real.sqrt_div (Real.exp_nonneg _)]
  congr 1
  rw [show 2 * s * ((k : ℝ) / n) =
      s * ((k : ℝ) / n) + s * ((k : ℝ) / n) by ring,
    Real.exp_add, Real.sqrt_mul_self (Real.exp_nonneg _)]

lemma exp_shift_pow (n k : ℕ) (s : ℝ) :
    Real.exp (s / n) ^ k = Real.exp (s * ((k : ℝ) / n)) := by
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Algebraic expansion of the normalized radial Littlewood polynomial. -/
theorem normalized_littlewood_eq_monomial_sum {Ω : Type*}
    (ξ : ℕ → Ω → Bool) (n : ℕ) (s : ℝ) (ω : Ω) :
    normalizedRadialPolynomial (littlewoodPolynomial ξ n ω) n s =
      ∑ k ∈ Finset.range (n + 1), Polynomial.monomial k
        ((((√(radialVariance n s) : ℝ) : ℂ))⁻¹ *
          rademacherSign (ξ k ω) *
          (((Real.exp (s / n) : ℝ) : ℂ)) ^ k) := by
  classical
  unfold normalizedRadialPolynomial littlewoodPolynomial
  simp [mul_pow, Polynomial.C_mul_X_pow_eq_monomial]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← Polynomial.C_mul_X_pow_eq_monomial]
  rw [← map_pow]
  rw [← mul_assoc, ← Polynomial.C_mul, ← mul_assoc, ← Polynomial.C_mul]

/-- The finite-vector polynomial used in F-020 is exactly the normalized
radial Littlewood polynomial, with squared weights `radialWeight`. -/
theorem weightedVectorPolynomial_radial_signs_eq {Ω : Type*}
    (ξ : ℕ → Ω → Bool) (n : ℕ) (s : ℝ) (ω : Ω) :
    weightedVectorPolynomial
      (fun k : Fin (n + 1) => radialWeight n s k)
      (fun k : Fin (n + 1) => realRademacherSign (ξ k ω)) =
    normalizedRadialPolynomial (littlewoodPolynomial ξ n ω) n s := by
  classical
  rw [normalized_littlewood_eq_monomial_sum]
  unfold weightedVectorPolynomial
  change (∑ k : Fin (n + 1),
      (fun j : ℕ => Polynomial.monomial j
        (((√(radialWeight n s j) * realRademacherSign (ξ j ω) : ℝ) : ℂ))) k) = _
  rw [Fin.sum_univ_eq_sum_range
    (fun j : ℕ => Polynomial.monomial j
      (((√(radialWeight n s j) * realRademacherSign (ξ j ω) : ℝ) : ℂ))) (n + 1)]
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  rw [sqrt_radialWeight, div_eq_mul_inv, ← exp_shift_pow]
  push_cast
  rw [coe_realRademacherSign]
  ring

end Erdos522

end AmalgamatedModule29


/-! ===== amalgamated from Research.HammingEuclidean ===== -/

section AmalgamatedModule30


open scoped BigOperators

namespace Erdos522

/-- Encoding Boolean bits as `±1` multiplies squared Hamming distance by four. -/
theorem sum_sq_realRademacherSign_sub_eq_hamming
    {N : ℕ} (x y : Fin N → Bool) :
    ∑ k : Fin N,
        (realRademacherSign (x k) - realRademacherSign (y k)) ^ 2 =
      4 * hammingDist x y := by
  classical
  unfold hammingDist
  calc
    ∑ k : Fin N,
        (realRademacherSign (x k) - realRademacherSign (y k)) ^ 2 =
      ∑ k : Fin N, if x k ≠ y k then 4 else 0 := by
        apply Finset.sum_congr rfl
        intro k hk
        cases hx : x k <;> cases hy : y k <;>
          simp [realRademacherSign, hx, hy] <;> norm_num
    _ = ∑ k ∈ Finset.univ.filter (fun i => x i ≠ y i), 4 := by
      rw [Finset.sum_filter]
    _ = 4 * (Finset.univ.filter fun i => x i ≠ y i).card := by
      simp
      ring

end Erdos522

end AmalgamatedModule30


/-! ===== amalgamated from Research.CubeCharacteristic ===== -/

section AmalgamatedModule31


open scoped BigOperators ComplexConjugate

namespace Erdos522

/-- Uniform average of a complex-valued function on a finite Boolean cube. -/
noncomputable def cubeComplexAverage {N : ℕ}
    (F : (Fin N → Bool) → ℂ) : ℂ :=
  (∑ x : Fin N → Bool, F x) / (2 : ℂ) ^ N

@[simp] theorem cubeComplexAverage_const {N : ℕ} (c : ℂ) :
    cubeComplexAverage (fun _ : Fin N → Bool => c) = c := by
  unfold cubeComplexAverage
  simp [Fintype.card_bool, Fintype.card_fin]

/-- The characteristic function of a weighted finite Rademacher sum factorizes
as a product of cosines. -/
theorem cubeComplexAverage_cexp_rademacher_sum
    {N : ℕ} (a : Fin N → ℝ) :
    cubeComplexAverage (fun x =>
      Complex.exp (Complex.I * (∑ k : Fin N, realRademacherSign (x k) * a k))) =
      ∏ k : Fin N, (Real.cos (a k) : ℂ) := by
  classical
  have hexp (x : Fin N → Bool) :
      Complex.exp (Complex.I * (∑ k : Fin N, realRademacherSign (x k) * a k)) =
        ∏ k : Fin N,
          Complex.exp (Complex.I * (realRademacherSign (x k) * a k)) := by
    push_cast
    rw [Finset.mul_sum]
    exact Complex.exp_sum Finset.univ _
  have hbool (t : ℝ) :
      ∑ b : Bool, Complex.exp (Complex.I * (realRademacherSign b * t)) =
        2 * (Real.cos t : ℂ) := by
    rw [Fintype.sum_bool]
    simp [realRademacherSign]
    rw [show Complex.I * (t : ℂ) = (t : ℂ) * Complex.I by ring,
      show -((t : ℂ) * Complex.I) = ((-t : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_mul_I, Complex.exp_mul_I]
    push_cast
    rw [Complex.cos_neg, Complex.sin_neg]
    ring
  unfold cubeComplexAverage
  simp_rw [hexp]
  have hfactor :
      (∑ x : Fin N → Bool,
        ∏ k : Fin N, Complex.exp
          (Complex.I * (realRademacherSign (x k) * a k))) =
      ∏ k : Fin N, ∑ b : Bool,
        Complex.exp (Complex.I * (realRademacherSign b * a k)) := by
    exact (Fintype.prod_sum (fun k : Fin N => fun b : Bool =>
      Complex.exp (Complex.I * (realRademacherSign b * a k)))).symm
  rw [hfactor]
  simp_rw [hbool]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  field_simp

/-- Coordinate-free scalar projection form of the preceding factorization. -/
theorem cubeComplexAverage_cexp_re_conj_mul_weighted_sum
    {N : ℕ} (c : Fin N → ℂ) (t : ℂ) :
    cubeComplexAverage (fun x =>
      Complex.exp (Complex.I *
        (star t * (∑ k : Fin N, (realRademacherSign (x k) : ℂ) * c k)).re)) =
      ∏ k : Fin N, (Real.cos ((star t * c k).re) : ℂ) := by
  convert cubeComplexAverage_cexp_rademacher_sum
    (fun k : Fin N => (star t * c k).re) using 1
  · congr 1
    funext x
    congr 2
    have hre :
        (star t * (∑ k : Fin N,
          (realRademacherSign (x k) : ℂ) * c k)).re =
        ∑ k : Fin N, realRademacherSign (x k) * (star t * c k).re := by
      rw [Finset.mul_sum]
      simp_rw [← mul_assoc]
      change Complex.reCLM (∑ k : Fin N,
        (star t * (realRademacherSign (x k) : ℂ)) * c k) = _
      rw [map_sum Complex.reCLM]
      apply Finset.sum_congr rfl
      intro k hk
      simp
      ring
    exact_mod_cast hre

end Erdos522

end AmalgamatedModule31


/-! ===== amalgamated from Research.CosineProductGaussian ===== -/

section AmalgamatedModule32


open scoped BigOperators
open Set Filter

namespace Erdos522

private lemma cos_taylor3_uIcc (x : ℝ) (hx : 0 ≠ x) :
    taylorWithinEval Real.cos 3 (uIcc 0 x) 0 x = 1 - x ^ 2 / 2 := by
  have hu : UniqueDiffOn ℝ (uIcc 0 x) := by
    rcases lt_or_gt_of_ne hx with h | h
    · rw [uIcc_of_lt h]
      exact uniqueDiffOn_Icc h
    · rw [uIcc_comm, uIcc_of_lt h]
      exact uniqueDiffOn_Icc h
  rw [taylor_within_apply]
  have hiter (k : ℕ) : iteratedDerivWithin k Real.cos (uIcc 0 x) 0 =
      iteratedDeriv k Real.cos 0 :=
    iteratedDerivWithin_eq_iteratedDeriv hu Real.contDiff_cos.contDiffAt left_mem_uIcc
  simp_rw [hiter]
  norm_num [Finset.sum_range_succ, Real.iteratedDeriv_even_cos,
    Real.iteratedDeriv_odd_cos]
  ring

/-- A global fourth-order cosine remainder bound. -/
theorem abs_cos_sub_one_add_sq_div_two_le (x : ℝ) :
    |Real.cos x - (1 - x ^ 2 / 2)| ≤ |x| ^ 4 / 24 := by
  by_cases hx : (0 : ℝ) = x
  · subst x
    norm_num
  obtain ⟨y, hy, hrem⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv (n := 3) hx
      Real.contDiff_cos.contDiffOn
  rw [cos_taylor3_uIcc x hx] at hrem
  rw [hrem, abs_div, abs_mul, abs_pow]
  norm_num
  apply div_le_div_of_nonneg_right
  · simpa using mul_le_mul_of_nonneg_right (Real.abs_cos_le_one y)
      (pow_nonneg (abs_nonneg x) 4)
  · norm_num

/-- A fourth-order comparison of the matching Gaussian factor and quadratic
factor, valid in the small-argument regime. -/
theorem abs_exp_neg_sq_div_two_sub_one_add_sq_div_two_le
    {x : ℝ} (hx : |x| ≤ 1) :
    |Real.exp (-x ^ 2 / 2) - (1 - x ^ 2 / 2)| ≤ |x| ^ 4 / 4 := by
  have hy : |-x ^ 2 / 2| ≤ 1 := by
    rw [abs_div, abs_neg, abs_pow]
    nlinarith [sq_nonneg (|x|), mul_self_le_mul_self (abs_nonneg x) hx]
  have h := Real.abs_exp_sub_one_sub_id_le hy
  convert h using 1 <;> ring_nf
  have habspow : |x| ^ 4 = x ^ 4 := by
    rw [← abs_pow, abs_of_nonneg (by positivity : 0 ≤ x ^ 4)]
  rw [habspow]

/-- Telescoping stability of finite products whose factors lie in the closed
unit disk. -/
theorem abs_finset_prod_sub_prod_le_sum_abs_sub
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i ∈ s, |a i| ≤ 1) (hb : ∀ i ∈ s, |b i| ≤ 1) :
    |∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ ∑ i ∈ s, |a i - b i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi,
        Finset.sum_insert hi]
      calc
        |a i * ∏ j ∈ s, a j - b i * ∏ j ∈ s, b j| =
            |a i * (∏ j ∈ s, a j - ∏ j ∈ s, b j) +
              (a i - b i) * ∏ j ∈ s, b j| := by ring_nf
        _ ≤ |a i| * |∏ j ∈ s, a j - ∏ j ∈ s, b j| +
              |a i - b i| * |∏ j ∈ s, b j| := by
            simpa [abs_mul] using abs_add_le
              (a i * (∏ j ∈ s, a j - ∏ j ∈ s, b j))
              ((a i - b i) * ∏ j ∈ s, b j)
        _ ≤ 1 * (∑ j ∈ s, |a j - b j|) + |a i - b i| * 1 := by
            gcongr
            · exact ha i (Finset.mem_insert_self i s)
            · exact ih (fun j hj => ha j (Finset.mem_insert_of_mem hj))
                (fun j hj => hb j (Finset.mem_insert_of_mem hj))
            · calc
                |∏ j ∈ s, b j| = ‖∏ j ∈ s, b j‖ := by rfl
                _ ≤ ∏ j ∈ s, ‖b j‖ := Finset.norm_prod_le s b
                _ = ∏ j ∈ s, |b j| := by simp [Real.norm_eq_abs]
                _ ≤ 1 := Finset.prod_le_one (fun j hj => abs_nonneg (b j))
                  (fun j hj => hb j (Finset.mem_insert_of_mem hj))
        _ = |a i - b i| + ∑ j ∈ s, |a j - b j| := by ring

/-- Explicit finite-array Gaussian approximation for a product of cosines. -/
theorem abs_prod_cos_sub_exp_neg_sum_sq_div_two_le
    {ι : Type*} [Fintype ι] (u : ι → ℝ)
    (hu : ∀ i, |u i| ≤ 1) :
    |(∏ i, Real.cos (u i)) - Real.exp (-(∑ i, (u i) ^ 2) / 2)| ≤
      (7 / 24 : ℝ) * ∑ i, |u i| ^ 4 := by
  let q : ι → ℝ := fun i => 1 - (u i) ^ 2 / 2
  let e : ι → ℝ := fun i => Real.exp (-(u i) ^ 2 / 2)
  have hq0 (i : ι) : 0 ≤ q i := by
    dsimp [q]
    have hi : (u i) ^ 2 ≤ (1 : ℝ) ^ 2 := by
      apply sq_le_sq.mpr
      simpa using hu i
    nlinarith [sq_nonneg (u i)]
  have hq1 (i : ι) : |q i| ≤ 1 := by
    rw [abs_of_nonneg (hq0 i)]
    dsimp [q]
    nlinarith [sq_nonneg (u i)]
  have he1 (i : ι) : |e i| ≤ 1 := by
    rw [abs_of_pos (Real.exp_pos _)]
    change Real.exp (-(u i) ^ 2 / 2) ≤ 1
    apply Real.exp_le_one_iff.mpr
    nlinarith [sq_nonneg (u i)]
  classical
  have hcos := abs_finset_prod_sub_prod_le_sum_abs_sub Finset.univ
    (fun i => Real.cos (u i)) q
    (fun i hi => Real.abs_cos_le_one _) (fun i hi => hq1 i)
  have hexp := abs_finset_prod_sub_prod_le_sum_abs_sub Finset.univ e q
    (fun i hi => he1 i) (fun i hi => hq1 i)
  have heprod : (∏ i, e i) = Real.exp (-(∑ i, (u i) ^ 2) / 2) := by
    dsimp [e]
    rw [← Real.exp_sum]
    congr 1
    simp_rw [neg_div]
    rw [Finset.sum_div, Finset.sum_neg_distrib]
  rw [← heprod]
  calc
    |(∏ i, Real.cos (u i)) - ∏ i, e i| ≤
        |(∏ i, Real.cos (u i)) - ∏ i, q i| +
          |(∏ i, q i) - ∏ i, e i| := by
      exact abs_sub_le _ _ _
    _ ≤ (∑ i, |Real.cos (u i) - q i|) +
          ∑ i, |e i - q i| := add_le_add hcos (by simpa [abs_sub_comm] using hexp)
    _ ≤ (∑ i, |u i| ^ 4 / 24) + ∑ i, |u i| ^ 4 / 4 := by
      gcongr with i
      · exact abs_cos_sub_one_add_sq_div_two_le (u i)
      · exact abs_exp_neg_sq_div_two_sub_one_add_sq_div_two_le (hu i)
    _ = (7 / 24 : ℝ) * ∑ i, |u i| ^ 4 := by
      rw [← Finset.sum_div, ← Finset.sum_div]
      ring

/-- If every coordinate is at most `d`, the approximation error is bounded by
`(7/24)d²` times the total quadratic mass. -/
theorem abs_prod_cos_sub_exp_neg_sum_sq_div_two_le_max
    {ι : Type*} [Fintype ι] (u : ι → ℝ) {d : ℝ}
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (hu : ∀ i, |u i| ≤ d) :
    |(∏ i, Real.cos (u i)) - Real.exp (-(∑ i, (u i) ^ 2) / 2)| ≤
      (7 / 24 : ℝ) * d ^ 2 * ∑ i, (u i) ^ 2 := by
  refine (abs_prod_cos_sub_exp_neg_sum_sq_div_two_le u
    (fun i => (hu i).trans hd1)).trans ?_
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hsquare : |u i| ^ 2 ≤ d ^ 2 :=
      (sq_le_sq₀ (abs_nonneg (u i)) hd0).mpr (hu i)
    calc
      |u i| ^ 4 = |u i| ^ 2 * |u i| ^ 2 := by ring
      _ = |u i| ^ 2 * (u i) ^ 2 := by rw [sq_abs]
      _ ≤ d ^ 2 * (u i) ^ 2 :=
        mul_le_mul_of_nonneg_right hsquare (sq_nonneg (u i))
  · norm_num

end Erdos522

end AmalgamatedModule32


/-! ===== amalgamated from Research.WeightedCharacteristicApproximation ===== -/

section AmalgamatedModule33


open scoped BigOperators ComplexConjugate

namespace Erdos522

/-- Quantitative Gaussian approximation for every scalar projection of a
finite complex Rademacher sum. -/
theorem norm_cubeCharacteristic_sub_gaussianProjection_le
    {N : ℕ} (c : Fin N → ℂ) (t : ℂ) {d : ℝ}
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (hproj : ∀ k, |(star t * c k).re| ≤ d) :
    ‖cubeComplexAverage (fun x =>
        Complex.exp (Complex.I *
          (star t * (∑ k : Fin N,
            (realRademacherSign (x k) : ℂ) * c k)).re)) -
      (Real.exp (-(∑ k : Fin N, ((star t * c k).re) ^ 2) / 2) : ℂ)‖ ≤
      (7 / 24 : ℝ) * d ^ 2 *
        ∑ k : Fin N, ((star t * c k).re) ^ 2 := by
  rw [cubeComplexAverage_cexp_re_conj_mul_weighted_sum c t]
  rw [show (∏ k : Fin N, (Real.cos ((star t * c k).re) : ℂ)) =
      ((∏ k : Fin N, Real.cos ((star t * c k).re) : ℝ) : ℂ) by push_cast; rfl]
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact abs_prod_cos_sub_exp_neg_sum_sq_div_two_le_max
    (fun k : Fin N => (star t * c k).re) hd0 hd1 hproj

/-- A convenient projection bound from coefficient norms. -/
theorem abs_re_conj_mul_le_norm_mul_norm (t z : ℂ) :
    |(star t * z).re| ≤ ‖t‖ * ‖z‖ := by
  calc
    |(star t * z).re| ≤ ‖star t * z‖ := Complex.abs_re_le_norm _
    _ = ‖t‖ * ‖z‖ := by rw [norm_mul, norm_star]

/-- Fourth-order characteristic error using only a uniform coefficient norm
bound and the projection's total quadratic mass. -/
theorem norm_cubeCharacteristic_sub_gaussianProjection_le_of_coeff
    {N : ℕ} (c : Fin N → ℂ) (t : ℂ) {b : ℝ}
    (hb0 : 0 ≤ b) (htb : ‖t‖ * b ≤ 1)
    (hc : ∀ k, ‖c k‖ ≤ b) :
    ‖cubeComplexAverage (fun x =>
        Complex.exp (Complex.I *
          (star t * (∑ k : Fin N,
            (realRademacherSign (x k) : ℂ) * c k)).re)) -
      (Real.exp (-(∑ k : Fin N, ((star t * c k).re) ^ 2) / 2) : ℂ)‖ ≤
      (7 / 24 : ℝ) * (‖t‖ * b) ^ 2 *
        ∑ k : Fin N, ((star t * c k).re) ^ 2 := by
  apply norm_cubeCharacteristic_sub_gaussianProjection_le c t
    (mul_nonneg (norm_nonneg t) hb0) htb
  intro k
  exact (abs_re_conj_mul_le_norm_mul_norm t (c k)).trans
    (mul_le_mul_of_nonneg_left (hc k) (norm_nonneg t))

end Erdos522

end AmalgamatedModule33


/-! ===== amalgamated from Research.ProjectionCovariance ===== -/

section AmalgamatedModule34


open scoped BigOperators ComplexConjugate

namespace Erdos522

/-- The scalar-projection variance of normalized complex coefficients is the
quadratic form determined by their pseudocorrelation. -/
theorem sum_sq_re_conj_mul_eq_covarianceQuadratic
    {N : ℕ} (c : Fin N → ℂ)
    (hnorm : ∑ k : Fin N, ‖c k‖ ^ 2 = 1) (t : ℂ) :
    ∑ k : Fin N, ((star t * c k).re) ^ 2 =
      covarianceQuadratic (∑ k : Fin N, (c k) ^ 2) t.re t.im := by
  classical
  let T : ℝ := t.re ^ 2 + t.im ^ 2
  have hlocal (k : Fin N) :
      2 * ((star t * c k).re) ^ 2 - ‖c k‖ ^ 2 * T =
        (star ((c k) ^ 2) * t ^ 2).re := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    dsimp [T]
    simp [Complex.mul_re, pow_two]
    ring
  have hsum :
      (∑ k : Fin N, (2 * ((star t * c k).re) ^ 2 - ‖c k‖ ^ 2 * T)) =
        ∑ k : Fin N, (star ((c k) ^ 2) * t ^ 2).re := by
    apply Finset.sum_congr rfl
    intro k hk
    exact hlocal k
  simp only [Finset.sum_sub_distrib] at hsum
  rw [← Finset.sum_mul, hnorm, one_mul] at hsum
  rw [← Finset.mul_sum] at hsum
  have hrhs :
      ∑ k : Fin N, (star ((c k) ^ 2) * t ^ 2).re =
        (star (∑ k : Fin N, (c k) ^ 2) * t ^ 2).re := by
    have hre :
        Complex.reCLM (∑ k : Fin N, star ((c k) ^ 2) * t ^ 2) =
          ∑ k : Fin N, Complex.reCLM (star ((c k) ^ 2) * t ^ 2) :=
      map_sum Complex.reCLM
        (fun k : Fin N => star ((c k) ^ 2) * t ^ 2) Finset.univ
    have hstar :
        ∑ k : Fin N, star ((c k) ^ 2) =
          star (∑ k : Fin N, (c k) ^ 2) := by
      exact (map_sum (starRingEnd ℂ) (fun k : Fin N => (c k) ^ 2)
        Finset.univ).symm
    have hcomplex :
        (∑ k : Fin N, star ((c k) ^ 2) * t ^ 2) =
          star (∑ k : Fin N, (c k) ^ 2) * t ^ 2 := by
      rw [← Finset.sum_mul, hstar]
    calc
      ∑ k : Fin N, (star ((c k) ^ 2) * t ^ 2).re =
          ∑ k : Fin N, Complex.reCLM (star ((c k) ^ 2) * t ^ 2) := rfl
      _ = Complex.reCLM (∑ k : Fin N, star ((c k) ^ 2) * t ^ 2) := hre.symm
      _ = Complex.reCLM (star (∑ k : Fin N, (c k) ^ 2) * t ^ 2) :=
        congrArg Complex.reCLM hcomplex
      _ = (star (∑ k : Fin N, (c k) ^ 2) * t ^ 2).re := rfl
  rw [hrhs] at hsum
  have hcov := covarianceQuadratic_perturbation_identity
    (∑ k : Fin N, (c k) ^ 2) t.re t.im
  rw [Complex.re_add_im] at hcov
  dsimp [T] at hsum ⊢
  linarith

/-- Every projection quadratic mass is at most `‖t‖²` for normalized
coefficients. -/
theorem sum_sq_re_conj_mul_le_norm_sq
    {N : ℕ} (c : Fin N → ℂ)
    (hnorm : ∑ k : Fin N, ‖c k‖ ^ 2 = 1) (t : ℂ) :
    ∑ k : Fin N, ((star t * c k).re) ^ 2 ≤ ‖t‖ ^ 2 := by
  calc
    ∑ k : Fin N, ((star t * c k).re) ^ 2 ≤
        ∑ k : Fin N, (‖t‖ * ‖c k‖) ^ 2 := by
      apply Finset.sum_le_sum
      intro k hk
      apply sq_le_sq.mpr
      simpa [abs_of_nonneg (mul_nonneg (norm_nonneg t) (norm_nonneg (c k)))] using
        abs_re_conj_mul_le_norm_mul_norm t (c k)
    _ = ‖t‖ ^ 2 := by
      simp_rw [mul_pow]
      rw [← Finset.mul_sum, hnorm, mul_one]

end Erdos522

end AmalgamatedModule34


/-! ===== amalgamated from Research.RadialCoefficientGeometry ===== -/

section AmalgamatedModule35


open scoped BigOperators ComplexConjugate

namespace Erdos522

/-- Polynomial placing a finite coefficient vector on the even frequencies. -/
noncomputable def evenFrequencyPolynomial {N : ℕ} (a : Fin N → ℂ) : Polynomial ℂ :=
  ∑ k : Fin N, Polynomial.monomial (2 * (k : ℕ)) (a k)

lemma coeff_evenFrequencyPolynomial {N : ℕ} (a : Fin N → ℂ) (k : Fin N) :
    (evenFrequencyPolynomial a).coeff (2 * (k : ℕ)) = a k := by
  classical
  unfold evenFrequencyPolynomial
  have hcoeff :
      (∑ j : Fin N, Polynomial.monomial (2 * (j : ℕ)) (a j)).coeff
          (2 * (k : ℕ)) =
        ∑ j : Fin N, if 2 * (j : ℕ) = 2 * (k : ℕ) then a j else 0 := by
    simp [Polynomial.coeff_monomial]
  rw [hcoeff]
  calc
    (∑ j : Fin N, if 2 * (j : ℕ) = 2 * (k : ℕ) then a j else 0) =
        (if 2 * (k : ℕ) = 2 * (k : ℕ) then a k else 0) := by
      apply Fintype.sum_eq_single k
      intro j hjk
      split_ifs with h
      · have : (j : ℕ) = (k : ℕ) :=
          Nat.eq_of_mul_eq_mul_left (by omega) h
        exact (hjk (Fin.ext this)).elim
      · rfl
    _ = a k := by simp

lemma support_evenFrequencyPolynomial_subset {N : ℕ} (a : Fin N → ℂ) :
    (evenFrequencyPolynomial a).support ⊆
      Finset.univ.image (fun k : Fin N => 2 * (k : ℕ)) := by
  classical
  intro j hj
  rw [Polynomial.mem_support_iff] at hj
  by_contra hnot
  apply hj
  unfold evenFrequencyPolynomial
  have hcoeff :
      (∑ k : Fin N, Polynomial.monomial (2 * (k : ℕ)) (a k)).coeff j =
        ∑ k : Fin N, if 2 * (k : ℕ) = j then a k else 0 := by
    simp [Polynomial.coeff_monomial]
  rw [hcoeff]
  apply Finset.sum_eq_zero
  intro k hk
  split_ifs with h
  · exfalso
    apply hnot
    rw [Finset.mem_image]
    exact ⟨k, Finset.mem_univ k, h⟩
  · rfl

/-- Parseval coefficient mass of the even-frequency embedding. -/
theorem sum_sq_norm_coeff_evenFrequencyPolynomial {N : ℕ} (a : Fin N → ℂ) :
    ∑ j ∈ (evenFrequencyPolynomial a).support,
        ‖(evenFrequencyPolynomial a).coeff j‖ ^ 2 =
      ∑ k : Fin N, ‖a k‖ ^ 2 := by
  classical
  rw [Finset.sum_subset (support_evenFrequencyPolynomial_subset a)]
  · rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro k hk
      rw [coeff_evenFrequencyPolynomial]
    · intro i hi j hj h
      exact Fin.ext (Nat.eq_of_mul_eq_mul_left (by omega) h)
  · intro j hjS hjSupp
    have hz : (evenFrequencyPolynomial a).coeff j = 0 := by
      by_contra hn
      exact hjSupp (Polynomial.mem_support_iff.mpr hn)
    simp [hz]

lemma eval_evenFrequencyPolynomial {N : ℕ} (a : Fin N → ℂ) (z : ℂ) :
    (evenFrequencyPolynomial a).eval z =
      ∑ k : Fin N, a k * z ^ (2 * (k : ℕ)) := by
  classical
  unfold evenFrequencyPolynomial
  change Polynomial.evalRingHom z
    (∑ k : Fin N, Polynomial.monomial (2 * (k : ℕ)) (a k)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  change Polynomial.eval z (Polynomial.monomial (2 * (k : ℕ)) (a k)) = _
  rw [Polynomial.eval_monomial]

/-- Normalized Fourier coefficient vector for the radial Littlewood array. -/
noncomputable def radialFourierCoefficient
    (n : ℕ) (s θ : ℝ) (k : Fin (n + 1)) : ℂ :=
  (Real.sqrt (radialWeight n s k) : ℂ) *
    (circleMap 0 1 θ) ^ (k : ℕ)

lemma norm_circleMap_zero_one (θ : ℝ) : ‖circleMap 0 1 θ‖ = 1 := by
  rw [circleMap_zero]
  simp [Complex.norm_exp]

lemma norm_sq_radialFourierCoefficient
    (n : ℕ) (s θ : ℝ) (k : Fin (n + 1)) :
    ‖radialFourierCoefficient n s θ k‖ ^ 2 = radialWeight n s k := by
  unfold radialFourierCoefficient
  rw [norm_mul, norm_pow, norm_circleMap_zero_one, one_pow, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (radialWeight_nonneg n s k)]

lemma sum_norm_sq_radialFourierCoefficient (n : ℕ) (s θ : ℝ) :
    ∑ k : Fin (n + 1), ‖radialFourierCoefficient n s θ k‖ ^ 2 = 1 := by
  simp_rw [norm_sq_radialFourierCoefficient]
  rw [Fin.sum_univ_eq_sum_range]
  exact sum_radialWeight n s

/-- Direct pseudocorrelation of the normalized radial Fourier vector. -/
noncomputable def directRadialPseudocorrelation (n : ℕ) (s θ : ℝ) : ℂ :=
  ∑ k : Fin (n + 1), (radialFourierCoefficient n s θ k) ^ 2

lemma directRadialPseudocorrelation_eq_eval (n : ℕ) (s θ : ℝ) :
    directRadialPseudocorrelation n s θ =
      (evenFrequencyPolynomial
        (fun k : Fin (n + 1) => (radialWeight n s k : ℂ))).eval
          (circleMap 0 1 θ) := by
  unfold directRadialPseudocorrelation
  rw [eval_evenFrequencyPolynomial]
  apply Finset.sum_congr rfl
  intro k hk
  unfold radialFourierCoefficient
  push_cast
  rw [mul_pow]
  rw [show ((Real.sqrt (radialWeight n s k) : ℂ) ^ 2) =
      (radialWeight n s k : ℂ) by
    exact_mod_cast Real.sq_sqrt (radialWeight_nonneg n s k)]
  ring

/-- Parameterized angular `L¹` pseudocorrelation bound, in the exact form used
for the annealed characteristic function. -/
theorem circleParameterAverage_norm_directRadialPseudocorrelation_le
    (n : ℕ) (s : ℝ) :
    Real.circleAverage
        (fun z => ‖(evenFrequencyPolynomial
          (fun k : Fin (n + 1) => (radialWeight n s k : ℂ))).eval z‖) 0 1 ≤
      Real.sqrt (∑ k : Fin (n + 1), (radialWeight n s k) ^ 2) := by
  let p := evenFrequencyPolynomial
    (fun k : Fin (n + 1) => (radialWeight n s k : ℂ))
  have h := circleAverage_norm_eval_le_sqrt_sum_sq p
  rw [sum_sq_norm_coeff_evenFrequencyPolynomial] at h
  simpa [p, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (radialWeight_nonneg n s _)] using h

/-- The squared radial weights inherit the explicit flatness bound. -/
theorem sum_sq_radialWeight_le (n : ℕ) (hn : 0 < n) (s : ℝ) :
    ∑ k : Fin (n + 1), (radialWeight n s k) ^ 2 ≤
      Real.exp (4 * |s|) / (n + 1 : ℝ) := by
  let B := Real.exp (4 * |s|) / (n + 1 : ℝ)
  calc
    ∑ k : Fin (n + 1), (radialWeight n s k) ^ 2 ≤
        ∑ k : Fin (n + 1), B * radialWeight n s k := by
      apply Finset.sum_le_sum
      intro k hk
      rw [pow_two]
      exact mul_le_mul_of_nonneg_right
        (radialWeight_le n hn s (Finset.mem_range.mpr k.isLt))
        (radialWeight_nonneg n s k)
    _ = B * ∑ k : Fin (n + 1), radialWeight n s k := by
      rw [Finset.mul_sum]
    _ = B := by
      rw [Fin.sum_univ_eq_sum_range, sum_radialWeight, mul_one]

/-- Consequently the angular mean pseudocorrelation is explicitly
`O_s((n+1)⁻¹ᐟ²)` without removing bad angular arcs. -/
theorem circleParameterAverage_norm_pseudocorrelation_le_flat
    (n : ℕ) (hn : 0 < n) (s : ℝ) :
    Real.circleAverage
        (fun z => ‖(evenFrequencyPolynomial
          (fun k : Fin (n + 1) => (radialWeight n s k : ℂ))).eval z‖) 0 1 ≤
      Real.sqrt (Real.exp (4 * |s|) / (n + 1 : ℝ)) := by
  exact (circleParameterAverage_norm_directRadialPseudocorrelation_le n s).trans
    (Real.sqrt_le_sqrt (sum_sq_radialWeight_le n hn s))

end Erdos522

end AmalgamatedModule35


/-! ===== amalgamated from Research.CircleNormBound ===== -/

section AmalgamatedModule36


open MeasureTheory

namespace Erdos522

/-- Pull a complex-valued planar test back to the unit-circle parameter. -/
noncomputable def circleParameterFunctionComplex (f : ℂ → ℂ) (θ : ℝ) : ℂ :=
  f (circleMap 0 1 θ)

lemma circleAverage_eq_integral_circleParameterMeasure_complex (f : ℂ → ℂ) :
    Real.circleAverage f 0 1 =
      ∫ θ, circleParameterFunctionComplex f θ ∂circleParameterMeasure := by
  rw [Real.circleAverage_eq_intervalAverage]
  rfl

/-- The norm of a complex circle average is at most the circle average of the
pointwise norm. -/
theorem norm_circleAverage_le_circleAverage_norm (f : ℂ → ℂ) :
    ‖Real.circleAverage f 0 1‖ ≤
      Real.circleAverage (fun z => ‖f z‖) 0 1 := by
  rw [circleAverage_eq_integral_circleParameterMeasure_complex,
    circleAverage_eq_integral_circleParameterMeasure]
  exact norm_integral_le_integral_norm _

end Erdos522

end AmalgamatedModule36


/-! ===== amalgamated from Research.AnnealedCharacteristicBound ===== -/

section AmalgamatedModule37


open scoped BigOperators ComplexConjugate
open Set

namespace Erdos522

/-- A normalized radial coefficient evaluated at a point of the unit circle. -/
noncomputable def radialCircleCoefficient
    (n : ℕ) (s : ℝ) (z : ℂ) (k : Fin (n + 1)) : ℂ :=
  (Real.sqrt (radialWeight n s k) : ℂ) * z ^ (k : ℕ)

/-- The finite-cube characteristic function at a fixed angular point. -/
noncomputable def radialCubeCharacteristicAt
    (n : ℕ) (s : ℝ) (t z : ℂ) : ℂ :=
  cubeComplexAverage (fun x =>
    Complex.exp (Complex.I *
      (star t * (∑ k : Fin (n + 1),
        (realRademacherSign (x k) : ℂ) *
          radialCircleCoefficient n s z k)).re))

/-- Characteristic function of the circular complex Gaussian with
`E ‖G‖² = 1`. -/
noncomputable def circularGaussianCharacteristic (t : ℂ) : ℂ :=
  (Real.exp (-‖t‖ ^ 2 / 4) : ℂ)

/-- The real exponential is one-Lipschitz on the negative half-line. -/
theorem abs_exp_sub_exp_le_abs_of_nonpos {x y : ℝ} (hx : x ≤ 0) (hy : y ≤ 0) :
    |Real.exp x - Real.exp y| ≤ |x - y| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (𝕜 := ℝ) (f := Real.exp) (s := Iic (0 : ℝ))
    (x := y) (y := x) (C := 1)
    (fun z hz => Real.differentiableAt_exp)
    (fun z hz => by
      rw [Real.deriv_exp, Real.norm_eq_abs, abs_of_pos (Real.exp_pos z)]
      exact Real.exp_le_one_iff.mpr hz)
    (convex_Iic 0) hy hx
  simpa [Real.norm_eq_abs] using h

lemma norm_radialCircleCoefficient_of_mem_sphere
    (n : ℕ) (s : ℝ) {z : ℂ} (hz : z ∈ Metric.sphere 0 1)
    (k : Fin (n + 1)) :
    ‖radialCircleCoefficient n s z k‖ = Real.sqrt (radialWeight n s k) := by
  have hznorm : ‖z‖ = 1 := by simpa [Metric.mem_sphere] using hz
  unfold radialCircleCoefficient
  rw [norm_mul, norm_pow, hznorm, one_pow, mul_one,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]

lemma sum_norm_sq_radialCircleCoefficient_of_mem_sphere
    (n : ℕ) (s : ℝ) {z : ℂ} (hz : z ∈ Metric.sphere 0 1) :
    ∑ k : Fin (n + 1), ‖radialCircleCoefficient n s z k‖ ^ 2 = 1 := by
  simp_rw [norm_radialCircleCoefficient_of_mem_sphere n s hz,
    Real.sq_sqrt (radialWeight_nonneg n s _)]
  rw [Fin.sum_univ_eq_sum_range]
  exact sum_radialWeight n s

lemma sum_sq_radialCircleCoefficient_of_mem_sphere
    (n : ℕ) (s : ℝ) {z : ℂ} (hz : z ∈ Metric.sphere 0 1) :
    ∑ k : Fin (n + 1), (radialCircleCoefficient n s z k) ^ 2 =
      (evenFrequencyPolynomial
        (fun k : Fin (n + 1) => (radialWeight n s k : ℂ))).eval z := by
  rw [eval_evenFrequencyPolynomial]
  apply Finset.sum_congr rfl
  intro k hk
  unfold radialCircleCoefficient
  rw [mul_pow]
  rw [show ((Real.sqrt (radialWeight n s k) : ℂ) ^ 2) =
      (radialWeight n s k : ℂ) by
    exact_mod_cast Real.sq_sqrt (radialWeight_nonneg n s k)]
  ring

lemma norm_radialCircleCoefficient_le_flat
    (n : ℕ) (hn : 0 < n) (s : ℝ) {z : ℂ}
    (hz : z ∈ Metric.sphere 0 1) (k : Fin (n + 1)) :
    ‖radialCircleCoefficient n s z k‖ ≤
      Real.sqrt (Real.exp (4 * |s|) / (n + 1 : ℝ)) := by
  rw [norm_radialCircleCoefficient_of_mem_sphere n s hz]
  exact Real.sqrt_le_sqrt
    (radialWeight_le n hn s (Finset.mem_range.mpr k.isLt))

/-- Pointwise characteristic-function approximation. The first term is the
fourth-order Rademacher-to-matching-Gaussian error; the second is the
pseudocorrelation error. -/
theorem norm_radialCubeCharacteristicAt_sub_circular_le
    (n : ℕ) (hn : 0 < n) (s : ℝ) (t : ℂ)
    {z : ℂ} (hz : z ∈ Metric.sphere 0 1)
    (hsmall : ‖t‖ * Real.sqrt
      (Real.exp (4 * |s|) / (n + 1 : ℝ)) ≤ 1) :
    ‖radialCubeCharacteristicAt n s t z - circularGaussianCharacteristic t‖ ≤
      (7 / 24 : ℝ) *
          (‖t‖ * Real.sqrt
            (Real.exp (4 * |s|) / (n + 1 : ℝ))) ^ 2 * ‖t‖ ^ 2 +
        ‖t‖ ^ 2 / 4 *
          ‖(evenFrequencyPolynomial
            (fun k : Fin (n + 1) => (radialWeight n s k : ℂ))).eval z‖ := by
  let c : Fin (n + 1) → ℂ := radialCircleCoefficient n s z
  let q : ℝ := ∑ k : Fin (n + 1), ((star t * c k).re) ^ 2
  let ρ : ℂ := ∑ k : Fin (n + 1), (c k) ^ 2
  let B : ℝ := Real.exp (4 * |s|) / (n + 1 : ℝ)
  have hB0 : 0 ≤ Real.sqrt B := Real.sqrt_nonneg _
  have hc : ∀ k, ‖c k‖ ≤ Real.sqrt B := by
    intro k
    exact norm_radialCircleCoefficient_le_flat n hn s hz k
  have hnorm : ∑ k : Fin (n + 1), ‖c k‖ ^ 2 = 1 := by
    exact sum_norm_sq_radialCircleCoefficient_of_mem_sphere n s hz
  have hq0 : 0 ≤ q := Finset.sum_nonneg (fun k hk => sq_nonneg _)
  have hqle : q ≤ ‖t‖ ^ 2 :=
    sum_sq_re_conj_mul_le_norm_sq c hnorm t
  have hchar :=
    norm_cubeCharacteristic_sub_gaussianProjection_le_of_coeff
      c t hB0 hsmall hc
  have hchar' :
      ‖radialCubeCharacteristicAt n s t z -
          (Real.exp (-q / 2) : ℂ)‖ ≤
        (7 / 24 : ℝ) * (‖t‖ * Real.sqrt B) ^ 2 * ‖t‖ ^ 2 := by
    apply hchar.trans
    apply mul_le_mul_of_nonneg_left hqle
    positivity
  have hqcov : q = covarianceQuadratic ρ t.re t.im := by
    exact sum_sq_re_conj_mul_eq_covarianceQuadratic c hnorm t
  have hpert := abs_two_covarianceQuadratic_sub_le ρ t.re t.im
  have htnorm : t.re ^ 2 + t.im ^ 2 = ‖t‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  rw [htnorm] at hpert
  have hgaussReal :
      |Real.exp (-q / 2) - Real.exp (-‖t‖ ^ 2 / 4)| ≤
        ‖ρ‖ * ‖t‖ ^ 2 / 4 := by
    have hxnonpos : -q / 2 ≤ 0 := by nlinarith [hq0]
    have hynonpos : -‖t‖ ^ 2 / 4 ≤ 0 := by
      nlinarith [sq_nonneg ‖t‖]
    have hlip := abs_exp_sub_exp_le_abs_of_nonpos
      (x := -q / 2) (y := -‖t‖ ^ 2 / 4) hxnonpos hynonpos
    calc
      |Real.exp (-q / 2) - Real.exp (-‖t‖ ^ 2 / 4)| ≤
          |-q / 2 - (-‖t‖ ^ 2 / 4)| := hlip
      _ = |2 * q - ‖t‖ ^ 2| / 4 := by
        have harg : -q / 2 - (-‖t‖ ^ 2 / 4) =
            -(2 * q - ‖t‖ ^ 2) / 4 := by ring
        rw [harg, abs_div, abs_neg]
        norm_num
      _ ≤ ‖ρ‖ * ‖t‖ ^ 2 / 4 := by
        gcongr
        simpa [hqcov] using hpert
  have hgauss :
      ‖(Real.exp (-q / 2) : ℂ) - circularGaussianCharacteristic t‖ ≤
        ‖ρ‖ * ‖t‖ ^ 2 / 4 := by
    unfold circularGaussianCharacteristic
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact hgaussReal
  have hrho : ρ =
      (evenFrequencyPolynomial
        (fun k : Fin (n + 1) => (radialWeight n s k : ℂ))).eval z := by
    exact sum_sq_radialCircleCoefficient_of_mem_sphere n s hz
  calc
    ‖radialCubeCharacteristicAt n s t z - circularGaussianCharacteristic t‖ =
        ‖(radialCubeCharacteristicAt n s t z - (Real.exp (-q / 2) : ℂ)) +
          ((Real.exp (-q / 2) : ℂ) - circularGaussianCharacteristic t)‖ := by
      congr 1
      ring
    _ ≤ ‖radialCubeCharacteristicAt n s t z - (Real.exp (-q / 2) : ℂ)‖ +
          ‖(Real.exp (-q / 2) : ℂ) - circularGaussianCharacteristic t‖ :=
      norm_add_le _ _
    _ ≤ (7 / 24 : ℝ) * (‖t‖ * Real.sqrt B) ^ 2 * ‖t‖ ^ 2 +
          ‖ρ‖ * ‖t‖ ^ 2 / 4 := add_le_add hchar' hgauss
    _ = (7 / 24 : ℝ) * (‖t‖ * Real.sqrt B) ^ 2 * ‖t‖ ^ 2 +
          ‖t‖ ^ 2 / 4 *
            ‖(evenFrequencyPolynomial
              (fun k : Fin (n + 1) => (radialWeight n s k : ℂ))).eval z‖ := by
      rw [hrho]
      ring

/-- Annealed characteristic function: average first over signs, then over the
unit-circle angular parameter. -/
noncomputable def radialAnnealedCharacteristic
    (n : ℕ) (s : ℝ) (t : ℂ) : ℂ :=
  Real.circleAverage (radialCubeCharacteristicAt n s t) 0 1

lemma continuous_radialCubeCharacteristicAt
    (n : ℕ) (s : ℝ) (t : ℂ) :
    Continuous (radialCubeCharacteristicAt n s t) := by
  unfold radialCubeCharacteristicAt cubeComplexAverage radialCircleCoefficient
  fun_prop

/-- Explicit angularly annealed characteristic-function bound. Unlike the
pointwise covariance argument, this needs no bad-angle decomposition: Parseval
controls the mean pseudocorrelation directly. -/
theorem norm_radialAnnealedCharacteristic_sub_circular_le
    (n : ℕ) (hn : 0 < n) (s : ℝ) (t : ℂ)
    (hsmall : ‖t‖ * Real.sqrt
      (Real.exp (4 * |s|) / (n + 1 : ℝ)) ≤ 1) :
    ‖radialAnnealedCharacteristic n s t - circularGaussianCharacteristic t‖ ≤
      (7 / 24 : ℝ) *
          (‖t‖ * Real.sqrt
            (Real.exp (4 * |s|) / (n + 1 : ℝ))) ^ 2 * ‖t‖ ^ 2 +
        ‖t‖ ^ 2 / 4 *
          Real.sqrt (Real.exp (4 * |s|) / (n + 1 : ℝ)) := by
  let F : ℂ → ℂ := fun z =>
    radialCubeCharacteristicAt n s t z - circularGaussianCharacteristic t
  let p := evenFrequencyPolynomial
    (fun k : Fin (n + 1) => (radialWeight n s k : ℂ))
  let A : ℝ := (7 / 24 : ℝ) *
    (‖t‖ * Real.sqrt (Real.exp (4 * |s|) / (n + 1 : ℝ))) ^ 2 * ‖t‖ ^ 2
  let C : ℝ := ‖t‖ ^ 2 / 4
  have hcharInt : CircleIntegrable (radialCubeCharacteristicAt n s t) 0 1 := by
    apply ContinuousOn.circleIntegrable (by norm_num)
    exact (continuous_radialCubeCharacteristicAt n s t).continuousOn
  have hconstInt : CircleIntegrable
      (fun _ : ℂ => circularGaussianCharacteristic t) 0 1 := by
    apply ContinuousOn.circleIntegrable (by norm_num)
    fun_prop
  have hFInt : CircleIntegrable F 0 1 := by
    exact hcharInt.sub hconstInt
  have hnormFInt : CircleIntegrable (fun z => ‖F z‖) 0 1 := hFInt.norm
  have hpNormInt : CircleIntegrable (fun z => ‖p.eval z‖) 0 1 := by
    apply ContinuousOn.circleIntegrable (by norm_num)
    fun_prop
  have hboundInt : CircleIntegrable (fun z => A + C * ‖p.eval z‖) 0 1 := by
    apply ContinuousOn.circleIntegrable (by norm_num)
    fun_prop
  have havgF : radialAnnealedCharacteristic n s t -
      circularGaussianCharacteristic t = Real.circleAverage F 0 1 := by
    unfold radialAnnealedCharacteristic
    calc
      Real.circleAverage (radialCubeCharacteristicAt n s t) 0 1 -
          circularGaussianCharacteristic t =
        Real.circleAverage (radialCubeCharacteristicAt n s t) 0 1 -
          Real.circleAverage (fun _ : ℂ => circularGaussianCharacteristic t) 0 1 := by
            rw [Real.circleAverage_const]
      _ = Real.circleAverage
          (radialCubeCharacteristicAt n s t -
            fun _ : ℂ => circularGaussianCharacteristic t) 0 1 :=
        (Real.circleAverage_sub hcharInt hconstInt).symm
      _ = Real.circleAverage F 0 1 := by
        congr 1
  rw [havgF]
  calc
    ‖Real.circleAverage F 0 1‖ ≤
        Real.circleAverage (fun z => ‖F z‖) 0 1 :=
      norm_circleAverage_le_circleAverage_norm F
    _ ≤ Real.circleAverage (fun z => A + C * ‖p.eval z‖) 0 1 := by
      apply Real.circleAverage_mono hnormFInt hboundInt
      intro z hz
      exact norm_radialCubeCharacteristicAt_sub_circular_le
        n hn s t (by simpa using hz) hsmall
    _ = A + C * Real.circleAverage (fun z => ‖p.eval z‖) 0 1 := by
      rw [show (fun z => A + C * ‖p.eval z‖) =
          (fun _ => A) + C • (fun z => ‖p.eval z‖) by
        funext z
        simp [smul_eq_mul]]
      rw [Real.circleAverage_add]
      · rw [Real.circleAverage_const, Real.circleAverage_smul]
        simp [smul_eq_mul]
      · apply ContinuousOn.circleIntegrable (by norm_num)
        fun_prop
      · exact hpNormInt.const_smul (a := C)
    _ ≤ A + C * Real.sqrt
          (Real.exp (4 * |s|) / (n + 1 : ℝ)) := by
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_left
      · exact circleParameterAverage_norm_pseudocorrelation_le_flat n hn s
      · dsimp [C]
        positivity

end Erdos522

end AmalgamatedModule37


/-! ===== amalgamated from Research.RadialCharacteristicMomentReduction ===== -/

section AmalgamatedModule38


open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace Erdos522

noncomputable def radialCharacteristicPhase
    (n : ℕ) (s : ℝ) (t z : ℂ) (k : Fin (n + 1)) : ℝ :=
  (star t * radialCircleCoefficient n s z k).re

noncomputable def radialCosineSum
    (n : ℕ) (s : ℝ) (t z : ℂ) : ℝ :=
  ∑ k : Fin (n + 1), Real.cos (2 * radialCharacteristicPhase n s t z k)

noncomputable def radialCosineSumMoment
    (n : ℕ) (s : ℝ) (t : ℂ) (q : ℕ) : ℝ :=
  Real.circleAverage (fun z => |radialCosineSum n s t z| ^ (2 * q)) 0 1

lemma radialCubeCharacteristicAt_eq_prod_cos
    (n : ℕ) (s : ℝ) (t z : ℂ) :
    radialCubeCharacteristicAt n s t z =
      ∏ k : Fin (n + 1),
        (Real.cos (radialCharacteristicPhase n s t z k) : ℂ) := by
  unfold radialCubeCharacteristicAt radialCharacteristicPhase
  exact cubeComplexAverage_cexp_re_conj_mul_weighted_sum
    (fun k => radialCircleCoefficient n s z k) t

lemma norm_radialCubeCharacteristicAt_eq_abs_prod_cos
    (n : ℕ) (s : ℝ) (t z : ℂ) :
    ‖radialCubeCharacteristicAt n s t z‖ =
      |∏ k : Fin (n + 1), Real.cos (radialCharacteristicPhase n s t z k)| := by
  rw [radialCubeCharacteristicAt_eq_prod_cos]
  rw [show ‖∏ k : Fin (n + 1),
      (Real.cos (radialCharacteristicPhase n s t z k) : ℂ)‖ =
      ∏ k : Fin (n + 1),
        ‖(Real.cos (radialCharacteristicPhase n s t z k) : ℂ)‖ by
    simpa using (norm_prod Finset.univ (fun k : Fin (n + 1) =>
      (Real.cos (radialCharacteristicPhase n s t z k) : ℂ)))]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  rw [← Finset.abs_prod]

lemma integral_norm_radialCubeCharacteristicAt_le_moment
    (n : ℕ) (s : ℝ) (t : ℂ) (q : ℕ) (hq : 0 < q) :
    (∫ θ, ‖radialCubeCharacteristicAt n s t (circleMap 0 1 θ)‖
      ∂circleParameterMeasure) ≤
      Real.exp (-((n + 1 : ℕ) : ℝ) / 8) +
        (2 / ((n + 1 : ℕ) : ℝ)) ^ (2 * q) * radialCosineSumMoment n s t q := by
  let a : Fin (n + 1) → ℝ → ℝ := fun k θ =>
    radialCharacteristicPhase n s t (circleMap 0 1 θ) k
  have hameas (k : Fin (n + 1)) : Measurable (a k) := by
    dsimp [a, radialCharacteristicPhase, radialCircleCoefficient]
    fun_prop
  have hprodInt : Integrable
      (fun θ => |∏ k : Fin (n + 1), Real.cos (a k θ)|)
      circleParameterMeasure := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards with θ
    rw [Real.norm_eq_abs, abs_abs]
    rw [Finset.abs_prod]
    calc
      (∏ k : Fin (n + 1), |Real.cos (a k θ)|) ≤
          ∏ _k : Fin (n + 1), (1 : ℝ) := by
        gcongr with k
        exact Real.abs_cos_le_one _
      _ = 1 := by simp
  have hmomInt : Integrable
      (fun θ => |∑ k : Fin (n + 1), Real.cos (2 * a k θ)| ^ (2 * q))
      circleParameterMeasure := by
    apply Integrable.of_bound (by fun_prop) (((n + 1 : ℕ) : ℝ) ^ (2 * q))
    filter_upwards with θ
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
    have hs : |∑ k : Fin (n + 1), Real.cos (2 * a k θ)| ≤ (n + 1 : ℝ) := by
      calc
        |∑ k : Fin (n + 1), Real.cos (2 * a k θ)| ≤
            ∑ k : Fin (n + 1), |Real.cos (2 * a k θ)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _k : Fin (n + 1), (1 : ℝ) := by
          gcongr with k
          exact Real.abs_cos_le_one _
        _ = (n + 1 : ℝ) := by simp
    have hs' : |∑ k : Fin (n + 1), Real.cos (2 * a k θ)| ≤
        (((n + 1 : ℕ) : ℝ)) := by
      norm_num at hs ⊢
      exact hs
    exact pow_le_pow_left₀ (abs_nonneg _) hs' (2 * q)
  have h := integral_abs_cosineProduct_le_exp_add_moment
    circleParameterMeasure (n + 1) q (by omega) hq a hameas hprodInt hmomInt
  rw [show (fun θ => |∏ k : Fin (n + 1), Real.cos (a k θ)|) =
      fun θ => ‖radialCubeCharacteristicAt n s t (circleMap 0 1 θ)‖ by
    funext θ
    exact (norm_radialCubeCharacteristicAt_eq_abs_prod_cos n s t _).symm] at h
  change _ ≤ Real.exp (-((n + 1 : ℕ) : ℝ) / 8) +
    (2 / ((n + 1 : ℕ) : ℝ)) ^ (2 * q) * _
  rw [show radialCosineSumMoment n s t q =
      ∫ θ, |∑ k : Fin (n + 1), Real.cos (2 * a k θ)| ^ (2 * q)
        ∂circleParameterMeasure by
    unfold radialCosineSumMoment
    rw [circleAverage_eq_integral_circleParameterMeasure]
    rfl]
  exact h

/-- The annealed characteristic function is bounded by the same high angular
cosine-sum moment. -/
theorem norm_radialAnnealedCharacteristic_le_moment
    (n : ℕ) (s : ℝ) (t : ℂ) (q : ℕ) (hq : 0 < q) :
    ‖radialAnnealedCharacteristic n s t‖ ≤
      Real.exp (-((n + 1 : ℕ) : ℝ) / 8) +
        (2 / ((n + 1 : ℕ) : ℝ)) ^ (2 * q) * radialCosineSumMoment n s t q := by
  unfold radialAnnealedCharacteristic
  rw [circleAverage_eq_integral_circleParameterMeasure_complex]
  exact (norm_integral_le_integral_norm _).trans
    (integral_norm_radialCubeCharacteristicAt_le_moment n s t q hq)

end Erdos522

end AmalgamatedModule38


/-! ===== amalgamated from Research.RadialTupleCoefficients ===== -/

section AmalgamatedModule39


open scoped BigOperators ComplexConjugate

namespace Erdos522

noncomputable def radialActiveCoefficient
    {q : ℕ} (n : ℕ) (s : ℝ) (t : ℂ)
    (K : Fin (2 * q) → Fin (n + 1)) (σ : Fin (2 * q) → Bool)
    (k : Fin (n + 1)) : ℂ :=
  (signedTupleMultiplicity K σ k : ℂ) * star t *
    Real.sqrt (radialWeight n s k)

noncomputable def radialTupleFrequencyIndex
    {q n : ℕ} (K : Fin (2 * q) → Fin (n + 1))
    (σ : Fin (2 * q) → Bool)
    (i : Fin (radialTupleFrequencySupport K σ).card) : Fin (n + 1) :=
  ⟨(radialTupleFrequencyEnumeration K σ i).natAbs,
    Nat.lt_succ_of_le (radialTupleFrequencyEnumeration_natAbs_le K σ i)⟩

noncomputable def radialTupleFrequencyCoefficient
    {q : ℕ} (n : ℕ) (s : ℝ) (t : ℂ)
    (K : Fin (2 * q) → Fin (n + 1)) (σ : Fin (2 * q) → Bool)
    (i : Fin (radialTupleFrequencySupport K σ).card) : ℂ :=
  if 0 < radialTupleFrequencyEnumeration K σ i then
    radialActiveCoefficient n s t K σ (radialTupleFrequencyIndex K σ i)
  else star (radialActiveCoefficient n s t K σ (radialTupleFrequencyIndex K σ i))

lemma radialTupleFrequencyIndex_mem_active
    {q n : ℕ} (K : Fin (2 * q) → Fin (n + 1))
    (σ : Fin (2 * q) → Bool)
    (i : Fin (radialTupleFrequencySupport K σ).card) :
    radialTupleFrequencyIndex K σ i ∈ activeTupleIndices K σ := by
  have hi := ((radialTupleFrequencySupport K σ).equivFin.symm i).2
  obtain ⟨k, hk, hsign⟩ := (mem_radialTupleFrequencySupport_iff K σ _).mp hi
  have heq : radialTupleFrequencyIndex K σ i = k := by
    apply Fin.ext
    unfold radialTupleFrequencyIndex radialTupleFrequencyEnumeration
    simp only
    rcases hsign with hp | hn
    · rw [hp]
      simp
    · rw [hn, Int.natAbs_neg]
      simp
  simpa [heq] using hk

lemma signedTupleMultiplicity_abs_le
    {q N : ℕ} (K : Fin (2 * q) → Fin N) (σ : Fin (2 * q) → Bool)
    (k : Fin N) :
    |(signedTupleMultiplicity K σ k : ℝ)| ≤ 2 * q := by
  unfold signedTupleMultiplicity
  rw [Int.cast_sum]
  calc
    |∑ j ∈ Finset.univ.filter (fun j => K j = k),
        (intBoolSign (σ j) : ℝ)| ≤
        ∑ j ∈ Finset.univ.filter (fun j => K j = k),
          |(intBoolSign (σ j) : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ _j ∈ Finset.univ.filter (fun j => K j = k), (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro j hj
      cases h : σ j <;> simp [h, intBoolSign]
    _ = ((Finset.univ.filter (fun j => K j = k)).card : ℝ) := by simp
    _ ≤ 2 * q := by
      have hc : (Finset.univ.filter (fun j => K j = k)).card ≤ 2 * q :=
        (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by simp)
      exact_mod_cast hc

lemma radialWeight_le_one (n : ℕ) (s : ℝ) (k : Fin (n + 1)) :
    radialWeight n s k ≤ 1 := by
  have hsum := sum_radialWeight n s
  have hk : k.val ∈ Finset.range (n + 1) := Finset.mem_range.mpr k.isLt
  calc
    radialWeight n s k ≤
        ∑ j ∈ Finset.range (n + 1), radialWeight n s j := by
      exact Finset.single_le_sum (fun j hj => radialWeight_nonneg n s j) hk
    _ = 1 := hsum

lemma sqrt_radialWeight_le_one (n : ℕ) (s : ℝ) (k : Fin (n + 1)) :
    Real.sqrt (radialWeight n s k) ≤ 1 := by
  rw [← Real.sqrt_one]
  exact Real.sqrt_le_sqrt (radialWeight_le_one n s k)

lemma norm_radialActiveCoefficient_eq
    {q : ℕ} (n : ℕ) (s : ℝ) (t : ℂ)
    (K : Fin (2 * q) → Fin (n + 1)) (σ : Fin (2 * q) → Bool)
    (k : Fin (n + 1)) :
    ‖radialActiveCoefficient n s t K σ k‖ =
      |(signedTupleMultiplicity K σ k : ℝ)| * ‖t‖ *
        Real.sqrt (radialWeight n s k) := by
  unfold radialActiveCoefficient
  rw [norm_mul, norm_mul, norm_star, Complex.norm_intCast,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]

lemma norm_radialActiveCoefficient_le
    {q : ℕ} (n : ℕ) (s : ℝ) (t : ℂ)
    (K : Fin (2 * q) → Fin (n + 1)) (σ : Fin (2 * q) → Bool)
    (k : Fin (n + 1)) :
    ‖radialActiveCoefficient n s t K σ k‖ ≤ (2 * q : ℝ) * ‖t‖ := by
  rw [norm_radialActiveCoefficient_eq]
  calc
    |(signedTupleMultiplicity K σ k : ℝ)| * ‖t‖ *
        Real.sqrt (radialWeight n s k) ≤
        ((2 * q : ℕ) : ℝ) * ‖t‖ * 1 := by
      gcongr
      simpa [Nat.cast_mul] using signedTupleMultiplicity_abs_le K σ k
      exact sqrt_radialWeight_le_one n s k
    _ = (2 * q : ℝ) * ‖t‖ := by push_cast; ring

lemma norm_radialTupleFrequencyCoefficient_le
    {q : ℕ} (n : ℕ) (s : ℝ) (t : ℂ)
    (K : Fin (2 * q) → Fin (n + 1)) (σ : Fin (2 * q) → Bool)
    (i : Fin (radialTupleFrequencySupport K σ).card) :
    ‖radialTupleFrequencyCoefficient n s t K σ i‖ ≤
      (2 * q : ℝ) * ‖t‖ := by
  unfold radialTupleFrequencyCoefficient
  split_ifs
  · exact norm_radialActiveCoefficient_le n s t K σ _
  · rw [norm_star]
    exact norm_radialActiveCoefficient_le n s t K σ _

lemma one_le_abs_signedTupleMultiplicity_of_active
    {q N : ℕ} (K : Fin (2 * q) → Fin N) (σ : Fin (2 * q) → Bool)
    {k : Fin N} (hk : k ∈ activeTupleIndices K σ) :
    1 ≤ |(signedTupleMultiplicity K σ k : ℝ)| := by
  have hne := (Finset.mem_filter.mp hk).2.2
  have hint : (signedTupleMultiplicity K σ k).natAbs > 0 := Int.natAbs_pos.mpr hne
  rw [← Int.cast_abs, ← Nat.cast_natAbs]
  exact_mod_cast hint

lemma norm_radialTupleFrequencyCoefficient_lower
    {q : ℕ} (n : ℕ) (hn : 0 < n) (s : ℝ) (t : ℂ)
    (K : Fin (2 * q) → Fin (n + 1)) (σ : Fin (2 * q) → Bool)
    (i : Fin (radialTupleFrequencySupport K σ).card) :
    Real.exp (-2 * |s|) / Real.sqrt (n + 1 : ℝ) * ‖t‖ ≤
      ‖radialTupleFrequencyCoefficient n s t K σ i‖ := by
  have hk := radialTupleFrequencyIndex_mem_active K σ i
  have hsqrt := sqrt_radialWeight_lower n hn s
    (Finset.mem_range.mpr (radialTupleFrequencyIndex K σ i).isLt)
  have hmult := one_le_abs_signedTupleMultiplicity_of_active K σ hk
  have hcoeff : ‖radialTupleFrequencyCoefficient n s t K σ i‖ =
      ‖radialActiveCoefficient n s t K σ (radialTupleFrequencyIndex K σ i)‖ := by
    unfold radialTupleFrequencyCoefficient
    split_ifs
    · rfl
    · exact norm_star _
  rw [hcoeff, norm_radialActiveCoefficient_eq]
  let d : ℝ := |(signedTupleMultiplicity K σ
    (radialTupleFrequencyIndex K σ i) : ℝ)|
  let w : ℝ := Real.sqrt (radialWeight n s (radialTupleFrequencyIndex K σ i))
  have hw : 0 ≤ w := Real.sqrt_nonneg _
  calc
    Real.exp (-2 * |s|) / Real.sqrt (n + 1 : ℝ) * ‖t‖ ≤
        w * ‖t‖ := mul_le_mul_of_nonneg_right hsqrt (norm_nonneg _)
    _ ≤ (d * w) * ‖t‖ := by
      gcongr
      dsimp [d]
      simpa using mul_le_mul_of_nonneg_right hmult hw
    _ = d * ‖t‖ * w := by ring

end Erdos522

end AmalgamatedModule39


/-! ===== amalgamated from Research.RadialPairedFrequencies ===== -/

section AmalgamatedModule40


open scoped BigOperators ComplexConjugate

namespace Erdos522

lemma fin_two_eq_zero_or_one (i : Fin 2) : i = 0 ∨ i = 1 := by
  fin_cases i <;> simp

noncomputable def radialActiveEnumeration
    {q N : ℕ} (K : Fin (2 * q) → Fin N) (σ : Fin (2 * q) → Bool) :
    Fin (activeTupleIndices K σ).card → Fin N :=
  fun i => ((activeTupleIndices K σ).equivFin.symm i).1

noncomputable def radialPairedDecode
    {q N : ℕ} (K : Fin (2 * q) → Fin N) (σ : Fin (2 * q) → Bool)
    (i : Fin (2 * (activeTupleIndices K σ).card)) :
    Fin 2 × Fin (activeTupleIndices K σ).card :=
  finProdFinEquiv.symm i

noncomputable def radialPairedFrequency
    {q N : ℕ} (K : Fin (2 * q) → Fin N) (σ : Fin (2 * q) → Bool)
    (i : Fin (2 * (activeTupleIndices K σ).card)) : ℤ :=
  let p := radialPairedDecode K σ i
  if p.1 = 0 then (radialActiveEnumeration K σ p.2).val
  else -((radialActiveEnumeration K σ p.2).val : ℤ)

noncomputable def radialPairedCoefficient
    {q : ℕ} (n : ℕ) (s : ℝ) (t : ℂ)
    (K : Fin (2 * q) → Fin (n + 1)) (σ : Fin (2 * q) → Bool)
    (i : Fin (2 * (activeTupleIndices K σ).card)) : ℂ :=
  let p := radialPairedDecode K σ i
  if p.1 = 0 then radialActiveCoefficient n s t K σ
      (radialActiveEnumeration K σ p.2)
  else star (radialActiveCoefficient n s t K σ
      (radialActiveEnumeration K σ p.2))

lemma radialActiveEnumeration_mem
    {q N : ℕ} (K : Fin (2 * q) → Fin N) (σ : Fin (2 * q) → Bool)
    (i : Fin (activeTupleIndices K σ).card) :
    radialActiveEnumeration K σ i ∈ activeTupleIndices K σ :=
  ((activeTupleIndices K σ).equivFin.symm i).2

lemma radialActiveEnumeration_injective
    {q N : ℕ} (K : Fin (2 * q) → Fin N) (σ : Fin (2 * q) → Bool) :
    Function.Injective (radialActiveEnumeration K σ) := by
  intro i j hij
  unfold radialActiveEnumeration at hij
  apply (activeTupleIndices K σ).equivFin.symm.injective
  apply Subtype.ext
  exact hij

lemma radialActiveEnumeration_pos
    {q N : ℕ} (K : Fin (2 * q) → Fin N) (σ : Fin (2 * q) → Bool)
    (i : Fin (activeTupleIndices K σ).card) :
    0 < (radialActiveEnumeration K σ i).val := by
  have hi := radialActiveEnumeration_mem K σ i
  exact Nat.pos_of_ne_zero (Finset.mem_filter.mp hi).2.1

lemma radialPairedFrequency_injective
    {q N : ℕ} (K : Fin (2 * q) → Fin N) (σ : Fin (2 * q) → Bool) :
    Function.Injective (radialPairedFrequency K σ) := by
  intro i j hij
  let pi := radialPairedDecode K σ i
  let pj := radialPairedDecode K σ j
  have hpi : pi.1 = 0 ∨ pi.1 = 1 := fin_two_eq_zero_or_one pi.1
  have hpj : pj.1 = 0 ∨ pj.1 = 1 := fin_two_eq_zero_or_one pj.1
  rcases hpi with hpi | hpi <;> rcases hpj with hpj | hpj
  · have hk : radialActiveEnumeration K σ pi.2 =
        radialActiveEnumeration K σ pj.2 := by
      apply Fin.ext
      simpa [radialPairedFrequency, pi, pj, hpi, hpj] using hij
    have hp2 := radialActiveEnumeration_injective K σ hk
    have hp : pi = pj := by ext <;> simp [hpi, hpj, hp2]
    apply (finProdFinEquiv.symm.injective)
    exact hp
  · have hposi := radialActiveEnumeration_pos K σ pi.2
    have hposj := radialActiveEnumeration_pos K σ pj.2
    have hh : ((radialActiveEnumeration K σ pi.2).val : ℤ) =
        -((radialActiveEnumeration K σ pj.2).val : ℤ) := by
      simpa [radialPairedFrequency, pi, pj, hpi, hpj] using hij
    exfalso
    omega
  · have hposi := radialActiveEnumeration_pos K σ pi.2
    have hposj := radialActiveEnumeration_pos K σ pj.2
    have hh : -((radialActiveEnumeration K σ pi.2).val : ℤ) =
        ((radialActiveEnumeration K σ pj.2).val : ℤ) := by
      simpa [radialPairedFrequency, pi, pj, hpi, hpj] using hij
    exfalso
    omega
  · have hk : radialActiveEnumeration K σ pi.2 =
        radialActiveEnumeration K σ pj.2 := by
      apply Fin.ext
      have hh := hij
      simp [radialPairedFrequency, pi, pj, hpi, hpj] at hh
      omega
    have hp2 := radialActiveEnumeration_injective K σ hk
    have hp : pi = pj := by ext <;> simp [hpi, hpj, hp2]
    apply (finProdFinEquiv.symm.injective)
    exact hp

lemma radialPairedFrequency_ne_zero
    {q N : ℕ} (K : Fin (2 * q) → Fin N) (σ : Fin (2 * q) → Bool)
    (i : Fin (2 * (activeTupleIndices K σ).card)) :
    radialPairedFrequency K σ i ≠ 0 := by
  let p := radialPairedDecode K σ i
  have hpos := radialActiveEnumeration_pos K σ p.2
  rcases fin_two_eq_zero_or_one p.1 with hp | hp
  · intro hz
    have hh : ((radialActiveEnumeration K σ p.2).val : ℤ) = 0 := by
      simpa [radialPairedFrequency, p, hp] using hz
    omega
  · intro hz
    have hh : -((radialActiveEnumeration K σ p.2).val : ℤ) = 0 := by
      simpa [radialPairedFrequency, p, hp] using hz
    omega

lemma radialPairedFrequency_natAbs_le
    {q n : ℕ} (K : Fin (2 * q) → Fin (n + 1)) (σ : Fin (2 * q) → Bool)
    (i : Fin (2 * (activeTupleIndices K σ).card)) :
    (radialPairedFrequency K σ i).natAbs ≤ n := by
  let p := radialPairedDecode K σ i
  have hk : (radialActiveEnumeration K σ p.2).val ≤ n :=
    Nat.le_of_lt_succ (radialActiveEnumeration K σ p.2).isLt
  rcases fin_two_eq_zero_or_one p.1 with hp | hp
  · simpa [radialPairedFrequency, p, hp] using hk
  · simpa [radialPairedFrequency, p, hp, Int.natAbs_neg] using hk

lemma card_radialPairedFrequency_le
    {q N : ℕ} (K : Fin (2 * q) → Fin N) (σ : Fin (2 * q) → Bool) :
    2 * (activeTupleIndices K σ).card ≤ 4 * q := by
  exact (Nat.mul_le_mul_left 2 (card_activeTupleIndices_le K σ)).trans_eq (by ring)

lemma norm_radialPairedCoefficient_le
    {q : ℕ} (n : ℕ) (s : ℝ) (t : ℂ)
    (K : Fin (2 * q) → Fin (n + 1)) (σ : Fin (2 * q) → Bool)
    (i : Fin (2 * (activeTupleIndices K σ).card)) :
    ‖radialPairedCoefficient n s t K σ i‖ ≤ (2 * q : ℝ) * ‖t‖ := by
  let p := radialPairedDecode K σ i
  rcases fin_two_eq_zero_or_one p.1 with hp | hp
  · simpa [radialPairedCoefficient, p, hp] using
      norm_radialActiveCoefficient_le n s t K σ (radialActiveEnumeration K σ p.2)
  · have heq : radialPairedCoefficient n s t K σ i =
        star (radialActiveCoefficient n s t K σ
          (radialActiveEnumeration K σ p.2)) := by
      simp [radialPairedCoefficient, p, hp]
    rw [heq, norm_star]
    exact norm_radialActiveCoefficient_le n s t K σ (radialActiveEnumeration K σ p.2)

lemma norm_radialPairedCoefficient_lower
    {q : ℕ} (n : ℕ) (hn : 0 < n) (s : ℝ) (t : ℂ)
    (K : Fin (2 * q) → Fin (n + 1)) (σ : Fin (2 * q) → Bool)
    (i : Fin (2 * (activeTupleIndices K σ).card)) :
    Real.exp (-2 * |s|) / Real.sqrt (n + 1 : ℝ) * ‖t‖ ≤
      ‖radialPairedCoefficient n s t K σ i‖ := by
  let p := radialPairedDecode K σ i
  have hk := radialActiveEnumeration_mem K σ p.2
  have hsqrt := sqrt_radialWeight_lower n hn s
    (Finset.mem_range.mpr (radialActiveEnumeration K σ p.2).isLt)
  have hmult := one_le_abs_signedTupleMultiplicity_of_active K σ hk
  have hactive : Real.exp (-2 * |s|) / Real.sqrt (n + 1 : ℝ) * ‖t‖ ≤
      ‖radialActiveCoefficient n s t K σ (radialActiveEnumeration K σ p.2)‖ := by
    rw [norm_radialActiveCoefficient_eq]
    let d : ℝ := |(signedTupleMultiplicity K σ
      (radialActiveEnumeration K σ p.2) : ℝ)|
    let w : ℝ := Real.sqrt (radialWeight n s (radialActiveEnumeration K σ p.2))
    have hw : 0 ≤ w := Real.sqrt_nonneg _
    calc
      _ ≤ w * ‖t‖ := mul_le_mul_of_nonneg_right hsqrt (norm_nonneg _)
      _ ≤ (d * w) * ‖t‖ := by
        gcongr
        dsimp [d]
        simpa using mul_le_mul_of_nonneg_right hmult hw
      _ = d * ‖t‖ * w := by ring
  rcases fin_two_eq_zero_or_one p.1 with hp | hp
  · simpa [radialPairedCoefficient, p, hp] using hactive
  · simpa [radialPairedCoefficient, p, hp, norm_star] using hactive


lemma star_complexFrequency (m : ℤ) :
    star (complexFrequency m) = complexFrequency (-m) := by
  unfold complexFrequency
  simp

lemma complexExponentialSumOrder_radialPaired_eq
    {q : ℕ} (r n : ℕ) (s : ℝ) (t : ℂ)
    (K : Fin (2 * q) → Fin (n + 1)) (σ : Fin (2 * q) → Bool)
    (z : ℂ) :
    complexExponentialSumOrder r (radialPairedFrequency K σ)
        (radialPairedCoefficient n s t K σ) z =
      ∑ l : Fin (activeTupleIndices K σ).card,
        (complexFrequency ((radialActiveEnumeration K σ l).val) ^ r *
            radialActiveCoefficient n s t K σ (radialActiveEnumeration K σ l) *
            Complex.exp (complexFrequency ((radialActiveEnumeration K σ l).val) * z) +
          complexFrequency (-((radialActiveEnumeration K σ l).val : ℤ)) ^ r *
            star (radialActiveCoefficient n s t K σ (radialActiveEnumeration K σ l)) *
            Complex.exp
              (complexFrequency (-((radialActiveEnumeration K σ l).val : ℤ)) * z)) := by
  unfold complexExponentialSumOrder
  let e : Fin 2 × Fin (activeTupleIndices K σ).card ≃
      Fin (2 * (activeTupleIndices K σ).card) := finProdFinEquiv
  let g : Fin (2 * (activeTupleIndices K σ).card) → ℂ := fun i =>
    complexFrequency (radialPairedFrequency K σ i) ^ r *
      radialPairedCoefficient n s t K σ i *
      Complex.exp (complexFrequency (radialPairedFrequency K σ i) * z)
  change (∑ i, g i) = _
  rw [← Equiv.sum_comp e g]
  rw [Fintype.sum_prod_type, Fin.sum_univ_two, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l hl
  have h0 : radialPairedDecode K σ (e (0, l)) = (0, l) := by
    unfold radialPairedDecode
    dsimp [e]
    exact Equiv.symm_apply_apply _ _
  have h1 : radialPairedDecode K σ (e (1, l)) = (1, l) := by
    unfold radialPairedDecode
    dsimp [e]
    exact Equiv.symm_apply_apply _ _
  dsimp [g]
  simp [radialPairedFrequency, radialPairedCoefficient, h0, h1]

lemma complexExponentialSumOrder_radialPaired_im_eq_zero
    {q : ℕ} (r n : ℕ) (s : ℝ) (t : ℂ)
    (K : Fin (2 * q) → Fin (n + 1)) (σ : Fin (2 * q) → Bool)
    (x : ℝ) :
    (complexExponentialSumOrder r (radialPairedFrequency K σ)
      (radialPairedCoefficient n s t K σ) (x : ℂ)).im = 0 := by
  rw [complexExponentialSumOrder_radialPaired_eq]
  change Complex.imLm (∑ l : Fin (activeTupleIndices K σ).card,
    (complexFrequency ((radialActiveEnumeration K σ l).val) ^ r *
      radialActiveCoefficient n s t K σ (radialActiveEnumeration K σ l) *
      Complex.exp (complexFrequency ((radialActiveEnumeration K σ l).val) * (x : ℂ)) +
    complexFrequency (-((radialActiveEnumeration K σ l).val : ℤ)) ^ r *
      star (radialActiveCoefficient n s t K σ (radialActiveEnumeration K σ l)) *
      Complex.exp (complexFrequency (-((radialActiveEnumeration K σ l).val : ℤ)) * (x : ℂ)))) = 0
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro l hl
  let w : ℂ :=
    complexFrequency ((radialActiveEnumeration K σ l).val) ^ r *
      radialActiveCoefficient n s t K σ (radialActiveEnumeration K σ l) *
      Complex.exp
        (complexFrequency ((radialActiveEnumeration K σ l).val) * (x : ℂ))
  have hneg :
      complexFrequency (-((radialActiveEnumeration K σ l).val : ℤ)) ^ r *
          star (radialActiveCoefficient n s t K σ (radialActiveEnumeration K σ l)) *
          Complex.exp
            (complexFrequency (-((radialActiveEnumeration K σ l).val : ℤ)) * (x : ℂ)) =
        star w := by
    dsimp [w]
    simp only [map_mul, map_pow]
    have hf : (starRingEnd ℂ) (complexFrequency
        ((radialActiveEnumeration K σ l).val : ℤ)) =
        complexFrequency (-((radialActiveEnumeration K σ l).val : ℤ)) :=
      star_complexFrequency _
    have hexp :
        Complex.exp
            (complexFrequency (-((radialActiveEnumeration K σ l).val : ℤ)) * (x : ℂ)) =
          (starRingEnd ℂ) (Complex.exp
            (complexFrequency ((radialActiveEnumeration K σ l).val : ℤ) * (x : ℂ))) := by
      rw [← Complex.exp_conj]
      congr 1
      rw [map_mul, hf]
      simp
    rw [hf, hexp]
  rw [hneg]
  change (w + star w).im = 0
  rw [Complex.add_im, Complex.star_def, Complex.conj_im]
  ring

end Erdos522

end AmalgamatedModule40


/-! ===== amalgamated from Research.CosinePowerExpansion ===== -/

section AmalgamatedModule41


open scoped BigOperators ComplexConjugate

namespace Erdos522

noncomputable def boolSign (b : Bool) : ℝ := if b then 1 else -1

lemma boolSign_abs (b : Bool) : |boolSign b| = 1 := by
  cases b <;> simp [boolSign]

lemma prod_cos_eq_sign_expansion
    {m : ℕ} (a : Fin m → ℝ) :
    (∏ j : Fin m, (Real.cos (a j) : ℂ)) =
      (∑ σ : Fin m → Bool,
        Complex.exp (((∑ j : Fin m, boolSign (σ j) * a j : ℝ) : ℂ) * Complex.I)) /
        (2 : ℂ) ^ m := by
  apply (eq_div_iff (pow_ne_zero _ (by norm_num : (2 : ℂ) ≠ 0))).2
  calc
    (∏ j : Fin m, (Real.cos (a j) : ℂ)) * (2 : ℂ) ^ m =
        ∏ j : Fin m, ((Real.cos (a j) : ℂ) * 2) := by
      rw [Finset.prod_mul_distrib]
      simp [mul_comm]
    _ = ∏ j : Fin m,
        (Complex.exp ((a j : ℂ) * Complex.I) +
          Complex.exp (-(a j : ℂ) * Complex.I)) := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [mul_comm]
      rw [Complex.ofReal_cos]
      exact Complex.two_cos (a j : ℂ)
    _ = ∑ σ : Fin m → Bool, ∏ j : Fin m,
        (if σ j then Complex.exp ((a j : ℂ) * Complex.I)
          else Complex.exp (-(a j : ℂ) * Complex.I)) := by
      rw [show (∏ j : Fin m,
          (Complex.exp ((a j : ℂ) * Complex.I) +
            Complex.exp (-(a j : ℂ) * Complex.I))) =
          ∏ j : Fin m, ∑ b : Bool,
            (if b then Complex.exp ((a j : ℂ) * Complex.I)
              else Complex.exp (-(a j : ℂ) * Complex.I)) by
        congr 1
        funext j
        simp]
      rw [Fintype.prod_sum]
    _ = ∑ σ : Fin m → Bool,
        Complex.exp (((∑ j : Fin m, boolSign (σ j) * a j : ℝ) : ℂ) * Complex.I) := by
      apply Finset.sum_congr rfl
      intro σ hσ
      rw [show (∏ j : Fin m,
          (if σ j then Complex.exp ((a j : ℂ) * Complex.I)
            else Complex.exp (-(a j : ℂ) * Complex.I))) =
          ∏ j : Fin m, Complex.exp
            (((boolSign (σ j) * a j : ℝ) : ℂ) * Complex.I) by
        apply Finset.prod_congr rfl
        intro j hj
        cases h : σ j <;> simp [h, boolSign]]
      rw [show (∏ j : Fin m, Complex.exp
          (((boolSign (σ j) * a j : ℝ) : ℂ) * Complex.I)) =
          Complex.exp (∑ j : Fin m,
            (((boolSign (σ j) * a j : ℝ) : ℂ) * Complex.I)) by
        simpa using (Complex.exp_sum Finset.univ
          (fun j : Fin m => (((boolSign (σ j) * a j : ℝ) : ℂ) *
            Complex.I))).symm]
      congr 1
      push_cast
      rw [Finset.sum_mul]

/-- Exact signed-exponential expansion of an arbitrary power of a finite cosine
sum. -/
theorem cosine_sum_power_expansion
    (m N : ℕ) (a : Fin N → ℝ) :
    ((∑ k : Fin N, Real.cos (a k)) ^ m : ℂ) =
      (∑ K : Fin m → Fin N, ∑ σ : Fin m → Bool,
        Complex.exp (((∑ j : Fin m, boolSign (σ j) * a (K j) : ℝ) : ℂ) *
          Complex.I)) / (2 : ℂ) ^ m := by
  rw [show ((∑ k : Fin N, Real.cos (a k)) ^ m : ℂ) =
      ∑ K : Fin m → Fin N,
        ∏ j : Fin m, (Real.cos (a (K j)) : ℂ) by
    push_cast
    simpa using (Finset.sum_pow' Finset.univ
      (fun k : Fin N => (Real.cos (a k) : ℂ)) m)]
  simp_rw [prod_cos_eq_sign_expansion]
  rw [Finset.sum_div]


open MeasureTheory

/-- The even angular moment is bounded by the sum of the absolute oscillatory
integrals arising from all index tuples and sign choices. -/
theorem integral_abs_cosineSum_pow_le_sum_norm_oscillatory
    {α : Type*} [MeasurableSpace α] [TopologicalSpace α] [BorelSpace α]
    (μ : Measure α) [IsFiniteMeasure μ]
    (q N : ℕ) (a : Fin N → α → ℝ)
    (ha : ∀ k, Continuous (a k)) :
    (∫ x, |∑ k : Fin N, Real.cos (a k x)| ^ (2 * q) ∂μ) ≤
      ∑ K : Fin (2 * q) → Fin N, ∑ σ : Fin (2 * q) → Bool,
        ‖∫ x, Complex.exp
          (((∑ j : Fin (2 * q), boolSign (σ j) * a (K j) x : ℝ) : ℂ) *
            Complex.I) ∂μ‖ := by
  let S : α → ℝ := fun x => ∑ k : Fin N, Real.cos (a k x)
  let F : (Fin (2 * q) → Fin N) → (Fin (2 * q) → Bool) → α → ℂ :=
    fun K σ x => Complex.exp
      (((∑ j : Fin (2 * q), boolSign (σ j) * a (K j) x : ℝ) : ℂ) *
        Complex.I)
  have hScont : Continuous S := by
    dsimp [S]
    fun_prop
  have hFcont (K : Fin (2 * q) → Fin N) (σ : Fin (2 * q) → Bool) :
      Continuous (F K σ) := by
    dsimp [F]
    fun_prop
  have hFint (K : Fin (2 * q) → Fin N) (σ : Fin (2 * q) → Bool) :
      Integrable (F K σ) μ := by
    apply Integrable.of_bound (hFcont K σ).aestronglyMeasurable 1
    filter_upwards with x
    dsimp [F]
    rw [Complex.norm_exp]
    simp
  have hpow_pointwise (x : α) : 0 ≤ (S x) ^ (2 * q) := by
    rw [show 2 * q = q * 2 by omega, pow_mul]
    positivity
  have hpow_nonneg : 0 ≤ ∫ x, (S x) ^ (2 * q) ∂μ :=
    integral_nonneg hpow_pointwise
  have hint :
      (((∫ x, (S x) ^ (2 * q) ∂μ) : ℝ) : ℂ) =
        (∑ K : Fin (2 * q) → Fin N, ∑ σ : Fin (2 * q) → Bool,
          ∫ x, F K σ x ∂μ) / (2 : ℂ) ^ (2 * q) := by
    calc
      (((∫ x, (S x) ^ (2 * q) ∂μ) : ℝ) : ℂ) =
          ∫ x, (((S x) ^ (2 * q) : ℝ) : ℂ) ∂μ := integral_ofReal.symm
      _ = ∫ x, (∑ K : Fin (2 * q) → Fin N,
            ∑ σ : Fin (2 * q) → Bool, F K σ x) /
              (2 : ℂ) ^ (2 * q) ∂μ := by
        apply integral_congr_ae
        filter_upwards with x
        simpa [S, F] using
          (cosine_sum_power_expansion (2 * q) N (fun k => a k x))
      _ = (∫ x, ∑ K : Fin (2 * q) → Fin N,
            ∑ σ : Fin (2 * q) → Bool, F K σ x ∂μ) /
              (2 : ℂ) ^ (2 * q) := by
        rw [integral_div]
      _ = (∑ K : Fin (2 * q) → Fin N, ∑ σ : Fin (2 * q) → Bool,
            ∫ x, F K σ x ∂μ) / (2 : ℂ) ^ (2 * q) := by
        congr 1
        rw [integral_finset_sum]
        · apply Finset.sum_congr rfl
          intro K hK
          rw [integral_finset_sum]
          intro σ hσ
          exact hFint K σ
        · intro K hK
          apply integrable_finset_sum
          intro σ hσ
          exact hFint K σ
  have hdiv :
      ‖(∑ K : Fin (2 * q) → Fin N, ∑ σ : Fin (2 * q) → Bool,
          ∫ x, F K σ x ∂μ) / (2 : ℂ) ^ (2 * q)‖ ≤
        ‖∑ K : Fin (2 * q) → Fin N, ∑ σ : Fin (2 * q) → Bool,
          ∫ x, F K σ x ∂μ‖ := by
    rw [norm_div, norm_pow, Complex.norm_ofNat]
    apply div_le_self (norm_nonneg _)
    exact one_le_pow₀ (by norm_num)
  calc
    (∫ x, |∑ k : Fin N, Real.cos (a k x)| ^ (2 * q) ∂μ) =
        ∫ x, (S x) ^ (2 * q) ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      dsimp [S]
      rw [show 2 * q = q * 2 by omega, pow_mul]
      rw [show (∑ k : Fin N, Real.cos (a k x)) ^ (q * 2) =
          ((∑ k : Fin N, Real.cos (a k x)) ^ q) ^ 2 by rw [pow_mul]]
      rw [← abs_pow]
      exact sq_abs ((∑ k : Fin N, Real.cos (a k x)) ^ q)
    _ = ‖(((∫ x, (S x) ^ (2 * q) ∂μ) : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpow_nonneg]
    _ = ‖(∑ K : Fin (2 * q) → Fin N, ∑ σ : Fin (2 * q) → Bool,
          ∫ x, F K σ x ∂μ) / (2 : ℂ) ^ (2 * q)‖ := congrArg norm hint
    _ ≤ ‖∑ K : Fin (2 * q) → Fin N, ∑ σ : Fin (2 * q) → Bool,
          ∫ x, F K σ x ∂μ‖ := hdiv
    _ ≤ ∑ K : Fin (2 * q) → Fin N,
          ‖∑ σ : Fin (2 * q) → Bool, ∫ x, F K σ x ∂μ‖ := norm_sum_le _ _
    _ ≤ ∑ K : Fin (2 * q) → Fin N, ∑ σ : Fin (2 * q) → Bool,
          ‖∫ x, F K σ x ∂μ‖ := by
      apply Finset.sum_le_sum
      intro K hK
      exact norm_sum_le _ _
    _ = _ := rfl

end Erdos522

end AmalgamatedModule41


/-! ===== amalgamated from Research.RadialTuplePhaseRepresentation ===== -/

section AmalgamatedModule42


open scoped BigOperators ComplexConjugate

namespace Erdos522

noncomputable def radialSignedTuplePhase
    {q : ℕ} (n : ℕ) (s : ℝ) (t : ℂ)
    (K : Fin (2 * q) → Fin (n + 1)) (σ : Fin (2 * q) → Bool)
    (θ : ℝ) : ℝ :=
  ∑ j : Fin (2 * q), boolSign (σ j) *
    (2 * radialCharacteristicPhase n s t (circleMap 0 1 θ) (K j))

lemma intBoolSign_cast_real (b : Bool) : (intBoolSign b : ℝ) = boolSign b := by
  cases b <;> simp [intBoolSign, boolSign]

lemma radialCharacteristicPhase_circleMap_eq_exp
    (n : ℕ) (s : ℝ) (t : ℂ) (k : Fin (n + 1)) (θ : ℝ) :
    radialCharacteristicPhase n s t (circleMap 0 1 θ) k =
      (star t * Real.sqrt (radialWeight n s k) *
        Complex.exp (complexFrequency (k.val : ℤ) * (θ : ℂ))).re := by
  have hpow : (circleMap 0 1 θ) ^ k.val =
      Complex.exp (complexFrequency (k.val : ℤ) * (θ : ℂ)) := by
    rw [circleMap_zero]
    norm_num
    rw [← Complex.exp_nat_mul]
    congr 1
    unfold complexFrequency
    push_cast
    ring
  unfold radialCharacteristicPhase radialCircleCoefficient
  rw [hpow]
  ring

lemma radialSignedTuplePhase_eq_sum_multiplicity
    {q : ℕ} (n : ℕ) (s : ℝ) (t : ℂ)
    (K : Fin (2 * q) → Fin (n + 1)) (σ : Fin (2 * q) → Bool)
    (θ : ℝ) :
    radialSignedTuplePhase n s t K σ θ =
      ∑ k : Fin (n + 1), (signedTupleMultiplicity K σ k : ℝ) *
        (2 * radialCharacteristicPhase n s t (circleMap 0 1 θ) k) := by
  unfold radialSignedTuplePhase
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := Finset.univ) (t := Finset.univ) (g := K)
    (fun i hi => Finset.mem_univ (K i))
    (fun j => boolSign (σ j) *
      (2 * radialCharacteristicPhase n s t (circleMap 0 1 θ) (K j)))]
  apply Finset.sum_congr rfl
  intro k hk
  let B : ℝ := 2 * radialCharacteristicPhase n s t (circleMap 0 1 θ) k
  calc
    (∑ j ∈ Finset.univ.filter (fun j => K j = k),
        boolSign (σ j) *
          (2 * radialCharacteristicPhase n s t (circleMap 0 1 θ) (K j))) =
        ∑ j ∈ Finset.univ.filter (fun j => K j = k), boolSign (σ j) * B := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjK := (Finset.mem_filter.mp hj).2
      simp only [B, hjK]
    _ = (∑ j ∈ Finset.univ.filter (fun j => K j = k), boolSign (σ j)) * B := by
      rw [Finset.sum_mul]
    _ = (signedTupleMultiplicity K σ k : ℝ) *
        (2 * radialCharacteristicPhase n s t (circleMap 0 1 θ) k) := by
      dsimp [B]
      congr 1
      unfold signedTupleMultiplicity
      rw [Int.cast_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [intBoolSign_cast_real]

lemma signedTupleMultiplicity_ne_zero_imp_mem_range
    {q N : ℕ} (K : Fin (2 * q) → Fin N) (σ : Fin (2 * q) → Bool)
    {k : Fin N} (hk : signedTupleMultiplicity K σ k ≠ 0) :
    k ∈ tupleRange K := by
  by_contra hkr
  have hempty : Finset.univ.filter (fun j => K j = k) = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro hne
    obtain ⟨j, hj⟩ := hne
    apply hkr
    exact (mem_tupleRange K k).mpr ⟨j, (Finset.mem_filter.mp hj).2⟩
  unfold signedTupleMultiplicity at hk
  rw [hempty] at hk
  simp at hk

lemma sum_multiplicity_eq_zero_add_active
    {q : ℕ} (n : ℕ) (s : ℝ) (t : ℂ)
    (K : Fin (2 * q) → Fin (n + 1)) (σ : Fin (2 * q) → Bool)
    (θ : ℝ) :
    (∑ k : Fin (n + 1), (signedTupleMultiplicity K σ k : ℝ) *
        (2 * radialCharacteristicPhase n s t (circleMap 0 1 θ) k)) =
      (signedTupleMultiplicity K σ 0 : ℝ) *
          (2 * radialCharacteristicPhase n s t (circleMap 0 1 θ) 0) +
        ∑ k ∈ activeTupleIndices K σ,
          (signedTupleMultiplicity K σ k : ℝ) *
            (2 * radialCharacteristicPhase n s t (circleMap 0 1 θ) k) := by
  let b : Fin (n + 1) → ℝ := fun k =>
    (signedTupleMultiplicity K σ k : ℝ) *
      (2 * radialCharacteristicPhase n s t (circleMap 0 1 θ) k)
  have hsubset : activeTupleIndices K σ ⊆
      (Finset.univ : Finset (Fin (n + 1))).erase 0 := by
    intro k hk
    apply Finset.mem_erase.mpr
    exact ⟨by
      intro heq
      subst k
      exact (Finset.mem_filter.mp hk).2.1 rfl, Finset.mem_univ _⟩
  have hzero : ∀ k ∈ (Finset.univ : Finset (Fin (n + 1))).erase 0,
      k ∉ activeTupleIndices K σ → b k = 0 := by
    intro k hkErase hkActive
    have hk0 : k.val ≠ 0 := by
      intro hv
      have : k = 0 := Fin.ext hv
      exact (Finset.mem_erase.mp hkErase).1 this
    by_cases hd : signedTupleMultiplicity K σ k = 0
    · simp [b, hd]
    · have hkr := signedTupleMultiplicity_ne_zero_imp_mem_range K σ hd
      exfalso
      apply hkActive
      exact Finset.mem_filter.mpr ⟨hkr, hk0, hd⟩
  have hactiveSum : ∑ k ∈ activeTupleIndices K σ, b k =
      ∑ k ∈ (Finset.univ : Finset (Fin (n + 1))).erase 0, b k :=
    Finset.sum_subset hsubset hzero
  change (∑ k : Fin (n + 1), b k) = b 0 + ∑ k ∈ activeTupleIndices K σ, b k
  rw [hactiveSum]
  rw [← Finset.sum_erase_add (Finset.univ : Finset (Fin (n + 1))) b
    (Finset.mem_univ 0)]
  ring

lemma realExponentialSum_radialPaired_eq_active
    {q : ℕ} (n : ℕ) (s : ℝ) (t : ℂ)
    (K : Fin (2 * q) → Fin (n + 1)) (σ : Fin (2 * q) → Bool)
    (θ : ℝ) :
    realExponentialSum (radialPairedFrequency K σ)
        (radialPairedCoefficient n s t K σ) θ =
      ∑ k ∈ activeTupleIndices K σ,
        (signedTupleMultiplicity K σ k : ℝ) *
          (2 * radialCharacteristicPhase n s t (circleMap 0 1 θ) k) := by
  unfold realExponentialSum
  rw [complexExponentialSumOrder_radialPaired_eq]
  let F : Fin (activeTupleIndices K σ).card → ℂ := fun l =>
    (complexFrequency ((radialActiveEnumeration K σ l).val) ^ 0 *
        radialActiveCoefficient n s t K σ (radialActiveEnumeration K σ l) *
        Complex.exp (complexFrequency ((radialActiveEnumeration K σ l).val) * (θ : ℂ)) +
      complexFrequency (-((radialActiveEnumeration K σ l).val : ℤ)) ^ 0 *
        star (radialActiveCoefficient n s t K σ (radialActiveEnumeration K σ l)) *
        Complex.exp
          (complexFrequency (-((radialActiveEnumeration K σ l).val : ℤ)) * (θ : ℂ)))
  change Complex.reCLM (∑ l : Fin (activeTupleIndices K σ).card, F l) = _
  rw [map_sum]
  dsimp [F]
  rw [show (∑ k ∈ activeTupleIndices K σ,
      (signedTupleMultiplicity K σ k : ℝ) *
        (2 * radialCharacteristicPhase n s t (circleMap 0 1 θ) k)) =
      ∑ l : Fin (activeTupleIndices K σ).card,
        (signedTupleMultiplicity K σ (radialActiveEnumeration K σ l) : ℝ) *
          (2 * radialCharacteristicPhase n s t (circleMap 0 1 θ)
            (radialActiveEnumeration K σ l)) by
    let g : Fin (n + 1) → ℝ := fun k =>
      (signedTupleMultiplicity K σ k : ℝ) *
        (2 * radialCharacteristicPhase n s t (circleMap 0 1 θ) k)
    calc
      (∑ k ∈ activeTupleIndices K σ, g k) =
          ∑ k : activeTupleIndices K σ, g k := by
        rw [← Finset.sum_attach]
        simp
      _ = ∑ l : Fin (activeTupleIndices K σ).card,
          g ((activeTupleIndices K σ).equivFin.symm l) :=
        (Equiv.sum_comp (activeTupleIndices K σ).equivFin.symm
          (fun k : activeTupleIndices K σ => g k)).symm
      _ = _ := by rfl]
  apply Finset.sum_congr rfl
  intro l hl
  simp only [pow_zero, one_mul]
  let A := radialActiveCoefficient n s t K σ (radialActiveEnumeration K σ l)
  let e := Complex.exp
    (complexFrequency ((radialActiveEnumeration K σ l).val : ℤ) * (θ : ℂ))
  have hpair :
      star A *
          Complex.exp
            (complexFrequency (-((radialActiveEnumeration K σ l).val : ℤ)) * (θ : ℂ)) =
        star (A * e) := by
    have hf := star_complexFrequency ((radialActiveEnumeration K σ l).val : ℤ)
    have hexp : Complex.exp
        (complexFrequency (-((radialActiveEnumeration K σ l).val : ℤ)) * (θ : ℂ)) =
        star e := by
      dsimp [e]
      rw [← Complex.exp_conj]
      congr 1
      rw [map_mul]
      have hf' : (starRingEnd ℂ) (complexFrequency
          ((radialActiveEnumeration K σ l).val : ℤ)) =
          complexFrequency (-((radialActiveEnumeration K σ l).val : ℤ)) := by
        simpa only [starRingEnd_apply] using hf
      rw [hf']
      simp
    rw [hexp]
    simpa only [starRingEnd_apply] using
      (map_mul (starRingEnd ℂ) A e).symm
  change (A * e).re +
    (star A * Complex.exp
      (complexFrequency (-((radialActiveEnumeration K σ l).val : ℤ)) * (θ : ℂ))).re = _
  rw [hpair, show (star (A * e)).re = (A * e).re by simp]
  rw [radialCharacteristicPhase_circleMap_eq_exp]
  unfold A e radialActiveCoefficient
  push_cast
  simp [Complex.mul_re, Complex.mul_im]
  ring

/-- The tuple phase is a constant zero-frequency shift plus the paired sparse
real exponential sum. -/
theorem radialSignedTuplePhase_eq_zero_add_realExponentialSum
    {q : ℕ} (n : ℕ) (s : ℝ) (t : ℂ)
    (K : Fin (2 * q) → Fin (n + 1)) (σ : Fin (2 * q) → Bool)
    (θ : ℝ) :
    radialSignedTuplePhase n s t K σ θ =
      (signedTupleMultiplicity K σ 0 : ℝ) *
          (2 * radialCharacteristicPhase n s t (circleMap 0 1 θ) 0) +
        realExponentialSum (radialPairedFrequency K σ)
          (radialPairedCoefficient n s t K σ) θ := by
  rw [radialSignedTuplePhase_eq_sum_multiplicity,
    sum_multiplicity_eq_zero_add_active,
    realExponentialSum_radialPaired_eq_active]

end Erdos522

end AmalgamatedModule42


/-! ===== amalgamated from Research.PositiveCosineMomentExceptionalSplit ===== -/

section AmalgamatedModule43


open MeasureTheory
open scoped BigOperators

namespace Erdos522

noncomputable def oscillatoryIntegralNorm
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {q N : ℕ} (a : Fin N → α → ℝ)
    (K : Fin (2 * q) → Fin N) (σ : Fin (2 * q) → Bool) : ℝ :=
  ‖∫ x, Complex.exp
    (((∑ j : Fin (2 * q), boolSign (σ j) * a (K j) x : ℝ) : ℂ) *
      Complex.I) ∂μ‖

lemma oscillatoryIntegralNorm_le_one
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {q N : ℕ} (a : Fin N → α → ℝ)
    (K : Fin (2 * q) → Fin N) (σ : Fin (2 * q) → Bool) :
    oscillatoryIntegralNorm μ a K σ ≤ 1 := by
  unfold oscillatoryIntegralNorm
  calc
    ‖∫ x, Complex.exp
        (((∑ j : Fin (2 * q), boolSign (σ j) * a (K j) x : ℝ) : ℂ) *
          Complex.I) ∂μ‖ ≤
        ∫ x, ‖Complex.exp
          (((∑ j : Fin (2 * q), boolSign (σ j) * a (K j) x : ℝ) : ℂ) *
            Complex.I)‖ ∂μ := norm_integral_le_integral_norm _
    _ = ∫ _x, (1 : ℝ) ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      rw [Complex.norm_exp]
      simp
    _ = 1 := by simp

/-- Once all non-even-multiplicity tuples have a common oscillatory bound `E`,
the full high cosine moment has the expected `O_q(N^q)+O_q(N^{2q}E)` form. -/
theorem integral_abs_cosineSum_pow_le_positiveExceptional_add
    {α : Type*} [MeasurableSpace α] [TopologicalSpace α] [BorelSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (q N : ℕ) (hN : 0 < N) (a : Fin N → α → ℝ)
    (ha : ∀ k, Continuous (a k)) (E : ℝ) (hE : 0 ≤ E)
    (hnon : ∀ (K : Fin (2 * q) → Fin N), K ∉ positiveEvenFiberTuples q N →
      ∀ σ : Fin (2 * q) → Bool, oscillatoryIntegralNorm μ a K σ ≤ E) :
    (∫ x, |∑ k : Fin N, Real.cos (a k x)| ^ (2 * q) ∂μ) ≤
      (2 : ℝ) ^ (2 * q) *
        ((((q + 1) ^ (2 * q + 1) : ℕ) : ℝ) * (N : ℝ) ^ q +
          (N : ℝ) ^ (2 * q) * E) := by
  have hexcard := card_positiveEvenFiberTuples_le q N hN
  have hterm (K : Fin (2 * q) → Fin N) (σ : Fin (2 * q) → Bool) :
      oscillatoryIntegralNorm μ a K σ ≤
        (if K ∈ positiveEvenFiberTuples q N then 1 else 0) + E := by
    by_cases hK : K ∈ positiveEvenFiberTuples q N
    · rw [if_pos hK]
      have h := oscillatoryIntegralNorm_le_one μ a K σ
      linarith
    · rw [if_neg hK, zero_add]
      exact hnon K hK σ
  have hexpand := integral_abs_cosineSum_pow_le_sum_norm_oscillatory μ q N a ha
  refine hexpand.trans ?_
  calc
    (∑ K : Fin (2 * q) → Fin N, ∑ σ : Fin (2 * q) → Bool,
        oscillatoryIntegralNorm μ a K σ) ≤
        ∑ K : Fin (2 * q) → Fin N, ∑ _σ : Fin (2 * q) → Bool,
          ((if K ∈ positiveEvenFiberTuples q N then 1 else 0) + E) := by
      apply Finset.sum_le_sum
      intro K hK
      apply Finset.sum_le_sum
      intro σ hσ
      exact hterm K σ
    _ = (2 : ℝ) ^ (2 * q) *
        (((positiveEvenFiberTuples q N).card : ℝ) + (N : ℝ) ^ (2 * q) * E) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin, Fintype.card_bool, nsmul_eq_mul]
      rw [← Finset.mul_sum]
      congr 1
      · norm_cast
      · rw [Finset.sum_add_distrib]
        simp
    _ ≤ (2 : ℝ) ^ (2 * q) *
        (((((q + 1) ^ (2 * q + 1) : ℕ) * N ^ q : ℕ) : ℝ) +
          (N : ℝ) ^ (2 * q) * E) := by
      gcongr
    _ = (2 : ℝ) ^ (2 * q) *
        ((((q + 1) ^ (2 * q + 1) : ℕ) : ℝ) * (N : ℝ) ^ q +
          (N : ℝ) ^ (2 * q) * E) := by
      push_cast
      ring

end Erdos522

end AmalgamatedModule43


/-! ===== amalgamated from Research.RadialTupleOscillatoryNorm ===== -/

section AmalgamatedModule44


open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace Erdos522

noncomputable def radialTupleZeroPhase
    {q : ℕ} (n : ℕ) (s : ℝ) (t : ℂ)
    (K : Fin (2 * q) → Fin (n + 1)) (σ : Fin (2 * q) → Bool) : ℝ :=
  (signedTupleMultiplicity K σ 0 : ℝ) *
    (2 * (star t * Real.sqrt (radialWeight n s 0)).re)

lemma radialCharacteristicPhase_circleMap_zero_frequency
    (n : ℕ) (s : ℝ) (t : ℂ) (θ : ℝ) :
    radialCharacteristicPhase n s t (circleMap 0 1 θ) (0 : Fin (n + 1)) =
      (star t * Real.sqrt (radialWeight n s 0)).re := by
  rw [radialCharacteristicPhase_circleMap_eq_exp]
  simp [complexFrequency]

lemma radialSignedTuplePhase_eq_const_add_realExponentialSum
    {q : ℕ} (n : ℕ) (s : ℝ) (t : ℂ)
    (K : Fin (2 * q) → Fin (n + 1)) (σ : Fin (2 * q) → Bool)
    (θ : ℝ) :
    radialSignedTuplePhase n s t K σ θ =
      radialTupleZeroPhase n s t K σ +
        realExponentialSum (radialPairedFrequency K σ)
          (radialPairedCoefficient n s t K σ) θ := by
  rw [radialSignedTuplePhase_eq_zero_add_realExponentialSum,
    radialCharacteristicPhase_circleMap_zero_frequency]
  rfl

/-- A zero-frequency phase only multiplies the oscillatory integral by a unit
complex number, so its norm is exactly the norm of the active sparse sum. -/
theorem radial_oscillatoryIntegralNorm_eq_realExponentialSum
    {q : ℕ} (n : ℕ) (s : ℝ) (t : ℂ)
    (K : Fin (2 * q) → Fin (n + 1)) (σ : Fin (2 * q) → Bool) :
    oscillatoryIntegralNorm circleParameterMeasure
        (fun k θ => 2 * radialCharacteristicPhase n s t
          (circleMap 0 1 θ) k) K σ =
      ‖∫ θ, Complex.exp
        (realExponentialSum (radialPairedFrequency K σ)
          (radialPairedCoefficient n s t K σ) θ * Complex.I)
        ∂circleParameterMeasure‖ := by
  unfold oscillatoryIntegralNorm
  have hphase (θ : ℝ) :
      (∑ j : Fin (2 * q), boolSign (σ j) *
          (2 * radialCharacteristicPhase n s t
            (circleMap 0 1 θ) (K j))) =
        radialTupleZeroPhase n s t K σ +
          realExponentialSum (radialPairedFrequency K σ)
            (radialPairedCoefficient n s t K σ) θ := by
    exact radialSignedTuplePhase_eq_const_add_realExponentialSum n s t K σ θ
  simp_rw [hphase]
  rw [show (fun θ : ℝ => Complex.exp
      ((((radialTupleZeroPhase n s t K σ +
        realExponentialSum (radialPairedFrequency K σ)
          (radialPairedCoefficient n s t K σ) θ : ℝ) : ℂ) * Complex.I))) =
      fun θ => Complex.exp ((radialTupleZeroPhase n s t K σ : ℂ) * Complex.I) *
        Complex.exp (realExponentialSum (radialPairedFrequency K σ)
          (radialPairedCoefficient n s t K σ) θ * Complex.I) by
    funext θ
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring]
  rw [MeasureTheory.integral_const_mul]
  rw [norm_mul, Complex.norm_exp]
  have hre : ((radialTupleZeroPhase n s t K σ : ℂ) * Complex.I).re = 0 := by
    simp
  rw [hre, Real.exp_zero, one_mul]

end Erdos522

end AmalgamatedModule44


/-! ===== amalgamated from Research.RadialTupleAutomaticOscillation ===== -/

section AmalgamatedModule45


open MeasureTheory
open scoped BigOperators

namespace Erdos522

noncomputable def radialTupleCoefficientScale (n : ℕ) (s : ℝ) (t : ℂ) : ℝ :=
  Real.exp (-2 * |s|) / (n + 1 : ℝ) * ‖t‖

noncomputable def radialTupleDerivativeScale
    (q H n : ℕ) (t : ℂ) : ℝ :=
  (8 * q ^ 2 : ℝ) * (n + 1 : ℝ) ^ (H + 1) * ‖t‖

noncomputable def radialTupleFiniteTypeScale
    {q : ℕ} (n : ℕ) (s : ℝ) (t : ℂ)
    (K : Fin (2 * q) → Fin (n + 1)) (σ : Fin (2 * q) → Bool) : ℝ :=
  let h := 2 * (activeTupleIndices K σ).card
  radialTupleCoefficientScale n s t /
    ((h : ℝ) * (h.factorial : ℝ) * ((n + 1 : ℝ) ^ (h + 1)) ^ h)

lemma radialTupleCoefficientScale_pos
    (n : ℕ) (s : ℝ) {t : ℂ} (ht : t ≠ 0) :
    0 < radialTupleCoefficientScale n s t := by
  unfold radialTupleCoefficientScale
  positivity

lemma radialTupleDerivativeScale_nonneg (q H n : ℕ) (t : ℂ) :
    0 ≤ radialTupleDerivativeScale q H n t := by
  unfold radialTupleDerivativeScale
  positivity

lemma radialTupleCoefficientScale_le_paired
    {q : ℕ} (n : ℕ) (hn : 0 < n) (s : ℝ) (t : ℂ)
    (K : Fin (2 * q) → Fin (n + 1)) (σ : Fin (2 * q) → Bool)
    (i : Fin (2 * (activeTupleIndices K σ).card)) :
    radialTupleCoefficientScale n s t ≤
      ‖radialPairedCoefficient n s t K σ i‖ := by
  apply le_trans ?_ (norm_radialPairedCoefficient_lower n hn s t K σ i)
  unfold radialTupleCoefficientScale
  have hNpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hsqrtpos : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.2 hNpos
  have hsqrt : Real.sqrt ((n : ℝ) + 1) ≤ (n : ℝ) + 1 := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · nlinarith [sq_nonneg ((n : ℝ))]
  have hfrac : Real.exp (-2 * |s|) / ((n : ℝ) + 1) ≤
      Real.exp (-2 * |s|) / Real.sqrt ((n : ℝ) + 1) := by
    apply (div_le_div_iff₀ hNpos hsqrtpos).2
    gcongr
  simpa [Nat.cast_add, Nat.cast_one] using
    mul_le_mul_of_nonneg_right hfrac (norm_nonneg t)

lemma radialPaired_derivative_sum_le_scale
    {q : ℕ} (H n : ℕ) (s : ℝ) (t : ℂ)
    (K : Fin (2 * q) → Fin (n + 1)) (σ : Fin (2 * q) → Bool)
    (r : ℕ) (hr : r ≤ H) :
    (∑ j : Fin (2 * (activeTupleIndices K σ).card),
        (n : ℝ) ^ (r + 1) * ‖radialPairedCoefficient n s t K σ j‖) ≤
      radialTupleDerivativeScale q H n t := by
  let h := 2 * (activeTupleIndices K σ).card
  let B : ℝ := (n + 1 : ℝ) ^ (H + 1) * ((2 * q : ℕ) : ℝ) * ‖t‖
  have hpow : (n : ℝ) ^ (r + 1) ≤ (n + 1 : ℝ) ^ (H + 1) := by
    calc
      (n : ℝ) ^ (r + 1) ≤ (n + 1 : ℝ) ^ (r + 1) := by
        apply pow_le_pow_left₀ (by positivity)
        norm_num
      _ ≤ (n + 1 : ℝ) ^ (H + 1) := by
        exact pow_le_pow_right₀ (by norm_num) (by omega)
  calc
    (∑ j : Fin h, (n : ℝ) ^ (r + 1) *
        ‖radialPairedCoefficient n s t K σ j‖) ≤
        ∑ _j : Fin h, B := by
      apply Finset.sum_le_sum
      intro j hj
      dsimp [B]
      calc
        (n : ℝ) ^ (r + 1) * ‖radialPairedCoefficient n s t K σ j‖ ≤
            (n + 1 : ℝ) ^ (H + 1) * ((2 * q : ℕ) : ℝ) * ‖t‖ := by
          rw [mul_assoc]
          have hc : ‖radialPairedCoefficient n s t K σ j‖ ≤
              (((2 * q : ℕ) : ℝ)) * ‖t‖ := by
            simpa [Nat.cast_mul] using
              norm_radialPairedCoefficient_le n s t K σ j
          exact mul_le_mul hpow hc (norm_nonneg _) (by positivity)
        _ = _ := by ring
    _ = (h : ℝ) * B := by simp
    _ ≤ ((4 * q : ℕ) : ℝ) * B := by
      gcongr
      exact_mod_cast card_radialPairedFrequency_le K σ
    _ = radialTupleDerivativeScale q H n t := by
      unfold radialTupleDerivativeScale
      dsimp [B]
      push_cast
      ring

/-- Every nonexceptional radial tuple satisfies the automatic-mesh sparse
oscillation estimate as soon as its explicit finite-type scale is at least two. -/
theorem radial_oscillatoryIntegralNorm_le_autoMesh
    (q H n : ℕ) (hn : 0 < n) (hH : 4 * q + 1 ≤ H)
    (s : ℝ) {t : ℂ} (ht : t ≠ 0)
    (K : Fin (2 * q) → Fin (n + 1))
    (hK : K ∉ positiveEvenFiberTuples q (n + 1))
    (σ : Fin (2 * q) → Bool)
    (hdelta : 2 ≤ radialTupleFiniteTypeScale n s t K σ) :
    oscillatoryIntegralNorm circleParameterMeasure
        (fun k θ => 2 * radialCharacteristicPhase n s t
          (circleMap 0 1 θ) k) K σ ≤
      (4 * Real.pi * radialTupleDerivativeScale q H n t /
          radialTupleFiniteTypeScale n s t K σ + 2) *
        (5 * 2 ^ H) *
        (radialTupleFiniteTypeScale n s t K σ / 2) ^
          (-(1 : ℝ) / H) := by
  let h := 2 * (activeTupleIndices K σ).card
  have hactive : 0 < (activeTupleIndices K σ).card := by
    rw [Finset.card_pos]
    obtain ⟨k, hk, _⟩ := exists_activeTupleIndex_of_not_positiveEven q (n + 1) K hK σ
    exact ⟨k, hk⟩
  have hh : 0 < h := by dsimp [h]; omega
  let j₀ : Fin h := ⟨0, hh⟩
  have hhH : h + 1 ≤ H := by
    have hc := card_radialPairedFrequency_le K σ
    dsimp [h]
    omega
  rw [radial_oscillatoryIntegralNorm_eq_realExponentialSum]
  apply norm_integral_circleParameterMeasure_realExponentialSum_le_autoMesh
    H (by omega) hhH (radialPairedFrequency K σ)
      (radialPairedFrequency_injective K σ)
      (radialPairedFrequency_ne_zero K σ)
      (radialPairedFrequency_natAbs_le K σ)
      (radialPairedCoefficient n s t K σ) j₀
      (radialTupleCoefficientScale n s t)
      (radialTupleCoefficientScale_pos n s ht)
      (radialTupleCoefficientScale_le_paired n hn s t K σ j₀)
      (fun r x =>
        complexExponentialSumOrder_radialPaired_im_eq_zero r n s t K σ x)
      (radialTupleDerivativeScale q H n t)
      (radialTupleDerivativeScale_nonneg q H n t)
      (radialPaired_derivative_sum_le_scale H n s t K σ)
  simpa [radialTupleFiniteTypeScale, h] using hdelta

end Erdos522

end AmalgamatedModule45


/-! ===== amalgamated from Research.RadialTuplePolynomialScales ===== -/

section AmalgamatedModule46


open scoped BigOperators

namespace Erdos522

noncomputable def radialUniversalFiniteTypeScale
    (H n : ℕ) (s : ℝ) (t : ℂ) : ℝ :=
  Real.exp (-2 * |s|) * ‖t‖ /
    ((H : ℝ) * (H.factorial : ℝ) *
      (n + 1 : ℝ) ^ ((H + 1) * H + 1))

lemma sparseFiniteTypeDenominator_le
    (H h n : ℕ) (hhH : h ≤ H) :
    (h : ℝ) * (h.factorial : ℝ) * ((n + 1 : ℝ) ^ (h + 1)) ^ h ≤
      (H : ℝ) * (H.factorial : ℝ) *
        (n + 1 : ℝ) ^ ((H + 1) * H) := by
  have hhfac : h.factorial ≤ H.factorial := Nat.factorial_le hhH
  have hexp : (h + 1) * h ≤ (H + 1) * H := by nlinarith
  have hp : ((n + 1 : ℝ) ^ (h + 1)) ^ h ≤
      (n + 1 : ℝ) ^ ((H + 1) * H) := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) hexp
  gcongr

lemma radialUniversalFiniteTypeScale_pos
    (H n : ℕ) (hH : 0 < H) (s : ℝ) {t : ℂ} (ht : t ≠ 0) :
    0 < radialUniversalFiniteTypeScale H n s t := by
  unfold radialUniversalFiniteTypeScale
  positivity

/-- The tuple-dependent finite-type scale is uniformly bounded below by one
fixed monomial scale depending only on `H,n,s,‖t‖`. -/
lemma radialUniversalFiniteTypeScale_le_tuple
    {q : ℕ} (H n : ℕ) (s : ℝ) (t : ℂ)
    (K : Fin (2 * q) → Fin (n + 1)) (σ : Fin (2 * q) → Bool)
    (hactive : 0 < (activeTupleIndices K σ).card)
    (hhH : 2 * (activeTupleIndices K σ).card ≤ H) :
    radialUniversalFiniteTypeScale H n s t ≤
      radialTupleFiniteTypeScale n s t K σ := by
  let h := 2 * (activeTupleIndices K σ).card
  let N : ℝ := n + 1
  let u : ℝ := Real.exp (-2 * |s|) * ‖t‖
  let D : ℝ := (h : ℝ) * (h.factorial : ℝ) * (N ^ (h + 1)) ^ h
  let C : ℝ := (H : ℝ) * (H.factorial : ℝ)
  let E : ℕ := (H + 1) * H
  have hh : 0 < h := by dsimp [h]; omega
  have hH : 0 < H := lt_of_lt_of_le hh hhH
  have hN : 0 < N := by dsimp [N]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hbound : D ≤ C * N ^ E := by
    dsimp [D, C, E, N, h]
    exact sparseFiniteTypeDenominator_le H _ n hhH
  have hden : N * D ≤ C * N ^ (E + 1) := by
    calc
      N * D ≤ N * (C * N ^ E) := mul_le_mul_of_nonneg_left hbound hN.le
      _ = C * N ^ (E + 1) := by rw [pow_succ]; ring
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hdiv : u / (C * N ^ (E + 1)) ≤ u / (N * D) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    exact mul_le_mul_of_nonneg_left hden hu
  calc
    radialUniversalFiniteTypeScale H n s t =
        u / (C * N ^ (E + 1)) := by
      unfold radialUniversalFiniteTypeScale
      dsimp [u, C, N, E]
    _ ≤ u / (N * D) := hdiv
    _ = radialTupleFiniteTypeScale n s t K σ := by
      unfold radialTupleFiniteTypeScale radialTupleCoefficientScale
      dsimp [u, N, D, h]
      field_simp
      <;> ring

end Erdos522

end AmalgamatedModule46


/-! ===== amalgamated from Research.RadialTupleUniversalOscillation ===== -/

section AmalgamatedModule47


open MeasureTheory

namespace Erdos522

noncomputable def radialUniversalOscillationEnvelope
    (q H n : ℕ) (s : ℝ) (t : ℂ) : ℝ :=
  let δ := radialUniversalFiniteTypeScale H n s t
  (4 * Real.pi * radialTupleDerivativeScale q H n t / δ + 2) *
    (5 * 2 ^ H) * (δ / 2) ^ (-(1 : ℝ) / H)

lemma radialUniversalOscillationEnvelope_nonneg
    (q H n : ℕ) (s : ℝ) (t : ℂ) :
    0 ≤ radialUniversalOscillationEnvelope q H n s t := by
  have hU : 0 ≤ radialUniversalFiniteTypeScale H n s t := by
    unfold radialUniversalFiniteTypeScale
    positivity
  have hM : 0 ≤ radialTupleDerivativeScale q H n t :=
    radialTupleDerivativeScale_nonneg q H n t
  unfold radialUniversalOscillationEnvelope
  exact mul_nonneg
    (mul_nonneg
      (add_nonneg
        (div_nonneg (mul_nonneg (by positivity)
          hM) hU) (by norm_num))
      (by positivity))
    (Real.rpow_nonneg (by positivity) _)

/-- Once the universal monomial finite-type scale is at least two, it gives a
single oscillatory envelope valid for every nonexceptional tuple and sign
choice. -/
theorem radial_oscillatoryIntegralNorm_le_universalEnvelope
    (q H n : ℕ) (hn : 0 < n) (hH : 4 * q + 1 ≤ H)
    (s : ℝ) {t : ℂ} (ht : t ≠ 0)
    (hδ : 2 ≤ radialUniversalFiniteTypeScale H n s t)
    (K : Fin (2 * q) → Fin (n + 1))
    (hK : K ∉ positiveEvenFiberTuples q (n + 1))
    (σ : Fin (2 * q) → Bool) :
    oscillatoryIntegralNorm circleParameterMeasure
        (fun k θ => 2 * radialCharacteristicPhase n s t
          (circleMap 0 1 θ) k) K σ ≤
      radialUniversalOscillationEnvelope q H n s t := by
  have hactive : 0 < (activeTupleIndices K σ).card := by
    rw [Finset.card_pos]
    obtain ⟨k, hk, _⟩ := exists_activeTupleIndex_of_not_positiveEven
      q (n + 1) K hK σ
    exact ⟨k, hk⟩
  have hcard : 2 * (activeTupleIndices K σ).card ≤ H :=
    (card_radialPairedFrequency_le K σ).trans (by omega)
  have hUpos : 0 < radialUniversalFiniteTypeScale H n s t :=
    radialUniversalFiniteTypeScale_pos H n (by omega) s ht
  have hUδ : radialUniversalFiniteTypeScale H n s t ≤
      radialTupleFiniteTypeScale n s t K σ :=
    radialUniversalFiniteTypeScale_le_tuple H n s t K σ hactive hcard
  have htupleδ : 2 ≤ radialTupleFiniteTypeScale n s t K σ := hδ.trans hUδ
  have hraw := radial_oscillatoryIntegralNorm_le_autoMesh
    q H n hn hH s ht K hK σ htupleδ
  let U := radialUniversalFiniteTypeScale H n s t
  let δ := radialTupleFiniteTypeScale n s t K σ
  let M := radialTupleDerivativeScale q H n t
  have hδpos : 0 < δ := hUpos.trans_le hUδ
  have hM : 0 ≤ M := radialTupleDerivativeScale_nonneg q H n t
  have hratio : M / δ ≤ M / U :=
    div_le_div_of_nonneg_left hM hUpos hUδ
  have hfirst : 4 * Real.pi * M / δ + 2 ≤
      4 * Real.pi * M / U + 2 := by
    have hc : 0 ≤ 4 * Real.pi := by positivity
    rw [show 4 * Real.pi * M / δ = (4 * Real.pi) * (M / δ) by ring,
      show 4 * Real.pi * M / U = (4 * Real.pi) * (M / U) by ring]
    gcongr
  have hpow : (δ / 2) ^ (-(1 : ℝ) / H) ≤
      (U / 2) ^ (-(1 : ℝ) / H) := by
    apply Real.rpow_le_rpow_of_nonpos (by positivity)
    · exact div_le_div_of_nonneg_right hUδ (by norm_num)
    · exact div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity)
  calc
    _ ≤ (4 * Real.pi * M / δ + 2) * (5 * 2 ^ H) *
        (δ / 2) ^ (-(1 : ℝ) / H) := by
      simpa [M, δ] using hraw
    _ ≤ (4 * Real.pi * M / U + 2) * (5 * 2 ^ H) *
        (U / 2) ^ (-(1 : ℝ) / H) := by
      gcongr
    _ = radialUniversalOscillationEnvelope q H n s t := by
      rfl

end Erdos522

end AmalgamatedModule47


/-! ===== amalgamated from Research.RadialOscillationPolynomialEnvelope ===== -/

section AmalgamatedModule48


namespace Erdos522

noncomputable def radialOscillationRatioConstant
    (q H : ℕ) (s : ℝ) : ℝ :=
  (8 * q ^ 2 : ℝ) * (H : ℝ) * (H.factorial : ℝ) *
    Real.exp (2 * |s|)

noncomputable def radialOscillationPowerConstant (H : ℕ) (s : ℝ) : ℝ :=
  (2 * (H : ℝ) * (H.factorial : ℝ) * Real.exp (2 * |s|)) ^
    ((1 : ℝ) / H)

noncomputable def radialOscillationPolynomialConstant
    (q H : ℕ) (s : ℝ) : ℝ :=
  (4 * Real.pi * radialOscillationRatioConstant q H s + 2) *
    (5 * 2 ^ H) * radialOscillationPowerConstant H s

def radialOscillationPolynomialExponent (H : ℕ) : ℕ :=
  H + 1 + 2 * ((H + 1) * H + 1)

lemma radialOscillationPolynomialConstant_nonneg (q H : ℕ) (s : ℝ) :
    0 ≤ radialOscillationPolynomialConstant q H s := by
  unfold radialOscillationPolynomialConstant radialOscillationRatioConstant
    radialOscillationPowerConstant
  positivity

lemma radialDerivative_div_universalScale
    (q H n : ℕ) (hH : 0 < H) (s : ℝ) {t : ℂ} (ht : t ≠ 0) :
    radialTupleDerivativeScale q H n t /
        radialUniversalFiniteTypeScale H n s t =
      radialOscillationRatioConstant q H s *
        (n + 1 : ℝ) ^ (H + 1 + ((H + 1) * H + 1)) := by
  have ht' : ‖t‖ ≠ 0 := norm_ne_zero_iff.mpr ht
  have hfac : (H.factorial : ℝ) ≠ 0 := by positivity
  have he : Real.exp (-(2 * |s|)) * Real.exp (2 * |s|) = 1 := by
    rw [← Real.exp_add]
    simp
  unfold radialTupleDerivativeScale radialUniversalFiniteTypeScale
    radialOscillationRatioConstant
  field_simp
  rw [show (n + 1 : ℝ) ^ (H + 1 + ((H + 1) * H + 1)) =
    (n + 1 : ℝ) ^ (H + 1) * (n + 1 : ℝ) ^ ((H + 1) * H + 1) by
      rw [pow_add]]
  rw [show (n + 1 : ℝ) ^ (H + 1) =
    (n + 1 : ℝ) ^ H * (n + 1 : ℝ) by rw [pow_succ]]
  ring_nf at he ⊢
  rw [he]
  ring

lemma radialUniversalScale_negativePower
    (H n : ℕ) (hH : 0 < H) (s : ℝ) {t : ℂ} (ht : t ≠ 0) :
    (radialUniversalFiniteTypeScale H n s t / 2) ^
        (-(1 : ℝ) / H) =
      radialOscillationPowerConstant H s *
        ((n + 1 : ℝ) ^ ((H + 1) * H + 1)) ^ ((1 : ℝ) / H) *
        (‖t‖⁻¹) ^ ((1 : ℝ) / H) := by
  let U := radialUniversalFiniteTypeScale H n s t
  let N : ℝ := n + 1
  let B : ℕ := (H + 1) * H + 1
  let C : ℝ := 2 * (H : ℝ) * (H.factorial : ℝ) * Real.exp (2 * |s|)
  have ht' : ‖t‖ ≠ 0 := norm_ne_zero_iff.mpr ht
  have hH' : (H : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hH)
  have hU : 0 ≤ U := by
    dsimp [U]
    unfold radialUniversalFiniteTypeScale
    positivity
  have hinv : (U / 2)⁻¹ = C * N ^ B * ‖t‖⁻¹ := by
    dsimp [U, C, N, B]
    unfold radialUniversalFiniteTypeScale
    have he : Real.exp (-(2 * |s|)) * Real.exp (2 * |s|) = 1 := by
      rw [← Real.exp_add]
      simp
    field_simp
    ring_nf at he ⊢
    rw [he]
  have hexp : (-(1 : ℝ) / H) = -((1 : ℝ) / H) := by ring
  rw [hexp, Real.rpow_neg (div_nonneg hU (by norm_num))]
  rw [← Real.inv_rpow (div_nonneg hU (by norm_num))]
  rw [hinv]
  rw [Real.mul_rpow (mul_nonneg (by positivity) (by positivity))
    (inv_nonneg.mpr (norm_nonneg t))]
  rw [Real.mul_rpow (by positivity) (by positivity)]
  rfl

lemma radialDegreePower_rpow_le
    (H n : ℕ) (hH : 0 < H) :
    ((n + 1 : ℝ) ^ ((H + 1) * H + 1)) ^ ((1 : ℝ) / H) ≤
      (n + 1 : ℝ) ^ ((H + 1) * H + 1) := by
  apply Real.rpow_le_self_of_one_le
  · exact one_le_pow₀ (by norm_num)
  · apply (div_le_one (by positivity)).2
    exact_mod_cast hH

/-- The tuple-uniform F-128 envelope is a fixed polynomial in degree times the
required fractional inverse-frequency power. -/
theorem radialUniversalOscillationEnvelope_le_polynomial
    (q H n : ℕ) (hH : 0 < H) (s : ℝ) {t : ℂ} (ht : t ≠ 0) :
    radialUniversalOscillationEnvelope q H n s t ≤
      radialOscillationPolynomialConstant q H s *
        (n + 1 : ℝ) ^ (radialOscillationPolynomialExponent H) *
        (‖t‖⁻¹) ^ ((1 : ℝ) / H) := by
  let N : ℝ := n + 1
  let B : ℕ := (H + 1) * H + 1
  let R : ℕ := H + 1 + B
  let Q : ℝ := radialOscillationRatioConstant q H s
  let P : ℝ := radialOscillationPowerConstant H s
  have hN : 1 ≤ N := by dsimp [N]; norm_num
  have hNB : 1 ≤ N ^ B := one_le_pow₀ hN
  have hQ : 0 ≤ Q := by dsimp [Q, radialOscillationRatioConstant]; positivity
  have hP : 0 ≤ P := by dsimp [P, radialOscillationPowerConstant]; positivity
  have hT : 0 ≤ (‖t‖⁻¹) ^ ((1 : ℝ) / H) := Real.rpow_nonneg (by positivity) _
  have hratio := radialDerivative_div_universalScale q H n hH s ht
  have hpower := radialUniversalScale_negativePower H n hH s ht
  have hdegree := radialDegreePower_rpow_le H n hH
  simp only [radialUniversalOscillationEnvelope]
  rw [show 4 * Real.pi * radialTupleDerivativeScale q H n t /
      radialUniversalFiniteTypeScale H n s t =
      (4 * Real.pi) * (radialTupleDerivativeScale q H n t /
        radialUniversalFiniteTypeScale H n s t) by ring,
    hratio, hpower]
  change (4 * Real.pi * (Q * N ^ R) + 2) * (5 * 2 ^ H) *
      (P * (N ^ B) ^ ((1 : ℝ) / H) * (‖t‖⁻¹) ^ ((1 : ℝ) / H)) ≤ _
  have hfirst : 4 * Real.pi * (Q * N ^ R) + 2 ≤
      (4 * Real.pi * Q + 2) * N ^ R := by
    calc
      _ ≤ 4 * Real.pi * (Q * N ^ R) + 2 * N ^ R := by
        have hNR : 1 ≤ N ^ R := one_le_pow₀ hN
        gcongr
        nlinarith
      _ = _ := by ring
  calc
    _ ≤ ((4 * Real.pi * Q + 2) * N ^ R) * (5 * 2 ^ H) *
        (P * (N ^ B) * (‖t‖⁻¹) ^ ((1 : ℝ) / H)) := by
      gcongr
    _ = radialOscillationPolynomialConstant q H s *
        N ^ (R + B) * (‖t‖⁻¹) ^ ((1 : ℝ) / H) := by
      unfold radialOscillationPolynomialConstant
      dsimp [Q, P]
      rw [pow_add]
      ring
    _ = _ := by
      congr 2
      congr 1
      unfold radialOscillationPolynomialExponent
      dsimp [R, B]
      omega

end Erdos522

end AmalgamatedModule48


/-! ===== amalgamated from Research.RadialNonexceptionalOscillation ===== -/

section AmalgamatedModule49


open MeasureTheory

namespace Erdos522

lemma one_le_radialUniversalOscillationEnvelope_of_scale_le_two
    (q H n : ℕ) (hH : 0 < H) (s : ℝ) {t : ℂ} (ht : t ≠ 0)
    (hUtwo : radialUniversalFiniteTypeScale H n s t ≤ 2) :
    1 ≤ radialUniversalOscillationEnvelope q H n s t := by
  let U := radialUniversalFiniteTypeScale H n s t
  let M := radialTupleDerivativeScale q H n t
  have hU : 0 < U := radialUniversalFiniteTypeScale_pos H n hH s ht
  have hM : 0 ≤ M := radialTupleDerivativeScale_nonneg q H n t
  have hfirst : 1 ≤ 4 * Real.pi * M / U + 2 := by
    have : 0 ≤ 4 * Real.pi * M / U := by positivity
    linarith
  have hmiddle : 1 ≤ (5 * 2 ^ H : ℝ) := by
    have hp : (1 : ℝ) ≤ 2 ^ H := one_le_pow₀ (by norm_num)
    nlinarith
  have hbase : 0 < U / 2 := by positivity
  have hbaseOne : U / 2 ≤ 1 := (div_le_one (by norm_num)).2 hUtwo
  have hexp : (-(1 : ℝ) / H) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity)
  have hlast : 1 ≤ (U / 2) ^ (-(1 : ℝ) / H) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hbase hbaseOne hexp
  unfold radialUniversalOscillationEnvelope
  exact one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le hfirst hmiddle) hlast

/-- The high-frequency van der Corput estimate and the low-frequency trivial
bound combine into one polynomial fractional-decay estimate, uniformly over
all nonexceptional tuples. -/
theorem radial_nonexceptional_oscillatoryIntegralNorm_le_polynomial
    (q H n : ℕ) (hn : 0 < n) (hH : 4 * q + 1 ≤ H)
    (s : ℝ) {t : ℂ} (ht : t ≠ 0)
    (K : Fin (2 * q) → Fin (n + 1))
    (hK : K ∉ positiveEvenFiberTuples q (n + 1))
    (σ : Fin (2 * q) → Bool) :
    oscillatoryIntegralNorm circleParameterMeasure
        (fun k θ => 2 * radialCharacteristicPhase n s t
          (circleMap 0 1 θ) k) K σ ≤
      radialOscillationPolynomialConstant q H s *
        (n + 1 : ℝ) ^ (radialOscillationPolynomialExponent H) *
        (‖t‖⁻¹) ^ ((1 : ℝ) / H) := by
  have hHpos : 0 < H := by omega
  have hpoly := radialUniversalOscillationEnvelope_le_polynomial
    q H n hHpos s ht
  by_cases hU : 2 ≤ radialUniversalFiniteTypeScale H n s t
  · exact (radial_oscillatoryIntegralNorm_le_universalEnvelope
      q H n hn hH s ht hU K hK σ).trans hpoly
  · have htriv := oscillatoryIntegralNorm_le_one circleParameterMeasure
      (fun k θ => 2 * radialCharacteristicPhase n s t
        (circleMap 0 1 θ) k) K σ
    have henv : 1 ≤ radialUniversalOscillationEnvelope q H n s t :=
      one_le_radialUniversalOscillationEnvelope_of_scale_le_two
        q H n hHpos s ht (le_of_not_ge hU)
    exact htriv.trans (henv.trans hpoly)

end Erdos522

end AmalgamatedModule49


/-! ===== amalgamated from Research.RadialCosineMomentPolynomial ===== -/

section AmalgamatedModule50


open MeasureTheory
open scoped BigOperators

namespace Erdos522

lemma continuous_radial_doubleCharacteristicPhase
    (n : ℕ) (s : ℝ) (t : ℂ) (k : Fin (n + 1)) :
    Continuous (fun θ : ℝ => 2 * radialCharacteristicPhase n s t
      (circleMap 0 1 θ) k) := by
  dsimp [radialCharacteristicPhase, radialCircleCoefficient]
  fun_prop

/-- A uniform bound for all nonexceptional tuple integrals gives the normalized
high cosine moment with the exceptional `N^{-q}` term and the same error. -/
theorem normalized_radialCosineSumMoment_le_exceptional_add
    (q n : ℕ) (s : ℝ) (t : ℂ) (E : ℝ) (hE : 0 ≤ E)
    (hnon : ∀ (K : Fin (2 * q) → Fin (n + 1)),
      K ∉ positiveEvenFiberTuples q (n + 1) →
      ∀ σ : Fin (2 * q) → Bool,
        oscillatoryIntegralNorm circleParameterMeasure
          (fun k θ => 2 * radialCharacteristicPhase n s t
            (circleMap 0 1 θ) k) K σ ≤ E) :
    (2 / (n + 1 : ℝ)) ^ (2 * q) * radialCosineSumMoment n s t q ≤
      (2 : ℝ) ^ (4 * q) *
        (((((q + 1) ^ (2 * q + 1) : ℕ) : ℝ)) *
            (((n + 1 : ℝ)⁻¹) ^ q) + E) := by
  let a : Fin (n + 1) → ℝ → ℝ := fun k θ =>
    2 * radialCharacteristicPhase n s t (circleMap 0 1 θ) k
  have hmom := integral_abs_cosineSum_pow_le_positiveExceptional_add
    circleParameterMeasure q (n + 1) (by omega) a
      (fun k => continuous_radial_doubleCharacteristicPhase n s t k)
      E hE hnon
  have hid : radialCosineSumMoment n s t q =
      ∫ θ, |∑ k : Fin (n + 1), Real.cos (a k θ)| ^ (2 * q)
        ∂circleParameterMeasure := by
    unfold radialCosineSumMoment
    rw [circleAverage_eq_integral_circleParameterMeasure]
    rfl
  rw [hid]
  let C : ℝ := (((q + 1) ^ (2 * q + 1) : ℕ) : ℝ)
  let N : ℝ := n + 1
  have hN : N ≠ 0 := by dsimp [N]; positivity
  calc
    (2 / N) ^ (2 * q) *
        (∫ θ, |∑ k : Fin (n + 1), Real.cos (a k θ)| ^ (2 * q)
          ∂circleParameterMeasure) ≤
      (2 / N) ^ (2 * q) *
        ((2 : ℝ) ^ (2 * q) *
          (C * N ^ q + N ^ (2 * q) * E)) := by
      gcongr
      simpa [a, C, N] using hmom
    _ = (2 : ℝ) ^ (4 * q) * (C * (N⁻¹) ^ q + E) := by
      rw [div_pow]
      rw [show N ^ (2 * q) = N ^ q * N ^ q by
        rw [show 2 * q = q + q by omega, pow_add]]
      rw [inv_pow]
      field_simp
      ring
    _ = _ := by rfl

/-- F-130 supplies the nonexceptional error in the preceding moment estimate. -/
theorem normalized_radialCosineSumMoment_le_polynomial
    (q H n : ℕ) (hn : 0 < n) (hH : 4 * q + 1 ≤ H)
    (s : ℝ) {t : ℂ} (ht : t ≠ 0) :
    (2 / (n + 1 : ℝ)) ^ (2 * q) * radialCosineSumMoment n s t q ≤
      (2 : ℝ) ^ (4 * q) *
        (((((q + 1) ^ (2 * q + 1) : ℕ) : ℝ)) *
            (((n + 1 : ℝ)⁻¹) ^ q) +
          radialOscillationPolynomialConstant q H s *
            (n + 1 : ℝ) ^ (radialOscillationPolynomialExponent H) *
            (‖t‖⁻¹) ^ ((1 : ℝ) / H)) := by
  apply normalized_radialCosineSumMoment_le_exceptional_add
  · exact mul_nonneg
      (mul_nonneg (radialOscillationPolynomialConstant_nonneg q H s)
        (pow_nonneg (by positivity) _))
      (Real.rpow_nonneg (by positivity) _)
  · intro K hK σ
    exact radial_nonexceptional_oscillatoryIntegralNorm_le_polynomial
      q H n hn hH s ht K hK σ

end Erdos522

end AmalgamatedModule50


/-! ===== amalgamated from Research.AnnealedCharacteristicConvergence ===== -/

section AmalgamatedModule51


open Filter Topology

namespace Erdos522

/-- For every fixed radial shift and scalar projection, the sign-angle
characteristic function converges to that of the variance-one circular complex
Gaussian. -/
theorem tendsto_radialAnnealedCharacteristic
    (s : ℝ) (t : ℂ) :
    Tendsto (fun n : ℕ => radialAnnealedCharacteristic n s t) atTop
      (𝓝 (circularGaussianCharacteristic t)) := by
  let B : ℕ → ℝ := fun n => Real.exp (4 * |s|) / (n + 1 : ℝ)
  let b : ℕ → ℝ := fun n => Real.sqrt (B n)
  let err : ℕ → ℝ := fun n =>
    (7 / 24 : ℝ) * (‖t‖ * b n) ^ 2 * ‖t‖ ^ 2 + ‖t‖ ^ 2 / 4 * b n
  have hden : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hB : Tendsto B atTop (𝓝 0) := by
    dsimp [B]
    exact tendsto_const_nhds.div_atTop hden
  have hb : Tendsto b atTop (𝓝 0) := by
    have := hB.sqrt
    simpa [b] using this
  have htb : Tendsto (fun n => ‖t‖ * b n) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hb
  have hsq : Tendsto (fun n => (‖t‖ * b n) ^ 2) atTop (𝓝 0) := by
    simpa using htb.pow 2
  have hfirst : Tendsto
      (fun n => (7 / 24 : ℝ) * (‖t‖ * b n) ^ 2 * ‖t‖ ^ 2)
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hsq).mul tendsto_const_nhds
  have hsecond : Tendsto (fun n => ‖t‖ ^ 2 / 4 * b n)
      atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hb
  have herr : Tendsto err atTop (𝓝 0) := by
    simpa [err] using hfirst.add hsecond
  have hsmall : ∀ᶠ n : ℕ in atTop, ‖t‖ * b n ≤ 1 := by
    have hlt := (tendsto_order.1 htb).2 1 (by norm_num)
    exact hlt.mono fun n hn => hn.le
  have hnpos : ∀ᶠ n : ℕ in atTop, 0 < n := by
    exact eventually_atTop.2 ⟨1, fun n hn => Nat.zero_lt_of_lt hn⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun n => norm_nonneg _
  · filter_upwards [hnpos, hsmall] with n hn hs
    exact norm_radialAnnealedCharacteristic_sub_circular_le n hn s t hs
  · exact herr

end Erdos522

end AmalgamatedModule51


/-! ===== amalgamated from Research.AnnealedLaw ===== -/

section AmalgamatedModule52


open MeasureTheory Filter Topology ProbabilityTheory
open scoped BigOperators ComplexConjugate

namespace Erdos522

/-- Canonical uniform probability measure on a finite Boolean cube. -/
noncomputable def uniformCubeProbabilityMeasure (N : ℕ) :
    ProbabilityMeasure (Fin N → Bool) :=
  ⟨(PMF.uniformOfFintype (Fin N → Bool)).toMeasure, inferInstance⟩

/-- Product of the normalized angular parameter and the finite uniform cube. -/
noncomputable def radialAnnealedSourceMeasure (n : ℕ) :
    ProbabilityMeasure (ℝ × (Fin (n + 1) → Bool)) :=
  ⟨circleParameterMeasure.prod (uniformCubeProbabilityMeasure (n + 1) :
      Measure (Fin (n + 1) → Bool)), inferInstance⟩

/-- Joint sign-angle normalized radial Fourier sum. -/
noncomputable def radialAnnealedValue
    (n : ℕ) (s : ℝ) (u : ℝ × (Fin (n + 1) → Bool)) : ℂ :=
  ∑ k : Fin (n + 1),
    (realRademacherSign (u.2 k) : ℂ) *
      radialCircleCoefficient n s (circleMap 0 1 u.1) k

lemma continuous_radialAnnealedValue (n : ℕ) (s : ℝ) :
    Continuous (radialAnnealedValue n s) := by
  unfold radialAnnealedValue radialCircleCoefficient
  apply continuous_finset_sum
  intro k hk
  apply Continuous.mul
  · exact (continuous_of_discreteTopology : Continuous
      (fun x : Fin (n + 1) → Bool =>
        (realRademacherSign (x k) : ℂ))).comp continuous_snd
  · fun_prop

/-- The annealed law of the normalized radial Littlewood value. -/
noncomputable def radialAnnealedLaw (n : ℕ) (s : ℝ) : ProbabilityMeasure ℂ :=
  (radialAnnealedSourceMeasure n).map
    (continuous_radialAnnealedValue n s).aemeasurable

/-- Standard Gaussian probability measure on the real Euclidean plane `ℂ`. -/
noncomputable def standardComplexGaussianLaw : ProbabilityMeasure ℂ :=
  ⟨stdGaussian ℂ, inferInstance⟩

/-- Circular complex Gaussian law normalized by `E‖G‖²=1`. -/
noncomputable def circularGaussianLaw : ProbabilityMeasure ℂ :=
  standardComplexGaussianLaw.map
    (by fun_prop : AEMeasurable (fun z : ℂ => (Real.sqrt 2)⁻¹ • z)
      standardComplexGaussianLaw)

lemma integral_uniformCube_eq_cubeComplexAverage
    (N : ℕ) (F : (Fin N → Bool) → ℂ) :
    ∫ x, F x ∂(uniformCubeProbabilityMeasure N :
      Measure (Fin N → Bool)) = cubeComplexAverage F := by
  change ∫ x, F x ∂(PMF.uniformOfFintype (Fin N → Bool)).toMeasure = _
  rw [PMF.integral_eq_sum]
  unfold cubeComplexAverage
  simp_rw [PMF.uniformOfFintype_apply]
  simp only [Fintype.card_pi, Fintype.card_bool,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, Complex.real_smul]
  rw [← Finset.mul_sum]
  push_cast
  ring

lemma charFun_circularGaussianLaw (t : ℂ) :
    charFun (circularGaussianLaw : ProbabilityMeasure ℂ) t =
      circularGaussianCharacteristic t := by
  unfold circularGaussianLaw
  rw [ProbabilityMeasure.toMeasure_map, charFun_map_smul]
  change charFun (stdGaussian ℂ) ((Real.sqrt 2)⁻¹ • t) = _
  rw [charFun_stdGaussian]
  unfold circularGaussianCharacteristic
  rw [Complex.ofReal_exp]
  congr 1
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)))]
  have hsqrt : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsqrt_ne : Real.sqrt 2 ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hreal : -(((Real.sqrt 2)⁻¹ * ‖t‖) ^ 2) / 2 = -‖t‖ ^ 2 / 4 := by
    field_simp [hsqrt_ne]
    nlinarith
  exact_mod_cast hreal

lemma charFun_radialAnnealedLaw (n : ℕ) (s : ℝ) (t : ℂ) :
    charFun (radialAnnealedLaw n s : ProbabilityMeasure ℂ) t =
      radialAnnealedCharacteristic n s t := by
  unfold radialAnnealedLaw
  rw [charFun_apply, ProbabilityMeasure.toMeasure_map]
  rw [integral_map
    (continuous_radialAnnealedValue n s).aemeasurable (by fun_prop)]
  let f : ℝ × (Fin (n + 1) → Bool) → ℂ := fun u =>
    Complex.exp ((inner ℝ (radialAnnealedValue n s u) t : ℝ) * Complex.I)
  have hfint : Integrable f
      (circleParameterMeasure.prod
        (uniformCubeProbabilityMeasure (n + 1) :
          Measure (Fin (n + 1) → Bool))) := by
    have hi : Continuous (fun u =>
        inner ℝ (radialAnnealedValue n s u) t) :=
      (continuous_radialAnnealedValue n s).inner continuous_const
    have hfcont : Continuous f := by
      dsimp [f]
      exact Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp hi).mul continuous_const)
    apply Integrable.of_bound hfcont.aestronglyMeasurable 1
    filter_upwards with u
    simp [f, Complex.norm_exp]
  rw [show (↑(radialAnnealedSourceMeasure n) :
      Measure (ℝ × (Fin (n + 1) → Bool))) =
      circleParameterMeasure.prod
        (uniformCubeProbabilityMeasure (n + 1) :
          Measure (Fin (n + 1) → Bool)) by rfl]
  rw [integral_prod f hfint]
  unfold radialAnnealedCharacteristic
  rw [circleAverage_eq_integral_circleParameterMeasure_complex]
  apply integral_congr_ae
  filter_upwards with θ
  rw [integral_uniformCube_eq_cubeComplexAverage]
  unfold radialCubeCharacteristicAt
  congr 1
  funext x
  dsimp [f, radialAnnealedValue]
  congr 1
  push_cast
  simp [Complex.mul_re]
  ring

/-- Lévy convergence upgrades F-044 to weak convergence of the complete
annealed laws. -/
theorem tendsto_radialAnnealedLaw (s : ℝ) :
    Tendsto (fun n => radialAnnealedLaw n s) atTop
      (𝓝 circularGaussianLaw) := by
  rw [ProbabilityMeasure.tendsto_iff_tendsto_charFun]
  intro t
  simpa [charFun_radialAnnealedLaw, charFun_circularGaussianLaw] using
    tendsto_radialAnnealedCharacteristic s t

end Erdos522

end AmalgamatedModule52


/-! ===== amalgamated from Research.RadialCubeStatistic ===== -/

section AmalgamatedModule53


open scoped BigOperators

namespace Erdos522

/-- An arbitrary planar test averaged over the normalized radial polynomial,
viewed as a function on the finite sign cube. -/
noncomputable def radialCubeAngularStatistic
    (n : ℕ) (s : ℝ) (h : ℂ → ℝ) (x : Fin (n + 1) → Bool) : ℝ :=
  angularStatistic h
    (weightedVectorPolynomial
      (fun k : Fin (n + 1) => radialWeight n s k)
      (fun k : Fin (n + 1) => realRademacherSign (x k)))

/-- Exact Hamming modulus for every Lipschitz planar test. -/
theorem radialCubeAngularStatistic_dist_le
    (n : ℕ) (hn : 0 < n) (s : ℝ) (h : ℂ → ℝ)
    {K : NNReal} (hK : LipschitzWith K h)
    (x y : Fin (n + 1) → Bool) :
    |radialCubeAngularStatistic n s h x -
      radialCubeAngularStatistic n s h y| ≤
      (K : ℝ) * √((Real.exp (4 * |s|) / (n + 1 : ℝ)) *
        (4 * (hammingDist x y : ℝ))) := by
  unfold radialCubeAngularStatistic
  have hbound := weightedVectorPolynomial_angular_lipschitz h hK
    (fun k : Fin (n + 1) => radialWeight n s k)
    (fun k : Fin (n + 1) => realRademacherSign (x k))
    (fun k : Fin (n + 1) => realRademacherSign (y k))
    (Real.exp (4 * |s|) / (n + 1 : ℝ))
    (fun k => radialWeight_nonneg n s k)
    (fun k => radialWeight_le n hn s (Finset.mem_range.mpr k.isLt))
  rw [sum_sq_realRademacherSign_sub_eq_hamming] at hbound
  exact hbound

/-- The clipped angular statistic as an explicit function on the finite Boolean
cube of the first `n+1` signs. -/
noncomputable def radialCubeClippedStatistic
    (n : ℕ) (s : ℝ) (M : NNReal) (x : Fin (n + 1) → Bool) : ℝ :=
  angularStatistic (clippedLog M)
    (weightedVectorPolynomial
      (fun k : Fin (n + 1) => radialWeight n s k)
      (fun k : Fin (n + 1) => realRademacherSign (x k)))

/-- Exact Hamming modulus of continuity for the clipped radial statistic. -/
theorem radialCubeClippedStatistic_dist_le
    (n : ℕ) (hn : 0 < n) (s : ℝ) (M : NNReal) (hM : 1 ≤ M)
    (x y : Fin (n + 1) → Bool) :
    |radialCubeClippedStatistic n s M x -
      radialCubeClippedStatistic n s M y| ≤
      (M : ℝ) * √((Real.exp (4 * |s|) / (n + 1 : ℝ)) *
        (4 * (hammingDist x y : ℝ))) := by
  unfold radialCubeClippedStatistic
  have h := clippedLog_weightedVectorPolynomial_lipschitz
    (fun k : Fin (n + 1) => radialWeight n s k)
    (fun k : Fin (n + 1) => realRademacherSign (x k))
    (fun k : Fin (n + 1) => realRademacherSign (y k))
    (Real.exp (4 * |s|) / (n + 1 : ℝ)) M hM
    (fun k => radialWeight_nonneg n s k)
    (fun k => radialWeight_le n hn s (Finset.mem_range.mpr k.isLt))
  rw [sum_sq_realRademacherSign_sub_eq_hamming] at h
  exact h

end Erdos522

end AmalgamatedModule53


/-! ===== amalgamated from Research.CubeMcDiarmid ===== -/

section AmalgamatedModule54


open scoped BigOperators

namespace Erdos522

/-- A bounded-differences condition expressed using adjacency in Hamming
metric. -/
def CubeBoundedDifferences {N : ℕ} (c : ℝ)
    (F : (Fin N → Bool) → ℝ) : Prop :=
  ∀ x y, hammingDist x y ≤ 1 → |F x - F y| ≤ c

lemma hammingDist_cons_same {N : ℕ} (b : Bool) (x y : Fin N → Bool) :
    hammingDist
      (Fin.cons (α := fun _ : Fin (N + 1) => Bool) b x)
      (Fin.cons (α := fun _ : Fin (N + 1) => Bool) b y) =
      hammingDist x y := by
  classical
  unfold hammingDist
  rw [Finset.card_filter, Fin.sum_univ_succ, Finset.card_filter]
  simp

lemma hammingDist_cons_ne {N : ℕ} (x : Fin N → Bool) :
    hammingDist
      (Fin.cons (α := fun _ : Fin (N + 1) => Bool) true x)
      (Fin.cons (α := fun _ : Fin (N + 1) => Bool) false x) = 1 := by
  classical
  unfold hammingDist
  rw [Finset.card_filter, Fin.sum_univ_succ]
  simp

lemma CubeBoundedDifferences.slice {N : ℕ} {c : ℝ}
    {F : (Fin (N + 1) → Bool) → ℝ} (hF : CubeBoundedDifferences c F)
    (b : Bool) :
    CubeBoundedDifferences c (fun x : Fin N → Bool => F (Fin.cons b x)) := by
  intro x y hxy
  apply hF
  rw [hammingDist_cons_same]
  exact hxy

lemma CubeBoundedDifferences.abs_average_slices_sub_le {N : ℕ} {c : ℝ}
    {F : (Fin (N + 1) → Bool) → ℝ} (hF : CubeBoundedDifferences c F) :
    |cubeAverage (fun x : Fin N → Bool => F (Fin.cons true x)) -
      cubeAverage (fun x : Fin N → Bool => F (Fin.cons false x))| ≤ c := by
  apply abs_cubeAverage_sub_le_of_pointwise
  intro x
  exact hF _ _ (by rw [hammingDist_cons_ne])

lemma cubeAverage_exp_center_change {N : ℕ}
    (F : (Fin N → Bool) → ℝ) (m t : ℝ) :
    cubeAverage (fun x => Real.exp (t * (F x - m))) =
      Real.exp (t * (cubeAverage F - m)) *
        cubeAverage (fun x => Real.exp (t * (F x - cubeAverage F))) := by
  rw [← cubeAverage_const_mul]
  apply congrArg cubeAverage
  funext x
  rw [← Real.exp_add]
  congr 1
  ring

/-- Hoeffding's exponential-moment estimate on the finite Boolean cube,
proved by recursively splitting the head bit. -/
theorem cubeAverage_exp_centered_le
    (N : ℕ) (c : ℝ) (hc : 0 ≤ c)
    (F : (Fin N → Bool) → ℝ) (hF : CubeBoundedDifferences c F)
    (t : ℝ) :
    cubeAverage (fun x => Real.exp (t * (F x - cubeAverage F))) ≤
      Real.exp (t ^ 2 * c ^ 2 * N / 8) := by
  induction N with
  | zero =>
      simp
  | succ N ih =>
      let FT : (Fin N → Bool) → ℝ := fun x => F (Fin.cons true x)
      let FF : (Fin N → Bool) → ℝ := fun x => F (Fin.cons false x)
      let mT := cubeAverage FT
      let mF := cubeAverage FF
      let m := (mT + mF) / 2
      have hFT : CubeBoundedDifferences c FT := hF.slice true
      have hFF : CubeBoundedDifferences c FF := hF.slice false
      have hiT := ih FT hFT
      have hiF := ih FF hFF
      have hm : cubeAverage F = m := by
        rw [cubeAverage_succ]
      have hmean : |mT - mF| ≤ c := hF.abs_average_slices_sub_le
      rw [cubeAverage_succ]
      rw [hm]
      rw [cubeAverage_exp_center_change FT m t,
        cubeAverage_exp_center_change FF m t]
      change (Real.exp (t * (mT - m)) *
          cubeAverage (fun x => Real.exp (t * (FT x - mT))) +
        Real.exp (t * (mF - m)) *
          cubeAverage (fun x => Real.exp (t * (FF x - mF)))) / 2 ≤ _
      calc
        _ ≤ (Real.exp (t * (mT - m)) *
              Real.exp (t ^ 2 * c ^ 2 * N / 8) +
            Real.exp (t * (mF - m)) *
              Real.exp (t ^ 2 * c ^ 2 * N / 8)) / 2 := by
          gcongr
        _ = Real.exp (t ^ 2 * c ^ 2 * N / 8) *
            Real.cosh (t * (mT - mF) / 2) := by
          rw [show t * (mT - m) = t * (mT - mF) / 2 by
            dsimp [m]; ring,
            show t * (mF - m) = -(t * (mT - mF) / 2) by
              dsimp [m]; ring,
            Real.cosh_eq]
          ring
        _ ≤ Real.exp (t ^ 2 * c ^ 2 * N / 8) *
            Real.exp ((t * (mT - mF) / 2) ^ 2 / 2) := by
          gcongr
          exact Real.cosh_le_exp_half_sq _
        _ ≤ Real.exp (t ^ 2 * c ^ 2 * N / 8) *
            Real.exp (t ^ 2 * c ^ 2 / 8) := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
          apply Real.exp_le_exp.mpr
          have hsq : (mT - mF) ^ 2 ≤ c ^ 2 :=
            (sq_le_sq).mpr (by simpa [abs_of_nonneg hc] using hmean)
          have hmul := mul_le_mul_of_nonneg_left hsq (sq_nonneg t)
          nlinarith
        _ = Real.exp (t ^ 2 * c ^ 2 * (↑(N + 1) : ℝ) / 8) := by
          rw [← Real.exp_add]
          congr 1
          norm_num [Nat.cast_add, Nat.cast_one]
          ring

/-- Uniform finite-cube probability of a set, expressed as an average of its
indicator. -/
noncomputable def cubeProbability {N : ℕ} (A : Set (Fin N → Bool)) : ℝ := by
  classical
  exact cubeAverage (fun x => if x ∈ A then 1 else 0)

/-- McDiarmid's upper-tail inequality on the uniform Boolean cube. -/
theorem cubeProbability_centered_ge_le
    {N : ℕ} (hN : 0 < N) {c u : ℝ} (hc : 0 < c) (hu : 0 ≤ u)
    (F : (Fin N → Bool) → ℝ) (hF : CubeBoundedDifferences c F) :
    cubeProbability {x | u ≤ F x - cubeAverage F} ≤
      Real.exp (-2 * u ^ 2 / (N * c ^ 2)) := by
  classical
  let t : ℝ := 4 * u / (N * c ^ 2)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpoint : ∀ x : Fin N → Bool,
      (if x ∈ {x | u ≤ F x - cubeAverage F} then (1 : ℝ) else 0) ≤
        Real.exp (-t * u) * Real.exp (t * (F x - cubeAverage F)) := by
    intro x
    by_cases hx : u ≤ F x - cubeAverage F
    · simp only [Set.mem_setOf_eq, hx, ↓reduceIte]
      rw [← Real.exp_add]
      have : 0 ≤ -t * u + t * (F x - cubeAverage F) := by
        nlinarith
      simpa using Real.one_le_exp_iff.mpr this
    · simp only [Set.mem_setOf_eq, hx, ↓reduceIte]
      positivity
  calc
    cubeProbability {x | u ≤ F x - cubeAverage F} ≤
        cubeAverage (fun x =>
          Real.exp (-t * u) * Real.exp (t * (F x - cubeAverage F))) :=
      cubeAverage_mono hpoint
    _ = Real.exp (-t * u) *
        cubeAverage (fun x => Real.exp (t * (F x - cubeAverage F))) :=
      cubeAverage_const_mul _ _
    _ ≤ Real.exp (-t * u) * Real.exp (t ^ 2 * c ^ 2 * N / 8) := by
      gcongr
      exact cubeAverage_exp_centered_le N c hc.le F hF t
    _ = Real.exp (-2 * u ^ 2 / (N * c ^ 2)) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [t]
      field_simp
      ring

/-- The matching lower-tail form of McDiarmid's inequality. -/
theorem cubeProbability_centered_le_neg_le
    {N : ℕ} (hN : 0 < N) {c u : ℝ} (hc : 0 < c) (hu : 0 ≤ u)
    (F : (Fin N → Bool) → ℝ) (hF : CubeBoundedDifferences c F) :
    cubeProbability {x | u ≤ cubeAverage F - F x} ≤
      Real.exp (-2 * u ^ 2 / (N * c ^ 2)) := by
  have hneg : CubeBoundedDifferences c (fun x => -F x) := by
    intro x y hxy
    rw [show -F x - -F y = -(F x - F y) by ring, abs_neg]
    exact hF x y hxy
  have h := cubeProbability_centered_ge_le hN hc hu (fun x => -F x) hneg
  rw [cubeAverage_neg] at h
  simpa only [neg_sub_neg] using h

end Erdos522

end AmalgamatedModule54


/-! ===== amalgamated from Research.CubeSetConcentration ===== -/

section AmalgamatedModule55


open scoped BigOperators
open Metric

namespace Erdos522

/-- A median for a real function on the finite uniform Boolean cube. -/
def IsCubeMedian {N : ℕ} (F : (Fin N → Bool) → ℝ) (a : ℝ) : Prop :=
  (1 : ℝ) / 2 ≤ cubeProbability {x | F x ≤ a} ∧
    (1 : ℝ) / 2 ≤ cubeProbability {x | a ≤ F x}

lemma nonempty_of_half_le_cubeProbability {N : ℕ}
    {A : Set (Fin N → Bool)} (hA : (1 : ℝ) / 2 ≤ cubeProbability A) :
    A.Nonempty := by
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty.mp hempty] at hA
  have hzero : cubeProbability (∅ : Set (Fin N → Bool)) = 0 := by
    unfold cubeProbability
    simp
  rw [hzero] at hA
  norm_num at hA

/-- A Boolean-cube subset transported to Mathlib's Hamming metric type. -/
def toHammingSet {N : ℕ} (A : Set (Fin N → Bool)) :
    Set (Hamming fun _ : Fin N => Bool) := Hamming.toHamming '' A

/-- Hamming distance of a cube point to a subset. -/
noncomputable def cubeInfDist {N : ℕ} (A : Set (Fin N → Bool))
    (x : Fin N → Bool) : ℝ :=
  infDist (Hamming.toHamming x) (toHammingSet A)

lemma cubeInfDist_nonneg {N : ℕ} (A : Set (Fin N → Bool))
    (x : Fin N → Bool) : 0 ≤ cubeInfDist A x := infDist_nonneg

lemma cubeInfDist_eq_zero_of_mem {N : ℕ} {A : Set (Fin N → Bool)}
    {x : Fin N → Bool} (hx : x ∈ A) : cubeInfDist A x = 0 := by
  apply infDist_zero_of_mem
  exact ⟨x, hx, rfl⟩

lemma cubeInfDist_boundedDifferences {N : ℕ} (A : Set (Fin N → Bool)) :
    CubeBoundedDifferences 1 (cubeInfDist A) := by
  intro x y hxy
  calc
    |cubeInfDist A x - cubeInfDist A y| =
        dist (cubeInfDist A x) (cubeInfDist A y) := by rw [Real.dist_eq]
    _ ≤ (1 : ℝ) * dist (Hamming.toHamming x) (Hamming.toHamming y) :=
      (lipschitz_infDist_pt (toHammingSet A)).dist_le_mul _ _
    _ = (hammingDist x y : ℝ) := by simp
    _ ≤ 1 := by exact_mod_cast hxy

lemma cubeProbability_mono {N : ℕ} {A B : Set (Fin N → Bool)}
    (hAB : A ⊆ B) : cubeProbability A ≤ cubeProbability B := by
  unfold cubeProbability
  apply cubeAverage_mono
  intro x
  by_cases hx : x ∈ A
  · simp [hx, hAB hx]
  · simp only [hx, ↓reduceIte]
    split <;> norm_num

lemma cubeAverage_cubeInfDist_nonneg {N : ℕ} (A : Set (Fin N → Bool)) :
    0 ≤ cubeAverage (cubeInfDist A) := by
  calc
    0 = cubeAverage (fun _ : Fin N → Bool => 0) := (cubeAverage_const 0).symm
    _ ≤ cubeAverage (cubeInfDist A) :=
      cubeAverage_mono (fun x => cubeInfDist_nonneg A x)

lemma exp_neg_two_lt_half : Real.exp (-2) < (1 : ℝ) / 2 := by
  have hfour := Real.two_mul_le_exp (x := (2 : ℝ))
  norm_num at hfour
  have htwoexp : (2 : ℝ) < Real.exp 2 :=
    (by norm_num : (2 : ℝ) < 4).trans_le hfour
  have hinv : (Real.exp 2)⁻¹ < (2 : ℝ)⁻¹ :=
    (inv_lt_inv₀ (Real.exp_pos 2) (by norm_num)).mpr htwoexp
  simpa [Real.exp_neg, one_div] using hinv

/-- A set of cube probability at least one half has mean Hamming distance at
most `√N`.  This is the only median-to-mean loss needed below. -/
theorem cubeAverage_cubeInfDist_le_sqrt
    {N : ℕ} (hN : 0 < N) (A : Set (Fin N → Bool))
    (hhalf : (1 : ℝ) / 2 ≤ cubeProbability A) :
    cubeAverage (cubeInfDist A) ≤ √(N : ℝ) := by
  let m := cubeAverage (cubeInfDist A)
  have hm0 : 0 ≤ m := cubeAverage_cubeInfDist_nonneg A
  have htail := cubeProbability_centered_le_neg_le hN (c := (1 : ℝ))
    (u := m) (by norm_num) hm0 (cubeInfDist A)
    (cubeInfDist_boundedDifferences A)
  have hsub : A ⊆ {x | m ≤ cubeAverage (cubeInfDist A) - cubeInfDist A x} := by
    intro x hx
    change m ≤ cubeAverage (cubeInfDist A) - cubeInfDist A x
    rw [cubeInfDist_eq_zero_of_mem hx]
    dsimp [m]
    simp
  have hlower : (1 : ℝ) / 2 ≤ Real.exp (-2 * m ^ 2 / (N : ℝ)) := by
    calc
      (1 : ℝ) / 2 ≤ cubeProbability A := hhalf
      _ ≤ cubeProbability
          {x | m ≤ cubeAverage (cubeInfDist A) - cubeInfDist A x} :=
        cubeProbability_mono hsub
      _ ≤ Real.exp (-2 * m ^ 2 / ((N : ℝ) * (1 : ℝ) ^ 2)) := htail
      _ = Real.exp (-2 * m ^ 2 / (N : ℝ)) := by ring
  by_contra hnot
  have hsqrtlt : √(N : ℝ) < m := lt_of_not_ge hnot
  have hsqrt0 : 0 ≤ √(N : ℝ) := Real.sqrt_nonneg _
  have hNSq : (N : ℝ) < m ^ 2 := by
    calc
      (N : ℝ) = (√(N : ℝ)) ^ 2 := (Real.sq_sqrt (by positivity)).symm
      _ < m ^ 2 := (sq_lt_sq₀ hsqrt0 hm0).mpr hsqrtlt
  have hexponent : -2 * m ^ 2 / (N : ℝ) < -2 := by
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < N)).mpr
    nlinarith
  have := (Real.exp_lt_exp.mpr hexponent).trans exp_neg_two_lt_half
  exact (not_lt_of_ge hlower) this

/-- Hamming enlargement of a half-probability set has a Gaussian tail once the
radius is at least `2√N`. -/
theorem cubeProbability_cubeInfDist_ge_le
    {N : ℕ} (hN : 0 < N) (A : Set (Fin N → Bool))
    (hhalf : (1 : ℝ) / 2 ≤ cubeProbability A)
    {r : ℝ} (hr : 2 * √(N : ℝ) ≤ r) :
    cubeProbability {x | r ≤ cubeInfDist A x} ≤
      Real.exp (-r ^ 2 / (2 * N)) := by
  let m := cubeAverage (cubeInfDist A)
  have hm0 : 0 ≤ m := cubeAverage_cubeInfDist_nonneg A
  have hm : m ≤ √(N : ℝ) := cubeAverage_cubeInfDist_le_sqrt hN A hhalf
  have hu : 0 ≤ r - m := by nlinarith [Real.sqrt_nonneg (N : ℝ)]
  have hsub : {x | r ≤ cubeInfDist A x} ⊆
      {x | r - m ≤ cubeInfDist A x - cubeAverage (cubeInfDist A)} := by
    intro x hx
    change r - m ≤ cubeInfDist A x - cubeAverage (cubeInfDist A)
    change r ≤ cubeInfDist A x at hx
    dsimp [m]
    linarith
  calc
    cubeProbability {x | r ≤ cubeInfDist A x} ≤
        cubeProbability
          {x | r - m ≤ cubeInfDist A x - cubeAverage (cubeInfDist A)} :=
      cubeProbability_mono hsub
    _ ≤ Real.exp (-2 * (r - m) ^ 2 / ((N : ℝ) * (1 : ℝ) ^ 2)) :=
      cubeProbability_centered_ge_le hN (by norm_num) hu _
        (cubeInfDist_boundedDifferences A)
    _ ≤ Real.exp (-r ^ 2 / (2 * N)) := by
      apply Real.exp_le_exp.mpr
      have hrm : r / 2 ≤ r - m := by nlinarith
      have hr0 : 0 ≤ r := by nlinarith [Real.sqrt_nonneg (N : ℝ)]
      have hsq := (sq_le_sq₀ (by positivity : 0 ≤ r / 2) hu).mpr hrm
      have hNR : (0 : ℝ) < N := by exact_mod_cast hN
      norm_num
      field_simp [ne_of_gt hNR]
      nlinarith

end Erdos522

end AmalgamatedModule55


/-! ===== amalgamated from Research.CubeMedianExistence ===== -/

section AmalgamatedModule56


namespace Erdos522

lemma cubeAverage_add {N : ℕ} (F G : (Fin N → Bool) → ℝ) :
    cubeAverage (fun x => F x + G x) = cubeAverage F + cubeAverage G := by
  unfold cubeAverage
  rw [Finset.sum_add_distrib]
  ring

@[simp] lemma cubeProbability_univ {N : ℕ} :
    cubeProbability (Set.univ : Set (Fin N → Bool)) = 1 := by
  unfold cubeProbability
  simpa using (cubeAverage_const (N := N) 1)

lemma cubeProbability_add_compl {N : ℕ} (A : Set (Fin N → Bool)) :
    cubeProbability A + cubeProbability Aᶜ = 1 := by
  classical
  unfold cubeProbability
  rw [← cubeAverage_add]
  convert cubeAverage_const (N := N) 1 using 1
  apply congrArg cubeAverage
  funext x
  by_cases hx : x ∈ A <;> simp [hx]

/-- Every real function on a finite uniform Boolean cube admits a median in the
probabilistic two-half-set sense used by the concentration argument. -/
theorem exists_isCubeMedian {N : ℕ} (F : (Fin N → Bool) → ℝ) :
    ∃ a, IsCubeMedian F a := by
  classical
  let C : Finset (Fin N → Bool) := Finset.univ.filter fun x =>
    (1 : ℝ) / 2 ≤ cubeProbability {y | F y ≤ F x}
  have huniv : (Finset.univ : Finset (Fin N → Bool)).Nonempty := Finset.univ_nonempty
  obtain ⟨xmax, hxmaxmem, hxmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin N → Bool)) F huniv
  have hfull : {y | F y ≤ F xmax} = (Set.univ : Set (Fin N → Bool)) := by
    apply Set.eq_univ_of_forall
    intro y
    exact hxmax y (Finset.mem_univ y)
  have hxmaxC : xmax ∈ C := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hfull, cubeProbability_univ]
    norm_num
  have hC : C.Nonempty := ⟨xmax, hxmaxC⟩
  obtain ⟨x0, hx0C, hx0min⟩ := Finset.exists_min_image C F hC
  refine ⟨F x0, ?_, ?_⟩
  · exact (Finset.mem_filter.mp hx0C).2
  · by_contra hupper
    have hupperlt : cubeProbability {y | F x0 ≤ F y} < (1 : ℝ) / 2 :=
      lt_of_not_ge hupper
    have hcomp : ({y | F x0 ≤ F y} : Set (Fin N → Bool))ᶜ =
        {y | F y < F x0} := by
      ext y
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
      exact not_le
    have hadd := cubeProbability_add_compl
      ({y | F x0 ≤ F y} : Set (Fin N → Bool))
    rw [hcomp] at hadd
    have hlowergt : (1 : ℝ) / 2 < cubeProbability {y | F y < F x0} := by
      linarith
    have hLset : ({y | F y < F x0} : Set (Fin N → Bool)).Nonempty :=
      nonempty_of_half_le_cubeProbability hlowergt.le
    let L : Finset (Fin N → Bool) := Finset.univ.filter fun y => F y < F x0
    have hL : L.Nonempty := by
      rcases hLset with ⟨z, hz⟩
      exact ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩⟩
    obtain ⟨z, hzL, hzmax⟩ := Finset.exists_max_image L F hL
    have hzlt : F z < F x0 := (Finset.mem_filter.mp hzL).2
    have hevents : {y | F y ≤ F z} = ({y | F y < F x0} : Set (Fin N → Bool)) := by
      ext y
      simp only [Set.mem_setOf_eq]
      constructor
      · intro hy
        exact hy.trans_lt hzlt
      · intro hy
        exact hzmax y (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩)
    have hzC : z ∈ C := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [hevents]
      exact hlowergt.le
    exact (not_lt_of_ge (hx0min z hzC)) hzlt

end Erdos522

end AmalgamatedModule56


/-! ===== amalgamated from Research.CubeSqrtHammingConcentration ===== -/

section AmalgamatedModule57


open Metric

namespace Erdos522

/-- A square-root Hamming modulus, the natural output of Parseval for angular
statistics. -/
def SqrtHammingModulus {N : ℕ} (L : ℝ) (F : (Fin N → Bool) → ℝ) : Prop :=
  ∀ x y, |F x - F y| ≤ L * √(hammingDist x y : ℝ)

lemma upper_deviation_infDist_of_sqrtHammingModulus
    {N : ℕ} {F : (Fin N → Bool) → ℝ} {L a u : ℝ}
    (hL : 0 < L) (hu : 0 ≤ u) (hmod : SqrtHammingModulus L F)
    (hAne : ({y | F y ≤ a} : Set (Fin N → Bool)).Nonempty)
    {x : Fin N → Bool} (hx : a + u ≤ F x) :
    u ^ 2 / L ^ 2 ≤ cubeInfDist {y | F y ≤ a} x := by
  let A : Set (Fin N → Bool) := {y | F y ≤ a}
  apply (le_infDist (s := toHammingSet A) (by
    rcases hAne with ⟨y, hy⟩
    exact ⟨Hamming.toHamming y, ⟨y, hy, rfl⟩⟩)).mpr
  rintro z ⟨y, hy, rfl⟩
  change F y ≤ a at hy
  change u ^ 2 / L ^ 2 ≤ dist (Hamming.toHamming x) (Hamming.toHamming y)
  rw [Hamming.dist_eq_hammingDist]
  change _ ≤ (hammingDist x y : ℝ)
  have hdiff : u ≤ |F x - F y| := by
    calc
      u ≤ F x - F y := by linarith
      _ ≤ |F x - F y| := le_abs_self _
  have hroot : 0 ≤ √(hammingDist x y : ℝ) := Real.sqrt_nonneg _
  have hsq := (sq_le_sq₀ hu (mul_nonneg hL.le hroot)).mpr
    (hdiff.trans (hmod x y))
  rw [mul_pow, Real.sq_sqrt (by positivity)] at hsq
  exact (div_le_iff₀ (sq_pos_of_pos hL)).mpr (by nlinarith)

lemma lower_deviation_infDist_of_sqrtHammingModulus
    {N : ℕ} {F : (Fin N → Bool) → ℝ} {L a u : ℝ}
    (hL : 0 < L) (hu : 0 ≤ u) (hmod : SqrtHammingModulus L F)
    (hAne : ({y | a ≤ F y} : Set (Fin N → Bool)).Nonempty)
    {x : Fin N → Bool} (hx : F x + u ≤ a) :
    u ^ 2 / L ^ 2 ≤ cubeInfDist {y | a ≤ F y} x := by
  let A : Set (Fin N → Bool) := {y | a ≤ F y}
  apply (le_infDist (s := toHammingSet A) (by
    rcases hAne with ⟨y, hy⟩
    exact ⟨Hamming.toHamming y, ⟨y, hy, rfl⟩⟩)).mpr
  rintro z ⟨y, hy, rfl⟩
  change a ≤ F y at hy
  change u ^ 2 / L ^ 2 ≤ dist (Hamming.toHamming x) (Hamming.toHamming y)
  rw [Hamming.dist_eq_hammingDist]
  change _ ≤ (hammingDist x y : ℝ)
  have hdiff : u ≤ |F x - F y| := by
    calc
      u ≤ F y - F x := by linarith
      _ ≤ |F x - F y| := by rw [abs_sub_comm]; exact le_abs_self _
  have hroot : 0 ≤ √(hammingDist x y : ℝ) := Real.sqrt_nonneg _
  have hsq := (sq_le_sq₀ hu (mul_nonneg hL.le hroot)).mpr
    (hdiff.trans (hmod x y))
  rw [mul_pow, Real.sq_sqrt (by positivity)] at hsq
  exact (div_le_iff₀ (sq_pos_of_pos hL)).mpr (by nlinarith)

/-- Quartic upper tail for every function with a square-root Hamming modulus. -/
theorem cubeProbability_upper_median_tail_of_sqrtHammingModulus
    {N : ℕ} (hN : 0 < N) {F : (Fin N → Bool) → ℝ} {L a u : ℝ}
    (hL : 0 < L) (hu : 0 ≤ u) (hmod : SqrtHammingModulus L F)
    (hmed : IsCubeMedian F a) (hr : 2 * √(N : ℝ) ≤ u ^ 2 / L ^ 2) :
    cubeProbability {x | a + u ≤ F x} ≤
      Real.exp (-(u ^ 2 / L ^ 2) ^ 2 / (2 * N)) := by
  let A : Set (Fin N → Bool) := {y | F y ≤ a}
  let r := u ^ 2 / L ^ 2
  have hAne : A.Nonempty :=
    nonempty_of_half_le_cubeProbability (by simpa [A] using hmed.1)
  have hsub : {x | a + u ≤ F x} ⊆ {x | r ≤ cubeInfDist A x} := by
    intro x hx
    exact upper_deviation_infDist_of_sqrtHammingModulus hL hu hmod hAne hx
  calc
    cubeProbability {x | a + u ≤ F x} ≤
        cubeProbability {x | r ≤ cubeInfDist A x} := cubeProbability_mono hsub
    _ ≤ Real.exp (-r ^ 2 / (2 * (N : ℝ))) :=
      cubeProbability_cubeInfDist_ge_le hN A (by simpa [A] using hmed.1)
        (by simpa [r] using hr)
    _ = _ := rfl

/-- Matching quartic lower tail. -/
theorem cubeProbability_lower_median_tail_of_sqrtHammingModulus
    {N : ℕ} (hN : 0 < N) {F : (Fin N → Bool) → ℝ} {L a u : ℝ}
    (hL : 0 < L) (hu : 0 ≤ u) (hmod : SqrtHammingModulus L F)
    (hmed : IsCubeMedian F a) (hr : 2 * √(N : ℝ) ≤ u ^ 2 / L ^ 2) :
    cubeProbability {x | F x + u ≤ a} ≤
      Real.exp (-(u ^ 2 / L ^ 2) ^ 2 / (2 * N)) := by
  let A : Set (Fin N → Bool) := {y | a ≤ F y}
  let r := u ^ 2 / L ^ 2
  have hAne : A.Nonempty :=
    nonempty_of_half_le_cubeProbability (by simpa [A] using hmed.2)
  have hsub : {x | F x + u ≤ a} ⊆ {x | r ≤ cubeInfDist A x} := by
    intro x hx
    exact lower_deviation_infDist_of_sqrtHammingModulus hL hu hmod hAne hx
  calc
    cubeProbability {x | F x + u ≤ a} ≤
        cubeProbability {x | r ≤ cubeInfDist A x} := cubeProbability_mono hsub
    _ ≤ Real.exp (-r ^ 2 / (2 * (N : ℝ))) :=
      cubeProbability_cubeInfDist_ge_le hN A (by simpa [A] using hmed.2)
        (by simpa [r] using hr)
    _ = _ := rfl

end Erdos522

end AmalgamatedModule57


/-! ===== amalgamated from Research.RadialAngularConcentration ===== -/

section AmalgamatedModule58


namespace Erdos522

/-- Parseval and radial flatness give a square-root Hamming modulus for every
Lipschitz angular test. -/
theorem radialCubeAngularStatistic_sqrtHammingModulus
    (n : ℕ) (hn : 0 < n) (s : ℝ) (h : ℂ → ℝ)
    {K : NNReal} (hK : LipschitzWith K h) :
    SqrtHammingModulus
      ((K : ℝ) * √(4 * (Real.exp (4 * |s|) / (n + 1 : ℝ))))
      (radialCubeAngularStatistic n s h) := by
  intro x y
  have hb := radialCubeAngularStatistic_dist_le n hn s h hK x y
  calc
    |radialCubeAngularStatistic n s h x - radialCubeAngularStatistic n s h y| ≤
        (K : ℝ) * √((Real.exp (4 * |s|) / (n + 1 : ℝ)) *
          (4 * (hammingDist x y : ℝ))) := hb
    _ = (K : ℝ) * √(4 * (Real.exp (4 * |s|) / (n + 1 : ℝ))) *
        √(hammingDist x y : ℝ) := by
      rw [show (Real.exp (4 * |s|) / (n + 1 : ℝ)) *
          (4 * (hammingDist x y : ℝ)) =
          (4 * (Real.exp (4 * |s|) / (n + 1 : ℝ))) *
            (hammingDist x y : ℝ) by ring,
        Real.sqrt_mul (by positivity)]
      ring

/-- Upper median tail for any `K`-Lipschitz angular statistic. -/
theorem radialCubeAngularStatistic_upper_median_tail
    (n : ℕ) (hn : 0 < n) (s : ℝ) (h : ℂ → ℝ)
    {K : NNReal} (hK0 : 0 < K) (hK : LipschitzWith K h)
    (a : ℝ) (hmed : IsCubeMedian (radialCubeAngularStatistic n s h) a)
    {u : ℝ} (hu : 0 ≤ u)
    (hr : 2 * √((n + 1 : ℝ)) ≤
      u ^ 2 /
        (((K : ℝ) * √(4 * (Real.exp (4 * |s|) / (n + 1 : ℝ)))) ^ 2)) :
    cubeProbability {x | a + u ≤ radialCubeAngularStatistic n s h x} ≤
      Real.exp (-
        (u ^ 2 /
          (((K : ℝ) * √(4 * (Real.exp (4 * |s|) / (n + 1 : ℝ)))) ^ 2)) ^ 2 /
        (2 * (↑(n + 1) : ℝ))) := by
  apply cubeProbability_upper_median_tail_of_sqrtHammingModulus (N := n + 1)
    (F := radialCubeAngularStatistic n s h)
    (L := (K : ℝ) * √(4 * (Real.exp (4 * |s|) / (n + 1 : ℝ))))
    (a := a) (u := u) (by omega)
  · positivity
  · exact hu
  · exact radialCubeAngularStatistic_sqrtHammingModulus n hn s h hK
  · exact hmed
  · simpa using hr

/-- Lower median tail for any `K`-Lipschitz angular statistic. -/
theorem radialCubeAngularStatistic_lower_median_tail
    (n : ℕ) (hn : 0 < n) (s : ℝ) (h : ℂ → ℝ)
    {K : NNReal} (hK0 : 0 < K) (hK : LipschitzWith K h)
    (a : ℝ) (hmed : IsCubeMedian (radialCubeAngularStatistic n s h) a)
    {u : ℝ} (hu : 0 ≤ u)
    (hr : 2 * √((n + 1 : ℝ)) ≤
      u ^ 2 /
        (((K : ℝ) * √(4 * (Real.exp (4 * |s|) / (n + 1 : ℝ)))) ^ 2)) :
    cubeProbability {x | radialCubeAngularStatistic n s h x + u ≤ a} ≤
      Real.exp (-
        (u ^ 2 /
          (((K : ℝ) * √(4 * (Real.exp (4 * |s|) / (n + 1 : ℝ)))) ^ 2)) ^ 2 /
        (2 * (↑(n + 1) : ℝ))) := by
  apply cubeProbability_lower_median_tail_of_sqrtHammingModulus (N := n + 1)
    (F := radialCubeAngularStatistic n s h)
    (L := (K : ℝ) * √(4 * (Real.exp (4 * |s|) / (n + 1 : ℝ))))
    (a := a) (u := u) (by omega)
  · positivity
  · exact hu
  · exact radialCubeAngularStatistic_sqrtHammingModulus n hn s h hK
  · exact hmed
  · simpa using hr

end Erdos522

end AmalgamatedModule58


/-! ===== amalgamated from Research.SmallBallCutoff ===== -/

section AmalgamatedModule59


namespace Erdos522

/-- A triangular radial majorant of the ball of radius `1/M`, vanishing outside
radius `2/M`. -/
noncomputable def smallBallCutoff (M : NNReal) (z : ℂ) : ℝ :=
  max 0 (min 1 (2 - (M : ℝ) * ‖z‖))

lemma smallBallCutoff_nonneg (M : NNReal) (z : ℂ) :
    0 ≤ smallBallCutoff M z := le_max_left _ _

lemma smallBallCutoff_le_one (M : NNReal) (z : ℂ) :
    smallBallCutoff M z ≤ 1 := by
  unfold smallBallCutoff
  exact max_le (by norm_num) (min_le_left _ _)

lemma smallBallCutoff_eq_one_of_norm_le
    {M : NNReal} (hM : 0 < M) {z : ℂ} (hz : ‖z‖ ≤ 1 / (M : ℝ)) :
    smallBallCutoff M z = 1 := by
  unfold smallBallCutoff
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hMz : (M : ℝ) * ‖z‖ ≤ 1 := by
    simpa [mul_comm] using (le_div_iff₀ hMr).mp hz
  rw [min_eq_left (by linarith), max_eq_right (by norm_num)]

lemma smallBallCutoff_eq_zero_of_le_norm
    {M : NNReal} (hM : 0 < M) {z : ℂ} (hz : 2 / (M : ℝ) ≤ ‖z‖) :
    smallBallCutoff M z = 0 := by
  unfold smallBallCutoff
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hMz : 2 ≤ (M : ℝ) * ‖z‖ := by
    simpa [mul_comm] using (div_le_iff₀ hMr).mp hz
  rw [min_eq_right (by linarith), max_eq_left (by linarith)]

/-- The cutoff has the sharp global Lipschitz constant `M`. -/
theorem smallBallCutoff_lipschitz (M : NNReal) :
    LipschitzWith M (smallBallCutoff M) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq]
  unfold smallBallCutoff
  calc
    |max 0 (min 1 (2 - (M : ℝ) * ‖x‖)) -
        max 0 (min 1 (2 - (M : ℝ) * ‖y‖))| =
        |max (min 1 (2 - (M : ℝ) * ‖x‖)) 0 -
          max (min 1 (2 - (M : ℝ) * ‖y‖)) 0| := by
      rw [max_comm 0, max_comm 0]
    _ ≤ |min 1 (2 - (M : ℝ) * ‖x‖) -
        min 1 (2 - (M : ℝ) * ‖y‖)| := abs_max_sub_max_le_abs _ _ _
    _ = |min (2 - (M : ℝ) * ‖x‖) 1 -
        min (2 - (M : ℝ) * ‖y‖) 1| := by rw [min_comm 1, min_comm 1]
    _ ≤ |(2 - (M : ℝ) * ‖x‖) - (2 - (M : ℝ) * ‖y‖)| := by
      simpa using abs_min_sub_min_le_max
        (2 - (M : ℝ) * ‖x‖) 1 (2 - (M : ℝ) * ‖y‖) 1
    _ = (M : ℝ) * |‖x‖ - ‖y‖| := by
      rw [show (2 - (M : ℝ) * ‖x‖) - (2 - (M : ℝ) * ‖y‖) =
        -(M : ℝ) * (‖x‖ - ‖y‖) by ring, abs_mul, abs_neg,
        abs_of_nonneg M.coe_nonneg]
    _ ≤ (M : ℝ) * dist x y := by
      rw [dist_eq_norm]
      exact mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le x y) M.coe_nonneg

end Erdos522

end AmalgamatedModule59


/-! ===== amalgamated from Research.RadialSmallBallConcentration ===== -/

section AmalgamatedModule60


namespace Erdos522

/-- Angular average of the standard small-ball majorant for the normalized
radial polynomial. -/
noncomputable def radialCubeSmallBallStatistic
    (n : ℕ) (s : ℝ) (M : NNReal) (x : Fin (n + 1) → Bool) : ℝ :=
  radialCubeAngularStatistic n s (smallBallCutoff M) x

lemma radialCubeSmallBallStatistic_sqrtHammingModulus
    (n : ℕ) (hn : 0 < n) (s : ℝ) (M : NNReal) :
    SqrtHammingModulus
      ((M : ℝ) * √(4 * (Real.exp (4 * |s|) / (n + 1 : ℝ))))
      (radialCubeSmallBallStatistic n s M) := by
  intro x y
  unfold radialCubeSmallBallStatistic
  exact (radialCubeAngularStatistic_sqrtHammingModulus n hn s
    (smallBallCutoff M) (smallBallCutoff_lipschitz M)) x y

/-- The small-ball statistic always has a two-sided cube median. -/
theorem exists_radialCubeSmallBallStatistic_median
    (n : ℕ) (s : ℝ) (M : NNReal) :
    ∃ a, IsCubeMedian (radialCubeSmallBallStatistic n s M) a :=
  exists_isCubeMedian _

/-- Explicit upper median tail for the small-ball angular majorant. -/
theorem radialCubeSmallBallStatistic_upper_median_tail
    (n : ℕ) (hn : 0 < n) (s : ℝ) (M : NNReal) (hM : 0 < M)
    (a : ℝ) (hmed : IsCubeMedian (radialCubeSmallBallStatistic n s M) a)
    {u : ℝ} (hu : 0 ≤ u)
    (hr : 2 * √((n + 1 : ℝ)) ≤
      u ^ 2 /
        (((M : ℝ) * √(4 * (Real.exp (4 * |s|) / (n + 1 : ℝ)))) ^ 2)) :
    cubeProbability {x | a + u ≤ radialCubeSmallBallStatistic n s M x} ≤
      Real.exp (-
        (u ^ 2 /
          (((M : ℝ) * √(4 * (Real.exp (4 * |s|) / (n + 1 : ℝ)))) ^ 2)) ^ 2 /
        (2 * (↑(n + 1) : ℝ))) := by
  simpa [radialCubeSmallBallStatistic] using
    radialCubeAngularStatistic_upper_median_tail n hn s (smallBallCutoff M)
      hM (smallBallCutoff_lipschitz M) a hmed hu hr

end Erdos522

end AmalgamatedModule60


/-! ===== amalgamated from Research.AnnealedExpectation ===== -/

section AmalgamatedModule61


open MeasureTheory Filter Topology
open scoped BigOperators BoundedContinuousFunction

namespace Erdos522

lemma eval_weightedVectorPolynomial {N : ℕ} (w x : Fin N → ℝ) (z : ℂ) :
    (weightedVectorPolynomial w x).eval z =
      ∑ k : Fin N, ((Real.sqrt (w k) * x k : ℝ) : ℂ) * z ^ (k : ℕ) := by
  unfold weightedVectorPolynomial
  change Polynomial.evalRingHom z
    (∑ k : Fin N, Polynomial.monomial (k : ℕ)
      (((Real.sqrt (w k) * x k : ℝ) : ℂ))) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  change Polynomial.eval z
    (Polynomial.monomial (k : ℕ)
      (((Real.sqrt (w k) * x k : ℝ) : ℂ))) = _
  rw [Polynomial.eval_monomial]

lemma radialAnnealedValue_eq_eval
    (n : ℕ) (s : ℝ) (θ : ℝ) (x : Fin (n + 1) → Bool) :
    radialAnnealedValue n s (θ, x) =
      (weightedVectorPolynomial
        (fun k : Fin (n + 1) => radialWeight n s k)
        (fun k => realRademacherSign (x k))).eval (circleMap 0 1 θ) := by
  rw [eval_weightedVectorPolynomial]
  unfold radialAnnealedValue radialCircleCoefficient
  apply Finset.sum_congr rfl
  intro k hk
  push_cast
  ring

/-- A bounded continuous function assembled from an explicit norm bound. -/
noncomputable def boundedContinuousFunctionOfNormBound
    (h : ℂ → ℝ) (hc : Continuous h) (B : ℝ)
    (hB : ∀ z, ‖h z‖ ≤ B) : ℂ →ᵇ ℝ where
  toFun := h
  continuous_toFun := hc
  map_bounded' := by
    refine ⟨2 * B, fun x y => ?_⟩
    rw [Real.dist_eq]
    calc
      |h x - h y| ≤ |h x| + |h y| := abs_sub _ _
      _ = ‖h x‖ + ‖h y‖ := by simp [Real.norm_eq_abs]
      _ ≤ B + B := add_le_add (hB x) (hB y)
      _ = 2 * B := by ring

/-- Integrating a planar test against the annealed law is exactly the cube
average of its angular statistic. -/
theorem integral_radialAnnealedLaw_eq_cubeAverage
    (n : ℕ) (s : ℝ) (h : ℂ → ℝ) (hc : Continuous h)
    (B : ℝ) (hB : ∀ z, ‖h z‖ ≤ B) :
    ∫ z, h z ∂(radialAnnealedLaw n s : ProbabilityMeasure ℂ) =
      cubeAverage (radialCubeAngularStatistic n s h) := by
  unfold radialAnnealedLaw
  rw [ProbabilityMeasure.toMeasure_map]
  rw [integral_map (continuous_radialAnnealedValue n s).aemeasurable
    hc.aestronglyMeasurable]
  let f : ℝ × (Fin (n + 1) → Bool) → ℝ := fun u => h (radialAnnealedValue n s u)
  have hfint : Integrable f
      (circleParameterMeasure.prod
        (uniformCubeProbabilityMeasure (n + 1) :
          Measure (Fin (n + 1) → Bool))) := by
    apply Integrable.of_bound (by
      exact (hc.comp
        (continuous_radialAnnealedValue n s)).aestronglyMeasurable) B
    filter_upwards with u
    exact hB _
  rw [show (↑(radialAnnealedSourceMeasure n) :
      Measure (ℝ × (Fin (n + 1) → Bool))) =
      circleParameterMeasure.prod
        (uniformCubeProbabilityMeasure (n + 1) :
          Measure (Fin (n + 1) → Bool)) by rfl]
  rw [integral_prod f hfint]
  unfold cubeAverage radialCubeAngularStatistic angularStatistic
  simp_rw [circleAverage_eq_integral_circleParameterMeasure]
  have hgint (x : Fin (n + 1) → Bool) : Integrable
      (circleParameterFunction
        (fun z => h ((weightedVectorPolynomial
          (fun k : Fin (n + 1) => radialWeight n s k)
          (fun k => realRademacherSign (x k))).eval z)))
      circleParameterMeasure := by
    apply Integrable.of_bound (by
      apply Continuous.aestronglyMeasurable
      unfold circleParameterFunction
      fun_prop) B
    filter_upwards with θ
    exact hB _
  rw [← integral_finset_sum Finset.univ (fun x _ => hgint x)]
  rw [← integral_div]
  apply integral_congr_ae
  filter_upwards with θ
  change ∫ y, f (θ, y) ∂(PMF.uniformOfFintype
    (Fin (n + 1) → Bool)).toMeasure = _
  rw [PMF.integral_eq_sum]
  simp_rw [PMF.uniformOfFintype_apply]
  simp only [Fintype.card_pi, Fintype.card_bool,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  dsimp [f, circleParameterFunction]
  simp_rw [radialAnnealedValue_eq_eval]
  rw [← Finset.mul_sum]
  push_cast
  ring

/-- Weak convergence of F-045 gives convergence of annealed expectations for
every bounded continuous planar test. -/
theorem tendsto_cubeAverage_radialCubeAngularStatistic
    (s : ℝ) (h : ℂ → ℝ) (hc : Continuous h)
    (B : ℝ) (hB : ∀ z, ‖h z‖ ≤ B) :
    Tendsto (fun n => cubeAverage (radialCubeAngularStatistic n s h)) atTop
      (𝓝 (∫ z, h z ∂(circularGaussianLaw : ProbabilityMeasure ℂ))) := by
  let H := boundedContinuousFunctionOfNormBound h hc B hB
  have hweak := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
    (tendsto_radialAnnealedLaw s)) H
  have heq :
      (fun n => ∫ z, H z ∂(radialAnnealedLaw n s : ProbabilityMeasure ℂ)) =
        fun n => cubeAverage (radialCubeAngularStatistic n s h) := by
    funext n
    exact integral_radialAnnealedLaw_eq_cubeAverage n s h hc B hB
  rw [heq] at hweak
  simpa [H, boundedContinuousFunctionOfNormBound] using hweak

end Erdos522

end AmalgamatedModule61


/-! ===== amalgamated from Research.AnnealedTestLimits ===== -/

section AmalgamatedModule62


open MeasureTheory Filter Topology

namespace Erdos522

/-- For a fixed clipping level, annealed clipped-log cube averages converge to
that clipped logarithm's circular-Gaussian expectation. -/
theorem tendsto_cubeAverage_radialCubeClippedStatistic
    (s : ℝ) (M : NNReal) (hM : 1 ≤ M) :
    Tendsto (fun n => cubeAverage (radialCubeClippedStatistic n s M)) atTop
      (𝓝 (∫ z, clippedLog M z
        ∂(circularGaussianLaw : ProbabilityMeasure ℂ))) := by
  change Tendsto
    (fun n => cubeAverage (radialCubeAngularStatistic n s (clippedLog M)))
    atTop (𝓝 (∫ z, clippedLog M z
      ∂(circularGaussianLaw : ProbabilityMeasure ℂ)))
  exact tendsto_cubeAverage_radialCubeAngularStatistic s (clippedLog M)
    (clippedLog_lipschitz M hM).continuous (Real.log (M : ℝ))
    (fun z => by simpa [Real.norm_eq_abs] using abs_clippedLog_le_log M hM z)

/-- For a fixed cutoff level, annealed radial small-ball statistics converge to
that cutoff's circular-Gaussian expectation. -/
theorem tendsto_cubeAverage_radialCubeSmallBallStatistic
    (s : ℝ) (M : NNReal) :
    Tendsto (fun n => cubeAverage (radialCubeSmallBallStatistic n s M)) atTop
      (𝓝 (∫ z, smallBallCutoff M z
        ∂(circularGaussianLaw : ProbabilityMeasure ℂ))) := by
  change Tendsto
    (fun n => cubeAverage (radialCubeAngularStatistic n s (smallBallCutoff M)))
    atTop (𝓝 (∫ z, smallBallCutoff M z
      ∂(circularGaussianLaw : ProbabilityMeasure ℂ)))
  exact tendsto_cubeAverage_radialCubeAngularStatistic s (smallBallCutoff M)
    (smallBallCutoff_lipschitz M).continuous 1
    (fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (smallBallCutoff_nonneg M z)]
      exact smallBallCutoff_le_one M z)

end Erdos522

end AmalgamatedModule62


/-! ===== amalgamated from Research.GaussianSmallBall ===== -/

section AmalgamatedModule63


open MeasureTheory Filter Topology ProbabilityTheory

namespace Erdos522

lemma stdGaussian_complex_noAtoms : NoAtoms (stdGaussian ℂ) := by
  apply IsGaussian.noAtoms
  intro x hx
  have hvar := variance_dual_stdGaussian (E := ℂ) Complex.reCLM
  rw [hx, variance_dirac, Complex.reCLM_norm] at hvar
  norm_num at hvar

lemma circularGaussian_measure_singleton_zero :
    (circularGaussianLaw : Measure ℂ) ({0} : Set ℂ) = 0 := by
  letI : NoAtoms (stdGaussian ℂ) := stdGaussian_complex_noAtoms
  unfold circularGaussianLaw standardComplexGaussianLaw
  rw [ProbabilityMeasure.toMeasure_map]
  change (Measure.map (fun z : ℂ => (Real.sqrt 2)⁻¹ • z)
    (stdGaussian ℂ)) {0} = 0
  rw [Measure.map_apply_of_aemeasurable
    (by fun_prop : AEMeasurable (fun z : ℂ => (Real.sqrt 2)⁻¹ • z)
      (stdGaussian ℂ)) (measurableSet_singleton 0)]
  have hsqrt : (Real.sqrt 2)⁻¹ ≠ 0 := by positivity
  have hpre : (fun z : ℂ => (Real.sqrt 2)⁻¹ • z) ⁻¹' ({0} : Set ℂ) = {0} := by
    ext z
    simp [hsqrt]
  rw [hpre, measure_singleton]

/-- The circular-Gaussian expectation of the shrinking triangular small-ball
cutoff tends to zero. -/
theorem tendsto_circularGaussian_smallBallCutoff_integral :
    Tendsto
      (fun n : ℕ => ∫ z, smallBallCutoff ((n + 1 : ℕ) : NNReal) z
        ∂(circularGaussianLaw : ProbabilityMeasure ℂ))
      atTop (𝓝 0) := by
  have hz_ne : ∀ᵐ z ∂(circularGaussianLaw : Measure ℂ), z ≠ 0 := by
    rw [ae_iff]
    simpa only [not_ne_iff, Set.setOf_eq_eq_singleton] using
      circularGaussian_measure_singleton_zero
  have hpoint : ∀ᵐ z ∂(circularGaussianLaw : Measure ℂ),
      Tendsto (fun n : ℕ => smallBallCutoff ((n + 1 : ℕ) : NNReal) z)
        atTop (𝓝 0) := by
    filter_upwards [hz_ne] with z hz
    have hnorm : 0 < ‖z‖ := norm_pos_iff.mpr hz
    obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (2 / ‖z‖)
    have heq : ∀ᶠ n : ℕ in atTop,
        smallBallCutoff ((n + 1 : ℕ) : NNReal) z = 0 := by
      filter_upwards [eventually_ge_atTop N] with n hn
      apply smallBallCutoff_eq_zero_of_le_norm (by positivity)
      have hNr : (N : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast (hn.trans (Nat.le_add_right n 1))
      have htwo : 2 < (N : ℝ) * ‖z‖ := (div_lt_iff₀ hnorm).mp hN
      have hden : (0 : ℝ) < (n + 1 : ℕ) := by positivity
      apply (div_le_iff₀ hden).2
      nlinarith [mul_le_mul_of_nonneg_right hNr hnorm.le]
    exact Filter.Tendsto.congr' (Filter.EventuallyEq.symm heq)
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have ht := tendsto_integral_of_dominated_convergence
    (μ := (circularGaussianLaw : Measure ℂ)) (F := fun n z =>
      smallBallCutoff ((n + 1 : ℕ) : NNReal) z) (f := fun _ => (0 : ℝ))
    (fun _ => (1 : ℝ))
    (fun n => (smallBallCutoff_lipschitz ((n + 1 : ℕ) : NNReal)).continuous.aestronglyMeasurable)
    (integrable_const 1)
    (fun n => Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (smallBallCutoff_nonneg _ z)]
      exact smallBallCutoff_le_one _ z)
    hpoint
  simpa using ht

end Erdos522

end AmalgamatedModule63


/-! ===== amalgamated from Research.GaussianProjection ===== -/

section AmalgamatedModule64


open MeasureTheory ProbabilityTheory

namespace Erdos522

lemma coe_standardComplexGaussianLaw :
    (standardComplexGaussianLaw : Measure ℂ) = stdGaussian ℂ := rfl

lemma isGaussian_circularGaussianLaw :
    IsGaussian (circularGaussianLaw : Measure ℂ) := by
  unfold circularGaussianLaw
  rw [ProbabilityMeasure.toMeasure_map, coe_standardComplexGaussianLaw]
  let L : ℂ →L[ℝ] ℂ := (Real.sqrt 2)⁻¹ • ContinuousLinearMap.id ℝ ℂ
  change IsGaussian ((stdGaussian ℂ).map L)
  infer_instance

lemma map_re_circularGaussianLaw :
    Measure.map Complex.re (circularGaussianLaw : Measure ℂ) =
      gaussianReal 0 (1 / 2 : NNReal) := by
  unfold circularGaussianLaw
  rw [ProbabilityMeasure.toMeasure_map, coe_standardComplexGaussianLaw]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  have hfun : (Complex.re ∘ fun z : ℂ => (Real.sqrt 2)⁻¹ • z) =
      ⇑((Real.sqrt 2)⁻¹ • Complex.reCLM) := by
    funext z
    simp only [Function.comp_apply, Complex.smul_re,
      ContinuousLinearMap.smul_apply]
    rfl
  rw [hfun, IsGaussian.map_eq_gaussianReal]
  congr 2
  · change (∫ x : ℂ, (Real.sqrt 2)⁻¹ * x.re ∂stdGaussian ℂ) = 0
    rw [integral_const_mul]
    change (Real.sqrt 2)⁻¹ * (stdGaussian ℂ)[Complex.reCLM] = 0
    rw [integral_strongDual_stdGaussian]
    simp
  · change (Var[fun x : ℂ => (Real.sqrt 2)⁻¹ * x.re;
        stdGaussian ℂ]).toNNReal = 1 / 2
    rw [variance_const_mul]
    have hvar := variance_dual_stdGaussian (E := ℂ) Complex.reCLM
    rw [Complex.reCLM_norm, one_pow] at hvar
    change Var[fun x : ℂ => x.re; stdGaussian ℂ] = 1 at hvar
    rw [hvar, mul_one]
    have hsqrt : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
    have hsqrt_ne : Real.sqrt 2 ≠ 0 := by positivity
    apply NNReal.eq
    rw [Real.coe_toNNReal _ (sq_nonneg _)]
    norm_num only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
    field_simp [hsqrt_ne]
    nlinarith

lemma gaussianPDFReal_zero_half_le_one (x : ℝ) :
    gaussianPDFReal 0 (1 / 2 : NNReal) x ≤ 1 := by
  have hsqrt : 1 ≤ Real.sqrt Real.pi := by
    rw [Real.le_sqrt (by norm_num) Real.pi_pos.le]
    nlinarith [Real.pi_gt_three]
  have hinv : (Real.sqrt Real.pi)⁻¹ ≤ 1 :=
    (inv_le_one₀ (Real.sqrt_pos.2 Real.pi_pos)).2 hsqrt
  rw [gaussianPDFReal]
  norm_num only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat,
    sub_zero, mul_div_cancel_left₀, OfNat.ofNat_ne_zero, inv_mul_cancel₀]
  have hcoef :
      (Real.sqrt (2 * Real.pi * (1 / 2 : ℝ)))⁻¹ =
        (Real.sqrt Real.pi)⁻¹ := by
    congr 2
    ring
  rw [hcoef, div_one]
  have hexp : Real.exp (-x ^ 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg x))
  exact mul_le_one₀ hinv (Real.exp_nonneg _) hexp

lemma integrable_circularGaussian_norm_sq :
    Integrable (fun z : ℂ => ‖z‖ ^ 2)
      (circularGaussianLaw : Measure ℂ) := by
  letI : IsGaussian (circularGaussianLaw : Measure ℂ) :=
    isGaussian_circularGaussianLaw
  have h := (IsGaussian.memLp_id
    (circularGaussianLaw : Measure ℂ) (2 : ENNReal) (by norm_num)).integrable_norm_rpow
      (by norm_num) (by norm_num)
  simpa using h

lemma integrable_circularGaussian_norm_pow_four :
    Integrable (fun z : ℂ => ‖z‖ ^ 4)
      (circularGaussianLaw : Measure ℂ) := by
  letI : IsGaussian (circularGaussianLaw : Measure ℂ) :=
    isGaussian_circularGaussianLaw
  have h := (IsGaussian.memLp_id
    (circularGaussianLaw : Measure ℂ) (4 : ENNReal) (by norm_num)).integrable_norm_rpow
      (by norm_num) (by norm_num)
  simpa using h

noncomputable def circularGaussianSecondNormMoment : ℝ :=
  ∫ z : ℂ, ‖z‖ ^ 2 ∂(circularGaussianLaw : Measure ℂ)

noncomputable def circularGaussianFourthNormMoment : ℝ :=
  ∫ z : ℂ, ‖z‖ ^ 4 ∂(circularGaussianLaw : Measure ℂ)

lemma circularGaussianSecondNormMoment_nonneg :
    0 ≤ circularGaussianSecondNormMoment :=
  integral_nonneg fun _ => sq_nonneg _

lemma circularGaussianFourthNormMoment_nonneg :
    0 ≤ circularGaussianFourthNormMoment :=
  integral_nonneg (by intro z; positivity)

/-- A one-coordinate density bound gives a quantitative radial Laplace bound
for the circular Gaussian.  The one-dimensional estimate is sufficient for
our later two-dimensional small-ball argument. -/
theorem circularGaussian_integral_exp_neg_sq_norm_le
    (a : ℝ) (ha : 0 < a) :
    (∫ z : ℂ, Real.exp (-(a * ‖z‖) ^ 2)
      ∂(circularGaussianLaw : Measure ℂ)) ≤ Real.sqrt Real.pi / a := by
  let F : ℂ → ℝ := fun z => Real.exp (-(a * ‖z‖) ^ 2)
  let G : ℂ → ℝ := fun z => Real.exp (-(a * z.re) ^ 2)
  have hFint : Integrable F (circularGaussianLaw : Measure ℂ) := by
    apply Integrable.of_bound (by
      dsimp [F]
      fun_prop) 1
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _))
  have hGint : Integrable G (circularGaussianLaw : Measure ℂ) := by
    apply Integrable.of_bound (by
      dsimp [G]
      fun_prop) 1
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _))
  calc
    (∫ z : ℂ, Real.exp (-(a * ‖z‖) ^ 2)
        ∂(circularGaussianLaw : Measure ℂ)) = ∫ z, F z
        ∂(circularGaussianLaw : Measure ℂ) := rfl
    _ ≤ ∫ z, G z ∂(circularGaussianLaw : Measure ℂ) := by
      apply integral_mono hFint hGint
      intro z
      apply Real.exp_le_exp.mpr
      have hre : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
      have hsq : (a * z.re) ^ 2 ≤ (a * ‖z‖) ^ 2 := by
        have hbase := (sq_le_sq₀ (abs_nonneg z.re) (norm_nonneg z)).2 hre
        rw [sq_abs] at hbase
        nlinarith [mul_le_mul_of_nonneg_left hbase (sq_nonneg a)]
      linarith
    _ = ∫ x : ℝ, Real.exp (-(a * x) ^ 2)
        ∂gaussianReal 0 (1 / 2 : NNReal) := by
      rw [← map_re_circularGaussianLaw]
      rw [integral_map Complex.continuous_re.aemeasurable (by fun_prop)]
    _ ≤ ∫ x : ℝ, Real.exp (-a ^ 2 * x ^ 2) := by
      rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 / 2 : NNReal) ≠ 0)]
      simp only [smul_eq_mul]
      have hg : Integrable (fun x : ℝ => Real.exp (-a ^ 2 * x ^ 2)) :=
        integrable_exp_neg_mul_sq (sq_pos_of_pos ha)
      have hf : Integrable (fun x : ℝ =>
          gaussianPDFReal 0 (1 / 2 : NNReal) x *
            Real.exp (-(a * x) ^ 2)) := by
        apply hg.mono' (by fun_prop)
        filter_upwards with x
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
          (gaussianPDFReal_nonneg _ _ _) (Real.exp_nonneg _))]
        rw [show -(a * x) ^ 2 = -a ^ 2 * x ^ 2 by ring]
        exact mul_le_of_le_one_left (Real.exp_nonneg _)
          (gaussianPDFReal_zero_half_le_one x)
      apply integral_mono hf hg
      intro x
      change gaussianPDFReal 0 (1 / 2 : NNReal) x *
        Real.exp (-(a * x) ^ 2) ≤ Real.exp (-a ^ 2 * x ^ 2)
      rw [show -(a * x) ^ 2 = -a ^ 2 * x ^ 2 by ring]
      exact mul_le_of_le_one_left (Real.exp_nonneg _)
        (gaussianPDFReal_zero_half_le_one x)
    _ = Real.sqrt (Real.pi / a ^ 2) := integral_gaussian (a ^ 2)
    _ = Real.sqrt Real.pi / a := by
      rw [Real.sqrt_div Real.pi_pos.le, Real.sqrt_sq ha.le]

end Erdos522

end AmalgamatedModule64


/-! ===== amalgamated from Research.GaussianBallBound ===== -/

section AmalgamatedModule65


open MeasureTheory

namespace Erdos522

/-- A crude linear small-ball bound for the circular Gaussian, sufficient for
splitting off a tiny frequency neighborhood. -/
theorem circularGaussian_measureReal_norm_le
    (r : ℝ) (hr : 0 < r) :
    (circularGaussianLaw : Measure ℂ).real {z | ‖z‖ ≤ r} ≤
      Real.exp 1 * Real.sqrt Real.pi * r := by
  let E : Set ℂ := {z | ‖z‖ ≤ r}
  have hE : MeasurableSet E := measurableSet_le measurable_norm measurable_const
  let f : ℂ → ℝ := E.indicator (fun _ => (1 : ℝ))
  let g : ℂ → ℝ := fun z => Real.exp 1 * Real.exp (-((r⁻¹) * ‖z‖) ^ 2)
  have hf : Integrable f (circularGaussianLaw : Measure ℂ) :=
    (integrable_const 1).indicator hE
  have hg : Integrable g (circularGaussianLaw : Measure ℂ) := by
    apply Integrable.of_bound (by dsimp [g]; fun_prop) (Real.exp 1)
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _))]
    exact mul_le_of_le_one_right (Real.exp_pos 1).le
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _)))
  have hfg : ∀ z, f z ≤ g z := by
    intro z
    by_cases hz : z ∈ E
    · have hratio : r⁻¹ * ‖z‖ ≤ 1 := by
        dsimp [E] at hz
        rw [inv_mul_le_one₀ hr]
        exact hz
      have hratio0 : 0 ≤ r⁻¹ * ‖z‖ := mul_nonneg (inv_nonneg.mpr hr.le) (norm_nonneg _)
      have hs : (r⁻¹ * ‖z‖) ^ 2 ≤ 1 := by nlinarith
      dsimp [f, g]
      rw [Set.indicator_of_mem hz]
      calc
        (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
        _ ≤ Real.exp (1 - (r⁻¹ * ‖z‖) ^ 2) := by
          apply Real.exp_le_exp.mpr
          linarith
        _ = Real.exp 1 * Real.exp (-((r⁻¹) * ‖z‖) ^ 2) := by
          rw [show 1 - (r⁻¹ * ‖z‖) ^ 2 = 1 + -((r⁻¹ * ‖z‖) ^ 2) by ring,
            Real.exp_add]
    · dsimp [f]
      simp [Set.indicator, hz]
      positivity
  calc
    (circularGaussianLaw : Measure ℂ).real {z | ‖z‖ ≤ r} =
        ∫ z, f z ∂(circularGaussianLaw : Measure ℂ) := by
      dsimp [f]
      symm
      simpa only [smul_eq_mul, mul_one] using
        (integral_indicator_const (1 : ℝ) hE)
    _ ≤ ∫ z, g z ∂(circularGaussianLaw : Measure ℂ) :=
      integral_mono hf hg hfg
    _ = Real.exp 1 *
        ∫ z, Real.exp (-((r⁻¹) * ‖z‖) ^ 2)
          ∂(circularGaussianLaw : Measure ℂ) := by
      dsimp [g]
      rw [integral_const_mul]
    _ ≤ Real.exp 1 * (Real.sqrt Real.pi / r⁻¹) := by
      gcongr
      exact circularGaussian_integral_exp_neg_sq_norm_le r⁻¹ (inv_pos.mpr hr)
    _ = Real.exp 1 * Real.sqrt Real.pi * r := by
      field_simp

end Erdos522

end AmalgamatedModule65


/-! ===== amalgamated from Research.RadialCharacteristicFractionalIntegralBound ===== -/

section AmalgamatedModule66


open MeasureTheory ProbabilityTheory

namespace Erdos522

/-- Fractional inverse-frequency version of F-099. -/
theorem integral_norm_radialAnnealedCharacteristic_smul_le_of_fractionalMoment
    (n q A : ℕ) (β s C M L : ℝ) (hq : 0 < q) (hβ : 0 ≤ β) (hC : 0 ≤ C)
    (hM : 0 < M) (hL : 0 < L)
    (hmom : ∀ t : ℂ, t ≠ 0 →
      (2 / ((n + 1 : ℕ) : ℝ)) ^ (2 * q) *
          radialCosineSumMoment n s t q ≤
        C * ((((n + 1 : ℕ) : ℝ)⁻¹) ^ q +
          (((n + 1 : ℕ) : ℝ) ^ A) * (‖t‖⁻¹) ^ β)) :
    (∫ w : ℂ, ‖radialAnnealedCharacteristic n s (M • w)‖
      ∂(circularGaussianLaw : Measure ℂ)) ≤
      Real.exp 1 * Real.sqrt Real.pi * (L / M) +
        (Real.exp (-((n + 1 : ℕ) : ℝ) / 8) +
          C * ((((n + 1 : ℕ) : ℝ)⁻¹) ^ q +
            (((n + 1 : ℕ) : ℝ) ^ A) * (L⁻¹) ^ β)) := by
  let E : Set ℂ := {w | ‖w‖ ≤ L / M}
  let B : ℝ := Real.exp (-((n + 1 : ℕ) : ℝ) / 8) +
    C * ((((n + 1 : ℕ) : ℝ)⁻¹) ^ q +
      (((n + 1 : ℕ) : ℝ) ^ A) * (L⁻¹) ^ β)
  have hLM : 0 < L / M := div_pos hL hM
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hE : MeasurableSet E := measurableSet_le measurable_norm measurable_const
  let f : ℂ → ℝ := fun w => ‖radialAnnealedCharacteristic n s (M • w)‖
  let g : ℂ → ℝ := fun w => E.indicator (fun _ => (1 : ℝ)) w + B
  have hfcont : Continuous f := by
    rw [show f = fun w : ℂ =>
        ‖charFun (radialAnnealedLaw n s : Measure ℂ) (M • w)‖ by
      funext w
      dsimp [f]
      rw [charFun_radialAnnealedLaw]]
    exact continuous_norm.comp
      (continuous_charFun.comp (continuous_const.smul continuous_id))
  have hf : Integrable f (circularGaussianLaw : Measure ℂ) := by
    apply Integrable.of_bound hfcont.aestronglyMeasurable 1
    filter_upwards with w
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    rw [← charFun_radialAnnealedLaw]
    exact norm_charFun_le_one _
  have hg : Integrable g (circularGaussianLaw : Measure ℂ) :=
    ((integrable_const 1).indicator hE).add (integrable_const B)
  have hfg : ∀ w, f w ≤ g w := by
    intro w
    by_cases hw : w ∈ E
    · dsimp [g]
      rw [Set.indicator_of_mem hw]
      have hf1 : f w ≤ 1 := by
        dsimp [f]
        rw [← charFun_radialAnnealedLaw]
        exact norm_charFun_le_one _
      linarith
    · have hwgt : L / M < ‖w‖ := lt_of_not_ge (by simpa [E] using hw)
      have hw0 : w ≠ 0 := by
        intro hwz
        subst w
        simp only [norm_zero] at hwgt
        linarith
      have ht0 : (M • w : ℂ) ≠ 0 := smul_ne_zero (ne_of_gt hM) hw0
      have hnorm : L < ‖(M • w : ℂ)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hM]
        simpa [mul_comm] using (div_lt_iff₀ hM).mp hwgt
      have hinv : ‖(M • w : ℂ)‖⁻¹ ≤ L⁻¹ :=
        (inv_le_inv₀ (norm_pos_iff.mpr ht0) hL).2 hnorm.le
      have hinvβ : (‖(M • w : ℂ)‖⁻¹) ^ β ≤ (L⁻¹) ^ β := by
        exact Real.rpow_le_rpow (inv_nonneg.mpr (norm_nonneg _)) hinv hβ
      have hchar := norm_radialAnnealedCharacteristic_le_moment n s (M • w) q hq
      have hm := hmom (M • w) ht0
      have hscaled :
          (2 / ((n + 1 : ℕ) : ℝ)) ^ (2 * q) *
              radialCosineSumMoment n s (M • w) q ≤
            C * ((((n + 1 : ℕ) : ℝ)⁻¹) ^ q +
              (((n + 1 : ℕ) : ℝ) ^ A) * (L⁻¹) ^ β) := by
        refine hm.trans ?_
        gcongr
      dsimp [f, g]
      simp only [Set.indicator, hw, ↓reduceIte, zero_add]
      apply hchar.trans
      dsimp [B]
      exact add_le_add (le_refl _) hscaled
  have hint := integral_mono hf hg hfg
  calc
    (∫ w : ℂ, ‖radialAnnealedCharacteristic n s (M • w)‖
        ∂(circularGaussianLaw : Measure ℂ)) = ∫ w, f w
        ∂(circularGaussianLaw : Measure ℂ) := rfl
    _ ≤ ∫ w, g w ∂(circularGaussianLaw : Measure ℂ) := hint
    _ = (circularGaussianLaw : Measure ℂ).real E + B := by
      dsimp [g]
      rw [integral_add ((integrable_const 1).indicator hE) (integrable_const B),
        integral_indicator_const (1 : ℝ) hE, integral_const]
      simp
    _ ≤ Real.exp 1 * Real.sqrt Real.pi * (L / M) + B := by
      gcongr
      exact circularGaussian_measureReal_norm_le (L / M) hLM
    _ = _ := rfl

end Erdos522

end AmalgamatedModule66


/-! ===== amalgamated from Research.AnnealedGaussianSmoothing ===== -/

section AmalgamatedModule67


open MeasureTheory Filter Topology ProbabilityTheory
open scoped ComplexConjugate

namespace Erdos522

/-- The local F-043 estimate and the trivial characteristic-function bound
combine into a global polynomial estimate, with the bad large-frequency region
absorbed by a fourth-order term. -/
theorem norm_radialAnnealedCharacteristic_sub_circular_global_le
    (n : ℕ) (hn : 0 < n) (s : ℝ) (t : ℂ) :
    ‖radialAnnealedCharacteristic n s t - circularGaussianCharacteristic t‖ ≤
      ((7 / 24 : ℝ) * (Real.exp (4 * |s|) / (n + 1 : ℝ)) +
          2 * (Real.exp (4 * |s|) / (n + 1 : ℝ)) ^ 2) * ‖t‖ ^ 4 +
        Real.sqrt (Real.exp (4 * |s|) / (n + 1 : ℝ)) / 4 * ‖t‖ ^ 2 := by
  let B : ℝ := Real.exp (4 * |s|) / (n + 1 : ℝ)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hsqrt : (Real.sqrt B) ^ 2 = B := Real.sq_sqrt hB
  by_cases hsmall : ‖t‖ * Real.sqrt B ≤ 1
  · have hlocal := norm_radialAnnealedCharacteristic_sub_circular_le
      n hn s t (by simpa [B] using hsmall)
    change ‖radialAnnealedCharacteristic n s t - circularGaussianCharacteristic t‖ ≤
      ((7 / 24 : ℝ) * B + 2 * B ^ 2) * ‖t‖ ^ 4 +
        Real.sqrt B / 4 * ‖t‖ ^ 2
    calc
      ‖radialAnnealedCharacteristic n s t - circularGaussianCharacteristic t‖ ≤
          (7 / 24 : ℝ) * (‖t‖ * Real.sqrt B) ^ 2 * ‖t‖ ^ 2 +
            ‖t‖ ^ 2 / 4 * Real.sqrt B := by simpa [B] using hlocal
      _ ≤ ((7 / 24 : ℝ) * B + 2 * B ^ 2) * ‖t‖ ^ 4 +
            Real.sqrt B / 4 * ‖t‖ ^ 2 := by
        rw [show (‖t‖ * Real.sqrt B) ^ 2 = ‖t‖ ^ 2 * B by
          rw [mul_pow, hsqrt]]
        ring_nf
        have hextra : 0 ≤ ‖t‖ ^ 4 * B ^ 2 * 2 := by positivity
        linarith
  · have hlarge : 1 < ‖t‖ * Real.sqrt B := lt_of_not_ge hsmall
    have htriv :
        ‖radialAnnealedCharacteristic n s t - circularGaussianCharacteristic t‖ ≤ 2 := by
      calc
        ‖radialAnnealedCharacteristic n s t - circularGaussianCharacteristic t‖ ≤
            ‖radialAnnealedCharacteristic n s t‖ +
              ‖circularGaussianCharacteristic t‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := by
          rw [← charFun_radialAnnealedLaw, ← charFun_circularGaussianLaw]
          exact add_le_add (norm_charFun_le_one t) (norm_charFun_le_one t)
        _ = 2 := by norm_num
    change ‖radialAnnealedCharacteristic n s t - circularGaussianCharacteristic t‖ ≤
      ((7 / 24 : ℝ) * B + 2 * B ^ 2) * ‖t‖ ^ 4 +
        Real.sqrt B / 4 * ‖t‖ ^ 2
    have hpow : 1 ≤ B ^ 2 * ‖t‖ ^ 4 := by
      have hp : 1 < (‖t‖ * Real.sqrt B) ^ 4 :=
        one_lt_pow₀ hlarge (by norm_num)
      rw [mul_pow, show (Real.sqrt B) ^ 4 = B ^ 2 by nlinarith] at hp
      nlinarith
    calc
      ‖radialAnnealedCharacteristic n s t - circularGaussianCharacteristic t‖ ≤ 2 := htriv
      _ ≤ ((7 / 24 : ℝ) * B + 2 * B ^ 2) * ‖t‖ ^ 4 +
            Real.sqrt B / 4 * ‖t‖ ^ 2 := by
        have ht0 : 0 ≤ ‖t‖ ^ 2 := sq_nonneg _
        have hs0 : 0 ≤ Real.sqrt B := Real.sqrt_nonneg _
        nlinarith [mul_nonneg hB ht0, sq_nonneg B,
          mul_nonneg (sq_nonneg B) (sq_nonneg (‖t‖ ^ 2))]

/-- Integrating the global characteristic-function error against a scaled
circular-Gaussian frequency gives an explicit bound in terms of its finite
second and fourth norm moments. -/
theorem integral_norm_radialAnnealedCharacteristic_sub_circular_le
    (n : ℕ) (hn : 0 < n) (s : ℝ) (M : NNReal) :
    (∫ z : ℂ, ‖radialAnnealedCharacteristic n s ((M : ℝ) • z) -
        circularGaussianCharacteristic ((M : ℝ) • z)‖
        ∂(circularGaussianLaw : Measure ℂ)) ≤
      ((7 / 24 : ℝ) * (Real.exp (4 * |s|) / (n + 1 : ℝ)) +
          2 * (Real.exp (4 * |s|) / (n + 1 : ℝ)) ^ 2) *
            (M : ℝ) ^ 4 * circularGaussianFourthNormMoment +
        Real.sqrt (Real.exp (4 * |s|) / (n + 1 : ℝ)) / 4 *
            (M : ℝ) ^ 2 * circularGaussianSecondNormMoment := by
  let B : ℝ := Real.exp (4 * |s|) / (n + 1 : ℝ)
  let A : ℝ := (7 / 24 : ℝ) * B + 2 * B ^ 2
  let D : ℝ := Real.sqrt B / 4
  let f : ℂ → ℝ := fun z =>
    ‖radialAnnealedCharacteristic n s ((M : ℝ) • z) -
      circularGaussianCharacteristic ((M : ℝ) • z)‖
  let g : ℂ → ℝ := fun z =>
    A * (M : ℝ) ^ 4 * ‖z‖ ^ 4 + D * (M : ℝ) ^ 2 * ‖z‖ ^ 2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hgint : Integrable g (circularGaussianLaw : Measure ℂ) := by
    dsimp [g]
    exact (integrable_circularGaussian_norm_pow_four.const_mul
      (A * (M : ℝ) ^ 4)).add
      (integrable_circularGaussian_norm_sq.const_mul (D * (M : ℝ) ^ 2))
  have hfmeas : AEStronglyMeasurable f
      (circularGaussianLaw : Measure ℂ) := by
    apply Continuous.aestronglyMeasurable
    dsimp [f]
    rw [show radialAnnealedCharacteristic n s =
      charFun (radialAnnealedLaw n s : Measure ℂ) by
        funext t; exact (charFun_radialAnnealedLaw n s t).symm]
    rw [show circularGaussianCharacteristic =
      charFun (circularGaussianLaw : Measure ℂ) by
        funext t; exact (charFun_circularGaussianLaw t).symm]
    fun_prop
  have hfint : Integrable f (circularGaussianLaw : Measure ℂ) := by
    apply hgint.mono' hfmeas
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    dsimp [f, g]
    have h := norm_radialAnnealedCharacteristic_sub_circular_global_le
      n hn s ((M : ℝ) • z)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg M.coe_nonneg] at h
    simpa [B, A, D, mul_pow, mul_assoc] using h
  calc
    (∫ z : ℂ, ‖radialAnnealedCharacteristic n s ((M : ℝ) • z) -
        circularGaussianCharacteristic ((M : ℝ) • z)‖
        ∂(circularGaussianLaw : Measure ℂ)) =
        ∫ z, f z ∂(circularGaussianLaw : Measure ℂ) := rfl
    _ ≤ ∫ z, g z ∂(circularGaussianLaw : Measure ℂ) := by
      apply integral_mono hfint hgint
      intro z
      dsimp [f, g]
      have h := norm_radialAnnealedCharacteristic_sub_circular_global_le
        n hn s ((M : ℝ) • z)
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg M.coe_nonneg] at h
      simpa [B, A, D, mul_pow, mul_assoc] using h
    _ = A * (M : ℝ) ^ 4 * circularGaussianFourthNormMoment +
        D * (M : ℝ) ^ 2 * circularGaussianSecondNormMoment := by
      dsimp [g]
      rw [integral_add, integral_const_mul, integral_const_mul]
      · rfl
      · exact integrable_circularGaussian_norm_pow_four.const_mul _
      · exact integrable_circularGaussian_norm_sq.const_mul _
    _ = _ := by rfl

/-- Gaussian smoothing converts a radial Gaussian kernel under the annealed law
into an average of its characteristic function under the circular Gaussian. -/
theorem integral_radialAnnealed_exp_kernel_eq
    (n : ℕ) (s a : ℝ) :
    ((∫ x : ℂ, Real.exp (-(a * ‖x‖) ^ 2 / 4)
        ∂(radialAnnealedLaw n s : Measure ℂ) : ℝ) : ℂ) =
      ∫ z : ℂ, radialAnnealedCharacteristic n s (a • z)
        ∂(circularGaussianLaw : Measure ℂ) := by
  let μ : Measure ℂ := radialAnnealedLaw n s
  let ν : Measure ℂ := circularGaussianLaw
  let f : ℂ → ℂ → ℂ := fun x z =>
    Complex.exp ((inner ℝ x (a • z) : ℝ) * Complex.I)
  have hf : Integrable (Function.uncurry f) (μ.prod ν) := by
    apply Integrable.of_bound (by
      dsimp [f]
      fun_prop) 1
    filter_upwards with u
    rcases u with ⟨x, z⟩
    change ‖Complex.exp (((inner ℝ x (a • z) : ℝ) : ℂ) * Complex.I)‖ ≤ 1
    rw [Complex.norm_exp]
    simp
  calc
    ((∫ x : ℂ, Real.exp (-(a * ‖x‖) ^ 2 / 4) ∂μ : ℝ) : ℂ) =
        ∫ x : ℂ, (Real.exp (-(a * ‖x‖) ^ 2 / 4) : ℂ) ∂μ := by
      exact integral_ofReal.symm
    _ = ∫ x : ℂ, ∫ z : ℂ, f x z ∂ν ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      have hchar : ∫ z : ℂ, f x z ∂ν =
          charFun (circularGaussianLaw : Measure ℂ) (a • x) := by
        rw [charFun_apply]
        apply integral_congr_ae
        filter_upwards with z
        have hinner : (inner ℝ x (a • z) : ℝ) = inner ℝ z (a • x) := by
          rw [real_inner_smul_right, real_inner_smul_right,
            real_inner_comm x z]
        change Complex.exp (((inner ℝ x (a • z) : ℝ) : ℂ) * Complex.I) =
          Complex.exp (((inner ℝ z (a • x) : ℝ) : ℂ) * Complex.I)
        rw [hinner]
      rw [hchar, charFun_circularGaussianLaw]
      unfold circularGaussianCharacteristic
      simp_rw [Complex.ofReal_exp]
      rw [norm_smul, Real.norm_eq_abs]
      have hsq : -(a * ‖x‖) ^ 2 / 4 = -(|a| * ‖x‖) ^ 2 / 4 := by
        calc
          -(a * ‖x‖) ^ 2 / 4 = -(a ^ 2 * ‖x‖ ^ 2) / 4 := by ring
          _ = -(|a| ^ 2 * ‖x‖ ^ 2) / 4 := by rw [sq_abs]
          _ = -(|a| * ‖x‖) ^ 2 / 4 := by ring
      exact congrArg (fun r : ℝ => Complex.exp (r : ℂ)) hsq
    _ = ∫ z : ℂ, ∫ x : ℂ, f x z ∂μ ∂ν :=
      integral_integral_swap hf
    _ = ∫ z : ℂ, radialAnnealedCharacteristic n s (a • z) ∂ν := by
      apply integral_congr_ae
      filter_upwards with z
      rw [← charFun_radialAnnealedLaw]
      rw [charFun_apply]

/-- The annealed Gaussian-kernel expectation is bounded by a one-dimensional
Gaussian main term and the integrated characteristic-function error. -/
theorem integral_radialAnnealed_exp_kernel_le
    (n : ℕ) (hn : 0 < n) (s : ℝ) (M : NNReal) (hM : 0 < M) :
    (∫ x : ℂ, Real.exp (-((M : ℝ) * ‖x‖) ^ 2 / 4)
        ∂(radialAnnealedLaw n s : Measure ℂ)) ≤
      2 * Real.sqrt Real.pi / (M : ℝ) +
        ((7 / 24 : ℝ) * (Real.exp (4 * |s|) / (n + 1 : ℝ)) +
          2 * (Real.exp (4 * |s|) / (n + 1 : ℝ)) ^ 2) *
            (M : ℝ) ^ 4 * circularGaussianFourthNormMoment +
        Real.sqrt (Real.exp (4 * |s|) / (n + 1 : ℝ)) / 4 *
            (M : ℝ) ^ 2 * circularGaussianSecondNormMoment := by
  let φ : ℂ → ℂ := fun z => radialAnnealedCharacteristic n s ((M : ℝ) • z)
  let γ : ℂ → ℂ := fun z => circularGaussianCharacteristic ((M : ℝ) • z)
  let e : ℂ → ℝ := fun z => ‖φ z - γ z‖
  have hid := integral_radialAnnealed_exp_kernel_eq n s (M : ℝ)
  have hleft0 : 0 ≤ ∫ x : ℂ, Real.exp (-((M : ℝ) * ‖x‖) ^ 2 / 4)
      ∂(radialAnnealedLaw n s : Measure ℂ) :=
    integral_nonneg (fun _ => (Real.exp_pos _).le)
  have hφint : Integrable φ (circularGaussianLaw : Measure ℂ) := by
    apply Integrable.of_bound (by
      dsimp [φ]
      rw [show radialAnnealedCharacteristic n s =
        charFun (radialAnnealedLaw n s : Measure ℂ) by
          funext t; exact (charFun_radialAnnealedLaw n s t).symm]
      fun_prop) 1
    filter_upwards with z
    dsimp [φ]
    rw [← charFun_radialAnnealedLaw]
    exact norm_charFun_le_one _
  have hγint : Integrable γ (circularGaussianLaw : Measure ℂ) := by
    apply Integrable.of_bound (by
      dsimp [γ]
      rw [show circularGaussianCharacteristic =
        charFun (circularGaussianLaw : Measure ℂ) by
          funext t; exact (charFun_circularGaussianLaw t).symm]
      fun_prop) 1
    filter_upwards with z
    dsimp [γ]
    rw [← charFun_circularGaussianLaw]
    exact norm_charFun_le_one _
  have heint : Integrable e (circularGaussianLaw : Measure ℂ) :=
    (hφint.sub hγint).norm
  have hmain :
      (∫ z : ℂ, ‖γ z‖ ∂(circularGaussianLaw : Measure ℂ)) ≤
        2 * Real.sqrt Real.pi / (M : ℝ) := by
    have hbound := circularGaussian_integral_exp_neg_sq_norm_le
      ((M : ℝ) / 2) (by positivity)
    dsimp [γ]
    simp only [circularGaussianCharacteristic, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), norm_smul, norm_mul, Real.norm_eq_abs,
      abs_of_nonneg M.coe_nonneg]
    convert hbound using 1 <;> ring
  have herr := integral_norm_radialAnnealedCharacteristic_sub_circular_le
    n hn s M
  calc
    (∫ x : ℂ, Real.exp (-((M : ℝ) * ‖x‖) ^ 2 / 4)
        ∂(radialAnnealedLaw n s : Measure ℂ)) =
        ‖((∫ x : ℂ, Real.exp (-((M : ℝ) * ‖x‖) ^ 2 / 4)
          ∂(radialAnnealedLaw n s : Measure ℂ) : ℝ) : ℂ)‖ := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hleft0]
    _ = ‖∫ z : ℂ, φ z ∂(circularGaussianLaw : Measure ℂ)‖ := by
      rw [hid]
    _ ≤ ∫ z : ℂ, ‖φ z‖ ∂(circularGaussianLaw : Measure ℂ) :=
      norm_integral_le_integral_norm φ
    _ ≤ ∫ z : ℂ, (‖γ z‖ + e z) ∂(circularGaussianLaw : Measure ℂ) := by
      apply integral_mono hφint.norm (hγint.norm.add heint)
      intro z
      dsimp [e]
      exact (norm_le_norm_add_norm_sub' (φ z) (γ z))
    _ = (∫ z : ℂ, ‖γ z‖ ∂(circularGaussianLaw : Measure ℂ)) +
        ∫ z : ℂ, e z ∂(circularGaussianLaw : Measure ℂ) := by
      rw [integral_add hγint.norm heint]
    _ ≤ 2 * Real.sqrt Real.pi / (M : ℝ) +
        ((7 / 24 : ℝ) * (Real.exp (4 * |s|) / (n + 1 : ℝ)) +
          2 * (Real.exp (4 * |s|) / (n + 1 : ℝ)) ^ 2) *
            (M : ℝ) ^ 4 * circularGaussianFourthNormMoment +
        Real.sqrt (Real.exp (4 * |s|) / (n + 1 : ℝ)) / 4 *
            (M : ℝ) ^ 2 * circularGaussianSecondNormMoment := by
      calc
        (∫ z : ℂ, ‖γ z‖ ∂(circularGaussianLaw : Measure ℂ)) +
            ∫ z : ℂ, e z ∂(circularGaussianLaw : Measure ℂ) ≤
            2 * Real.sqrt Real.pi / (M : ℝ) +
              (((7 / 24 : ℝ) * (Real.exp (4 * |s|) / (n + 1 : ℝ)) +
                2 * (Real.exp (4 * |s|) / (n + 1 : ℝ)) ^ 2) *
                  (M : ℝ) ^ 4 * circularGaussianFourthNormMoment +
              Real.sqrt (Real.exp (4 * |s|) / (n + 1 : ℝ)) / 4 *
                  (M : ℝ) ^ 2 * circularGaussianSecondNormMoment) := by
                    apply add_le_add hmain
                    simpa [e, φ, γ] using herr
        _ = _ := by ring

end Erdos522

end AmalgamatedModule67


/-! ===== amalgamated from Research.AnnealedSmallBallBound ===== -/

section AmalgamatedModule68


open MeasureTheory

namespace Erdos522

/-- The triangular cutoff is pointwise dominated by a Gaussian kernel at the
same inverse-radius scale. -/
lemma smallBallCutoff_le_exp_kernel
    (M : NNReal) (hM : 0 < M) (z : ℂ) :
    smallBallCutoff M z ≤
      Real.exp 1 * Real.exp (-((M : ℝ) * ‖z‖) ^ 2 / 4) := by
  by_cases hz : 2 / (M : ℝ) ≤ ‖z‖
  · rw [smallBallCutoff_eq_zero_of_le_norm hM hz]
    positivity
  · have hMr : (0 : ℝ) < M := by exact_mod_cast hM
    have hMn : (M : ℝ) * ‖z‖ < 2 := by
      apply (lt_div_iff₀' hMr).mp
      simpa [mul_comm] using lt_of_not_ge hz
    have hMn0 : 0 ≤ (M : ℝ) * ‖z‖ := mul_nonneg hMr.le (norm_nonneg z)
    have hsq : ((M : ℝ) * ‖z‖) ^ 2 ≤ 4 := by nlinarith
    calc
      smallBallCutoff M z ≤ 1 := smallBallCutoff_le_one M z
      _ ≤ Real.exp 1 * Real.exp (-((M : ℝ) * ‖z‖) ^ 2 / 4) := by
        calc
          (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
          _ ≤ Real.exp (1 + (-((M : ℝ) * ‖z‖) ^ 2 / 4)) := by
            apply Real.exp_le_exp.mpr
            nlinarith
          _ = Real.exp 1 * Real.exp (-((M : ℝ) * ‖z‖) ^ 2 / 4) :=
            Real.exp_add _ _

/-- Explicit annealed small-ball bound obtained from F-043 by Gaussian
smoothing.  It is quantitative for clipping levels that grow with `n`. -/
theorem cubeAverage_radialCubeSmallBallStatistic_le
    (n : ℕ) (hn : 0 < n) (s : ℝ) (M : NNReal) (hM : 0 < M) :
    cubeAverage (radialCubeSmallBallStatistic n s M) ≤
      Real.exp 1 *
        (2 * Real.sqrt Real.pi / (M : ℝ) +
          ((7 / 24 : ℝ) * (Real.exp (4 * |s|) / (n + 1 : ℝ)) +
            2 * (Real.exp (4 * |s|) / (n + 1 : ℝ)) ^ 2) *
              (M : ℝ) ^ 4 * circularGaussianFourthNormMoment +
          Real.sqrt (Real.exp (4 * |s|) / (n + 1 : ℝ)) / 4 *
              (M : ℝ) ^ 2 * circularGaussianSecondNormMoment) := by
  have hcutInt : Integrable (smallBallCutoff M)
      (radialAnnealedLaw n s : Measure ℂ) := by
    apply Integrable.of_bound (smallBallCutoff_lipschitz M).continuous.aestronglyMeasurable 1
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (smallBallCutoff_nonneg M z)]
    exact smallBallCutoff_le_one M z
  have hkernelInt : Integrable
      (fun z : ℂ => Real.exp 1 *
        Real.exp (-((M : ℝ) * ‖z‖) ^ 2 / 4))
      (radialAnnealedLaw n s : Measure ℂ) := by
    apply Integrable.of_bound (by fun_prop) (Real.exp 1)
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _))]
    exact mul_le_of_le_one_right (Real.exp_pos 1).le
      (Real.exp_le_one_iff.mpr (by
        nlinarith [sq_nonneg ((M : ℝ) * ‖z‖)]))
  change cubeAverage (radialCubeAngularStatistic n s (smallBallCutoff M)) ≤ _
  rw [← integral_radialAnnealedLaw_eq_cubeAverage n s (smallBallCutoff M)
    (smallBallCutoff_lipschitz M).continuous 1 (fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (smallBallCutoff_nonneg M z)]
      exact smallBallCutoff_le_one M z)]
  calc
    (∫ z : ℂ, smallBallCutoff M z
        ∂(radialAnnealedLaw n s : Measure ℂ)) ≤
        ∫ z : ℂ, Real.exp 1 *
          Real.exp (-((M : ℝ) * ‖z‖) ^ 2 / 4)
          ∂(radialAnnealedLaw n s : Measure ℂ) := by
      apply integral_mono hcutInt hkernelInt
      exact smallBallCutoff_le_exp_kernel M hM
    _ = Real.exp 1 *
        ∫ z : ℂ, Real.exp (-((M : ℝ) * ‖z‖) ^ 2 / 4)
          ∂(radialAnnealedLaw n s : Measure ℂ) := by
      rw [integral_const_mul]
    _ ≤ Real.exp 1 *
        (2 * Real.sqrt Real.pi / (M : ℝ) +
          ((7 / 24 : ℝ) * (Real.exp (4 * |s|) / (n + 1 : ℝ)) +
            2 * (Real.exp (4 * |s|) / (n + 1 : ℝ)) ^ 2) *
              (M : ℝ) ^ 4 * circularGaussianFourthNormMoment +
          Real.sqrt (Real.exp (4 * |s|) / (n + 1 : ℝ)) / 4 *
              (M : ℝ) ^ 2 * circularGaussianSecondNormMoment) := by
      apply mul_le_mul_of_nonneg_left
        (integral_radialAnnealed_exp_kernel_le n hn s M hM)
        (Real.exp_pos 1).le

end Erdos522

end AmalgamatedModule68


/-! ===== amalgamated from Research.AnnealedSmallBallCharacteristicIntegral ===== -/

section AmalgamatedModule69


open MeasureTheory

namespace Erdos522

/-- Gaussian smoothing converts an integrated annealed characteristic estimate
at frequency scale `M` into a spatial small-ball estimate at radius `1/M`. -/
theorem radialAnnealedLaw_smallBall_le_characteristicIntegral
    (n : ℕ) (s : ℝ) (M : NNReal) (hM : 0 < M) :
    (radialAnnealedLaw n s : Measure ℂ).real
        {z | ‖z‖ ≤ ((M : ℝ)⁻¹)} ≤
      Real.exp 1 *
        ∫ w : ℂ, ‖radialAnnealedCharacteristic n s ((M : ℝ) • w)‖
          ∂(circularGaussianLaw : Measure ℂ) := by
  let E : Set ℂ := {z | ‖z‖ ≤ ((M : ℝ)⁻¹)}
  let f : ℂ → ℝ := E.indicator (fun _ => (1 : ℝ))
  let k : ℂ → ℝ := fun z =>
    Real.exp 1 * Real.exp (-(((M : ℝ) * ‖z‖) ^ 2) / 4)
  have hE : MeasurableSet E := measurableSet_le measurable_norm measurable_const
  have hf : Integrable f (radialAnnealedLaw n s : Measure ℂ) :=
    (integrable_const 1).indicator hE
  have hk : Integrable k (radialAnnealedLaw n s : Measure ℂ) := by
    apply Integrable.of_bound (by dsimp [k]; fun_prop) (Real.exp 1)
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _))]
    exact mul_le_of_le_one_right (Real.exp_pos 1).le
      (Real.exp_le_one_iff.mpr (by
        nlinarith [sq_nonneg ((M : ℝ) * ‖z‖)]))
  have hfk : ∀ z, f z ≤ k z := by
    intro z
    by_cases hz : z ∈ E
    · have hMr : (0 : ℝ) < M := by exact_mod_cast hM
      have hnorm : ‖z‖ ≤ 1 / (M : ℝ) := by simpa [E, one_div] using hz
      have hcut : smallBallCutoff M z = 1 :=
        smallBallCutoff_eq_one_of_norm_le hM hnorm
      dsimp [f]
      rw [Set.indicator_of_mem hz, ← hcut]
      exact smallBallCutoff_le_exp_kernel M hM z
    · dsimp [f]
      simp only [Set.indicator, hz, ↓reduceIte]
      positivity
  have hkernel_nonneg : 0 ≤
      ∫ z : ℂ, Real.exp (-(((M : ℝ) * ‖z‖) ^ 2) / 4)
        ∂(radialAnnealedLaw n s : Measure ℂ) :=
    integral_nonneg fun _ => (Real.exp_pos _).le
  have hsmooth :
      (∫ z : ℂ, Real.exp (-(((M : ℝ) * ‖z‖) ^ 2) / 4)
          ∂(radialAnnealedLaw n s : Measure ℂ)) ≤
        ∫ w : ℂ, ‖radialAnnealedCharacteristic n s ((M : ℝ) • w)‖
          ∂(circularGaussianLaw : Measure ℂ) := by
    let I : ℝ := ∫ z : ℂ, Real.exp (-(((M : ℝ) * ‖z‖) ^ 2) / 4)
      ∂(radialAnnealedLaw n s : Measure ℂ)
    have hid := integral_radialAnnealed_exp_kernel_eq n s (M : ℝ)
    calc
      (∫ z : ℂ, Real.exp (-(((M : ℝ) * ‖z‖) ^ 2) / 4)
          ∂(radialAnnealedLaw n s : Measure ℂ)) = I := rfl
      _ = ‖(I : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hkernel_nonneg]
      _ = ‖∫ w : ℂ, radialAnnealedCharacteristic n s ((M : ℝ) • w)
          ∂(circularGaussianLaw : Measure ℂ)‖ := congrArg norm hid
      _ ≤ ∫ w : ℂ, ‖radialAnnealedCharacteristic n s ((M : ℝ) • w)‖
          ∂(circularGaussianLaw : Measure ℂ) := norm_integral_le_integral_norm _
  calc
    (radialAnnealedLaw n s : Measure ℂ).real
        {z | ‖z‖ ≤ ((M : ℝ)⁻¹)} =
        ∫ z, f z ∂(radialAnnealedLaw n s : Measure ℂ) := by
      dsimp [f, E]
      symm
      simpa only [smul_eq_mul, mul_one] using
        (integral_indicator_const (1 : ℝ) hE)
    _ ≤ ∫ z, k z ∂(radialAnnealedLaw n s : Measure ℂ) :=
      integral_mono hf hk hfk
    _ = Real.exp 1 *
        ∫ z : ℂ, Real.exp (-(((M : ℝ) * ‖z‖) ^ 2) / 4)
          ∂(radialAnnealedLaw n s : Measure ℂ) := by
      dsimp [k]
      rw [integral_const_mul]
    _ ≤ Real.exp 1 *
        ∫ w : ℂ, ‖radialAnnealedCharacteristic n s ((M : ℝ) • w)‖
          ∂(circularGaussianLaw : Measure ℂ) := by
      gcongr

end Erdos522

end AmalgamatedModule69


/-! ===== amalgamated from Research.StretchedExponentialPolynomial ===== -/

section AmalgamatedModule70


open Filter Topology Asymptotics

namespace Erdos522

/-- A positive stretched exponential eventually absorbs an arbitrary fixed
constant and polynomial, with any prescribed inverse-polynomial remainder. -/
theorem eventually_const_mul_pow_div_exp_rpow_le_inv_pow
    (c : ℝ) (hc : 0 ≤ c) (d K : ℕ) (r : ℝ) (hr : 0 < r) :
    ∀ᶠ n : ℕ in atTop,
      c * (((n + 1 : ℕ) : ℝ) ^ d) /
          Real.exp ((((n + 1 : ℕ) : ℝ) ^ r)) ≤
        ((((n + 1 : ℕ) : ℝ)⁻¹) ^ K) := by
  let X : ℕ → ℝ := fun n => ((n + 1 : ℕ) : ℝ)
  let D : ℕ := d + K + 1
  have hD : (0 : ℝ) < D := by
    dsimp [D]
    positivity
  have hXtop : Tendsto X atTop atTop := by
    dsimp [X]
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hcX : ∀ᶠ n : ℕ in atTop, c ≤ X n := hXtop.eventually_ge_atTop c
  have hXone : ∀ᶠ n : ℕ in atTop, 1 ≤ X n := by
    filter_upwards with n
    dsimp [X]
    simp
  have hlittle : ∀ᶠ x : ℝ in atTop,
      ‖Real.log x‖ ≤ (1 / (D : ℝ)) * ‖x ^ r‖ :=
    (isLittleO_log_rpow_atTop hr).bound (by positivity)
  have hlog : ∀ᶠ n : ℕ in atTop,
      ‖Real.log (X n)‖ ≤ (1 / (D : ℝ)) * ‖(X n) ^ r‖ :=
    hXtop.eventually hlittle
  filter_upwards [hcX, hXone, hlog] with n hcn hxn hln
  have hx : 0 < X n := lt_of_lt_of_le zero_lt_one hxn
  have hlog0 : 0 ≤ Real.log (X n) := Real.log_nonneg hxn
  have hrpow0 : 0 ≤ (X n) ^ r := Real.rpow_nonneg hx.le _
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hlog0, abs_of_nonneg hrpow0] at hln
  have hdom : (D : ℝ) * Real.log (X n) ≤ (X n) ^ r := by
    have hD0 : (0 : ℝ) < D := hD
    calc
      (D : ℝ) * Real.log (X n) ≤
          (D : ℝ) * ((1 / (D : ℝ)) * (X n) ^ r) := by gcongr
      _ = (X n) ^ r := by field_simp
  have hexp : Real.exp (-((X n) ^ r)) ≤ (X n) ^ (-(D : ℝ)) := by
    calc
      Real.exp (-((X n) ^ r)) ≤
          Real.exp (-(D : ℝ) * Real.log (X n)) := by
        apply Real.exp_le_exp.mpr
        linarith
      _ = (X n) ^ (-(D : ℝ)) := by
        rw [Real.rpow_def_of_pos hx]
        congr 1
        ring
  have hpowD : (X n) ^ (-(D : ℝ)) = 1 / (X n) ^ D := by
    rw [Real.rpow_neg hx.le, Real.rpow_natCast, one_div]
  have hexp' : Real.exp (-((X n) ^ r)) ≤ 1 / (X n) ^ D := by
    rwa [← hpowD]
  have hmain : c * (X n) ^ d * Real.exp (-((X n) ^ r)) ≤
      X n * (X n) ^ d * (1 / (X n) ^ D) := by
    calc
      c * (X n) ^ d * Real.exp (-((X n) ^ r)) ≤
          c * (X n) ^ d * (1 / (X n) ^ D) := by
        gcongr
      _ ≤ X n * (X n) ^ d * (1 / (X n) ^ D) := by
        gcongr
  dsimp [X] at *
  rw [div_eq_mul_inv, ← Real.exp_neg] 
  calc
    c * (((n + 1 : ℕ) : ℝ) ^ d) *
        Real.exp (-(((n + 1 : ℕ) : ℝ) ^ r)) ≤
        ((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) ^ d) *
          (1 / (((n + 1 : ℕ) : ℝ) ^ D)) := hmain
    _ = ((((n + 1 : ℕ) : ℝ)⁻¹) ^ K) := by
      have hne : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
      dsimp [D]
      rw [inv_pow]
      field_simp
      ring

end Erdos522

end AmalgamatedModule70


/-! ===== amalgamated from Research.ExponentialPolynomialDomination ===== -/

section AmalgamatedModule71


open Filter Topology Asymptotics

namespace Erdos522

/-- Version of F-101 with an arbitrary positive coefficient in the stretched
exponent. -/
theorem eventually_const_mul_pow_div_exp_mul_rpow_le_inv_pow
    (c a : ℝ) (hc : 0 ≤ c) (ha : 0 < a) (d K : ℕ) (r : ℝ) (hr : 0 < r) :
    ∀ᶠ n : ℕ in atTop,
      c * (((n + 1 : ℕ) : ℝ) ^ d) /
          Real.exp (a * (((n + 1 : ℕ) : ℝ) ^ r)) ≤
        ((((n + 1 : ℕ) : ℝ)⁻¹) ^ K) := by
  let X : ℕ → ℝ := fun n => ((n + 1 : ℕ) : ℝ)
  let D : ℕ := d + K + 1
  have hD : (0 : ℝ) < D := by dsimp [D]; positivity
  have hXtop : Tendsto X atTop atTop := by
    dsimp [X]
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hcX : ∀ᶠ n : ℕ in atTop, c ≤ X n := hXtop.eventually_ge_atTop c
  have hXone : ∀ᶠ n : ℕ in atTop, 1 ≤ X n := by
    filter_upwards with n
    dsimp [X]
    simp
  have hlittle : ∀ᶠ x : ℝ in atTop,
      ‖Real.log x‖ ≤ (a / (D : ℝ)) * ‖x ^ r‖ :=
    (isLittleO_log_rpow_atTop hr).bound (by positivity)
  have hlog : ∀ᶠ n : ℕ in atTop,
      ‖Real.log (X n)‖ ≤ (a / (D : ℝ)) * ‖(X n) ^ r‖ :=
    hXtop.eventually hlittle
  filter_upwards [hcX, hXone, hlog] with n hcn hxn hln
  have hx : 0 < X n := lt_of_lt_of_le zero_lt_one hxn
  have hlog0 : 0 ≤ Real.log (X n) := Real.log_nonneg hxn
  have hrpow0 : 0 ≤ (X n) ^ r := Real.rpow_nonneg hx.le _
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hlog0, abs_of_nonneg hrpow0] at hln
  have hdom : (D : ℝ) * Real.log (X n) ≤ a * (X n) ^ r := by
    calc
      (D : ℝ) * Real.log (X n) ≤
          (D : ℝ) * ((a / (D : ℝ)) * (X n) ^ r) := by gcongr
      _ = a * (X n) ^ r := by field_simp
  have hexp : Real.exp (-(a * (X n) ^ r)) ≤ (X n) ^ (-(D : ℝ)) := by
    calc
      Real.exp (-(a * (X n) ^ r)) ≤
          Real.exp (-(D : ℝ) * Real.log (X n)) := by
        apply Real.exp_le_exp.mpr
        linarith
      _ = (X n) ^ (-(D : ℝ)) := by
        rw [Real.rpow_def_of_pos hx]
        congr 1
        ring
  have hpowD : (X n) ^ (-(D : ℝ)) = 1 / (X n) ^ D := by
    rw [Real.rpow_neg hx.le, Real.rpow_natCast, one_div]
  have hexp' : Real.exp (-(a * (X n) ^ r)) ≤ 1 / (X n) ^ D := by
    rwa [← hpowD]
  have hmain : c * (X n) ^ d * Real.exp (-(a * (X n) ^ r)) ≤
      X n * (X n) ^ d * (1 / (X n) ^ D) := by
    calc
      c * (X n) ^ d * Real.exp (-(a * (X n) ^ r)) ≤
          c * (X n) ^ d * (1 / (X n) ^ D) := by gcongr
      _ ≤ X n * (X n) ^ d * (1 / (X n) ^ D) := by gcongr
  dsimp [X] at *
  rw [div_eq_mul_inv, ← Real.exp_neg]
  calc
    c * (((n + 1 : ℕ) : ℝ) ^ d) *
        Real.exp (-(a * (((n + 1 : ℕ) : ℝ) ^ r))) ≤
        ((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) ^ d) *
          (1 / (((n + 1 : ℕ) : ℝ) ^ D)) := hmain
    _ = ((((n + 1 : ℕ) : ℝ)⁻¹) ^ K) := by
      have hne : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
      dsimp [D]
      rw [inv_pow]
      field_simp
      ring

end Erdos522

end AmalgamatedModule71


/-! ===== amalgamated from Research.InversePowerDomination ===== -/

section AmalgamatedModule72


open Filter Topology

namespace Erdos522

/-- A fixed nonnegative constant is absorbed by one spare inverse power, and
hence by any strictly smaller target exponent. -/
theorem eventually_const_mul_inv_pow_le_inv_pow
    (c : ℝ) (hc : 0 ≤ c) (D K : ℕ) (hDK : K < D) :
    ∀ᶠ n : ℕ in atTop,
      c * ((((n + 1 : ℕ) : ℝ)⁻¹) ^ D) ≤
        ((((n + 1 : ℕ) : ℝ)⁻¹) ^ K) := by
  have htop : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hcX : ∀ᶠ n : ℕ in atTop, c ≤ ((n + 1 : ℕ) : ℝ) :=
    htop.eventually_ge_atTop c
  filter_upwards [hcX] with n hcn
  let X : ℝ := ((n + 1 : ℕ) : ℝ)
  have hX : 1 ≤ X := by simp [X]
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hstep : c * (X⁻¹ ^ D) ≤ X * (X⁻¹ ^ D) := by gcongr
  have hpow : X * (X⁻¹ ^ D) = X⁻¹ ^ (D - 1) := by
    rw [show D = (D - 1) + 1 by omega, pow_add, pow_one]
    calc
      X * (X⁻¹ ^ (D - 1) * X⁻¹) =
          X⁻¹ ^ (D - 1) * (X * X⁻¹) := by ring
      _ = X⁻¹ ^ (D - 1) := by rw [mul_inv_cancel₀ hX0.ne']; simp
  have hmono : X⁻¹ ^ (D - 1) ≤ X⁻¹ ^ K := by
    have hinv : X⁻¹ ≤ 1 := (inv_le_one₀ hX0).mpr hX
    exact pow_le_pow_of_le_one (inv_nonneg.mpr hX0.le) hinv (by omega)
  exact hstep.trans (hpow.le.trans hmono)

end Erdos522

end AmalgamatedModule72


/-! ===== amalgamated from Research.HighBallCutoff ===== -/

section AmalgamatedModule73


open MeasureTheory

namespace Erdos522

/-- A bounded continuous majorant of the event `M ≤ ‖z‖`. -/
noncomputable def highBallCutoff (M : NNReal) (z : ℂ) : ℝ :=
  min 1 ((‖z‖ / (M : ℝ)) ^ 2)

lemma highBallCutoff_nonneg (M : NNReal) (z : ℂ) :
    0 ≤ highBallCutoff M z := by
  unfold highBallCutoff
  exact le_min (by norm_num) (sq_nonneg _)

lemma highBallCutoff_le_one (M : NNReal) (z : ℂ) :
    highBallCutoff M z ≤ 1 := min_le_left _ _

lemma highBallCutoff_eq_one_of_le_norm
    {M : NNReal} (hM : 0 < M) {z : ℂ} (hz : (M : ℝ) ≤ ‖z‖) :
    highBallCutoff M z = 1 := by
  unfold highBallCutoff
  rw [min_eq_left]
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have : 1 ≤ ‖z‖ / (M : ℝ) := (le_div_iff₀ hMr).mpr (by simpa using hz)
  nlinarith

lemma highBallCutoff_le_sq_div
    {M : NNReal} (z : ℂ) :
    highBallCutoff M z ≤ ‖z‖ ^ 2 / (M : ℝ) ^ 2 := by
  unfold highBallCutoff
  calc
    min 1 ((‖z‖ / (M : ℝ)) ^ 2) ≤ (‖z‖ / (M : ℝ)) ^ 2 := min_le_right _ _
    _ = ‖z‖ ^ 2 / (M : ℝ) ^ 2 := by ring

/-- The normalized weighted sign polynomial has exact angular `L²` norm one. -/
theorem weightedVectorPolynomial_circleAverage_sq_norm_eq_one
    {N : ℕ} (w : Fin N → ℝ) (hw0 : ∀ k, 0 ≤ w k)
    (hsum : ∑ k, w k = 1) (x : Fin N → Bool) :
    Real.circleAverage
      (fun z => ‖(weightedVectorPolynomial w
        (fun k => realRademacherSign (x k))).eval z‖ ^ 2) 0 1 = 1 := by
  let p := weightedVectorPolynomial w (fun k => realRademacherSign (x k))
  rw [← Polynomial.sum_sq_norm_coeff_eq_circleAverage]
  have hsupp : p.support ⊆ Finset.range N := by
    intro j hj
    rw [Finset.mem_range]
    by_contra hnot
    have hge : N ≤ j := Nat.le_of_not_gt hnot
    have hz := coeff_weightedVectorPolynomial_eq_zero_of_ge w
      (fun k => realRademacherSign (x k)) hge
    exact (Polynomial.mem_support_iff.mp hj) hz
  rw [Finset.sum_subset hsupp]
  · rw [← Fin.sum_univ_eq_sum_range]
    calc
      ∑ k : Fin N, ‖p.coeff k‖ ^ 2 = ∑ k : Fin N, w k := by
        apply Finset.sum_congr rfl
        intro k hk
        dsimp [p]
        rw [coeff_weightedVectorPolynomial]
        simp only [Complex.norm_real, Real.norm_eq_abs, abs_mul]
        rw [abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
          Real.sq_sqrt (hw0 k)]
        simp [realRademacherSign]
      _ = 1 := hsum
  · intro j hj hnot
    have hz : p.coeff j = 0 := by
      by_contra hj0
      exact hnot (Polynomial.mem_support_iff.mpr hj0)
    rw [hz]
    simp

/-- Markov's bound for the high-value cutoff of every normalized weighted sign
polynomial. -/
theorem weightedVectorPolynomial_highBall_circleAverage_le
    {N : ℕ} (w : Fin N → ℝ) (hw0 : ∀ k, 0 ≤ w k)
    (hsum : ∑ k, w k = 1) (x : Fin N → Bool)
    (M : NNReal) (hM : 0 < M) :
    Real.circleAverage
      (fun z => highBallCutoff M
        ((weightedVectorPolynomial w
          (fun k => realRademacherSign (x k))).eval z)) 0 1 ≤
      1 / (M : ℝ) ^ 2 := by
  have hcontHigh : CircleIntegrable
      (fun z => highBallCutoff M
        ((weightedVectorPolynomial w
          (fun k => realRademacherSign (x k))).eval z)) 0 1 := by
    apply ContinuousOn.circleIntegrable (by norm_num)
    unfold highBallCutoff
    fun_prop
  have hcontSq : CircleIntegrable
      (fun z => ‖(weightedVectorPolynomial w
        (fun k => realRademacherSign (x k))).eval z‖ ^ 2 /
          (M : ℝ) ^ 2) 0 1 := by
    apply ContinuousOn.circleIntegrable (by norm_num)
    fun_prop
  calc
    Real.circleAverage
      (fun z => highBallCutoff M
        ((weightedVectorPolynomial w
          (fun k => realRademacherSign (x k))).eval z)) 0 1 ≤
      Real.circleAverage
        (fun z => ‖(weightedVectorPolynomial w
          (fun k => realRademacherSign (x k))).eval z‖ ^ 2 /
            (M : ℝ) ^ 2) 0 1 := by
      apply Real.circleAverage_mono hcontHigh hcontSq
      intro z hz
      exact highBallCutoff_le_sq_div (M := M)
        ((weightedVectorPolynomial w
          (fun k => realRademacherSign (x k))).eval z)
    _ = 1 / (M : ℝ) ^ 2 := by
      rw [show (fun z => ‖(weightedVectorPolynomial w
          (fun k => realRademacherSign (x k))).eval z‖ ^ 2 / (M : ℝ) ^ 2) =
          (1 / (M : ℝ) ^ 2) •
            (fun z => ‖(weightedVectorPolynomial w
              (fun k => realRademacherSign (x k))).eval z‖ ^ 2) by
        funext z; simp [smul_eq_mul]; ring,
        Real.circleAverage_smul,
        weightedVectorPolynomial_circleAverage_sq_norm_eq_one w hw0 hsum x]
      simp [smul_eq_mul]

end Erdos522

end AmalgamatedModule73


/-! ===== amalgamated from Research.ClippingDomination ===== -/

section AmalgamatedModule74


namespace Erdos522

/-- The ordinary radial logarithm (with Mathlib's harmless value `log 0 = 0`). -/
noncomputable def rawLog (z : ℂ) : ℝ := Real.log ‖z‖

/-- Clipping error is supported on the low/high cutoff regions and dominated by
`|log| + log M` there. -/
theorem abs_rawLog_sub_clippedLog_le
    (M : NNReal) (hM : 1 ≤ M) (z : ℂ) :
    |rawLog z - clippedLog M z| ≤
      (|rawLog z| + Real.log (M : ℝ)) *
        (smallBallCutoff M z + highBallCutoff M z) := by
  have hMp : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hlogM : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg (by exact_mod_cast hM)
  have hfac0 : 0 ≤ |rawLog z| + Real.log (M : ℝ) := by positivity
  by_cases hlow : 1 / (M : ℝ) ≤ ‖z‖
  · by_cases hupp : ‖z‖ ≤ (M : ℝ)
    · rw [clippedLog_eq_log_norm M hlow hupp]
      simp only [rawLog, sub_self, abs_zero, zero_le]
      exact mul_nonneg hfac0
        (add_nonneg (smallBallCutoff_nonneg M z) (highBallCutoff_nonneg M z))
    · have hhigh : (M : ℝ) ≤ ‖z‖ := le_of_not_ge hupp
      have hcut : 1 ≤ smallBallCutoff M z + highBallCutoff M z := by
        rw [highBallCutoff_eq_one_of_le_norm hMp hhigh]
        linarith [smallBallCutoff_nonneg M z]
      calc
        |rawLog z - clippedLog M z| ≤ |rawLog z| + |clippedLog M z| :=
          abs_sub _ _
        _ ≤ |rawLog z| + Real.log (M : ℝ) :=
          add_le_add le_rfl (abs_clippedLog_le_log M hM z)
        _ ≤ (|rawLog z| + Real.log (M : ℝ)) *
            (smallBallCutoff M z + highBallCutoff M z) := by
          nlinarith
  · have hsmall : ‖z‖ ≤ 1 / (M : ℝ) := le_of_not_ge hlow
    have hcut : 1 ≤ smallBallCutoff M z + highBallCutoff M z := by
      rw [smallBallCutoff_eq_one_of_norm_le hMp hsmall]
      linarith [highBallCutoff_nonneg M z]
    calc
      |rawLog z - clippedLog M z| ≤ |rawLog z| + |clippedLog M z| :=
        abs_sub _ _
      _ ≤ |rawLog z| + Real.log (M : ℝ) :=
        add_le_add le_rfl (abs_clippedLog_le_log M hM z)
      _ ≤ (|rawLog z| + Real.log (M : ℝ)) *
          (smallBallCutoff M z + highBallCutoff M z) := by
        nlinarith

end Erdos522

end AmalgamatedModule74


/-! ===== amalgamated from Research.ClippingIntegralBound ===== -/

section AmalgamatedModule75


open MeasureTheory

namespace Erdos522

/-- A generic probability-space clipping-removal inequality.  It isolates the
exact Cauchy--Schwarz step used with logarithmic moments and low/high cutoffs. -/
theorem abs_integral_sub_integral_le_of_clipping_domination
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {f g c : α → ℝ} {L : ℝ}
    (hL : 0 ≤ L)
    (hf : MemLp f 2 μ) (hg : Integrable g μ) (hc : MemLp c 2 μ)
    (hc0 : ∀ x, 0 ≤ c x) (hc2 : ∀ x, c x ≤ 2)
    (hdom : ∀ x, |f x - g x| ≤ (|f x| + L) * c x) :
    |(∫ x, f x ∂μ) - ∫ x, g x ∂μ| ≤
      √(∫ x, f x ^ 2 ∂μ) * √(2 * ∫ x, c x ∂μ) +
        L * ∫ x, c x ∂μ := by
  have hfint : Integrable f μ := hf.integrable (by norm_num)
  have hcint : Integrable c μ := hc.integrable (by norm_num)
  have habsf : MemLp (fun x => |f x|) 2 μ := by
    simpa [Real.norm_eq_abs] using hf.norm
  have habsfint : Integrable (fun x => |f x|) μ :=
    habsf.integrable (by norm_num)
  have hcmeas : AEStronglyMeasurable c μ := hc.1
  have hcbound : ∀ᵐ x ∂μ, ‖c x‖ ≤ 2 := by
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hc0 x)]
    exact hc2 x
  have hprodfc : Integrable (fun x => |f x| * c x) μ :=
    habsfint.mul_bdd hcmeas hcbound
  have hLc : Integrable (fun x => L * c x) μ := hcint.const_mul L
  have hmajor : Integrable (fun x => (|f x| + L) * c x) μ := by
    apply (hprodfc.add hLc).congr
    filter_upwards with x
    simp only [Pi.add_apply]
    ring
  have hdiff : Integrable (fun x => |f x - g x|) μ :=
    (hfint.sub hg).norm
  calc
    |(∫ x, f x ∂μ) - ∫ x, g x ∂μ| =
        |∫ x, (f x - g x) ∂μ| := by rw [integral_sub hfint hg]
    _ ≤ ∫ x, |f x - g x| ∂μ := by
      simpa [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm (fun x => f x - g x))
    _ ≤ ∫ x, (|f x| + L) * c x ∂μ :=
      integral_mono hdiff hmajor hdom
    _ = (∫ x, |f x| * c x ∂μ) + L * ∫ x, c x ∂μ := by
      calc
        (∫ x, (|f x| + L) * c x ∂μ) =
            ∫ x, |f x| * c x + L * c x ∂μ := by
          apply integral_congr_ae
          filter_upwards with x
          ring
        _ = _ := by rw [integral_add hprodfc hLc, integral_const_mul]
    _ ≤ √(∫ x, f x ^ 2 ∂μ) * √(∫ x, c x ^ 2 ∂μ) +
        L * ∫ x, c x ∂μ := by
      gcongr
      have hcs := integral_mul_nonneg_le_sqrt_mul_sqrt (μ := μ)
        (Filter.Eventually.of_forall fun x => abs_nonneg (f x))
        (Filter.Eventually.of_forall hc0) habsf hc
      simpa [sq_abs] using hcs
    _ ≤ √(∫ x, f x ^ 2 ∂μ) * √(2 * ∫ x, c x ∂μ) +
        L * ∫ x, c x ∂μ := by
      gcongr
      have hcSq : Integrable (fun x => c x ^ 2) μ := hc.integrable_sq
      have h2c : Integrable (fun x => 2 * c x) μ := hcint.const_mul 2
      have hsquares : (∫ x, c x ^ 2 ∂μ) ≤ ∫ x, 2 * c x ∂μ := by
        apply integral_mono hcSq h2c
        intro x
        nlinarith [hc0 x, hc2 x]
      rw [integral_const_mul] at hsquares
      exact hsquares

end Erdos522

end AmalgamatedModule75


/-! ===== amalgamated from Research.PolynomialClippingRemoval ===== -/

section AmalgamatedModule76


open MeasureTheory

namespace Erdos522

/-- Angular second moment of the ordinary logarithm. -/
noncomputable def polynomialLogSecondMoment (p : Polynomial ℂ) : ℝ :=
  Real.circleAverage (fun z => (rawLog (p.eval z)) ^ 2) 0 1

/-- Total low/high cutoff mass controlling clipping. -/
noncomputable def polynomialCutoffMass (p : Polynomial ℂ) (M : NNReal) : ℝ :=
  Real.circleAverage
    (fun z => smallBallCutoff M (p.eval z) + highBallCutoff M (p.eval z)) 0 1

/-- Exact specialization of F-035 and F-034 to polynomial circle averages. -/
theorem abs_logMahlerMeasure_sub_clipped_angularStatistic_le
    (p : Polynomial ℂ) (M : NNReal) (hM : 1 ≤ M)
    (hlog : MemLp
      (circleParameterFunction (fun z => rawLog (p.eval z))) 2
      circleParameterMeasure) :
    |p.logMahlerMeasure - angularStatistic (clippedLog M) p| ≤
      √(polynomialLogSecondMoment p) * √(2 * polynomialCutoffMass p M) +
        Real.log (M : ℝ) * polynomialCutoffMass p M := by
  let f : ℝ → ℝ := circleParameterFunction (fun z => rawLog (p.eval z))
  let g : ℝ → ℝ := circleParameterFunction (fun z => clippedLog M (p.eval z))
  let c : ℝ → ℝ := circleParameterFunction
    (fun z => smallBallCutoff M (p.eval z) + highBallCutoff M (p.eval z))
  have hMp : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hgmeas : AEStronglyMeasurable g circleParameterMeasure := by
    apply Continuous.aestronglyMeasurable
    dsimp [g, circleParameterFunction]
    exact (clippedLog_lipschitz M hM).continuous.comp (by fun_prop)
  have hgLp : MemLp g 2 circleParameterMeasure := by
    apply MemLp.of_bound hgmeas (Real.log (M : ℝ))
    filter_upwards with θ
    rw [Real.norm_eq_abs]
    exact abs_clippedLog_le_log M hM _
  have hcmeas : AEStronglyMeasurable c circleParameterMeasure := by
    apply Continuous.aestronglyMeasurable
    change Continuous (fun θ =>
      smallBallCutoff M (p.eval (circleMap 0 1 θ)) +
        highBallCutoff M (p.eval (circleMap 0 1 θ)))
    unfold smallBallCutoff highBallCutoff
    fun_prop
  have hcLp : MemLp c 2 circleParameterMeasure := by
    apply MemLp.of_bound hcmeas 2
    filter_upwards with θ
    dsimp [c, circleParameterFunction]
    rw [abs_of_nonneg]
    · linarith [smallBallCutoff_le_one M (p.eval (circleMap 0 1 θ)),
        highBallCutoff_le_one M (p.eval (circleMap 0 1 θ))]
    · exact add_nonneg (smallBallCutoff_nonneg M _) (highBallCutoff_nonneg M _)
  have hgeneric := abs_integral_sub_integral_le_of_clipping_domination
    circleParameterMeasure (L := Real.log (M : ℝ))
    (f := f) (g := g) (c := c)
    (Real.log_nonneg (by exact_mod_cast hM)) hlog
    (hgLp.integrable (by norm_num)) hcLp
    (fun θ => add_nonneg (smallBallCutoff_nonneg M _)
      (highBallCutoff_nonneg M _))
    (fun θ => by
      dsimp [c, circleParameterFunction]
      linarith [smallBallCutoff_le_one M (p.eval (circleMap 0 1 θ)),
        highBallCutoff_le_one M (p.eval (circleMap 0 1 θ))])
    (fun θ => by
      dsimp [f, g, c, circleParameterFunction]
      exact abs_rawLog_sub_clippedLog_le M hM _)
  dsimp [f, g, c, circleParameterFunction] at hgeneric
  have hrawAvg := circleAverage_eq_integral_circleParameterMeasure
    (fun z => rawLog (p.eval z))
  have hclipAvg := circleAverage_eq_integral_circleParameterMeasure
    (fun z => clippedLog M (p.eval z))
  have hsqAvg := circleAverage_eq_integral_circleParameterMeasure
    (fun z => (rawLog (p.eval z)) ^ 2)
  have hcAvg := circleAverage_eq_integral_circleParameterMeasure
    (fun z => smallBallCutoff M (p.eval z) + highBallCutoff M (p.eval z))
  dsimp [circleParameterFunction] at hrawAvg hclipAvg hsqAvg hcAvg
  rw [← hrawAvg, ← hclipAvg, ← hsqAvg, ← hcAvg] at hgeneric
  simpa [f, g, c, rawLog, angularStatistic, Polynomial.logMahlerMeasure_def,
    polynomialLogSecondMoment, polynomialCutoffMass] using hgeneric

end Erdos522

end AmalgamatedModule76


/-! ===== amalgamated from Research.RadialClippingRemoval ===== -/

section AmalgamatedModule77


namespace Erdos522

/-- The normalized weighted polynomial attached to a finite sign vector. -/
noncomputable def radialWeightedSignPolynomial
    (n : ℕ) (s : ℝ) (x : Fin (n + 1) → Bool) : Polynomial ℂ :=
  weightedVectorPolynomial
    (fun k : Fin (n + 1) => radialWeight n s k)
    (fun k => realRademacherSign (x k))

lemma sum_radialWeight_fin (n : ℕ) (s : ℝ) :
    ∑ k : Fin (n + 1), radialWeight n s k = 1 := by
  rw [Fin.sum_univ_eq_sum_range]
  exact sum_radialWeight n s

/-- The total cutoff mass is controlled by the concentrated low cutoff plus the
explicit Parseval high-tail term. -/
theorem radialWeightedSignPolynomial_cutoffMass_le
    (n : ℕ) (s : ℝ) (x : Fin (n + 1) → Bool)
    (M : NNReal) (hM : 0 < M) :
    polynomialCutoffMass (radialWeightedSignPolynomial n s x) M ≤
      radialCubeSmallBallStatistic n s M x + 1 / (M : ℝ) ^ 2 := by
  let p := radialWeightedSignPolynomial n s x
  have hlowInt : CircleIntegrable (fun z => smallBallCutoff M (p.eval z)) 0 1 := by
    apply ContinuousOn.circleIntegrable (by norm_num)
    unfold smallBallCutoff
    fun_prop
  have hhighInt : CircleIntegrable (fun z => highBallCutoff M (p.eval z)) 0 1 := by
    apply ContinuousOn.circleIntegrable (by norm_num)
    unfold highBallCutoff
    fun_prop
  have hsplit : polynomialCutoffMass p M =
      Real.circleAverage (fun z => smallBallCutoff M (p.eval z)) 0 1 +
      Real.circleAverage (fun z => highBallCutoff M (p.eval z)) 0 1 := by
    unfold polynomialCutoffMass
    exact Real.circleAverage_add hlowInt hhighInt
  have hhigh := weightedVectorPolynomial_highBall_circleAverage_le
    (fun k : Fin (n + 1) => radialWeight n s k)
    (fun k => radialWeight_nonneg n s k)
    (sum_radialWeight_fin n s) x M hM
  rw [hsplit]
  exact add_le_add_right hhigh _

/-- The explicit clipping-removal estimate in radial-cube coordinates. -/
theorem radialWeightedSignPolynomial_clipping_error_le
    (n : ℕ) (s : ℝ) (x : Fin (n + 1) → Bool)
    (M : NNReal) (hM : 1 ≤ M)
    (hlog : MeasureTheory.MemLp
      (circleParameterFunction
        (fun z => rawLog ((radialWeightedSignPolynomial n s x).eval z))) 2
      circleParameterMeasure) :
    |(radialWeightedSignPolynomial n s x).logMahlerMeasure -
        radialCubeClippedStatistic n s M x| ≤
      √(polynomialLogSecondMoment (radialWeightedSignPolynomial n s x)) *
        √(2 * polynomialCutoffMass (radialWeightedSignPolynomial n s x) M) +
      Real.log (M : ℝ) *
        polynomialCutoffMass (radialWeightedSignPolynomial n s x) M := by
  simpa [radialCubeClippedStatistic, radialWeightedSignPolynomial,
    angularStatistic] using
    abs_logMahlerMeasure_sub_clipped_angularStatistic_le
      (radialWeightedSignPolynomial n s x) M hM hlog

end Erdos522

end AmalgamatedModule77


/-! ===== amalgamated from Research.AnnealedExpectationIntegrable ===== -/

section AmalgamatedModule78


open MeasureTheory
open scoped BigOperators

namespace Erdos522

/-- Separate angular integrability on the finite coefficient cube implies
integrability under the annealed pushforward law. -/
theorem integrable_radialAnnealedLaw_of_angular
    (n : ℕ) (s : ℝ) (h : ℂ → ℝ) (hmeas : Measurable h)
    (hang : ∀ x : Fin (n + 1) → Bool,
      Integrable (circleParameterFunction
        (fun z => h ((radialWeightedSignPolynomial n s x).eval z)))
        circleParameterMeasure) :
    Integrable h (radialAnnealedLaw n s : Measure ℂ) := by
  let ν : Measure (Fin (n + 1) → Bool) :=
    uniformCubeProbabilityMeasure (n + 1)
  let f : ℝ × (Fin (n + 1) → Bool) → ℝ :=
    fun u => h (radialAnnealedValue n s u)
  have hfmeas : AEStronglyMeasurable f (circleParameterMeasure.prod ν) :=
    (hmeas.comp (continuous_radialAnnealedValue n s).measurable).aestronglyMeasurable
  have hang' (x : Fin (n + 1) → Bool) : Integrable
      (circleParameterFunction
        (fun z => h ((weightedVectorPolynomial
          (fun k : Fin (n + 1) => radialWeight n s k)
          (fun k => realRademacherSign (x k))).eval z)))
      circleParameterMeasure := by
    simpa [radialWeightedSignPolynomial] using hang x
  have hfint : Integrable f (circleParameterMeasure.prod ν) := by
    rw [integrable_prod_iff' hfmeas]
    constructor
    · filter_upwards with x
      apply (hang' x).congr
      filter_upwards with θ
      dsimp [f, circleParameterFunction]
      rw [radialAnnealedValue_eq_eval]
    · let J : (Fin (n + 1) → Bool) → ℝ := fun x =>
        ∫ θ, ‖f (θ, x)‖ ∂circleParameterMeasure
      obtain ⟨B, hB⟩ := Finite.exists_le J
      apply Integrable.of_bound
        (measurable_of_finite J).aestronglyMeasurable |B|
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · exact (hB x).trans (le_abs_self B)
      · exact integral_nonneg fun θ => norm_nonneg _
  unfold radialAnnealedLaw
  rw [ProbabilityMeasure.toMeasure_map]
  apply (integrable_map_measure hmeas.aestronglyMeasurable
    (continuous_radialAnnealedValue n s).aemeasurable).2
  change Integrable f (circleParameterMeasure.prod ν)
  exact hfint

/-- Unbounded, integrable version of the exact annealed-law/cube-average
identity.  Finite coefficient space makes separate angular integrability
sufficient. -/
theorem integral_radialAnnealedLaw_eq_cubeAverage_of_integrable
    (n : ℕ) (s : ℝ) (h : ℂ → ℝ) (hmeas : Measurable h)
    (hang : ∀ x : Fin (n + 1) → Bool,
      Integrable (circleParameterFunction
        (fun z => h ((radialWeightedSignPolynomial n s x).eval z)))
        circleParameterMeasure) :
    ∫ z, h z ∂(radialAnnealedLaw n s : ProbabilityMeasure ℂ) =
      cubeAverage (radialCubeAngularStatistic n s h) := by
  let ν : Measure (Fin (n + 1) → Bool) :=
    uniformCubeProbabilityMeasure (n + 1)
  let f : ℝ × (Fin (n + 1) → Bool) → ℝ :=
    fun u => h (radialAnnealedValue n s u)
  have hfmeas : AEStronglyMeasurable f (circleParameterMeasure.prod ν) := by
    apply Measurable.aestronglyMeasurable
    exact hmeas.comp (continuous_radialAnnealedValue n s).measurable
  have hang' (x : Fin (n + 1) → Bool) : Integrable
      (circleParameterFunction
        (fun z => h ((weightedVectorPolynomial
          (fun k : Fin (n + 1) => radialWeight n s k)
          (fun k => realRademacherSign (x k))).eval z)))
      circleParameterMeasure := by
    simpa [radialWeightedSignPolynomial] using hang x
  have hfint : Integrable f (circleParameterMeasure.prod ν) := by
    rw [integrable_prod_iff' hfmeas]
    constructor
    · filter_upwards with x
      apply (hang' x).congr
      filter_upwards with θ
      dsimp [f, circleParameterFunction]
      rw [radialAnnealedValue_eq_eval]
    · let J : (Fin (n + 1) → Bool) → ℝ := fun x =>
        ∫ θ, ‖f (θ, x)‖ ∂circleParameterMeasure
      obtain ⟨B, hB⟩ := Finite.exists_le J
      apply Integrable.of_bound
        (measurable_of_finite J).aestronglyMeasurable |B|
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · exact (hB x).trans (le_abs_self B)
      · exact integral_nonneg fun θ => norm_nonneg _
  unfold radialAnnealedLaw
  rw [ProbabilityMeasure.toMeasure_map]
  rw [integral_map (continuous_radialAnnealedValue n s).aemeasurable
    hmeas.aestronglyMeasurable]
  rw [show (↑(radialAnnealedSourceMeasure n) :
      Measure (ℝ × (Fin (n + 1) → Bool))) =
      circleParameterMeasure.prod ν by rfl]
  rw [integral_prod f hfint]
  unfold cubeAverage radialCubeAngularStatistic angularStatistic
  simp_rw [circleAverage_eq_integral_circleParameterMeasure]
  rw [← integral_finset_sum Finset.univ (fun x _ => hang' x)]
  rw [← integral_div]
  apply integral_congr_ae
  filter_upwards with θ
  change ∫ y, f (θ, y) ∂(PMF.uniformOfFintype
    (Fin (n + 1) → Bool)).toMeasure = _
  rw [PMF.integral_eq_sum]
  simp_rw [PMF.uniformOfFintype_apply]
  simp only [Fintype.card_pi, Fintype.card_bool,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  dsimp [f, circleParameterFunction]
  simp_rw [radialAnnealedValue_eq_eval]
  rw [← Finset.mul_sum]
  push_cast
  ring

end Erdos522

end AmalgamatedModule78


/-! ===== amalgamated from Research.LogMomentTruncation ===== -/

section AmalgamatedModule79


open MeasureTheory Set

namespace Erdos522

noncomputable def absoluteRawLog (z : ℂ) : ℝ := |rawLog z|

lemma absoluteRawLog_nonneg (z : ℂ) : 0 ≤ absoluteRawLog z := abs_nonneg _

lemma measurable_absoluteRawLog : Measurable absoluteRawLog := by
  unfold absoluteRawLog rawLog
  exact (Real.measurable_log.comp measurable_norm).abs

lemma absoluteRawLog_pow_128_le_norm_sq_of_one_le
    {z : ℂ} (hz : 1 ≤ ‖z‖) :
    (absoluteRawLog z) ^ 128 ≤ (64 : ℝ) ^ 128 * ‖z‖ ^ 2 := by
  have hlog0 : 0 ≤ Real.log ‖z‖ := Real.log_nonneg hz
  have hbound := Real.log_le_rpow_div (show 0 ≤ ‖z‖ from norm_nonneg z)
    (show (0 : ℝ) < 1 / 64 by norm_num)
  have hp := pow_le_pow_left₀ hlog0 hbound 128
  have hroot := Real.rpow_inv_natCast_pow (x := ‖z‖)
    (norm_nonneg z) (show (64 : ℕ) ≠ 0 by norm_num)
  have hroot' : (‖z‖ ^ (64 : ℝ)⁻¹) ^ 64 = ‖z‖ := by
    convert hroot using 1 <;> norm_num
  unfold absoluteRawLog rawLog
  rw [abs_of_nonneg hlog0]
  calc
    (Real.log ‖z‖) ^ 128 ≤ (‖z‖ ^ (1 / 64 : ℝ) / (1 / 64 : ℝ)) ^ 128 := hp
    _ = (64 : ℝ) ^ 128 * ‖z‖ ^ 2 := by
      rw [show (1 / 64 : ℝ) = (64 : ℝ)⁻¹ by norm_num]
      rw [div_eq_mul_inv, inv_inv, mul_pow]
      rw [show (‖z‖ ^ (64 : ℝ)⁻¹) ^ 128 =
        ((‖z‖ ^ (64 : ℝ)⁻¹) ^ 64) ^ 2 by ring, hroot']
      ring

lemma absoluteRawLog_le_of_exp_neg_le_norm_le_one
    {T : ℝ} (hT : 0 ≤ T) {z : ℂ}
    (hlow : Real.exp (-T) ≤ ‖z‖) (hupp : ‖z‖ ≤ 1) :
    absoluteRawLog z ≤ T := by
  have hnorm : 0 < ‖z‖ := lt_of_lt_of_le (Real.exp_pos _) hlow
  have hloLog := (Real.strictMonoOn_log.le_iff_le (Real.exp_pos _) hnorm).mpr hlow
  have hupLog : Real.log ‖z‖ ≤ 0 := by
    simpa using Real.log_nonpos (norm_nonneg z) hupp
  rw [Real.log_exp] at hloLog
  unfold absoluteRawLog rawLog
  rw [abs_of_nonpos hupLog]
  linarith

/-- Truncation estimate: a high deterministic moment and a small lower-tail set
control the intermediate log moment, while the positive tail costs only the
second norm moment. -/
theorem integral_absoluteRawLog_pow_128_le_of_truncation
    (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (T D p : ℝ) (hT : 0 ≤ T) (hD : 0 ≤ D) (hp : 0 ≤ p)
    (h256int : Integrable (fun z => (absoluteRawLog z) ^ 256) μ)
    (h256 : (∫ z, (absoluteRawLog z) ^ 256 ∂μ) ≤ D)
    (hnorm2int : Integrable (fun z : ℂ => ‖z‖ ^ 2) μ)
    (hnorm2 : (∫ z : ℂ, ‖z‖ ^ 2 ∂μ) ≤ 1)
    (hsmall : μ.real {z | ‖z‖ ≤ Real.exp (-T)} ≤ p) :
    (∫ z, (absoluteRawLog z) ^ 128 ∂μ) ≤
      T ^ 128 + (64 : ℝ) ^ 128 + Real.sqrt D * Real.sqrt p := by
  let A : Set ℂ := {z | ‖z‖ ≤ Real.exp (-T)}
  let X : ℂ → ℝ := fun z => (absoluteRawLog z) ^ 128
  have hAmeas : MeasurableSet A := by
    dsimp [A]
    exact measurableSet_le measurable_norm measurable_const
  have hXmeas : Measurable X := by
    dsimp [X]
    exact measurable_absoluteRawLog.pow_const 128
  have hX0 : ∀ z, 0 ≤ X z := fun z => pow_nonneg (absoluteRawLog_nonneg z) _
  have hXsq : (fun z => (X z) ^ 2) = fun z => (absoluteRawLog z) ^ 256 := by
    funext z
    dsimp [X]
    ring
  have hXLp : MemLp X 2 μ := by
    rw [memLp_two_iff_integrable_sq hXmeas.aestronglyMeasurable]
    rw [hXsq]
    exact h256int
  let I : ℂ → ℝ := A.indicator (fun _ => (1 : ℝ))
  have hImeas : Measurable I := measurable_const.indicator hAmeas
  have hILp : MemLp I 2 μ := by
    apply MemLp.of_bound hImeas.aestronglyMeasurable 1
    filter_upwards with z
    by_cases hz : z ∈ A <;> simp [I, hz]
  have hcs := integral_mul_nonneg_le_sqrt_mul_sqrt
    (μ := μ) (f := X) (g := I)
    (Filter.Eventually.of_forall hX0)
    (Filter.Eventually.of_forall fun z => by
      by_cases hz : z ∈ A <;> simp [I, hz]) hXLp hILp
  have hlowPart : (∫ z, X z * I z ∂μ) ≤ Real.sqrt D * Real.sqrt p := by
    calc
      (∫ z, X z * I z ∂μ) ≤
          Real.sqrt (∫ z, X z ^ 2 ∂μ) * Real.sqrt (∫ z, I z ^ 2 ∂μ) := hcs
      _ = Real.sqrt (∫ z, (absoluteRawLog z) ^ 256 ∂μ) *
          Real.sqrt (μ.real A) := by
        congr 2
        · rw [show (fun z => X z ^ 2) =
            (fun z => (absoluteRawLog z) ^ 256) from hXsq]
        · have hI2 : (fun z => I z ^ 2) = I := by
            funext z
            by_cases hz : z ∈ A <;> simp [I, hz]
          rw [hI2]
          exact integral_indicator_one hAmeas
      _ ≤ Real.sqrt D * Real.sqrt p := by
        exact mul_le_mul (Real.sqrt_le_sqrt h256) (Real.sqrt_le_sqrt hsmall)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hpoint : ∀ z, X z ≤ T ^ 128 + (64 : ℝ) ^ 128 * ‖z‖ ^ 2 + X z * I z := by
    intro z
    by_cases hzA : z ∈ A
    · simp [I, hzA]
      positivity
    · have hlow : Real.exp (-T) ≤ ‖z‖ := le_of_not_ge hzA
      by_cases hz1 : ‖z‖ ≤ 1
      · have hxT := absoluteRawLog_le_of_exp_neg_le_norm_le_one hT hlow hz1
        have hpT := pow_le_pow_left₀ (absoluteRawLog_nonneg z) hxT 128
        simp [I, hzA]
        exact hpT.trans (le_add_of_nonneg_right
          (mul_nonneg (by positivity) (sq_nonneg _)))
      · have hxNorm := absoluteRawLog_pow_128_le_norm_sq_of_one_le
          (le_of_not_ge hz1)
        simp [I, hzA]
        exact hxNorm.trans (le_add_of_nonneg_left (pow_nonneg hT 128))
  have hXint : Integrable X μ := hXLp.integrable (by norm_num)
  have hXIint : Integrable (fun z => X z * I z) μ :=
    hXLp.integrable_mul hILp
  calc
    (∫ z, (absoluteRawLog z) ^ 128 ∂μ) = ∫ z, X z ∂μ := rfl
    _ ≤ ∫ z, (T ^ 128 + (64 : ℝ) ^ 128 * ‖z‖ ^ 2 + X z * I z) ∂μ := by
      apply integral_mono hXint
        (((integrable_const _).add (hnorm2int.const_mul _)).add hXIint)
      exact hpoint
    _ = T ^ 128 + (64 : ℝ) ^ 128 * (∫ z, ‖z‖ ^ 2 ∂μ) +
        ∫ z, X z * I z ∂μ := by
      have hμreal : μ.real (Set.univ : Set ℂ) = 1 := by
        rw [measureReal_def, measure_univ]
        simp
      calc
        (∫ z, (T ^ 128 + (64 : ℝ) ^ 128 * ‖z‖ ^ 2 + X z * I z) ∂μ) =
            (∫ z, (T ^ 128 + (64 : ℝ) ^ 128 * ‖z‖ ^ 2) ∂μ) +
              ∫ z, X z * I z ∂μ := by
          exact integral_add ((integrable_const _).add (hnorm2int.const_mul _)) hXIint
        _ = ((∫ _z : ℂ, T ^ 128 ∂μ) +
              ∫ z, (64 : ℝ) ^ 128 * ‖z‖ ^ 2 ∂μ) +
              ∫ z, X z * I z ∂μ := by
          rw [integral_add (integrable_const _) (hnorm2int.const_mul _)]
        _ = _ := by
          rw [integral_const, hμreal, one_smul, integral_const_mul]
    _ ≤ T ^ 128 + (64 : ℝ) ^ 128 + Real.sqrt D * Real.sqrt p := by
      have hc : 0 ≤ (64 : ℝ) ^ 128 := by positivity
      nlinarith

end Erdos522

end AmalgamatedModule79


/-! ===== amalgamated from Research.CubeCauchySchwarz ===== -/

section AmalgamatedModule80


open scoped BigOperators

namespace Erdos522

/-- Cauchy--Schwarz for the uniform Boolean-cube average. -/
theorem cubeAverage_mul_le_sqrt_mul_sqrt {N : ℕ}
    (f g : (Fin N → Bool) → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) :
    cubeAverage (fun x => f x * g x) ≤
      Real.sqrt (cubeAverage (fun x => (f x) ^ 2)) *
        Real.sqrt (cubeAverage (fun x => (g x) ^ 2)) := by
  let d : ℝ := (2 : ℝ) ^ N
  let A : ℝ := ∑ x : Fin N → Bool, (f x) ^ 2
  let B : ℝ := ∑ x : Fin N → Bool, (g x) ^ 2
  let S : ℝ := ∑ x : Fin N → Bool, f x * g x
  have hd : 0 < d := by dsimp [d]; positivity
  have hA : 0 ≤ A := Finset.sum_nonneg fun x hx => sq_nonneg _
  have hB : 0 ≤ B := Finset.sum_nonneg fun x hx => sq_nonneg _
  have hS : 0 ≤ S := Finset.sum_nonneg fun x hx => mul_nonneg (hf x) (hg x)
  have hcs : S ^ 2 ≤ A * B := by
    simpa [S, A, B] using
      (Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin N → Bool)) f g)
  have hsum : S ≤ Real.sqrt A * Real.sqrt B := by
    rw [← Real.sqrt_mul hA]
    exact (Real.le_sqrt hS (mul_nonneg hA hB)).2 hcs
  unfold cubeAverage
  change S / d ≤ Real.sqrt (A / d) * Real.sqrt (B / d)
  calc
    S / d ≤ (Real.sqrt A * Real.sqrt B) / d :=
      div_le_div_of_nonneg_right hsum hd.le
    _ = Real.sqrt (A / d) * Real.sqrt (B / d) := by
      rw [Real.sqrt_div hA, Real.sqrt_div hB]
      have hsqrtd : 0 < Real.sqrt d := Real.sqrt_pos.2 hd
      field_simp [ne_of_gt hsqrtd]
      nlinarith [Real.sq_sqrt hd.le]

end Erdos522

end AmalgamatedModule80


/-! ===== amalgamated from Research.AnnealedClippingRemoval ===== -/

section AmalgamatedModule81


open MeasureTheory

namespace Erdos522

noncomputable def radialCubeLogSecondMoment
    (n : ℕ) (s : ℝ) (x : Fin (n + 1) → Bool) : ℝ :=
  polynomialLogSecondMoment (radialWeightedSignPolynomial n s x)

noncomputable def radialCubeCutoffMass
    (n : ℕ) (s : ℝ) (M : NNReal) (x : Fin (n + 1) → Bool) : ℝ :=
  polynomialCutoffMass (radialWeightedSignPolynomial n s x) M

lemma radialCubeLogSecondMoment_nonneg
    (n : ℕ) (s : ℝ) (x : Fin (n + 1) → Bool) :
    0 ≤ radialCubeLogSecondMoment n s x := by
  unfold radialCubeLogSecondMoment polynomialLogSecondMoment
  exact Real.circleAverage_nonneg_of_nonneg (fun z hz => sq_nonneg _)

lemma radialCubeCutoffMass_nonneg
    (n : ℕ) (s : ℝ) (M : NNReal) (x : Fin (n + 1) → Bool) :
    0 ≤ radialCubeCutoffMass n s M x := by
  unfold radialCubeCutoffMass polynomialCutoffMass
  apply Real.circleAverage_nonneg_of_nonneg
  intro z hz
  exact add_nonneg (smallBallCutoff_nonneg _ _) (highBallCutoff_nonneg _ _)

lemma cubeAverage_radialCubeCutoffMass_le
    (n : ℕ) (s : ℝ) (M : NNReal) (hM : 0 < M) :
    cubeAverage (radialCubeCutoffMass n s M) ≤
      cubeAverage (radialCubeSmallBallStatistic n s M) + (M : ℝ)⁻¹ ^ 2 := by
  calc
    cubeAverage (radialCubeCutoffMass n s M) ≤
        cubeAverage (fun x => radialCubeSmallBallStatistic n s M x +
          (M : ℝ)⁻¹ ^ 2) := by
      apply cubeAverage_mono
      intro x
      simpa [radialCubeCutoffMass, one_div] using
        radialWeightedSignPolynomial_cutoffMass_le n s x M hM
    _ = cubeAverage (radialCubeSmallBallStatistic n s M) +
        (M : ℝ)⁻¹ ^ 2 := by
      unfold cubeAverage
      simp_rw [Finset.sum_add_distrib]
      simp [Fintype.card_bool, Fintype.card_fin]
      field_simp
      <;> ring

/-- Annealed clipping removal: averaging the pointwise angular Cauchy--Schwarz
bound over the coefficient cube costs only the averaged log second moment and
averaged cutoff mass. -/
theorem abs_cubeAverage_raw_sub_clipped_le
    (n : ℕ) (s : ℝ) (M : NNReal) (hM : 1 ≤ M)
    (hlog : ∀ x : Fin (n + 1) → Bool,
      MemLp
        (circleParameterFunction
          (fun z => rawLog ((radialWeightedSignPolynomial n s x).eval z))) 2
        circleParameterMeasure) :
    |cubeAverage (fun x => (radialWeightedSignPolynomial n s x).logMahlerMeasure) -
        cubeAverage (radialCubeClippedStatistic n s M)| ≤
      Real.sqrt (cubeAverage (radialCubeLogSecondMoment n s)) *
        Real.sqrt (2 * (cubeAverage (radialCubeSmallBallStatistic n s M) +
          (M : ℝ)⁻¹ ^ 2)) +
      Real.log (M : ℝ) *
        (cubeAverage (radialCubeSmallBallStatistic n s M) + (M : ℝ)⁻¹ ^ 2) := by
  let Y : (Fin (n + 1) → Bool) → ℝ := radialCubeLogSecondMoment n s
  let C : (Fin (n + 1) → Bool) → ℝ := radialCubeCutoffMass n s M
  let R : (Fin (n + 1) → Bool) → ℝ := fun x =>
    (radialWeightedSignPolynomial n s x).logMahlerMeasure
  let H : (Fin (n + 1) → Bool) → ℝ := radialCubeClippedStatistic n s M
  have hpoint : ∀ x, |R x - H x| ≤
      Real.sqrt (Y x) * Real.sqrt (2 * C x) + Real.log (M : ℝ) * C x := by
    intro x
    simpa [R, H, Y, C, radialCubeLogSecondMoment, radialCubeCutoffMass] using
      radialWeightedSignPolynomial_clipping_error_le n s x M hM (hlog x)
  have hCavg := cubeAverage_radialCubeCutoffMass_le n s M
    (lt_of_lt_of_le zero_lt_one hM)
  have hcs : cubeAverage (fun x => Real.sqrt (Y x) * Real.sqrt (2 * C x)) ≤
      Real.sqrt (cubeAverage Y) * Real.sqrt (2 * cubeAverage C) := by
    have h := cubeAverage_mul_le_sqrt_mul_sqrt
      (fun x => Real.sqrt (Y x)) (fun x => Real.sqrt (2 * C x))
      (fun x => Real.sqrt_nonneg _) (fun x => Real.sqrt_nonneg _)
    calc
      cubeAverage (fun x => Real.sqrt (Y x) * Real.sqrt (2 * C x)) ≤
          Real.sqrt (cubeAverage (fun x => (Real.sqrt (Y x)) ^ 2)) *
            Real.sqrt (cubeAverage (fun x => (Real.sqrt (2 * C x)) ^ 2)) := h
      _ = Real.sqrt (cubeAverage Y) * Real.sqrt (2 * cubeAverage C) := by
        congr 2
        · apply congrArg cubeAverage
          funext x
          exact Real.sq_sqrt (radialCubeLogSecondMoment_nonneg n s x)
        · calc
            cubeAverage (fun x => Real.sqrt (2 * C x) ^ 2) =
                cubeAverage (fun x => 2 * C x) := by
              apply congrArg cubeAverage
              funext x
              exact Real.sq_sqrt
                (mul_nonneg (by norm_num) (radialCubeCutoffMass_nonneg n s M x))
            _ = 2 * cubeAverage C := cubeAverage_const_mul 2 C
  calc
    |cubeAverage (fun x => (radialWeightedSignPolynomial n s x).logMahlerMeasure) -
        cubeAverage (radialCubeClippedStatistic n s M)| =
        |cubeAverage (fun x => R x - H x)| := by
      unfold cubeAverage R H
      rw [Finset.sum_sub_distrib]
      ring
    _ ≤ cubeAverage (fun x => |R x - H x|) := abs_cubeAverage_le _
    _ ≤ cubeAverage (fun x =>
        Real.sqrt (Y x) * Real.sqrt (2 * C x) + Real.log (M : ℝ) * C x) :=
      cubeAverage_mono hpoint
    _ = cubeAverage (fun x => Real.sqrt (Y x) * Real.sqrt (2 * C x)) +
        Real.log (M : ℝ) * cubeAverage C := by
      unfold cubeAverage
      simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      ring
    _ ≤ Real.sqrt (cubeAverage Y) * Real.sqrt (2 * cubeAverage C) +
        Real.log (M : ℝ) * cubeAverage C := by
      exact add_le_add hcs (le_refl _)
    _ ≤ Real.sqrt (cubeAverage Y) *
          Real.sqrt (2 * (cubeAverage (radialCubeSmallBallStatistic n s M) +
            (M : ℝ)⁻¹ ^ 2)) +
        Real.log (M : ℝ) *
          (cubeAverage (radialCubeSmallBallStatistic n s M) + (M : ℝ)⁻¹ ^ 2) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left
          (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hCavg (by norm_num)))
          (Real.sqrt_nonneg _)
      · exact mul_le_mul_of_nonneg_left hCavg
          (Real.log_nonneg (by exact_mod_cast hM))
    _ = _ := by rfl

end Erdos522

end AmalgamatedModule81


/-! ===== amalgamated from Research.GaussianCutoffRate ===== -/

section AmalgamatedModule82


open MeasureTheory ProbabilityTheory

namespace Erdos522

/-- Quantitative circular-Gaussian small-ball cutoff bound. -/
theorem integral_smallBallCutoff_circularGaussian_le
    (M : NNReal) (hM : 0 < M) :
    (∫ z : ℂ, smallBallCutoff M z
      ∂(circularGaussianLaw : Measure ℂ)) ≤
      2 * Real.exp 1 * Real.sqrt Real.pi / (M : ℝ) := by
  have hkernel := circularGaussian_integral_exp_neg_sq_norm_le
    ((M : ℝ) / 2) (by positivity)
  have hsmallInt : Integrable (smallBallCutoff M)
      (circularGaussianLaw : Measure ℂ) := by
    apply Integrable.of_bound (smallBallCutoff_lipschitz M).continuous.aestronglyMeasurable 1
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (smallBallCutoff_nonneg M z)]
    exact smallBallCutoff_le_one M z
  have hkernelInt : Integrable (fun z : ℂ => Real.exp 1 *
      Real.exp (-(((M : ℝ) / 2) * ‖z‖) ^ 2))
      (circularGaussianLaw : Measure ℂ) := by
    apply Integrable.const_mul
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _))
  have hmono :
      (∫ z : ℂ, smallBallCutoff M z
        ∂(circularGaussianLaw : Measure ℂ)) ≤
      ∫ z : ℂ, Real.exp 1 *
        Real.exp (-(((M : ℝ) / 2) * ‖z‖) ^ 2)
        ∂(circularGaussianLaw : Measure ℂ) := by
    apply integral_mono hsmallInt hkernelInt
    intro z
    calc
      smallBallCutoff M z ≤
          Real.exp 1 * Real.exp (-((M : ℝ) * ‖z‖) ^ 2 / 4) :=
        smallBallCutoff_le_exp_kernel M hM z
      _ = Real.exp 1 * Real.exp (-(((M : ℝ) / 2) * ‖z‖) ^ 2) := by
        congr 2
        ring
  calc
    (∫ z : ℂ, smallBallCutoff M z
      ∂(circularGaussianLaw : Measure ℂ)) ≤
        ∫ z : ℂ, Real.exp 1 *
          Real.exp (-(((M : ℝ) / 2) * ‖z‖) ^ 2)
          ∂(circularGaussianLaw : Measure ℂ) := hmono
    _ = Real.exp 1 *
        ∫ z : ℂ, Real.exp (-(((M : ℝ) / 2) * ‖z‖) ^ 2)
          ∂(circularGaussianLaw : Measure ℂ) := by rw [integral_const_mul]
    _ ≤ Real.exp 1 * (Real.sqrt Real.pi / ((M : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_left hkernel (Real.exp_pos _).le
    _ = 2 * Real.exp 1 * Real.sqrt Real.pi / (M : ℝ) := by
      field_simp
      <;> ring

end Erdos522

end AmalgamatedModule82


/-! ===== amalgamated from Research.TriangularApproximation ===== -/

section AmalgamatedModule83


open Filter Topology

namespace Erdos522

/-- If a sequence is uniformly approximable, with error tending to zero in an
auxiliary cutoff parameter, by sequences which converge for every fixed
cutoff, then the original sequence converges. -/
theorem exists_tendsto_of_triangular_approximation
    (A : ℕ → ℝ) (H : ℕ → ℕ → ℝ) (g err : ℕ → ℝ)
    (herr : Tendsto err atTop (𝓝 0))
    (hfixed : ∀ k, Tendsto (fun n => H n k) atTop (𝓝 (g k)))
    (happrox : ∀ k, ∀ᶠ n : ℕ in atTop, |A n - H n k| ≤ err k) :
    ∃ c : ℝ, Tendsto A atTop (𝓝 c) := by
  have hAcauchy : CauchySeq A := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨K, hK⟩ := (Metric.tendsto_atTop.mp herr (ε / 6) (by positivity))
    have herrK : |err K| < ε / 6 := by
      simpa [Real.dist_eq] using hK K (le_refl K)
    have herrK' : err K < ε / 6 := lt_of_le_of_lt (le_abs_self _) herrK
    obtain ⟨N₁, hN₁⟩ := (Metric.cauchySeq_iff.mp (hfixed K).cauchySeq)
      (ε / 3) (by positivity)
    obtain ⟨N₂, hN₂⟩ := (eventually_atTop.1 (happrox K))
    refine ⟨max N₁ N₂, ?_⟩
    intro m hm n hn
    have hm1 : N₁ ≤ m := (le_max_left _ _).trans hm
    have hn1 : N₁ ≤ n := (le_max_left _ _).trans hn
    have hm2 : N₂ ≤ m := (le_max_right _ _).trans hm
    have hn2 : N₂ ≤ n := (le_max_right _ _).trans hn
    have hmiddle := hN₁ m hm1 n hn1
    have hleft := hN₂ m hm2
    have hright := hN₂ n hn2
    rw [← Real.dist_eq] at hleft hright
    calc
      dist (A m) (A n) ≤
          dist (A m) (H m K) + dist (H m K) (H n K) +
            dist (H n K) (A n) := dist_triangle4 _ _ _ _
      _ < ε := by
        rw [dist_comm (H n K) (A n)]
        linarith
  exact cauchySeq_tendsto_of_complete hAcauchy

/-- In the same setting, the limits of the fixed-cutoff approximants converge
to the very same limit as the target sequence. -/
theorem exists_common_tendsto_of_triangular_approximation
    (A : ℕ → ℝ) (H : ℕ → ℕ → ℝ) (g err : ℕ → ℝ)
    (herr : Tendsto err atTop (𝓝 0))
    (hfixed : ∀ k, Tendsto (fun n => H n k) atTop (𝓝 (g k)))
    (happrox : ∀ k, ∀ᶠ n : ℕ in atTop, |A n - H n k| ≤ err k) :
    ∃ c : ℝ, Tendsto A atTop (𝓝 c) ∧ Tendsto g atTop (𝓝 c) := by
  obtain ⟨c, hA⟩ := exists_tendsto_of_triangular_approximation
    A H g err herr hfixed happrox
  refine ⟨c, hA, ?_⟩
  have hlimitBound : ∀ k, |c - g k| ≤ err k := by
    intro k
    have hd := hA.sub (hfixed k)
    have habs : Tendsto (fun n => |A n - H n k|) atTop (𝓝 |c - g k|) := by
      exact (continuous_abs.tendsto _).comp hd
    exact le_of_tendsto habs (happrox k)
  have habsGC : Tendsto (fun k => |g k - c|) atTop (𝓝 0) := by
    apply squeeze_zero (g := err)
    · intro k
      exact abs_nonneg _
    · intro k
      rw [abs_sub_comm]
      exact hlimitBound k
    · exact herr
  have hdiff : Tendsto (fun k => g k - c) atTop (𝓝 0) := by
    apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
    simpa [Function.comp_def] using habsGC
  have h := hdiff.add
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => c) atTop (𝓝 c))
  convert h using 1 <;> ring

end Erdos522

end AmalgamatedModule83


/-! ===== amalgamated from Research.UniformMomentFixedCutoff ===== -/

section AmalgamatedModule84


open Filter Topology MeasureTheory Asymptotics

namespace Erdos522

noncomputable def integerCutoff (k : ℕ) : NNReal := (k + 1 : ℕ)

noncomputable def fixedCutoffMassEnvelope (k : ℕ) : ℝ :=
  (2 * Real.exp 1 * Real.sqrt Real.pi + 1) * (integerCutoff k : ℝ)⁻¹ +
    (integerCutoff k : ℝ)⁻¹ ^ 2

noncomputable def uniformMomentFixedError (C : ℝ) (k : ℕ) : ℝ :=
  Real.sqrt C * Real.sqrt (2 * fixedCutoffMassEnvelope k) +
    Real.log (integerCutoff k : ℝ) * fixedCutoffMassEnvelope k

lemma integerCutoff_coe (k : ℕ) :
    (integerCutoff k : ℝ) = (k : ℝ) + 1 := by
  simp [integerCutoff]

lemma integerCutoff_pos (k : ℕ) : 0 < integerCutoff k := by
  simp [integerCutoff]

lemma one_le_integerCutoff (k : ℕ) : (1 : NNReal) ≤ integerCutoff k := by
  simp [integerCutoff]

lemma fixedCutoffMassEnvelope_nonneg (k : ℕ) :
    0 ≤ fixedCutoffMassEnvelope k := by
  unfold fixedCutoffMassEnvelope
  positivity

lemma tendsto_integerCutoff_coe :
    Tendsto (fun k => (integerCutoff k : ℝ)) atTop atTop := by
  exact Tendsto.congr'
    (Filter.Eventually.of_forall fun k => (integerCutoff_coe k).symm)
    (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)

lemma tendsto_fixedCutoffMassEnvelope :
    Tendsto fixedCutoffMassEnvelope atTop (𝓝 0) := by
  have h1 : Tendsto (fun k => (integerCutoff k : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_integerCutoff_coe
  unfold fixedCutoffMassEnvelope
  convert (h1.const_mul (2 * Real.exp 1 * Real.sqrt Real.pi + 1)).add
    (h1.pow 2) using 1 <;> ring

lemma tendsto_log_integerCutoff_mul_massEnvelope :
    Tendsto (fun k => Real.log (integerCutoff k : ℝ) *
      fixedCutoffMassEnvelope k) atTop (𝓝 0) := by
  have hlogInv (j : ℕ) (hj : 0 < j) :
      Tendsto (fun k => Real.log (integerCutoff k : ℝ) *
        (integerCutoff k : ℝ)⁻¹ ^ j) atTop (𝓝 0) := by
    have hjr : (0 : ℝ) < j := by exact_mod_cast hj
    have h := (isLittleO_log_rpow_atTop hjr).tendsto_div_nhds_zero.comp
      tendsto_integerCutoff_coe
    apply Tendsto.congr' (Filter.Eventually.of_forall fun k => ?_) h
    simp only [Function.comp_apply, Real.rpow_natCast, div_eq_mul_inv, inv_pow]
  have h1 := (hlogInv 1 (by norm_num)).const_mul
    (2 * Real.exp 1 * Real.sqrt Real.pi + 1)
  have h2 := hlogInv 2 (by norm_num)
  have hsum := h1.add h2
  have hsum0 : Tendsto (fun k =>
      (2 * Real.exp 1 * Real.sqrt Real.pi + 1) *
          (Real.log (integerCutoff k : ℝ) * (integerCutoff k : ℝ)⁻¹) +
        Real.log (integerCutoff k : ℝ) * (integerCutoff k : ℝ)⁻¹ ^ 2)
      atTop (𝓝 0) := by
    convert hsum using 1
    · funext k
      ring
    · ring
  unfold fixedCutoffMassEnvelope
  apply Tendsto.congr' (Filter.Eventually.of_forall fun k => by ring) hsum0

lemma tendsto_uniformMomentFixedError (C : ℝ) (hC : 0 ≤ C) :
    Tendsto (uniformMomentFixedError C) atTop (𝓝 0) := by
  have htwice : Tendsto (fun k => 2 * fixedCutoffMassEnvelope k)
      atTop (𝓝 0) := by
    convert tendsto_fixedCutoffMassEnvelope.const_mul 2 using 1 <;> ring
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp htwice
  simp only [Real.sqrt_zero] at hsqrt
  have hsqrt0 : Tendsto (fun k => Real.sqrt (2 * fixedCutoffMassEnvelope k))
      atTop (𝓝 0) := by
    change Tendsto (fun k => Real.sqrt (2 * fixedCutoffMassEnvelope k))
      atTop (𝓝 0) at hsqrt
    exact hsqrt
  have hsum := (hsqrt0.const_mul (Real.sqrt C)).add
    tendsto_log_integerCutoff_mul_massEnvelope
  unfold uniformMomentFixedError
  convert hsum using 1 <;> ring

noncomputable def annealedRawLogMean (n : ℕ) (s : ℝ) : ℝ :=
  cubeAverage (fun x : Fin (n + 1) → Bool =>
    (radialWeightedSignPolynomial n s x).logMahlerMeasure)

noncomputable def gaussianClippedMean (k : ℕ) : ℝ :=
  ∫ z : ℂ, clippedLog (integerCutoff k) z
    ∂(circularGaussianLaw : ProbabilityMeasure ℂ)

lemma tendsto_fixedCutoff_clippedMean (s : ℝ) (k : ℕ) :
    Tendsto (fun n => cubeAverage
      (radialCubeClippedStatistic n s (integerCutoff k))) atTop
      (𝓝 (gaussianClippedMean k)) := by
  exact tendsto_cubeAverage_radialCubeClippedStatistic s (integerCutoff k)
    (one_le_integerCutoff k)

/-- A uniform bound on annealed angular log second moments makes the raw
annealed log means a triangular limit of fixed clipped means. -/
theorem exists_common_limit_raw_and_gaussianClipped_of_uniform_moment
    (C : ℝ) (hC : 0 ≤ C)
    (hlog : ∀ n s (x : Fin (n + 1) → Bool),
      MemLp
        (circleParameterFunction
          (fun z => rawLog ((radialWeightedSignPolynomial n s x).eval z))) 2
        circleParameterMeasure)
    (hmoment : ∀ s : ℝ, ∀ᶠ n : ℕ in atTop,
      cubeAverage (radialCubeLogSecondMoment n s) ≤ C) :
    ∃ c : ℝ,
      (∀ s : ℝ, Tendsto (fun n => annealedRawLogMean n s) atTop (𝓝 c)) ∧
      Tendsto gaussianClippedMean atTop (𝓝 c) := by
  have happrox (s : ℝ) (k : ℕ) : ∀ᶠ n : ℕ in atTop,
      |annealedRawLogMean n s -
        cubeAverage (radialCubeClippedStatistic n s (integerCutoff k))| ≤
      uniformMomentFixedError C k := by
    let G : ℝ := ∫ z : ℂ, smallBallCutoff (integerCutoff k) z
      ∂(circularGaussianLaw : ProbabilityMeasure ℂ)
    have hG : G ≤ 2 * Real.exp 1 * Real.sqrt Real.pi /
        (integerCutoff k : ℝ) := by
      exact integral_smallBallCutoff_circularGaussian_le
        (integerCutoff k) (integerCutoff_pos k)
    have hS := tendsto_cubeAverage_radialCubeSmallBallStatistic s (integerCutoff k)
    have hδ : 0 < (integerCutoff k : ℝ)⁻¹ := by
      apply inv_pos.mpr
      rw [integerCutoff_coe]
      positivity
    have hclose := hS.eventually (Metric.ball_mem_nhds G hδ)
    filter_upwards [hmoment s, hclose] with n hY hSn
    have hSupper : cubeAverage
        (radialCubeSmallBallStatistic n s (integerCutoff k)) ≤
        (2 * Real.exp 1 * Real.sqrt Real.pi + 1) *
          (integerCutoff k : ℝ)⁻¹ := by
      rw [Real.dist_eq] at hSn
      have hdev : cubeAverage
          (radialCubeSmallBallStatistic n s (integerCutoff k)) ≤
          G + (integerCutoff k : ℝ)⁻¹ := by
        linarith [le_abs_self (cubeAverage
          (radialCubeSmallBallStatistic n s (integerCutoff k)) - G)]
      rw [div_eq_mul_inv] at hG
      linarith
    have hbase := abs_cubeAverage_raw_sub_clipped_le n s (integerCutoff k)
      (one_le_integerCutoff k) (fun x => hlog n s x)
    have hD : cubeAverage
          (radialCubeSmallBallStatistic n s (integerCutoff k)) +
          (integerCutoff k : ℝ)⁻¹ ^ 2 ≤
        (2 * Real.exp 1 * Real.sqrt Real.pi + 1) *
          (integerCutoff k : ℝ)⁻¹ + (integerCutoff k : ℝ)⁻¹ ^ 2 :=
      add_le_add hSupper (le_refl _)
    unfold annealedRawLogMean
    calc
      |cubeAverage (fun x : Fin (n + 1) → Bool =>
          (radialWeightedSignPolynomial n s x).logMahlerMeasure) -
          cubeAverage (radialCubeClippedStatistic n s (integerCutoff k))| ≤
        Real.sqrt (cubeAverage (radialCubeLogSecondMoment n s)) *
          Real.sqrt (2 * (cubeAverage
            (radialCubeSmallBallStatistic n s (integerCutoff k)) +
              (integerCutoff k : ℝ)⁻¹ ^ 2)) +
        Real.log (integerCutoff k : ℝ) *
          (cubeAverage (radialCubeSmallBallStatistic n s (integerCutoff k)) +
            (integerCutoff k : ℝ)⁻¹ ^ 2) := hbase
      _ ≤ uniformMomentFixedError C k := by
        unfold uniformMomentFixedError fixedCutoffMassEnvelope
        apply add_le_add
        · exact mul_le_mul
            (Real.sqrt_le_sqrt hY)
            (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hD (by norm_num)))
            (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        · exact mul_le_mul_of_nonneg_left hD
            (Real.log_nonneg (by exact_mod_cast one_le_integerCutoff k))
  obtain ⟨c, hraw0, hgauss⟩ :=
    exists_common_tendsto_of_triangular_approximation
      (fun n => annealedRawLogMean n 0)
      (fun n k => cubeAverage
        (radialCubeClippedStatistic n 0 (integerCutoff k)))
      gaussianClippedMean (uniformMomentFixedError C)
      (tendsto_uniformMomentFixedError C hC)
      (tendsto_fixedCutoff_clippedMean 0) (happrox 0)
  refine ⟨c, ?_, hgauss⟩
  intro s
  obtain ⟨cs, hraws, hgausss⟩ :=
    exists_common_tendsto_of_triangular_approximation
      (fun n => annealedRawLogMean n s)
      (fun n k => cubeAverage
        (radialCubeClippedStatistic n s (integerCutoff k)))
      gaussianClippedMean (uniformMomentFixedError C)
      (tendsto_uniformMomentFixedError C hC)
      (tendsto_fixedCutoff_clippedMean s) (happrox s)
  have hcs : cs = c := tendsto_nhds_unique hgausss hgauss
  simpa [hcs] using hraws

end Erdos522

end AmalgamatedModule84


/-! ===== amalgamated from Research.PowerCutoff ===== -/

section AmalgamatedModule85


open Filter Topology

namespace Erdos522

/-- The deterministic clipping level `(n+1)^(1/16)`, bundled as a nonnegative
real. -/
noncomputable def radialPowerCutoff (n : ℕ) : NNReal :=
  Real.toNNReal (((n : ℝ) + 1) ^ (1 / 16 : ℝ))

@[simp]
lemma coe_radialPowerCutoff (n : ℕ) :
    (radialPowerCutoff n : ℝ) = ((n : ℝ) + 1) ^ (1 / 16 : ℝ) := by
  unfold radialPowerCutoff
  rw [Real.coe_toNNReal]
  exact Real.rpow_nonneg (by positivity) _

lemma radialPowerCutoff_pos (n : ℕ) : 0 < radialPowerCutoff n := by
  apply NNReal.coe_pos.mp
  rw [coe_radialPowerCutoff]
  exact Real.rpow_pos_of_pos (by positivity) _

/-- The sixteenth power recovers the coefficient count exactly. -/
lemma radialPowerCutoff_pow_sixteen (n : ℕ) :
    (radialPowerCutoff n : ℝ) ^ 16 = (n : ℝ) + 1 := by
  rw [coe_radialPowerCutoff]
  convert Real.rpow_inv_natCast_pow
    (x := (n : ℝ) + 1) (by positivity) (by norm_num : (16 : ℕ) ≠ 0) using 1 <;>
    norm_num

/-- The deterministic clipping level tends to infinity. -/
theorem tendsto_radialPowerCutoff_coe :
    Tendsto (fun n : ℕ => (radialPowerCutoff n : ℝ)) atTop atTop := by
  have hbase : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have h := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 16)).comp hbase
  apply Tendsto.congr' (Filter.Eventually.of_forall fun n => by
    simp only [Function.comp_apply, coe_radialPowerCutoff]) h

/-- Every fixed positive inverse power of the clipping level vanishes. -/
theorem tendsto_radialPowerCutoff_inv_pow (k : ℕ) (hk : 0 < k) :
    Tendsto (fun n : ℕ => ((radialPowerCutoff n : ℝ)⁻¹) ^ k)
      atTop (𝓝 0) := by
  have hinv : Tendsto (fun n : ℕ => (radialPowerCutoff n : ℝ)⁻¹)
      atTop (𝓝 0) := tendsto_inv_atTop_zero.comp tendsto_radialPowerCutoff_coe
  convert hinv.pow k using 1
  norm_num [hk.ne']

end Erdos522

end AmalgamatedModule85


/-! ===== amalgamated from Research.PowerSmallBallLimit ===== -/

section AmalgamatedModule86


open Filter Topology

namespace Erdos522

lemma radialPowerCutoff_div_mul_pow_four (c : ℝ) (n : ℕ) :
    c / ((n : ℝ) + 1) * (radialPowerCutoff n : ℝ) ^ 4 =
      c * ((radialPowerCutoff n : ℝ)⁻¹) ^ 12 := by
  rw [← radialPowerCutoff_pow_sixteen n]
  have hm : (radialPowerCutoff n : ℝ) ≠ 0 :=
    ne_of_gt (by exact_mod_cast radialPowerCutoff_pos n)
  field_simp [hm]

lemma radialPowerCutoff_div_sq_mul_pow_four (c : ℝ) (n : ℕ) :
    (c / ((n : ℝ) + 1)) ^ 2 * (radialPowerCutoff n : ℝ) ^ 4 =
      c ^ 2 * ((radialPowerCutoff n : ℝ)⁻¹) ^ 28 := by
  rw [← radialPowerCutoff_pow_sixteen n]
  have hm : (radialPowerCutoff n : ℝ) ≠ 0 :=
    ne_of_gt (by exact_mod_cast radialPowerCutoff_pos n)
  field_simp [hm]

lemma sqrt_div_mul_radialPowerCutoff_sq
    (c : ℝ) (hc : 0 ≤ c) (n : ℕ) :
    Real.sqrt (c / ((n : ℝ) + 1)) * (radialPowerCutoff n : ℝ) ^ 2 =
      Real.sqrt c * ((radialPowerCutoff n : ℝ)⁻¹) ^ 6 := by
  rw [← radialPowerCutoff_pow_sixteen n]
  rw [Real.sqrt_div hc]
  rw [show (radialPowerCutoff n : ℝ) ^ 16 =
      ((radialPowerCutoff n : ℝ) ^ 8) ^ 2 by ring,
    Real.sqrt_sq (by positivity)]
  have hm : (radialPowerCutoff n : ℝ) ≠ 0 :=
    ne_of_gt (by exact_mod_cast radialPowerCutoff_pos n)
  field_simp [hm]

/-- At the deterministic scale `M_n=(n+1)^(1/16)`, the annealed angular
small-ball cutoff mean tends to zero for every fixed radial shift. -/
theorem tendsto_cubeAverage_radialCubeSmallBallStatistic_powerCutoff
    (s : ℝ) :
    Tendsto (fun n => cubeAverage
      (radialCubeSmallBallStatistic n s (radialPowerCutoff n)))
      atTop (𝓝 0) := by
  let E : ℝ := Real.exp (4 * |s|)
  let C2 : ℝ := circularGaussianSecondNormMoment
  let C4 : ℝ := circularGaussianFourthNormMoment
  let upper : ℕ → ℝ := fun n => Real.exp 1 *
    (2 * Real.sqrt Real.pi / (radialPowerCutoff n : ℝ) +
      ((7 / 24 : ℝ) * (E / ((n : ℝ) + 1)) +
        2 * (E / ((n : ℝ) + 1)) ^ 2) *
          (radialPowerCutoff n : ℝ) ^ 4 * C4 +
      Real.sqrt (E / ((n : ℝ) + 1)) / 4 *
        (radialPowerCutoff n : ℝ) ^ 2 * C2)
  have h1 := tendsto_radialPowerCutoff_inv_pow 1 (by norm_num)
  have h6 := tendsto_radialPowerCutoff_inv_pow 6 (by norm_num)
  have h12 := tendsto_radialPowerCutoff_inv_pow 12 (by norm_num)
  have h28 := tendsto_radialPowerCutoff_inv_pow 28 (by norm_num)
  have hfirst : Tendsto
      (fun n : ℕ => 2 * Real.sqrt Real.pi / (radialPowerCutoff n : ℝ))
      atTop (𝓝 0) := by
    have h := h1.const_mul (2 * Real.sqrt Real.pi)
    convert h using 1 <;> ring
  have hmiddle : Tendsto
      (fun n : ℕ => ((7 / 24 : ℝ) * (E / ((n : ℝ) + 1)) +
        2 * (E / ((n : ℝ) + 1)) ^ 2) *
          (radialPowerCutoff n : ℝ) ^ 4 * C4)
      atTop (𝓝 0) := by
    have hleft := h12.const_mul ((7 / 24 : ℝ) * E)
    have hright := h28.const_mul (2 * E ^ 2)
    have h := (hleft.add hright).mul_const C4
    have h' : Tendsto
        (fun n : ℕ => (((7 / 24 : ℝ) * E) *
            ((radialPowerCutoff n : ℝ)⁻¹) ^ 12 +
          (2 * E ^ 2) * ((radialPowerCutoff n : ℝ)⁻¹) ^ 28) * C4)
        atTop (𝓝 0) := by convert h using 1 <;> ring
    apply Tendsto.congr' (Filter.Eventually.of_forall fun n => ?_) h'
    symm
    calc
      ((7 / 24 : ℝ) * (E / ((n : ℝ) + 1)) +
          2 * (E / ((n : ℝ) + 1)) ^ 2) *
            (radialPowerCutoff n : ℝ) ^ 4 * C4 =
          ((7 / 24 : ℝ) *
              (E / ((n : ℝ) + 1) * (radialPowerCutoff n : ℝ) ^ 4) +
            2 * ((E / ((n : ℝ) + 1)) ^ 2 *
              (radialPowerCutoff n : ℝ) ^ 4)) * C4 := by ring
      _ = ((7 / 24 : ℝ) *
              (E * ((radialPowerCutoff n : ℝ)⁻¹) ^ 12) +
            2 * (E ^ 2 * ((radialPowerCutoff n : ℝ)⁻¹) ^ 28)) * C4 := by
          rw [radialPowerCutoff_div_mul_pow_four,
            radialPowerCutoff_div_sq_mul_pow_four]
      _ = (((7 / 24 : ℝ) * E) *
              ((radialPowerCutoff n : ℝ)⁻¹) ^ 12 +
            (2 * E ^ 2) * ((radialPowerCutoff n : ℝ)⁻¹) ^ 28) * C4 := by ring
  have hlast : Tendsto
      (fun n : ℕ => Real.sqrt (E / ((n : ℝ) + 1)) / 4 *
        (radialPowerCutoff n : ℝ) ^ 2 * C2)
      atTop (𝓝 0) := by
    have h := h6.const_mul (Real.sqrt E / 4 * C2)
    have h' : Tendsto
        (fun n : ℕ => (Real.sqrt E / 4 * C2) *
          ((radialPowerCutoff n : ℝ)⁻¹) ^ 6) atTop (𝓝 0) := by
      convert h using 1 <;> ring
    apply Tendsto.congr' (Filter.Eventually.of_forall fun n => ?_) h'
    symm
    calc
      Real.sqrt (E / ((n : ℝ) + 1)) / 4 *
          (radialPowerCutoff n : ℝ) ^ 2 * C2 =
        (Real.sqrt (E / ((n : ℝ) + 1)) *
          (radialPowerCutoff n : ℝ) ^ 2) / 4 * C2 := by ring
      _ = (Real.sqrt E * ((radialPowerCutoff n : ℝ)⁻¹) ^ 6) / 4 * C2 := by
        rw [sqrt_div_mul_radialPowerCutoff_sq E (by dsimp [E]; positivity) n]
      _ = (Real.sqrt E / 4 * C2) *
          ((radialPowerCutoff n : ℝ)⁻¹) ^ 6 := by ring
  have hupper : Tendsto upper atTop (𝓝 0) := by
    dsimp [upper]
    convert ((hfirst.add hmiddle).add hlast).const_mul (Real.exp 1) using 1 <;> ring
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)) hupper
  · filter_upwards with n
    calc
      (0 : ℝ) = cubeAverage (fun _ : Fin (n + 1) → Bool => (0 : ℝ)) :=
        (cubeAverage_const (N := n + 1) 0).symm
      _ ≤ cubeAverage
          (radialCubeSmallBallStatistic n s (radialPowerCutoff n)) := by
        apply cubeAverage_mono
        intro x
        unfold radialCubeSmallBallStatistic radialCubeAngularStatistic angularStatistic
        apply Real.circleAverage_nonneg_of_nonneg
        intro z hz
        exact smallBallCutoff_nonneg _ _
  · filter_upwards [eventually_ge_atTop 1] with n hn
    dsimp [upper]
    exact cubeAverage_radialCubeSmallBallStatistic_le n hn s
      (radialPowerCutoff n) (radialPowerCutoff_pos n)

end Erdos522

end AmalgamatedModule86


/-! ===== amalgamated from Research.StretchedExponentialSummable ===== -/

section AmalgamatedModule87


open Filter Topology Asymptotics

namespace Erdos522

/-- Every positive stretched exponential on the natural numbers is summable. -/
theorem summable_stretched_exponential_nat
    (c r : ℝ) (hc : 0 < c) (hr : 0 < r) :
    Summable (fun n : ℕ => Real.exp (-c * (((n : ℝ) + 1) ^ r))) := by
  let g : ℕ → ℝ := fun n => 1 / (((n : ℝ) + 1) ^ (2 : ℕ))
  have hg0 : Summable (fun n : ℕ => 1 / ((n : ℝ) ^ (2 : ℝ))) :=
    Real.summable_one_div_nat_rpow.mpr (by norm_num)
  have hg : Summable g := by
    have hs := (summable_nat_add_iff (f := fun n : ℕ =>
      1 / ((n : ℝ) ^ (2 : ℝ))) 1).mpr hg0
    simpa [g, Nat.cast_add, Real.rpow_two] using hs
  apply Summable.of_norm_bounded_eventually hg
  rw [Nat.cofinite_eq_atTop]
  have hbase : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hlittle := (isLittleO_log_rpow_atTop hr).bound (show 0 < c / 2 by positivity)
  have hlittleNat : ∀ᶠ n : ℕ in atTop,
      ‖Real.log ((n : ℝ) + 1)‖ ≤
        (c / 2) * ‖((n : ℝ) + 1) ^ r‖ := hbase.eventually hlittle
  filter_upwards [hlittleNat, eventually_ge_atTop 1] with n hnlog hn
  have hx : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hone : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hlog0 : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg hone
  have hrpow0 : 0 ≤ ((n : ℝ) + 1) ^ r := Real.rpow_nonneg hx.le _
  dsimp [g]
  rw [abs_of_pos (Real.exp_pos _)]
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hlog0, abs_of_nonneg hrpow0] at hnlog
  have hdom : 2 * Real.log ((n : ℝ) + 1) ≤
      c * ((n : ℝ) + 1) ^ r := by nlinarith
  calc
    Real.exp (-c * ((n : ℝ) + 1) ^ r) ≤
        Real.exp (-2 * Real.log ((n : ℝ) + 1)) := by
      apply Real.exp_le_exp.mpr
      linarith
    _ = ((n : ℝ) + 1) ^ (-2 : ℝ) := by
      rw [Real.rpow_def_of_pos hx]
      congr 1
      ring
    _ = 1 / (((n : ℝ) + 1) ^ (2 : ℕ)) := by
      rw [Real.rpow_neg hx.le, Real.rpow_two, one_div]

end Erdos522

end AmalgamatedModule87


/-! ===== amalgamated from Research.CubeMedianMean ===== -/

section AmalgamatedModule88


namespace Erdos522

lemma cubeProbability_union_le {N : ℕ} (A B : Set (Fin N → Bool)) :
    cubeProbability (A ∪ B) ≤ cubeProbability A + cubeProbability B := by
  classical
  unfold cubeProbability
  rw [← cubeAverage_add]
  apply cubeAverage_mono
  intro x
  by_cases hxA : x ∈ A <;> by_cases hxB : x ∈ B <;> simp [hxA, hxB]

lemma abs_cubeAverage_sub_const_le {N : ℕ}
    (F : (Fin N → Bool) → ℝ) (a : ℝ) :
    |cubeAverage F - a| ≤ cubeAverage (fun x => |F x - a|) := by
  have heq : cubeAverage F - a = cubeAverage (fun x => F x - a) := by
    rw [show (fun x => F x - a) = (fun x => F x + (-a)) by rfl,
      cubeAverage_add, cubeAverage_const]
    ring
  rw [heq]
  exact abs_cubeAverage_le _

lemma abs_median_le_of_bounded {N : ℕ}
    {F : (Fin N → Bool) → ℝ} {a B : ℝ}
    (hmed : IsCubeMedian F a) (hbound : ∀ x, |F x| ≤ B) :
    |a| ≤ B := by
  have hlow := nonempty_of_half_le_cubeProbability hmed.1
  have hupp := nonempty_of_half_le_cubeProbability hmed.2
  rcases hlow with ⟨x, hx⟩
  rcases hupp with ⟨y, hy⟩
  change F x ≤ a at hx
  change a ≤ F y at hy
  rw [abs_le]
  constructor
  · exact (neg_le_of_abs_le (hbound x)).trans hx
  · exact hy.trans (le_of_abs_le (hbound y))

/-- A bounded cube function's mean lies close to any median as soon as both
median tails are small at one scale. -/
theorem abs_cubeAverage_sub_median_le
    {N : ℕ} {F : (Fin N → Bool) → ℝ} {a B u pu pl : ℝ}
    (hB : 0 ≤ B) (hu : 0 ≤ u) (hbound : ∀ x, |F x| ≤ B)
    (hmed : IsCubeMedian F a)
    (hupper : cubeProbability {x | a + u ≤ F x} ≤ pu)
    (hlower : cubeProbability {x | F x + u ≤ a} ≤ pl) :
    |cubeAverage F - a| ≤ u + 2 * B * (pu + pl) := by
  classical
  have ha := abs_median_le_of_bounded hmed hbound
  let E : Set (Fin N → Bool) := {x | u < |F x - a|}
  have hEsub : E ⊆ {x | a + u ≤ F x} ∪ {x | F x + u ≤ a} := by
    intro x hx
    change u < |F x - a| at hx
    change (a + u ≤ F x) ∨ (F x + u ≤ a)
    rcases (lt_abs.mp hx) with hpos | hneg
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  have hEprob : cubeProbability E ≤ pu + pl := by
    calc
      cubeProbability E ≤ cubeProbability
          ({x | a + u ≤ F x} ∪ {x | F x + u ≤ a}) := cubeProbability_mono hEsub
      _ ≤ cubeProbability {x | a + u ≤ F x} +
          cubeProbability {x | F x + u ≤ a} := cubeProbability_union_le _ _
      _ ≤ pu + pl := add_le_add hupper hlower
  calc
    |cubeAverage F - a| ≤ cubeAverage (fun x => |F x - a|) :=
      abs_cubeAverage_sub_const_le F a
    _ ≤ cubeAverage (fun x => u + 2 * B * (if x ∈ E then 1 else 0)) := by
      apply cubeAverage_mono
      intro x
      by_cases hx : x ∈ E
      · simp only [hx, ↓reduceIte]
        have hFa : |F x - a| ≤ 2 * B := by
          calc
            |F x - a| ≤ |F x| + |a| := abs_sub _ _
            _ ≤ B + B := add_le_add (hbound x) ha
            _ = 2 * B := by ring
        linarith
      · simp only [hx, ↓reduceIte, mul_zero, add_zero]
        exact le_of_not_gt hx
    _ = u + 2 * B * cubeProbability E := by
      rw [cubeAverage_add, cubeAverage_const, cubeAverage_const_mul]
      rfl
    _ ≤ u + 2 * B * (pu + pl) := by
      gcongr

end Erdos522

end AmalgamatedModule88


/-! ===== amalgamated from Research.PowerSmallBallConcentration ===== -/

section AmalgamatedModule89


open Filter Topology

namespace Erdos522

noncomputable def powerSmallBallMedian (n : ℕ) (s : ℝ) : ℝ :=
  Classical.choose
    (exists_radialCubeSmallBallStatistic_median n s (radialPowerCutoff n))

lemma powerSmallBallMedian_isMedian (n : ℕ) (s : ℝ) :
    IsCubeMedian
      (radialCubeSmallBallStatistic n s (radialPowerCutoff n))
      (powerSmallBallMedian n s) :=
  Classical.choose_spec
    (exists_radialCubeSmallBallStatistic_median n s (radialPowerCutoff n))

noncomputable def powerSmallBallTail (s : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-((radialPowerCutoff n : ℝ) ^ 8 /
    (32 * (Real.exp (4 * |s|)) ^ 2)))

lemma radialPowerCutoff_pow_eight (n : ℕ) :
    (radialPowerCutoff n : ℝ) ^ 8 =
      ((n : ℝ) + 1) ^ (1 / 2 : ℝ) := by
  rw [coe_radialPowerCutoff]
  let x : ℝ := (n : ℝ) + 1
  have hx : 0 ≤ x := by dsimp [x]; positivity
  calc
    (x ^ (1 / 16 : ℝ)) ^ (8 : ℕ) =
        (x ^ (1 / 16 : ℝ)) ^ (8 : ℝ) :=
      (Real.rpow_natCast (x ^ (1 / 16 : ℝ)) 8).symm
    _ = x ^ ((1 / 16 : ℝ) * 8) := (Real.rpow_mul hx _ _).symm
    _ = x ^ (1 / 2 : ℝ) := by norm_num

lemma powerSmallBallTail_eq_stretched (s : ℝ) (n : ℕ) :
    powerSmallBallTail s n =
      Real.exp (-(1 / (32 * (Real.exp (4 * |s|)) ^ 2)) *
        (((n : ℝ) + 1) ^ (1 / 2 : ℝ))) := by
  unfold powerSmallBallTail
  rw [radialPowerCutoff_pow_eight]
  congr 1
  ring

/-- The explicit median-concentration tails at the power cutoff are summable. -/
theorem summable_powerSmallBallTail (s : ℝ) :
    Summable (powerSmallBallTail s) := by
  have hc : 0 < 1 / (32 * (Real.exp (4 * |s|)) ^ 2) := by positivity
  have h := summable_stretched_exponential_nat
    (1 / (32 * (Real.exp (4 * |s|)) ^ 2)) (1 / 2) hc (by norm_num)
  exact h.congr (fun n => (powerSmallBallTail_eq_stretched s n).symm)

lemma powerSmallBall_radius_eq (s : ℝ) (n : ℕ) :
    (((radialPowerCutoff n : ℝ)⁻¹) ^ 2 /
      (((radialPowerCutoff n : ℝ) *
        Real.sqrt (4 * (Real.exp (4 * |s|) / ((n : ℝ) + 1)))) ^ 2)) =
      (radialPowerCutoff n : ℝ) ^ 12 /
        (4 * Real.exp (4 * |s|)) := by
  let M : ℝ := radialPowerCutoff n
  let E : ℝ := Real.exp (4 * |s|)
  have hM : 0 < M := by dsimp [M]; exact_mod_cast radialPowerCutoff_pos n
  have hE : 0 < E := by dsimp [E]; positivity
  rw [← radialPowerCutoff_pow_sixteen n]
  have hsqrt : (Real.sqrt (4 * (E / M ^ 16))) ^ 2 = 4 * (E / M ^ 16) := by
    rw [Real.sq_sqrt]
    positivity
  change M⁻¹ ^ 2 / (M * Real.sqrt (4 * (E / M ^ 16))) ^ 2 = M ^ 12 / (4 * E)
  rw [mul_pow, hsqrt]
  field_simp [hM.ne', hE.ne']

lemma powerSmallBall_tail_exponent_eq (s : ℝ) (n : ℕ) :
    -(((radialPowerCutoff n : ℝ) ^ 12 /
        (4 * Real.exp (4 * |s|))) ^ 2 /
      (2 * ((n : ℝ) + 1))) =
      -((radialPowerCutoff n : ℝ) ^ 8 /
        (32 * (Real.exp (4 * |s|)) ^ 2)) := by
  rw [← radialPowerCutoff_pow_sixteen n]
  have hM : (radialPowerCutoff n : ℝ) ≠ 0 :=
    ne_of_gt (by exact_mod_cast radialPowerCutoff_pos n)
  have hE : Real.exp (4 * |s|) ≠ 0 := (Real.exp_pos _).ne'
  field_simp [hM, hE]
  ring

lemma eventually_powerSmallBall_radius_condition (s : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      2 * Real.sqrt ((n : ℝ) + 1) ≤
        ((radialPowerCutoff n : ℝ)⁻¹) ^ 2 /
          (((radialPowerCutoff n : ℝ) *
            Real.sqrt (4 * (Real.exp (4 * |s|) / ((n : ℝ) + 1)))) ^ 2) := by
  have hpowRaw := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 4)).comp
    tendsto_radialPowerCutoff_coe
  have hpow : Tendsto (fun n : ℕ => (radialPowerCutoff n : ℝ) ^ 4)
      atTop atTop := by
    apply Tendsto.congr' (Filter.Eventually.of_forall fun n => by
      change (radialPowerCutoff n : ℝ) ^ (4 : ℝ) =
        (radialPowerCutoff n : ℝ) ^ (4 : ℕ)
      exact Real.rpow_natCast _ 4) hpowRaw
  have hev : ∀ᶠ n : ℕ in atTop,
      8 * Real.exp (4 * |s|) ≤ (radialPowerCutoff n : ℝ) ^ 4 :=
    (tendsto_atTop.1 hpow (8 * Real.exp (4 * |s|)))
  filter_upwards [hev] with n hn
  rw [powerSmallBall_radius_eq]
  rw [show Real.sqrt ((n : ℝ) + 1) = (radialPowerCutoff n : ℝ) ^ 8 by
    rw [← radialPowerCutoff_pow_sixteen n,
      show (radialPowerCutoff n : ℝ) ^ 16 =
        ((radialPowerCutoff n : ℝ) ^ 8) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]]
  have hM : (0 : ℝ) < radialPowerCutoff n := by
    exact_mod_cast radialPowerCutoff_pos n
  have hE : 0 < Real.exp (4 * |s|) := Real.exp_pos _
  apply (le_div_iff₀ (mul_pos (by norm_num) hE)).2
  nlinarith [mul_le_mul_of_nonneg_right hn (pow_nonneg hM.le 8)]

/-- Summable upper median tails for the power-scale small-ball statistic. -/
theorem eventually_powerSmallBall_upper_median_tail (s : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      cubeProbability {x |
        powerSmallBallMedian n s + (radialPowerCutoff n : ℝ)⁻¹ ≤
          radialCubeSmallBallStatistic n s (radialPowerCutoff n) x} ≤
        powerSmallBallTail s n := by
  filter_upwards [eventually_ge_atTop 1,
    eventually_powerSmallBall_radius_condition s] with n hn hr
  have ht := radialCubeSmallBallStatistic_upper_median_tail
    n hn s (radialPowerCutoff n) (radialPowerCutoff_pos n)
    (powerSmallBallMedian n s) (powerSmallBallMedian_isMedian n s)
    (u := (radialPowerCutoff n : ℝ)⁻¹) (by positivity) (by
      simpa [Nat.cast_add, Nat.cast_one] using hr)
  calc
    cubeProbability {x |
        powerSmallBallMedian n s + (radialPowerCutoff n : ℝ)⁻¹ ≤
          radialCubeSmallBallStatistic n s (radialPowerCutoff n) x} ≤
      Real.exp (-
        (((radialPowerCutoff n : ℝ)⁻¹) ^ 2 /
          (((radialPowerCutoff n : ℝ) *
            Real.sqrt (4 * (Real.exp (4 * |s|) / ((n : ℝ) + 1)))) ^ 2)) ^ 2 /
        (2 * ((n : ℝ) + 1))) := by
          simpa [Nat.cast_add, Nat.cast_one] using ht
    _ = powerSmallBallTail s n := by
      rw [powerSmallBall_radius_eq]
      unfold powerSmallBallTail
      congr 1
      convert powerSmallBall_tail_exponent_eq s n using 1 <;> ring

/-- Summable lower median tails for the power-scale small-ball statistic. -/
theorem eventually_powerSmallBall_lower_median_tail (s : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      cubeProbability {x |
        radialCubeSmallBallStatistic n s (radialPowerCutoff n) x +
          (radialPowerCutoff n : ℝ)⁻¹ ≤ powerSmallBallMedian n s} ≤
        powerSmallBallTail s n := by
  filter_upwards [eventually_ge_atTop 1,
    eventually_powerSmallBall_radius_condition s] with n hn hr
  have ht := radialCubeAngularStatistic_lower_median_tail
    n hn s (smallBallCutoff (radialPowerCutoff n))
    (radialPowerCutoff_pos n) (smallBallCutoff_lipschitz (radialPowerCutoff n))
    (powerSmallBallMedian n s) (powerSmallBallMedian_isMedian n s)
    (u := (radialPowerCutoff n : ℝ)⁻¹) (by positivity) (by
      simpa [Nat.cast_add, Nat.cast_one] using hr)
  calc
    cubeProbability {x |
        radialCubeSmallBallStatistic n s (radialPowerCutoff n) x +
          (radialPowerCutoff n : ℝ)⁻¹ ≤ powerSmallBallMedian n s} ≤
      Real.exp (-
        (((radialPowerCutoff n : ℝ)⁻¹) ^ 2 /
          (((radialPowerCutoff n : ℝ) *
            Real.sqrt (4 * (Real.exp (4 * |s|) / ((n : ℝ) + 1)))) ^ 2)) ^ 2 /
        (2 * ((n : ℝ) + 1))) := by
          simpa [radialCubeSmallBallStatistic, Nat.cast_add, Nat.cast_one] using ht
    _ = powerSmallBallTail s n := by
      rw [powerSmallBall_radius_eq]
      unfold powerSmallBallTail
      congr 1
      convert powerSmallBall_tail_exponent_eq s n using 1 <;> ring

lemma abs_radialCubeSmallBallStatistic_le_one
    (n : ℕ) (s : ℝ) (x : Fin (n + 1) → Bool) :
    |radialCubeSmallBallStatistic n s (radialPowerCutoff n) x| ≤ 1 := by
  let p := weightedVectorPolynomial
    (fun k : Fin (n + 1) => radialWeight n s k)
    (fun k => realRademacherSign (x k))
  have hf : CircleIntegrable (fun z => smallBallCutoff (radialPowerCutoff n) (p.eval z))
      0 1 := by
    apply ContinuousOn.circleIntegrable (by norm_num)
    exact ((smallBallCutoff_lipschitz _).continuous.comp (by fun_prop)).continuousOn
  have h0 : 0 ≤ radialCubeSmallBallStatistic n s (radialPowerCutoff n) x := by
    unfold radialCubeSmallBallStatistic radialCubeAngularStatistic angularStatistic
    apply Real.circleAverage_nonneg_of_nonneg
    intro z hz
    exact smallBallCutoff_nonneg _ _
  rw [abs_of_nonneg h0]
  unfold radialCubeSmallBallStatistic radialCubeAngularStatistic angularStatistic
  change Real.circleAverage (fun z => smallBallCutoff (radialPowerCutoff n) (p.eval z))
    0 1 ≤ 1
  calc
    Real.circleAverage (fun z => smallBallCutoff (radialPowerCutoff n) (p.eval z))
        0 1 ≤ Real.circleAverage (fun _ : ℂ => (1 : ℝ)) 0 1 := by
      apply Real.circleAverage_mono hf
      · apply ContinuousOn.circleIntegrable (by norm_num)
        fun_prop
      · intro z hz
        exact smallBallCutoff_le_one _ _
    _ = 1 := Real.circleAverage_const 1 0 1

lemma eventually_abs_powerSmallBall_mean_sub_median_le (s : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      |cubeAverage (radialCubeSmallBallStatistic n s (radialPowerCutoff n)) -
          powerSmallBallMedian n s| ≤
        (radialPowerCutoff n : ℝ)⁻¹ + 4 * powerSmallBallTail s n := by
  filter_upwards [eventually_powerSmallBall_upper_median_tail s,
    eventually_powerSmallBall_lower_median_tail s] with n hu hl
  have h := abs_cubeAverage_sub_median_le
    (B := 1) (u := (radialPowerCutoff n : ℝ)⁻¹)
    (pu := powerSmallBallTail s n) (pl := powerSmallBallTail s n)
    (by norm_num) (by positivity)
    (abs_radialCubeSmallBallStatistic_le_one n s)
    (powerSmallBallMedian_isMedian n s) hu hl
  convert h using 1 <;> ring

/-- The two-sided cube medians of the power-scale small-ball statistics tend to
zero. -/
theorem tendsto_powerSmallBallMedian (s : ℝ) :
    Tendsto (fun n => powerSmallBallMedian n s) atTop (𝓝 0) := by
  have hinv0 : Tendsto (fun n : ℕ => (radialPowerCutoff n : ℝ)⁻¹)
      atTop (𝓝 0) := by
    have h := tendsto_radialPowerCutoff_inv_pow 1 (by norm_num)
    simpa using h
  have htail0 : Tendsto (powerSmallBallTail s) atTop (𝓝 0) :=
    (summable_powerSmallBallTail s).tendsto_atTop_zero
  have hupper0 : Tendsto
      (fun n : ℕ => (radialPowerCutoff n : ℝ)⁻¹ +
        4 * powerSmallBallTail s n) atTop (𝓝 0) := by
    convert hinv0.add (htail0.const_mul 4) using 1 <;> ring
  have habs : Tendsto
      (fun n : ℕ =>
        |cubeAverage (radialCubeSmallBallStatistic n s (radialPowerCutoff n)) -
          powerSmallBallMedian n s|) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)) hupper0
    · filter_upwards with n
      exact abs_nonneg _
    · exact eventually_abs_powerSmallBall_mean_sub_median_le s
  have hdiff : Tendsto
      (fun n : ℕ =>
        cubeAverage (radialCubeSmallBallStatistic n s (radialPowerCutoff n)) -
          powerSmallBallMedian n s) atTop (𝓝 0) := by
    apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
    simpa [Function.comp_def] using habs
  have hmean := tendsto_cubeAverage_radialCubeSmallBallStatistic_powerCutoff s
  have hmed := hmean.sub hdiff
  convert hmed using 1 <;> ring

/-- At every fixed positive threshold, the finite-cube deviation probabilities
for the power-scale small-ball statistic are summable. -/
theorem summable_powerSmallBall_cube_deviations (s : ℝ) (j : ℕ) :
    Summable (fun n : ℕ => cubeProbability {x |
      (1 : ℝ) / ((j : ℝ) + 1) ≤
        radialCubeSmallBallStatistic n s (radialPowerCutoff n) x}) := by
  let ε : ℝ := (1 : ℝ) / ((j : ℝ) + 1)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hinv0 : Tendsto (fun n : ℕ => (radialPowerCutoff n : ℝ)⁻¹)
      atTop (𝓝 0) := by
    have h := tendsto_radialPowerCutoff_inv_pow 1 (by norm_num)
    simpa using h
  have hsum0 : Tendsto
      (fun n : ℕ => powerSmallBallMedian n s +
        (radialPowerCutoff n : ℝ)⁻¹) atTop (𝓝 0) := by
    convert (tendsto_powerSmallBallMedian s).add hinv0 using 1 <;> ring
  have hsumSmall : ∀ᶠ n : ℕ in atTop,
      powerSmallBallMedian n s + (radialPowerCutoff n : ℝ)⁻¹ ≤ ε := by
    have hev := hsum0.eventually (Metric.ball_mem_nhds 0 hε)
    filter_upwards [hev] with n hn
    rw [Real.dist_eq, sub_zero] at hn
    exact (le_abs_self _).trans hn.le
  apply (summable_powerSmallBallTail s).of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [hsumSmall,
    eventually_powerSmallBall_upper_median_tail s] with n hsmall htail
  rw [Real.norm_eq_abs, abs_of_nonneg (by
    unfold cubeProbability cubeAverage
    positivity)]
  apply (cubeProbability_mono (B := {x |
    powerSmallBallMedian n s + (radialPowerCutoff n : ℝ)⁻¹ ≤
      radialCubeSmallBallStatistic n s (radialPowerCutoff n) x}) ?_).trans htail
  intro x hx
  exact hsmall.trans hx

end Erdos522

end AmalgamatedModule89


/-! ===== amalgamated from Research.FinitePrefixUniform ===== -/

section AmalgamatedModule90


open MeasureTheory ProbabilityTheory

namespace Erdos522

universe u

/-- Cylinder event fixing the first `N` Boolean coordinates. -/
def prefixCylinder {Ω : Type u} (ξ : ℕ → Ω → Bool)
    {N : ℕ} (x : Fin N → Bool) : Set Ω :=
  {ω | ∀ k : Fin N, ξ k ω = x k}

lemma measurableSet_bool_fiber {Ω : Type u} [MeasurableSpace Ω]
    {f : Ω → Bool} (hf : Measurable f) (b : Bool) :
    MeasurableSet {ω | f ω = b} := by
  change MeasurableSet (f ⁻¹' {b})
  exact (measurableSet_singleton b).preimage hf

lemma fair_bool_fiber {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → Bool) (hf : Measurable f)
    (htrue : μ {ω | f ω = true} = (1 : ENNReal) / 2)
    (b : Bool) : μ {ω | f ω = b} = (1 : ENNReal) / 2 := by
  cases b with
  | true => exact htrue
  | false =>
      have hcomp : {ω | f ω = false} = ({ω | f ω = true} : Set Ω)ᶜ := by
        ext ω
        cases f ω <;> simp
      rw [hcomp, measure_compl (measurableSet_bool_fiber hf true)]
      · rw [IsProbabilityMeasure.measure_univ, htrue]
        norm_num
      · rw [htrue]
        exact ENNReal.div_ne_top ENNReal.one_ne_top (by norm_num)

/-- Every finite prefix of an independent fair Boolean process is exactly
uniform on the finite cube. -/
theorem measure_prefixCylinder {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : ℕ → Ω → Bool) (hξ_meas : ∀ k, Measurable (ξ k))
    (hξ_indep : iIndepFun ξ μ)
    (hξ_fair : ∀ k, μ {ω | ξ k ω = true} = (1 : ENNReal) / 2)
    {N : ℕ} (x : Fin N → Bool) :
    μ (prefixCylinder ξ x) = ((1 : ENNReal) / 2) ^ N := by
  let ξN : Fin N → Ω → Bool := fun k => ξ k
  have hN : iIndepFun ξN μ :=
    iIndepFun.precomp Fin.val_injective hξ_indep
  have hs : ∀ k : Fin N,
      MeasurableSet[(inferInstance : MeasurableSpace Bool).comap (ξN k)]
        {ω | ξN k ω = x k} := by
    intro k
    rw [MeasurableSpace.measurableSet_comap]
    exact ⟨{x k}, measurableSet_singleton _, by ext ω; simp [ξN]⟩
  have hinter := hN.meas_iInter hs
  have hevent : prefixCylinder ξ x = ⋂ k : Fin N, {ω | ξN k ω = x k} := by
    ext ω
    simp [prefixCylinder, ξN]
  have hfiber (k : Fin N) :
      μ {ω | ξN k ω = x k} = (1 : ENNReal) / 2 :=
    fair_bool_fiber μ (ξN k) (hξ_meas k) (hξ_fair k) (x k)
  rw [hevent, hinter]
  simp_rw [hfiber]
  simp

end Erdos522

end AmalgamatedModule90


/-! ===== amalgamated from Research.FinitePrefixLaw ===== -/

section AmalgamatedModule91


open MeasureTheory ProbabilityTheory

namespace Erdos522

universe u

/-- The measurable vector of the first `N` coordinates. -/
def prefixVector {Ω : Type u} (ξ : ℕ → Ω → Bool) (N : ℕ) :
    Ω → (Fin N → Bool) := fun ω k => ξ k ω

lemma measurable_prefixVector {Ω : Type u} [MeasurableSpace Ω]
    (ξ : ℕ → Ω → Bool) (hξ_meas : ∀ k, Measurable (ξ k)) (N : ℕ) :
    Measurable (prefixVector ξ N) := by
  apply measurable_pi_lambda
  intro k
  exact hξ_meas k

/-- The pushforward law of every finite prefix is the canonical uniform PMF
on the Boolean cube. -/
theorem map_prefixVector_eq_uniform {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : ℕ → Ω → Bool) (hξ_meas : ∀ k, Measurable (ξ k))
    (hξ_indep : iIndepFun ξ μ)
    (hξ_fair : ∀ k, μ {ω | ξ k ω = true} = (1 : ENNReal) / 2)
    (N : ℕ) :
    Measure.map (prefixVector ξ N) μ =
      (PMF.uniformOfFintype (Fin N → Bool)).toMeasure := by
  apply Measure.ext_of_singleton
  intro x
  rw [Measure.map_apply (measurable_prefixVector ξ hξ_meas N)
    (measurableSet_singleton x), PMF.toMeasure_apply_singleton]
  · have hpre : prefixVector ξ N ⁻¹' {x} = prefixCylinder ξ x := by
      ext ω
      simp [prefixVector, prefixCylinder, funext_iff]
    rw [hpre, measure_prefixCylinder μ ξ hξ_meas hξ_indep hξ_fair,
      PMF.uniformOfFintype_apply]
    simp [Fintype.card_bool, Fintype.card_fin]
    exact (@ENNReal.inv_pow (2 : ENNReal) N).symm
  · exact measurableSet_singleton x

/-- Consequently every event depending on the first `N` bits has exactly its
uniform finite-cube probability. -/
theorem measure_prefix_event_eq_uniform {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : ℕ → Ω → Bool) (hξ_meas : ∀ k, Measurable (ξ k))
    (hξ_indep : iIndepFun ξ μ)
    (hξ_fair : ∀ k, μ {ω | ξ k ω = true} = (1 : ENNReal) / 2)
    (N : ℕ) (A : Set (Fin N → Bool)) :
    μ ((prefixVector ξ N) ⁻¹' A) =
      (PMF.uniformOfFintype (Fin N → Bool)).toMeasure A := by
  have hm := measurable_prefixVector ξ hξ_meas N
  have hA : MeasurableSet A := Set.toFinite A |>.measurableSet
  rw [← Measure.map_apply hm hA, map_prefixVector_eq_uniform μ ξ hξ_meas
    hξ_indep hξ_fair N]

end Erdos522

end AmalgamatedModule91


/-! ===== amalgamated from Research.CubeProbabilityMeasure ===== -/

section AmalgamatedModule92


open MeasureTheory ProbabilityTheory

namespace Erdos522

lemma cubeProbability_eq_card_div {N : ℕ} (A : Set (Fin N → Bool)) :
    cubeProbability A = (A.ncard : ℝ) / (2 : ℝ) ^ N := by
  classical
  unfold cubeProbability cubeAverage
  rw [Finset.sum_boole]
  congr 2
  simpa using (Set.ncard_eq_toFinset_card' A).symm

lemma uniformBooleanCube_measure_eq_card_div {N : ℕ} (A : Set (Fin N → Bool)) :
    (PMF.uniformOfFintype (Fin N → Bool)).toMeasure A =
      (A.ncard : ENNReal) / (2 : ENNReal) ^ N := by
  classical
  rw [PMF.toMeasure_apply (PMF.uniformOfFintype (Fin N → Bool))
    (Set.toFinite A |>.measurableSet), tsum_fintype]
  calc
    ∑ x : Fin N → Bool,
        A.indicator (⇑(PMF.uniformOfFintype (Fin N → Bool))) x =
        ∑ x ∈ A.toFinset,
          A.indicator (⇑(PMF.uniformOfFintype (Fin N → Bool))) x := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro x hx hnot
      simp only [Set.mem_toFinset] at hnot
      simp [Set.indicator_of_notMem hnot]
    _ = ∑ _x ∈ A.toFinset,
        ((Fintype.card (Fin N → Bool) : ENNReal)⁻¹) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Set.indicator_of_mem (Set.mem_toFinset.mp hx),
        PMF.uniformOfFintype_apply]
    _ = (A.ncard : ENNReal) / (2 : ENNReal) ^ N := by
      simp [Fintype.card_bool, Fintype.card_fin, ENNReal.div_eq_inv_mul,
        ← Set.ncard_eq_toFinset_card' A, mul_comm]

lemma ofReal_cubeProbability_eq_uniformMeasure {N : ℕ}
    (A : Set (Fin N → Bool)) :
    ENNReal.ofReal (cubeProbability A) =
      (PMF.uniformOfFintype (Fin N → Bool)).toMeasure A := by
  rw [cubeProbability_eq_card_div, uniformBooleanCube_measure_eq_card_div,
    ENNReal.ofReal_div_of_pos (by positivity)]
  norm_num [ENNReal.ofReal_natCast, ENNReal.ofReal_pow]

/-- Prefix events inherit the real-valued `cubeProbability` bound exactly. -/
theorem measure_prefix_event_eq_ofReal_cubeProbability
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : ℕ → Ω → Bool) (hξ_meas : ∀ k, Measurable (ξ k))
    (hξ_indep : iIndepFun ξ μ)
    (hξ_fair : ∀ k, μ {ω | ξ k ω = true} = (1 : ENNReal) / 2)
    (N : ℕ) (A : Set (Fin N → Bool)) :
    μ ((prefixVector ξ N) ⁻¹' A) = ENNReal.ofReal (cubeProbability A) := by
  rw [measure_prefix_event_eq_uniform μ ξ hξ_meas hξ_indep hξ_fair,
    ofReal_cubeProbability_eq_uniformMeasure]

end Erdos522

end AmalgamatedModule92


/-! ===== amalgamated from Research.BorelCantelliConvergence ===== -/

section AmalgamatedModule93


open Filter MeasureTheory
open scoped Topology

namespace Erdos522

/-- A countable family of summable fixed-threshold deviation probabilities
implies almost-sure convergence.  This is the precise first-Borel--Cantelli
mechanism used in the quenched logarithmic argument. -/
theorem ae_tendsto_of_summable_reciprocal_deviations
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : ℕ → Ω → ℝ) (c : ℝ)
    (hsum : ∀ j : ℕ,
      (∑' n : ℕ, μ {ω | (1 : ℝ) / ((j : ℝ) + 1) ≤ |f n ω - c|}) ≠ ⊤) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (nhds c) := by
  have hbc : ∀ j : ℕ, ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop,
      ω ∉ {ω | (1 : ℝ) / ((j : ℝ) + 1) ≤ |f n ω - c|} := by
    intro j
    exact ae_eventually_notMem (hsum j)
  have hall : ∀ᵐ ω ∂μ, ∀ j : ℕ, ∀ᶠ n : ℕ in atTop,
      ω ∉ {ω | (1 : ℝ) / ((j : ℝ) + 1) ≤ |f n ω - c|} :=
    MeasureTheory.ae_all_iff.mpr hbc
  filter_upwards [hall] with ω hω
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt hε
  obtain ⟨N, hN⟩ := (eventually_atTop.mp (hω j))
  refine ⟨N, fun n hn => ?_⟩
  have hnot := hN n hn
  rw [Real.dist_eq]
  exact (lt_of_not_ge hnot).trans hj

end Erdos522

end AmalgamatedModule93


/-! ===== amalgamated from Research.ProcessSmallBallLimit ===== -/

section AmalgamatedModule94


open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace Erdos522

lemma cubeProbability_nonneg' {N : ℕ} (A : Set (Fin N → Bool)) :
    0 ≤ cubeProbability A := by
  classical
  unfold cubeProbability cubeAverage
  positivity

/-- The power-scale small-ball observable of the first `n+1` signs of an
abstract process. -/
noncomputable def processPowerSmallBallStatistic
    {Ω : Type*} (ξ : ℕ → Ω → Bool) (n : ℕ) (s : ℝ) (ω : Ω) : ℝ :=
  radialCubeSmallBallStatistic n s (radialPowerCutoff n)
    (prefixVector ξ (n + 1) ω)

lemma processPowerSmallBallStatistic_nonneg
    {Ω : Type*} (ξ : ℕ → Ω → Bool) (n : ℕ) (s : ℝ) (ω : Ω) :
    0 ≤ processPowerSmallBallStatistic ξ n s ω := by
  unfold processPowerSmallBallStatistic radialCubeSmallBallStatistic
    radialCubeAngularStatistic angularStatistic
  apply Real.circleAverage_nonneg_of_nonneg
  intro z hz
  exact smallBallCutoff_nonneg _ _

lemma measure_processPowerSmallBall_deviation_eq
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : ℕ → Ω → Bool) (hξ_meas : ∀ k, Measurable (ξ k))
    (hξ_indep : iIndepFun ξ μ)
    (hξ_fair : ∀ k, μ {ω | ξ k ω = true} = (1 : ENNReal) / 2)
    (s : ℝ) (j n : ℕ) :
    μ {ω | (1 : ℝ) / ((j : ℝ) + 1) ≤
      processPowerSmallBallStatistic ξ n s ω} =
      ENNReal.ofReal (cubeProbability {x |
        (1 : ℝ) / ((j : ℝ) + 1) ≤
          radialCubeSmallBallStatistic n s (radialPowerCutoff n) x}) := by
  simpa [processPowerSmallBallStatistic] using
    measure_prefix_event_eq_ofReal_cubeProbability μ ξ hξ_meas hξ_indep hξ_fair
      (n + 1) {x | (1 : ℝ) / ((j : ℝ) + 1) ≤
        radialCubeSmallBallStatistic n s (radialPowerCutoff n) x}

lemma tsum_measure_processPowerSmallBall_deviation_ne_top
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : ℕ → Ω → Bool) (hξ_meas : ∀ k, Measurable (ξ k))
    (hξ_indep : iIndepFun ξ μ)
    (hξ_fair : ∀ k, μ {ω | ξ k ω = true} = (1 : ENNReal) / 2)
    (s : ℝ) (j : ℕ) :
    (∑' n : ℕ, μ {ω | (1 : ℝ) / ((j : ℝ) + 1) ≤
      processPowerSmallBallStatistic ξ n s ω}) ≠ ⊤ := by
  let p : ℕ → ℝ := fun n => cubeProbability {x |
    (1 : ℝ) / ((j : ℝ) + 1) ≤
      radialCubeSmallBallStatistic n s (radialPowerCutoff n) x}
  let q : ℕ → NNReal := fun n => ⟨p n, cubeProbability_nonneg' _⟩
  have hp : Summable p := summable_powerSmallBall_cube_deviations s j
  have hq : Summable q := by
    apply NNReal.summable_coe.mp
    have hcoe : (fun n => (q n : ℝ)) = p := by
      funext n
      rfl
    rw [hcoe]
    exact hp
  have heq : (fun n : ℕ => μ {ω | (1 : ℝ) / ((j : ℝ) + 1) ≤
      processPowerSmallBallStatistic ξ n s ω}) =
      fun n => (q n : ENNReal) := by
    funext n
    rw [measure_processPowerSmallBall_deviation_eq μ ξ hξ_meas hξ_indep hξ_fair]
    exact ENNReal.ofReal_eq_coe_nnreal (cubeProbability_nonneg' _)
  rw [heq]
  exact ENNReal.tsum_coe_ne_top_iff_summable.mpr hq

/-- For every fixed shift, the angular small-ball mass at radius
`(n+1)^(-1/16)` tends to zero almost surely for an arbitrary measurable i.i.d.
fair sign process. -/
theorem ae_tendsto_processPowerSmallBallStatistic
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : ℕ → Ω → Bool) (hξ_meas : ∀ k, Measurable (ξ k))
    (hξ_indep : iIndepFun ξ μ)
    (hξ_fair : ∀ k, μ {ω | ξ k ω = true} = (1 : ENNReal) / 2)
    (s : ℝ) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n => processPowerSmallBallStatistic ξ n s ω)
        atTop (𝓝 0) := by
  apply ae_tendsto_of_summable_reciprocal_deviations μ
    (fun n ω => processPowerSmallBallStatistic ξ n s ω) 0
  intro j
  have hsum := tsum_measure_processPowerSmallBall_deviation_ne_top
    μ ξ hξ_meas hξ_indep hξ_fair s j
  convert hsum using 1
  congr 1
  funext n
  congr 1
  ext ω
  simp only [sub_zero, Set.mem_setOf_eq]
  rw [abs_of_nonneg (processPowerSmallBallStatistic_nonneg ξ n s ω)]

end Erdos522

end AmalgamatedModule94


/-! ===== amalgamated from Research.ProcessSmallBallRate ===== -/

section AmalgamatedModule95


open Filter MeasureTheory ProbabilityTheory

namespace Erdos522

noncomputable def powerSmallBallUpperCubeEvent (s : ℝ) (n : ℕ) :
    Set (Fin (n + 1) → Bool) :=
  {x | powerSmallBallMedian n s + (radialPowerCutoff n : ℝ)⁻¹ ≤
    radialCubeSmallBallStatistic n s (radialPowerCutoff n) x}

noncomputable def processPowerSmallBallUpperEvent
    {Ω : Type*} (ξ : ℕ → Ω → Bool) (s : ℝ) (n : ℕ) : Set Ω :=
  {ω | powerSmallBallMedian n s + (radialPowerCutoff n : ℝ)⁻¹ ≤
    processPowerSmallBallStatistic ξ n s ω}

lemma summable_powerSmallBall_upper_cube_probabilities (s : ℝ) :
    Summable (fun n : ℕ => cubeProbability (powerSmallBallUpperCubeEvent s n)) := by
  apply (summable_powerSmallBallTail s).of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_powerSmallBall_upper_median_tail s] with n hn
  rw [Real.norm_eq_abs, abs_of_nonneg (cubeProbability_nonneg' _)]
  exact hn

lemma tsum_processPowerSmallBallUpperEvent_ne_top
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : ℕ → Ω → Bool) (hξ_meas : ∀ k, Measurable (ξ k))
    (hξ_indep : iIndepFun ξ μ)
    (hξ_fair : ∀ k, μ {ω | ξ k ω = true} = (1 : ENNReal) / 2)
    (s : ℝ) :
    (∑' n : ℕ, μ (processPowerSmallBallUpperEvent ξ s n)) ≠ ⊤ := by
  let p : ℕ → ℝ := fun n => cubeProbability (powerSmallBallUpperCubeEvent s n)
  let q : ℕ → NNReal := fun n => ⟨p n, cubeProbability_nonneg' _⟩
  have hp : Summable p := summable_powerSmallBall_upper_cube_probabilities s
  have hq : Summable q := by
    apply NNReal.summable_coe.mp
    have hcoe : (fun n => (q n : ℝ)) = p := by funext n; rfl
    rw [hcoe]
    exact hp
  have heq : (fun n : ℕ => μ (processPowerSmallBallUpperEvent ξ s n)) =
      fun n => (q n : ENNReal) := by
    funext n
    have hm := measure_prefix_event_eq_ofReal_cubeProbability
      μ ξ hξ_meas hξ_indep hξ_fair (n + 1)
      (powerSmallBallUpperCubeEvent s n)
    rw [show processPowerSmallBallUpperEvent ξ s n =
        (prefixVector ξ (n + 1)) ⁻¹' powerSmallBallUpperCubeEvent s n by
      ext ω
      rfl]
    rw [hm]
    exact ENNReal.ofReal_eq_coe_nnreal (cubeProbability_nonneg' _)
  rw [heq]
  exact ENNReal.tsum_coe_ne_top_iff_summable.mpr hq

/-- Almost surely the random small-ball statistic is eventually bounded by its
cube mean plus the explicit `2/M_n + 4p_n` concentration correction. -/
theorem ae_eventually_processPowerSmallBallStatistic_le_rate
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : ℕ → Ω → Bool) (hξ_meas : ∀ k, Measurable (ξ k))
    (hξ_indep : iIndepFun ξ μ)
    (hξ_fair : ∀ k, μ {ω | ξ k ω = true} = (1 : ENNReal) / 2)
    (s : ℝ) :
    ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop,
      processPowerSmallBallStatistic ξ n s ω ≤
        cubeAverage (radialCubeSmallBallStatistic n s (radialPowerCutoff n)) +
          2 * (radialPowerCutoff n : ℝ)⁻¹ + 4 * powerSmallBallTail s n := by
  have hbc : ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop,
      ω ∉ processPowerSmallBallUpperEvent ξ s n :=
    ae_eventually_notMem
      (tsum_processPowerSmallBallUpperEvent_ne_top
        μ ξ hξ_meas hξ_indep hξ_fair s)
  filter_upwards [hbc] with ω hω
  filter_upwards [hω, eventually_abs_powerSmallBall_mean_sub_median_le s]
    with n hn hmed
  have hstrict : processPowerSmallBallStatistic ξ n s ω <
      powerSmallBallMedian n s + (radialPowerCutoff n : ℝ)⁻¹ :=
    lt_of_not_ge hn
  have hmedian : powerSmallBallMedian n s ≤
      cubeAverage (radialCubeSmallBallStatistic n s (radialPowerCutoff n)) +
        (radialPowerCutoff n : ℝ)⁻¹ + 4 * powerSmallBallTail s n := by
    have hside := neg_le_of_abs_le hmed
    linarith
  linarith

end Erdos522

end AmalgamatedModule95


/-! ===== amalgamated from Research.PowerSmallBallExplicitRate ===== -/

section AmalgamatedModule96


open MeasureTheory ProbabilityTheory

namespace Erdos522

noncomputable def powerSmallBallRateConstant (s : ℝ) : ℝ :=
  Real.exp 1 *
    (2 * Real.sqrt Real.pi +
      (((7 / 24 : ℝ) * Real.exp (4 * |s|) +
        2 * (Real.exp (4 * |s|)) ^ 2) *
          circularGaussianFourthNormMoment) +
      (Real.sqrt (Real.exp (4 * |s|)) / 4 *
        circularGaussianSecondNormMoment))

lemma one_le_radialPowerCutoff (n : ℕ) :
    (1 : ℝ) ≤ radialPowerCutoff n := by
  rw [coe_radialPowerCutoff]
  have h := Real.rpow_le_rpow (x := (1 : ℝ)) (y := (n : ℝ) + 1)
    (z := (1 / 16 : ℝ)) (by norm_num)
    (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)) (by norm_num)
  simpa using h

lemma inv_pow_radialPowerCutoff_le_inv (n k : ℕ) (hk : 0 < k) :
    ((radialPowerCutoff n : ℝ)⁻¹) ^ k ≤
      (radialPowerCutoff n : ℝ)⁻¹ := by
  have hM : (0 : ℝ) < radialPowerCutoff n := by
    exact_mod_cast radialPowerCutoff_pos n
  have hinv0 : 0 ≤ (radialPowerCutoff n : ℝ)⁻¹ := inv_nonneg.mpr hM.le
  have hinv1 : (radialPowerCutoff n : ℝ)⁻¹ ≤ 1 :=
    (inv_le_one₀ hM).mpr (one_le_radialPowerCutoff n)
  simpa using pow_le_pow_of_le_one hinv0 hinv1 (show 1 ≤ k from hk)

/-- The annealed small-ball cube mean has the explicit `O_s(M_n⁻¹)` bound. -/
theorem cubeAverage_radialCubeSmallBallStatistic_powerCutoff_le
    (s : ℝ) (n : ℕ) (hn : 0 < n) :
    cubeAverage (radialCubeSmallBallStatistic n s (radialPowerCutoff n)) ≤
      powerSmallBallRateConstant s * (radialPowerCutoff n : ℝ)⁻¹ := by
  let E : ℝ := Real.exp (4 * |s|)
  let C2 : ℝ := circularGaussianSecondNormMoment
  let C4 : ℝ := circularGaussianFourthNormMoment
  have hraw := cubeAverage_radialCubeSmallBallStatistic_le n hn s
    (radialPowerCutoff n) (radialPowerCutoff_pos n)
  have h12 := inv_pow_radialPowerCutoff_le_inv n 12 (by norm_num)
  have h28 := inv_pow_radialPowerCutoff_le_inv n 28 (by norm_num)
  have h6 := inv_pow_radialPowerCutoff_le_inv n 6 (by norm_num)
  have hC2 : 0 ≤ C2 := circularGaussianSecondNormMoment_nonneg
  have hC4 : 0 ≤ C4 := circularGaussianFourthNormMoment_nonneg
  have hE : 0 < E := by dsimp [E]; positivity
  have hexact :
      2 * Real.sqrt Real.pi / (radialPowerCutoff n : ℝ) +
        ((7 / 24 : ℝ) * (E / ((n : ℝ) + 1)) +
          2 * (E / ((n : ℝ) + 1)) ^ 2) *
            (radialPowerCutoff n : ℝ) ^ 4 * C4 +
        Real.sqrt (E / ((n : ℝ) + 1)) / 4 *
          (radialPowerCutoff n : ℝ) ^ 2 * C2 =
      2 * Real.sqrt Real.pi * (radialPowerCutoff n : ℝ)⁻¹ +
        (((7 / 24 : ℝ) * E) * ((radialPowerCutoff n : ℝ)⁻¹) ^ 12 +
          (2 * E ^ 2) * ((radialPowerCutoff n : ℝ)⁻¹) ^ 28) * C4 +
        (Real.sqrt E / 4 * C2) *
          ((radialPowerCutoff n : ℝ)⁻¹) ^ 6 := by
    have hA := radialPowerCutoff_div_mul_pow_four E n
    have hB := radialPowerCutoff_div_sq_mul_pow_four E n
    have hC := sqrt_div_mul_radialPowerCutoff_sq E hE.le n
    calc
      2 * Real.sqrt Real.pi / (radialPowerCutoff n : ℝ) +
          ((7 / 24 : ℝ) * (E / ((n : ℝ) + 1)) +
            2 * (E / ((n : ℝ) + 1)) ^ 2) *
              (radialPowerCutoff n : ℝ) ^ 4 * C4 +
          Real.sqrt (E / ((n : ℝ) + 1)) / 4 *
            (radialPowerCutoff n : ℝ) ^ 2 * C2 =
        2 * Real.sqrt Real.pi * (radialPowerCutoff n : ℝ)⁻¹ +
          ((7 / 24 : ℝ) *
              (E / ((n : ℝ) + 1) * (radialPowerCutoff n : ℝ) ^ 4) +
            2 * ((E / ((n : ℝ) + 1)) ^ 2 *
              (radialPowerCutoff n : ℝ) ^ 4)) * C4 +
          (Real.sqrt (E / ((n : ℝ) + 1)) *
            (radialPowerCutoff n : ℝ) ^ 2) / 4 * C2 := by ring
      _ = _ := by rw [hA, hB, hC]; ring
  calc
    cubeAverage (radialCubeSmallBallStatistic n s (radialPowerCutoff n)) ≤
        Real.exp 1 *
          (2 * Real.sqrt Real.pi / (radialPowerCutoff n : ℝ) +
            ((7 / 24 : ℝ) * (E / ((n : ℝ) + 1)) +
              2 * (E / ((n : ℝ) + 1)) ^ 2) *
                (radialPowerCutoff n : ℝ) ^ 4 * C4 +
            Real.sqrt (E / ((n : ℝ) + 1)) / 4 *
              (radialPowerCutoff n : ℝ) ^ 2 * C2) := by
        simpa [E, C2, C4] using hraw
    _ = Real.exp 1 *
        (2 * Real.sqrt Real.pi * (radialPowerCutoff n : ℝ)⁻¹ +
          (((7 / 24 : ℝ) * E) * ((radialPowerCutoff n : ℝ)⁻¹) ^ 12 +
            (2 * E ^ 2) * ((radialPowerCutoff n : ℝ)⁻¹) ^ 28) * C4 +
          (Real.sqrt E / 4 * C2) *
            ((radialPowerCutoff n : ℝ)⁻¹) ^ 6) := by rw [hexact]
    _ ≤ Real.exp 1 *
        ((2 * Real.sqrt Real.pi +
          (((7 / 24 : ℝ) * E + 2 * E ^ 2) * C4) +
          (Real.sqrt E / 4 * C2)) *
            (radialPowerCutoff n : ℝ)⁻¹) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos 1).le
      have hpi : 0 ≤ Real.sqrt Real.pi := Real.sqrt_nonneg _
      nlinarith [mul_le_mul_of_nonneg_left h12 (by positivity : 0 ≤ (7 / 24 : ℝ) * E),
        mul_le_mul_of_nonneg_left h28 (by positivity : 0 ≤ 2 * E ^ 2),
        mul_le_mul_of_nonneg_right
          (add_le_add
            (mul_le_mul_of_nonneg_left h12 (by positivity : 0 ≤ (7 / 24 : ℝ) * E))
            (mul_le_mul_of_nonneg_left h28 (by positivity : 0 ≤ 2 * E ^ 2))) hC4,
        mul_le_mul_of_nonneg_left h6 (by positivity : 0 ≤ Real.sqrt E / 4 * C2)]
    _ = powerSmallBallRateConstant s *
        (radialPowerCutoff n : ℝ)⁻¹ := by
      dsimp [powerSmallBallRateConstant, E, C2, C4]
      ring

/-- The quenched rate envelope can therefore be made completely explicit:
`O_s(M_n⁻¹)` plus a summable stretched exponential. -/
theorem ae_eventually_processPowerSmallBallStatistic_le_explicit_rate
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : ℕ → Ω → Bool) (hξ_meas : ∀ k, Measurable (ξ k))
    (hξ_indep : iIndepFun ξ μ)
    (hξ_fair : ∀ k, μ {ω | ξ k ω = true} = (1 : ENNReal) / 2)
    (s : ℝ) :
    ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in Filter.atTop,
      processPowerSmallBallStatistic ξ n s ω ≤
        (powerSmallBallRateConstant s + 2) *
          (radialPowerCutoff n : ℝ)⁻¹ + 4 * powerSmallBallTail s n := by
  filter_upwards [ae_eventually_processPowerSmallBallStatistic_le_rate
    μ ξ hξ_meas hξ_indep hξ_fair s] with ω hω
  filter_upwards [hω, Filter.eventually_ge_atTop 1] with n hn hnone
  have hmean := cubeAverage_radialCubeSmallBallStatistic_powerCutoff_le
    s n hnone
  linarith

end Erdos522

end AmalgamatedModule96


/-! ===== amalgamated from Research.RadialCubeConcentration ===== -/

section AmalgamatedModule97


open scoped BigOperators
open Metric

namespace Erdos522

lemma radialCube_upper_deviation_infDist
    (n : ℕ) (hn : 0 < n) (s : ℝ) (M : NNReal) (hM : 1 ≤ M)
    (a u : ℝ) (hu : 0 ≤ u)
    (hAne : ({y | radialCubeClippedStatistic n s M y ≤ a} :
      Set (Fin (n + 1) → Bool)).Nonempty)
    {x : Fin (n + 1) → Bool}
    (hx : a + u ≤ radialCubeClippedStatistic n s M x) :
    u ^ 2 /
        (4 * (M : ℝ) ^ 2 * (Real.exp (4 * |s|) / (n + 1 : ℝ))) ≤
      cubeInfDist
        {y | radialCubeClippedStatistic n s M y ≤ a} x := by
  let A : Set (Fin (n + 1) → Bool) :=
    {y | radialCubeClippedStatistic n s M y ≤ a}
  have hA : A.Nonempty := hAne
  apply (le_infDist (s := toHammingSet A) (by
    rcases hA with ⟨y, hy⟩
    exact ⟨Hamming.toHamming y, ⟨y, hy, rfl⟩⟩)).mpr
  rintro z ⟨y, hy, rfl⟩
  change u ^ 2 /
      (4 * (M : ℝ) ^ 2 * (Real.exp (4 * |s|) / (n + 1 : ℝ))) ≤
    dist (Hamming.toHamming x) (Hamming.toHamming y)
  rw [Hamming.dist_eq_hammingDist]
  change _ ≤ (hammingDist x y : ℝ)
  have hdiff : u ≤
      |radialCubeClippedStatistic n s M x -
        radialCubeClippedStatistic n s M y| := by
    have hy' : radialCubeClippedStatistic n s M y ≤ a := hy
    calc
      u ≤ radialCubeClippedStatistic n s M x -
          radialCubeClippedStatistic n s M y := by linarith
      _ ≤ |radialCubeClippedStatistic n s M x -
          radialCubeClippedStatistic n s M y| := le_abs_self _
  have hmod := radialCubeClippedStatistic_dist_le n hn s M hM x y
  have hroot : 0 ≤ √((Real.exp (4 * |s|) / (n + 1 : ℝ)) *
      (4 * (hammingDist x y : ℝ))) := Real.sqrt_nonneg _
  have hsq := (sq_le_sq₀ hu (mul_nonneg (by positivity : (0 : ℝ) ≤ M) hroot)).mpr
    (hdiff.trans hmod)
  rw [mul_pow, Real.sq_sqrt (by positivity)] at hsq
  apply (div_le_iff₀ (by positivity :
    (0 : ℝ) < 4 * (M : ℝ) ^ 2 *
      (Real.exp (4 * |s|) / (n + 1 : ℝ)))).mpr
  nlinarith

lemma radialCube_lower_deviation_infDist
    (n : ℕ) (hn : 0 < n) (s : ℝ) (M : NNReal) (hM : 1 ≤ M)
    (a u : ℝ) (hu : 0 ≤ u)
    (hAne : ({y | a ≤ radialCubeClippedStatistic n s M y} :
      Set (Fin (n + 1) → Bool)).Nonempty)
    {x : Fin (n + 1) → Bool}
    (hx : radialCubeClippedStatistic n s M x + u ≤ a) :
    u ^ 2 /
        (4 * (M : ℝ) ^ 2 * (Real.exp (4 * |s|) / (n + 1 : ℝ))) ≤
      cubeInfDist
        {y | a ≤ radialCubeClippedStatistic n s M y} x := by
  let A : Set (Fin (n + 1) → Bool) :=
    {y | a ≤ radialCubeClippedStatistic n s M y}
  have hA : A.Nonempty := hAne
  apply (le_infDist (s := toHammingSet A) (by
    rcases hA with ⟨y, hy⟩
    exact ⟨Hamming.toHamming y, ⟨y, hy, rfl⟩⟩)).mpr
  rintro z ⟨y, hy, rfl⟩
  change u ^ 2 /
      (4 * (M : ℝ) ^ 2 * (Real.exp (4 * |s|) / (n + 1 : ℝ))) ≤
    dist (Hamming.toHamming x) (Hamming.toHamming y)
  rw [Hamming.dist_eq_hammingDist]
  change _ ≤ (hammingDist x y : ℝ)
  have hdiff : u ≤
      |radialCubeClippedStatistic n s M x -
        radialCubeClippedStatistic n s M y| := by
    have hy' : a ≤ radialCubeClippedStatistic n s M y := hy
    calc
      u ≤ radialCubeClippedStatistic n s M y -
          radialCubeClippedStatistic n s M x := by linarith
      _ ≤ |radialCubeClippedStatistic n s M x -
          radialCubeClippedStatistic n s M y| := by
        rw [abs_sub_comm]
        exact le_abs_self _
  have hmod := radialCubeClippedStatistic_dist_le n hn s M hM x y
  have hroot : 0 ≤ √((Real.exp (4 * |s|) / (n + 1 : ℝ)) *
      (4 * (hammingDist x y : ℝ))) := Real.sqrt_nonneg _
  have hsq := (sq_le_sq₀ hu (mul_nonneg (by positivity : (0 : ℝ) ≤ M) hroot)).mpr
    (hdiff.trans hmod)
  rw [mul_pow, Real.sq_sqrt (by positivity)] at hsq
  apply (div_le_iff₀ (by positivity :
    (0 : ℝ) < 4 * (M : ℝ) ^ 2 *
      (Real.exp (4 * |s|) / (n + 1 : ℝ)))).mpr
  nlinarith

/-- Upper deviation from any median has the quartic finite-cube tail obtained
by combining F-026 with F-027. -/
theorem radialCube_upper_median_tail
    (n : ℕ) (hn : 0 < n) (s : ℝ) (M : NNReal) (hM : 1 ≤ M)
    (a : ℝ) (hmed : IsCubeMedian (radialCubeClippedStatistic n s M) a)
    {u : ℝ} (hu : 0 ≤ u)
    (hr : 2 * √((n + 1 : ℝ)) ≤
      u ^ 2 /
        (4 * (M : ℝ) ^ 2 * (Real.exp (4 * |s|) / (n + 1 : ℝ)))) :
    cubeProbability
        {x | a + u ≤ radialCubeClippedStatistic n s M x} ≤
      Real.exp (-
        (u ^ 2 /
          (4 * (M : ℝ) ^ 2 * (Real.exp (4 * |s|) / (n + 1 : ℝ)))) ^ 2 /
        (2 * (n + 1 : ℝ))) := by
  let A : Set (Fin (n + 1) → Bool) :=
    {y | radialCubeClippedStatistic n s M y ≤ a}
  let r : ℝ := u ^ 2 /
    (4 * (M : ℝ) ^ 2 * (Real.exp (4 * |s|) / (n + 1 : ℝ)))
  have hAne : A.Nonempty :=
    nonempty_of_half_le_cubeProbability (by simpa [A] using hmed.1)
  have hsubset : {x | a + u ≤ radialCubeClippedStatistic n s M x} ⊆
      {x | r ≤ cubeInfDist A x} := by
    intro x hx
    exact radialCube_upper_deviation_infDist n hn s M hM a u hu hAne hx
  calc
    cubeProbability {x | a + u ≤ radialCubeClippedStatistic n s M x} ≤
        cubeProbability {x | r ≤ cubeInfDist A x} := cubeProbability_mono hsubset
    _ ≤ Real.exp (-r ^ 2 / (2 * (↑(n + 1) : ℝ))) :=
      cubeProbability_cubeInfDist_ge_le (N := n + 1) (r := r) (by omega) A
        (by simpa [A] using hmed.1) (by simpa [r] using hr)
    _ = _ := by
      norm_num [r, Nat.cast_add, Nat.cast_one]

/-- The matching lower-deviation tail from any cube median. -/
theorem radialCube_lower_median_tail
    (n : ℕ) (hn : 0 < n) (s : ℝ) (M : NNReal) (hM : 1 ≤ M)
    (a : ℝ) (hmed : IsCubeMedian (radialCubeClippedStatistic n s M) a)
    {u : ℝ} (hu : 0 ≤ u)
    (hr : 2 * √((n + 1 : ℝ)) ≤
      u ^ 2 /
        (4 * (M : ℝ) ^ 2 * (Real.exp (4 * |s|) / (n + 1 : ℝ)))) :
    cubeProbability
        {x | radialCubeClippedStatistic n s M x + u ≤ a} ≤
      Real.exp (-
        (u ^ 2 /
          (4 * (M : ℝ) ^ 2 * (Real.exp (4 * |s|) / (n + 1 : ℝ)))) ^ 2 /
        (2 * (n + 1 : ℝ))) := by
  let A : Set (Fin (n + 1) → Bool) :=
    {y | a ≤ radialCubeClippedStatistic n s M y}
  let r : ℝ := u ^ 2 /
    (4 * (M : ℝ) ^ 2 * (Real.exp (4 * |s|) / (n + 1 : ℝ)))
  have hAne : A.Nonempty :=
    nonempty_of_half_le_cubeProbability (by simpa [A] using hmed.2)
  have hsubset : {x | radialCubeClippedStatistic n s M x + u ≤ a} ⊆
      {x | r ≤ cubeInfDist A x} := by
    intro x hx
    exact radialCube_lower_deviation_infDist n hn s M hM a u hu hAne hx
  calc
    cubeProbability {x | radialCubeClippedStatistic n s M x + u ≤ a} ≤
        cubeProbability {x | r ≤ cubeInfDist A x} := cubeProbability_mono hsubset
    _ ≤ Real.exp (-r ^ 2 / (2 * (↑(n + 1) : ℝ))) :=
      cubeProbability_cubeInfDist_ge_le (N := n + 1) (r := r) (by omega) A
        (by simpa [A] using hmed.2) (by simpa [r] using hr)
    _ = _ := by
      norm_num [r, Nat.cast_add, Nat.cast_one]

end Erdos522

end AmalgamatedModule97


/-! ===== amalgamated from Research.PowerClippedConcentration ===== -/

section AmalgamatedModule98


open Filter Topology

namespace Erdos522

noncomputable def powerClippedMedian (n : ℕ) (s : ℝ) : ℝ :=
  Classical.choose
    (exists_isCubeMedian (radialCubeClippedStatistic n s (radialPowerCutoff n)))

lemma powerClippedMedian_isMedian (n : ℕ) (s : ℝ) :
    IsCubeMedian (radialCubeClippedStatistic n s (radialPowerCutoff n))
      (powerClippedMedian n s) :=
  Classical.choose_spec
    (exists_isCubeMedian (radialCubeClippedStatistic n s (radialPowerCutoff n)))

lemma powerClipped_radius_eq (s : ℝ) (n : ℕ) :
    (((radialPowerCutoff n : ℝ)⁻¹) ^ 2 /
      (4 * (radialPowerCutoff n : ℝ) ^ 2 *
        (Real.exp (4 * |s|) / ((n : ℝ) + 1)))) =
      (radialPowerCutoff n : ℝ) ^ 12 /
        (4 * Real.exp (4 * |s|)) := by
  rw [← powerSmallBall_radius_eq s n]
  rw [show ((radialPowerCutoff n : ℝ) *
      Real.sqrt (4 * (Real.exp (4 * |s|) / ((n : ℝ) + 1)))) ^ 2 =
      4 * (radialPowerCutoff n : ℝ) ^ 2 *
        (Real.exp (4 * |s|) / ((n : ℝ) + 1)) by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    ring]

lemma eventually_powerClipped_radius_condition (s : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      2 * Real.sqrt ((n : ℝ) + 1) ≤
        ((radialPowerCutoff n : ℝ)⁻¹) ^ 2 /
          (4 * (radialPowerCutoff n : ℝ) ^ 2 *
            (Real.exp (4 * |s|) / ((n : ℝ) + 1))) := by
  filter_upwards [eventually_powerSmallBall_radius_condition s] with n hn
  rw [powerClipped_radius_eq]
  rw [powerSmallBall_radius_eq] at hn
  exact hn

/-- Upper clipped-log median tails at deviation `M_n⁻¹`. -/
theorem eventually_powerClipped_upper_median_tail (s : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      cubeProbability {x |
        powerClippedMedian n s + (radialPowerCutoff n : ℝ)⁻¹ ≤
          radialCubeClippedStatistic n s (radialPowerCutoff n) x} ≤
        powerSmallBallTail s n := by
  filter_upwards [eventually_ge_atTop 1,
    eventually_powerClipped_radius_condition s] with n hn hr
  have ht := radialCube_upper_median_tail n hn s (radialPowerCutoff n)
    (by exact_mod_cast one_le_radialPowerCutoff n)
    (powerClippedMedian n s) (powerClippedMedian_isMedian n s)
    (u := (radialPowerCutoff n : ℝ)⁻¹) (by positivity)
    (by simpa [Nat.cast_add, Nat.cast_one] using hr)
  calc
    cubeProbability {x |
        powerClippedMedian n s + (radialPowerCutoff n : ℝ)⁻¹ ≤
          radialCubeClippedStatistic n s (radialPowerCutoff n) x} ≤
      Real.exp (-
        (((radialPowerCutoff n : ℝ)⁻¹) ^ 2 /
          (4 * (radialPowerCutoff n : ℝ) ^ 2 *
            (Real.exp (4 * |s|) / ((n : ℝ) + 1)))) ^ 2 /
        (2 * ((n : ℝ) + 1))) := by
          simpa [Nat.cast_add, Nat.cast_one] using ht
    _ = powerSmallBallTail s n := by
      rw [powerClipped_radius_eq]
      unfold powerSmallBallTail
      congr 1
      convert powerSmallBall_tail_exponent_eq s n using 1 <;> ring

/-- Lower clipped-log median tails at deviation `M_n⁻¹`. -/
theorem eventually_powerClipped_lower_median_tail (s : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      cubeProbability {x |
        radialCubeClippedStatistic n s (radialPowerCutoff n) x +
          (radialPowerCutoff n : ℝ)⁻¹ ≤ powerClippedMedian n s} ≤
        powerSmallBallTail s n := by
  filter_upwards [eventually_ge_atTop 1,
    eventually_powerClipped_radius_condition s] with n hn hr
  have ht := radialCube_lower_median_tail n hn s (radialPowerCutoff n)
    (by exact_mod_cast one_le_radialPowerCutoff n)
    (powerClippedMedian n s) (powerClippedMedian_isMedian n s)
    (u := (radialPowerCutoff n : ℝ)⁻¹) (by positivity)
    (by simpa [Nat.cast_add, Nat.cast_one] using hr)
  calc
    cubeProbability {x |
        radialCubeClippedStatistic n s (radialPowerCutoff n) x +
          (radialPowerCutoff n : ℝ)⁻¹ ≤ powerClippedMedian n s} ≤
      Real.exp (-
        (((radialPowerCutoff n : ℝ)⁻¹) ^ 2 /
          (4 * (radialPowerCutoff n : ℝ) ^ 2 *
            (Real.exp (4 * |s|) / ((n : ℝ) + 1)))) ^ 2 /
        (2 * ((n : ℝ) + 1))) := by
          simpa [Nat.cast_add, Nat.cast_one] using ht
    _ = powerSmallBallTail s n := by
      rw [powerClipped_radius_eq]
      unfold powerSmallBallTail
      congr 1
      convert powerSmallBall_tail_exponent_eq s n using 1 <;> ring

lemma abs_radialCubeClippedStatistic_power_le_log
    (n : ℕ) (s : ℝ) (x : Fin (n + 1) → Bool) :
    |radialCubeClippedStatistic n s (radialPowerCutoff n) x| ≤
      Real.log (radialPowerCutoff n : ℝ) := by
  unfold radialCubeClippedStatistic angularStatistic
  have hM : (1 : NNReal) ≤ radialPowerCutoff n := by
    exact_mod_cast one_le_radialPowerCutoff n
  have hint : CircleIntegrable
      (fun z => clippedLog (radialPowerCutoff n)
        ((weightedVectorPolynomial
          (fun k : Fin (n + 1) => radialWeight n s k)
          (fun k => realRademacherSign (x k))).eval z)) 0 1 := by
    apply ContinuousOn.circleIntegrable (by norm_num)
    exact ((clippedLog_lipschitz _ hM).continuous.comp (by fun_prop)).continuousOn
  calc
    |Real.circleAverage
        (fun z => clippedLog (radialPowerCutoff n)
          ((weightedVectorPolynomial
            (fun k : Fin (n + 1) => radialWeight n s k)
            (fun k => realRademacherSign (x k))).eval z)) 0 1| ≤
      Real.circleAverage
        (fun z => |clippedLog (radialPowerCutoff n)
          ((weightedVectorPolynomial
            (fun k : Fin (n + 1) => radialWeight n s k)
            (fun k => realRademacherSign (x k))).eval z)|) 0 1 := by
        exact Real.abs_circleAverage_le_circleAverage_abs
    _ ≤ Real.circleAverage (fun _ : ℂ =>
        Real.log (radialPowerCutoff n : ℝ)) 0 1 := by
      apply Real.circleAverage_mono hint.abs
      · apply ContinuousOn.circleIntegrable (by norm_num)
        fun_prop
      · intro z hz
        exact abs_clippedLog_le_log _ hM _
    _ = Real.log (radialPowerCutoff n : ℝ) := Real.circleAverage_const _ _ _

lemma tendsto_log_powerCutoff_mul_tail (s : ℝ) :
    Tendsto (fun n : ℕ => Real.log (radialPowerCutoff n : ℝ) *
      powerSmallBallTail s n) atTop (𝓝 0) := by
  let c : ℝ := 1 / (32 * (Real.exp (4 * |s|)) ^ 2)
  have hc : 0 < c := by dsimp [c]; positivity
  have hbase : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hx : Tendsto (fun n : ℕ => (radialPowerCutoff n : ℝ) ^ 8)
      atTop atTop := by
    have hr := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp hbase
    apply Tendsto.congr' (Filter.Eventually.of_forall fun n => by
      change ((n : ℝ) + 1) ^ (1 / 2 : ℝ) =
        (radialPowerCutoff n : ℝ) ^ 8
      exact (radialPowerCutoff_pow_eight n).symm) hr
  have huRaw := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 c hc).comp hx
  have hu : Tendsto (fun n : ℕ => (radialPowerCutoff n : ℝ) ^ 8 *
      powerSmallBallTail s n) atTop (𝓝 0) := by
    apply Tendsto.congr' (Filter.Eventually.of_forall fun n => ?_) huRaw
    change ((radialPowerCutoff n : ℝ) ^ 8) ^ (1 : ℝ) *
      Real.exp (-c * (radialPowerCutoff n : ℝ) ^ 8) =
      (radialPowerCutoff n : ℝ) ^ 8 * powerSmallBallTail s n
    rw [Real.rpow_one]
    unfold powerSmallBallTail
    congr 2
    dsimp [c]
    ring
  apply squeeze_zero
  · intro n
    exact mul_nonneg (Real.log_nonneg (one_le_radialPowerCutoff n))
      (Real.exp_pos _).le
  · intro n
    have hlog := Real.log_le_self (show (0 : ℝ) ≤ radialPowerCutoff n by positivity)
    have hpow : (radialPowerCutoff n : ℝ) ≤
        (radialPowerCutoff n : ℝ) ^ 8 := by
      simpa using pow_le_pow_right₀ (one_le_radialPowerCutoff n)
        (show 1 ≤ 8 by norm_num)
    exact mul_le_mul_of_nonneg_right (hlog.trans hpow)
      (Real.exp_pos _).le
  · exact hu

lemma eventually_abs_powerClipped_mean_sub_median_le (s : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      |cubeAverage (radialCubeClippedStatistic n s (radialPowerCutoff n)) -
          powerClippedMedian n s| ≤
        (radialPowerCutoff n : ℝ)⁻¹ +
          4 * Real.log (radialPowerCutoff n : ℝ) * powerSmallBallTail s n := by
  filter_upwards [eventually_powerClipped_upper_median_tail s,
    eventually_powerClipped_lower_median_tail s] with n hu hl
  have h := abs_cubeAverage_sub_median_le
    (B := Real.log (radialPowerCutoff n : ℝ))
    (u := (radialPowerCutoff n : ℝ)⁻¹)
    (pu := powerSmallBallTail s n) (pl := powerSmallBallTail s n)
    (Real.log_nonneg (one_le_radialPowerCutoff n)) (by positivity)
    (abs_radialCubeClippedStatistic_power_le_log n s)
    (powerClippedMedian_isMedian n s) hu hl
  convert h using 1 <;> ring

/-- The clipped statistic's median and cube mean differ by `o(1)`, independently
of any logarithmic-integrability input. -/
theorem tendsto_powerClipped_mean_sub_median (s : ℝ) :
    Tendsto (fun n : ℕ =>
      cubeAverage (radialCubeClippedStatistic n s (radialPowerCutoff n)) -
        powerClippedMedian n s) atTop (𝓝 0) := by
  have hinv0 : Tendsto (fun n : ℕ => (radialPowerCutoff n : ℝ)⁻¹)
      atTop (𝓝 0) := by
    have h := tendsto_radialPowerCutoff_inv_pow 1 (by norm_num)
    simpa using h
  have hupper0 : Tendsto (fun n : ℕ =>
      (radialPowerCutoff n : ℝ)⁻¹ +
        4 * Real.log (radialPowerCutoff n : ℝ) * powerSmallBallTail s n)
      atTop (𝓝 0) := by
    convert hinv0.add ((tendsto_log_powerCutoff_mul_tail s).const_mul 4) using 1 <;> ring
  have habs : Tendsto (fun n : ℕ =>
      |cubeAverage (radialCubeClippedStatistic n s (radialPowerCutoff n)) -
        powerClippedMedian n s|) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)) hupper0
    · filter_upwards with n
      exact abs_nonneg _
    · exact eventually_abs_powerClipped_mean_sub_median_le s
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  simpa [Function.comp_def] using habs

end Erdos522

end AmalgamatedModule98


/-! ===== amalgamated from Research.ProcessClippedConcentration ===== -/

section AmalgamatedModule99


open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace Erdos522

noncomputable def processPowerClippedStatistic
    {Ω : Type*} (ξ : ℕ → Ω → Bool) (n : ℕ) (s : ℝ) (ω : Ω) : ℝ :=
  radialCubeClippedStatistic n s (radialPowerCutoff n)
    (prefixVector ξ (n + 1) ω)

lemma tendsto_powerClippedMedian_of_mean
    (s c : ℝ)
    (hmean : Tendsto (fun n => cubeAverage
      (radialCubeClippedStatistic n s (radialPowerCutoff n))) atTop (𝓝 c)) :
    Tendsto (fun n => powerClippedMedian n s) atTop (𝓝 c) := by
  have hdiff := tendsto_powerClipped_mean_sub_median s
  have h := hmean.sub hdiff
  convert h using 1 <;> ring

lemma summable_powerClipped_cube_deviations_of_mean
    (s c : ℝ)
    (hmean : Tendsto (fun n => cubeAverage
      (radialCubeClippedStatistic n s (radialPowerCutoff n))) atTop (𝓝 c))
    (j : ℕ) :
    Summable (fun n : ℕ => cubeProbability {x |
      (1 : ℝ) / ((j : ℝ) + 1) ≤
        |radialCubeClippedStatistic n s (radialPowerCutoff n) x - c|}) := by
  let ε : ℝ := (1 : ℝ) / ((j : ℝ) + 1)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hinv0 : Tendsto (fun n : ℕ => (radialPowerCutoff n : ℝ)⁻¹)
      atTop (𝓝 0) := by
    have h := tendsto_radialPowerCutoff_inv_pow 1 (by norm_num)
    simpa using h
  have hmed := tendsto_powerClippedMedian_of_mean s c hmean
  have hmedAbs : Tendsto (fun n : ℕ => |powerClippedMedian n s - c|)
      atTop (𝓝 0) := by
    have hd := hmed.sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => c) atTop (𝓝 c))
    have hd0 : Tendsto (fun n : ℕ => powerClippedMedian n s - c)
        atTop (𝓝 0) := by convert hd using 1 <;> ring
    apply (tendsto_zero_iff_abs_tendsto_zero _).mp hd0
  have hsmall0 : Tendsto (fun n : ℕ =>
      |powerClippedMedian n s - c| + (radialPowerCutoff n : ℝ)⁻¹)
      atTop (𝓝 0) := by
    convert hmedAbs.add hinv0 using 1 <;> ring
  have hsmall : ∀ᶠ n : ℕ in atTop,
      |powerClippedMedian n s - c| + (radialPowerCutoff n : ℝ)⁻¹ ≤ ε := by
    have hev := hsmall0.eventually (Metric.ball_mem_nhds 0 hε)
    filter_upwards [hev] with n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (add_nonneg (abs_nonneg _) (by positivity))] at hn
    exact hn.le
  apply ((summable_powerSmallBallTail s).mul_left 2).of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [hsmall, eventually_powerClipped_upper_median_tail s,
    eventually_powerClipped_lower_median_tail s] with n hclose hu hl
  rw [Real.norm_eq_abs, abs_of_nonneg (cubeProbability_nonneg' _)]
  let U : Set (Fin (n + 1) → Bool) := {x |
    powerClippedMedian n s + (radialPowerCutoff n : ℝ)⁻¹ ≤
      radialCubeClippedStatistic n s (radialPowerCutoff n) x}
  let L : Set (Fin (n + 1) → Bool) := {x |
    radialCubeClippedStatistic n s (radialPowerCutoff n) x +
      (radialPowerCutoff n : ℝ)⁻¹ ≤ powerClippedMedian n s}
  have hsub : {x |
      ε ≤ |radialCubeClippedStatistic n s (radialPowerCutoff n) x - c|} ⊆
      U ∪ L := by
    intro x hx
    change ε ≤ |radialCubeClippedStatistic n s (radialPowerCutoff n) x - c| at hx
    have hmup : powerClippedMedian n s - c ≤
        |powerClippedMedian n s - c| := le_abs_self _
    have hmlow : -|powerClippedMedian n s - c| ≤
        powerClippedMedian n s - c := neg_le_of_abs_le (le_refl _)
    rcases le_abs.mp hx with hx | hx
    · left
      change powerClippedMedian n s + (radialPowerCutoff n : ℝ)⁻¹ ≤
        radialCubeClippedStatistic n s (radialPowerCutoff n) x
      linarith
    · right
      change radialCubeClippedStatistic n s (radialPowerCutoff n) x +
        (radialPowerCutoff n : ℝ)⁻¹ ≤ powerClippedMedian n s
      linarith
  calc
    cubeProbability {x |
        (1 : ℝ) / ((j : ℝ) + 1) ≤
          |radialCubeClippedStatistic n s (radialPowerCutoff n) x - c|} =
        cubeProbability {x |
          ε ≤ |radialCubeClippedStatistic n s (radialPowerCutoff n) x - c|} := rfl
    _ ≤ cubeProbability (U ∪ L) := cubeProbability_mono hsub
    _ ≤ cubeProbability U + cubeProbability L := cubeProbability_union_le U L
    _ ≤ 2 * powerSmallBallTail s n := by
      dsimp [U, L]
      linarith

lemma measure_processPowerClipped_deviation_eq
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : ℕ → Ω → Bool) (hξ_meas : ∀ k, Measurable (ξ k))
    (hξ_indep : iIndepFun ξ μ)
    (hξ_fair : ∀ k, μ {ω | ξ k ω = true} = (1 : ENNReal) / 2)
    (s c : ℝ) (j n : ℕ) :
    μ {ω | (1 : ℝ) / ((j : ℝ) + 1) ≤
      |processPowerClippedStatistic ξ n s ω - c|} =
      ENNReal.ofReal (cubeProbability {x |
        (1 : ℝ) / ((j : ℝ) + 1) ≤
          |radialCubeClippedStatistic n s (radialPowerCutoff n) x - c|}) := by
  simpa [processPowerClippedStatistic] using
    measure_prefix_event_eq_ofReal_cubeProbability μ ξ hξ_meas hξ_indep hξ_fair
      (n + 1) {x | (1 : ℝ) / ((j : ℝ) + 1) ≤
        |radialCubeClippedStatistic n s (radialPowerCutoff n) x - c|}

/-- If the annealed clipped means have a limit `c`, finite-cube concentration
and prefix transfer upgrade this to quenched almost-sure convergence. -/
theorem ae_tendsto_processPowerClippedStatistic_of_mean
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : ℕ → Ω → Bool) (hξ_meas : ∀ k, Measurable (ξ k))
    (hξ_indep : iIndepFun ξ μ)
    (hξ_fair : ∀ k, μ {ω | ξ k ω = true} = (1 : ENNReal) / 2)
    (s c : ℝ)
    (hmean : Tendsto (fun n => cubeAverage
      (radialCubeClippedStatistic n s (radialPowerCutoff n))) atTop (𝓝 c)) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n => processPowerClippedStatistic ξ n s ω) atTop (𝓝 c) := by
  apply ae_tendsto_of_summable_reciprocal_deviations μ
    (fun n ω => processPowerClippedStatistic ξ n s ω) c
  intro j
  let p : ℕ → ℝ := fun n => cubeProbability {x |
    (1 : ℝ) / ((j : ℝ) + 1) ≤
      |radialCubeClippedStatistic n s (radialPowerCutoff n) x - c|}
  let q : ℕ → NNReal := fun n => ⟨p n, cubeProbability_nonneg' _⟩
  have hp : Summable p := summable_powerClipped_cube_deviations_of_mean s c hmean j
  have hq : Summable q := by
    apply NNReal.summable_coe.mp
    have hcoe : (fun n => (q n : ℝ)) = p := by funext n; rfl
    rw [hcoe]
    exact hp
  have heq : (fun n : ℕ => μ {ω | (1 : ℝ) / ((j : ℝ) + 1) ≤
      |processPowerClippedStatistic ξ n s ω - c|}) =
      fun n => (q n : ENNReal) := by
    funext n
    rw [measure_processPowerClipped_deviation_eq μ ξ hξ_meas hξ_indep hξ_fair]
    exact ENNReal.ofReal_eq_coe_nnreal (cubeProbability_nonneg' _)
  rw [heq]
  exact ENNReal.tsum_coe_ne_top_iff_summable.mpr hq

end Erdos522

end AmalgamatedModule99


/-! ===== amalgamated from Research.ProcessClippingRemoval ===== -/

section AmalgamatedModule100


open MeasureTheory

namespace Erdos522

noncomputable def processRadialWeightedSignPolynomial
    {Ω : Type*} (ξ : ℕ → Ω → Bool) (n : ℕ) (s : ℝ) (ω : Ω) : Polynomial ℂ :=
  radialWeightedSignPolynomial n s (prefixVector ξ (n + 1) ω)

noncomputable def processPolynomialLogSecondMoment
    {Ω : Type*} (ξ : ℕ → Ω → Bool) (n : ℕ) (s : ℝ) (ω : Ω) : ℝ :=
  polynomialLogSecondMoment (processRadialWeightedSignPolynomial ξ n s ω)

lemma processRadialWeightedSignPolynomial_eq_normalized
    {Ω : Type*} (ξ : ℕ → Ω → Bool) (n : ℕ) (s : ℝ) (ω : Ω) :
    processRadialWeightedSignPolynomial ξ n s ω =
      normalizedRadialPolynomial (littlewoodPolynomial ξ n ω) n s := by
  unfold processRadialWeightedSignPolynomial radialWeightedSignPolynomial
  simpa [prefixVector] using weightedVectorPolynomial_radial_signs_eq ξ n s ω

lemma littlewoodPolynomial_ne_zero' {Ω : Type*}
    (ξ : ℕ → Ω → Bool) (n : ℕ) (ω : Ω) :
    littlewoodPolynomial ξ n ω ≠ 0 := by
  intro hp
  have hcoeff := congrArg (fun p : Polynomial ℂ => p.coeff 0) hp
  have hne : (littlewoodPolynomial ξ n ω).coeff 0 ≠ 0 := by
    rw [show (littlewoodPolynomial ξ n ω).coeff 0 =
      rademacherSign (ξ 0 ω) by simp [littlewoodPolynomial]]
    cases ξ 0 ω <;> simp [rademacherSign]
  exact hne (by simpa [hp] using hcoeff)

lemma processRadialWeightedSignPolynomial_logMahlerMeasure
    {Ω : Type*} (ξ : ℕ → Ω → Bool) (n : ℕ) (s : ℝ) (ω : Ω) :
    (processRadialWeightedSignPolynomial ξ n s ω).logMahlerMeasure =
      centeredRadialLogMahler (littlewoodPolynomial ξ n ω) n s := by
  rw [processRadialWeightedSignPolynomial_eq_normalized]
  exact normalizedRadialPolynomial_logMahlerMeasure
    (littlewoodPolynomial_ne_zero' ξ n ω) n s

lemma processPowerClippedStatistic_eq
    {Ω : Type*} (ξ : ℕ → Ω → Bool) (n : ℕ) (s : ℝ) (ω : Ω) :
    processPowerClippedStatistic ξ n s ω =
      angularStatistic (clippedLog (radialPowerCutoff n))
        (processRadialWeightedSignPolynomial ξ n s ω) := by
  rfl

lemma processPowerSmallBallStatistic_eq
    {Ω : Type*} (ξ : ℕ → Ω → Bool) (n : ℕ) (s : ℝ) (ω : Ω) :
    processPowerSmallBallStatistic ξ n s ω =
      radialCubeSmallBallStatistic n s (radialPowerCutoff n)
        (prefixVector ξ (n + 1) ω) := rfl

lemma process_cutoffMass_le
    {Ω : Type*} (ξ : ℕ → Ω → Bool) (n : ℕ) (s : ℝ) (ω : Ω) :
    polynomialCutoffMass (processRadialWeightedSignPolynomial ξ n s ω)
        (radialPowerCutoff n) ≤
      processPowerSmallBallStatistic ξ n s ω +
        (radialPowerCutoff n : ℝ)⁻¹ ^ 2 := by
  have h := radialWeightedSignPolynomial_cutoffMass_le n s
    (prefixVector ξ (n + 1) ω) (radialPowerCutoff n)
    (radialPowerCutoff_pos n)
  rw [processPowerSmallBallStatistic_eq]
  simpa [processRadialWeightedSignPolynomial, one_div] using h

lemma processPolynomialLogSecondMoment_nonneg
    {Ω : Type*} (ξ : ℕ → Ω → Bool) (n : ℕ) (s : ℝ) (ω : Ω) :
    0 ≤ processPolynomialLogSecondMoment ξ n s ω := by
  unfold processPolynomialLogSecondMoment polynomialLogSecondMoment
  exact Real.circleAverage_nonneg_of_nonneg (fun z hz => sq_nonneg _)

/-- Exact clipping-removal estimate for a process prefix, with the cutoff mass
already replaced by the explicit low cutoff plus Parseval high tail. -/
theorem abs_centeredRadialLogMahler_sub_processPowerClippedStatistic_le
    {Ω : Type*} (ξ : ℕ → Ω → Bool) (n : ℕ) (s : ℝ) (ω : Ω)
    (hlog : MemLp
      (circleParameterFunction
        (fun z => rawLog ((processRadialWeightedSignPolynomial ξ n s ω).eval z))) 2
      circleParameterMeasure) :
    |centeredRadialLogMahler (littlewoodPolynomial ξ n ω) n s -
        processPowerClippedStatistic ξ n s ω| ≤
      Real.sqrt (processPolynomialLogSecondMoment ξ n s ω) *
        Real.sqrt (2 * (processPowerSmallBallStatistic ξ n s ω +
          (radialPowerCutoff n : ℝ)⁻¹ ^ 2)) +
      Real.log (radialPowerCutoff n : ℝ) *
        (processPowerSmallBallStatistic ξ n s ω +
          (radialPowerCutoff n : ℝ)⁻¹ ^ 2) := by
  let p := processRadialWeightedSignPolynomial ξ n s ω
  let M := radialPowerCutoff n
  let C := polynomialCutoffMass p M
  let D := processPowerSmallBallStatistic ξ n s ω + (M : ℝ)⁻¹ ^ 2
  have hM : (1 : NNReal) ≤ M := by exact_mod_cast one_le_radialPowerCutoff n
  have hbase := radialWeightedSignPolynomial_clipping_error_le n s
    (prefixVector ξ (n + 1) ω) M hM hlog
  have hCD : C ≤ D := by
    exact process_cutoffMass_le ξ n s ω
  have hC0 : 0 ≤ C := by
    unfold C polynomialCutoffMass
    apply Real.circleAverage_nonneg_of_nonneg
    intro z hz
    exact add_nonneg (smallBallCutoff_nonneg _ _) (highBallCutoff_nonneg _ _)
  have hD0 : 0 ≤ D := hC0.trans hCD
  have hY0 : 0 ≤ processPolynomialLogSecondMoment ξ n s ω :=
    processPolynomialLogSecondMoment_nonneg ξ n s ω
  change |p.logMahlerMeasure - angularStatistic (clippedLog M) p| ≤
      Real.sqrt (polynomialLogSecondMoment p) * Real.sqrt (2 * C) +
        Real.log (M : ℝ) * C at hbase
  rw [← processRadialWeightedSignPolynomial_logMahlerMeasure,
    processPowerClippedStatistic_eq]
  calc
    |p.logMahlerMeasure - angularStatistic (clippedLog M) p| ≤
      Real.sqrt (processPolynomialLogSecondMoment ξ n s ω) * Real.sqrt (2 * C) +
        Real.log (M : ℝ) * C := by
          simpa [p, M, C, processPolynomialLogSecondMoment] using hbase
    _ ≤ Real.sqrt (processPolynomialLogSecondMoment ξ n s ω) * Real.sqrt (2 * D) +
        Real.log (M : ℝ) * D := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left
          (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hCD (by norm_num)))
          (Real.sqrt_nonneg _)
      · exact mul_le_mul_of_nonneg_left hCD
          (Real.log_nonneg (one_le_radialPowerCutoff n))
    _ = _ := by rfl

end Erdos522

end AmalgamatedModule100


/-! ===== amalgamated from Research.ClippingEnvelope ===== -/

section AmalgamatedModule101


open Filter Topology Asymptotics

namespace Erdos522

noncomputable def processCutoffMassEnvelope (s : ℝ) (n : ℕ) : ℝ :=
  (powerSmallBallRateConstant s + 2) * (radialPowerCutoff n : ℝ)⁻¹ +
    4 * powerSmallBallTail s n + (radialPowerCutoff n : ℝ)⁻¹ ^ 2

noncomputable def processClippingErrorEnvelope (s : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (Real.sqrt (radialPowerCutoff n : ℝ)) *
      Real.sqrt (2 * processCutoffMassEnvelope s n) +
    Real.log (radialPowerCutoff n : ℝ) * processCutoffMassEnvelope s n

lemma powerSmallBallRateConstant_nonneg (s : ℝ) :
    0 ≤ powerSmallBallRateConstant s := by
  unfold powerSmallBallRateConstant
  have h2 := circularGaussianSecondNormMoment_nonneg
  have h4 := circularGaussianFourthNormMoment_nonneg
  positivity

lemma processCutoffMassEnvelope_nonneg (s : ℝ) (n : ℕ) :
    0 ≤ processCutoffMassEnvelope s n := by
  unfold processCutoffMassEnvelope
  exact add_nonneg
    (add_nonneg
      (mul_nonneg (by linarith [powerSmallBallRateConstant_nonneg s]) (by positivity))
      (mul_nonneg (by norm_num) (Real.exp_pos _).le))
    (sq_nonneg _)

lemma tendsto_powerCutoff_pow_eight_mul_tail (s : ℝ) :
    Tendsto (fun n : ℕ => (radialPowerCutoff n : ℝ) ^ 8 *
      powerSmallBallTail s n) atTop (𝓝 0) := by
  let c : ℝ := 1 / (32 * (Real.exp (4 * |s|)) ^ 2)
  have hc : 0 < c := by dsimp [c]; positivity
  have hbase : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hx : Tendsto (fun n : ℕ => (radialPowerCutoff n : ℝ) ^ 8)
      atTop atTop := by
    have hr := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp hbase
    apply Tendsto.congr' (Filter.Eventually.of_forall fun n => by
      change ((n : ℝ) + 1) ^ (1 / 2 : ℝ) =
        (radialPowerCutoff n : ℝ) ^ 8
      exact (radialPowerCutoff_pow_eight n).symm) hr
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 c hc).comp hx
  apply Tendsto.congr' (Filter.Eventually.of_forall fun n => ?_) h
  change ((radialPowerCutoff n : ℝ) ^ 8) ^ (1 : ℝ) *
    Real.exp (-c * (radialPowerCutoff n : ℝ) ^ 8) =
    (radialPowerCutoff n : ℝ) ^ 8 * powerSmallBallTail s n
  rw [Real.rpow_one]
  unfold powerSmallBallTail
  congr 2
  dsimp [c]
  ring

lemma tendsto_sqrt_powerCutoff_mul_tail (s : ℝ) :
    Tendsto (fun n : ℕ => Real.sqrt (radialPowerCutoff n : ℝ) *
      powerSmallBallTail s n) atTop (𝓝 0) := by
  apply squeeze_zero
  · intro n
    exact mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le
  · intro n
    have hsM : Real.sqrt (radialPowerCutoff n : ℝ) ≤
        (radialPowerCutoff n : ℝ) := by
      rw [Real.sqrt_le_iff]
      constructor
      · linarith [one_le_radialPowerCutoff n]
      · nlinarith [one_le_radialPowerCutoff n]
    have hM8 : (radialPowerCutoff n : ℝ) ≤
        (radialPowerCutoff n : ℝ) ^ 8 := by
      simpa using pow_le_pow_right₀ (one_le_radialPowerCutoff n)
        (show 1 ≤ 8 by norm_num)
    exact mul_le_mul_of_nonneg_right (hsM.trans hM8) (Real.exp_pos _).le
  · exact tendsto_powerCutoff_pow_eight_mul_tail s

lemma tendsto_sqrt_powerCutoff_atTop :
    Tendsto (fun n : ℕ => Real.sqrt (radialPowerCutoff n : ℝ)) atTop atTop := by
  have h := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
    tendsto_radialPowerCutoff_coe
  apply Tendsto.congr' (Filter.Eventually.of_forall fun n => ?_) h
  exact (Real.sqrt_eq_rpow _).symm

lemma tendsto_sqrt_powerCutoff_mul_massEnvelope (s : ℝ) :
    Tendsto (fun n : ℕ => Real.sqrt (radialPowerCutoff n : ℝ) *
      processCutoffMassEnvelope s n) atTop (𝓝 0) := by
  let R : ℕ → ℝ := fun n => Real.sqrt (radialPowerCutoff n : ℝ)
  have hR := tendsto_sqrt_powerCutoff_atTop
  have hRinv : Tendsto (fun n => (R n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hR
  have hRinv3 : Tendsto (fun n => (R n)⁻¹ ^ 3) atTop (𝓝 0) := by
    convert hRinv.pow 3 using 1 <;> simp [R]
  have htail := tendsto_sqrt_powerCutoff_mul_tail s
  have hsum :=
    (hRinv.const_mul (powerSmallBallRateConstant s + 2)).add
      ((htail.const_mul 4).add hRinv3)
  have hsum0 : Tendsto (fun n =>
      (powerSmallBallRateConstant s + 2) * (R n)⁻¹ +
        (4 * (Real.sqrt (radialPowerCutoff n : ℝ) * powerSmallBallTail s n) +
          (R n)⁻¹ ^ 3)) atTop (𝓝 0) := by
    convert hsum using 1 <;> ring
  apply Tendsto.congr' (Filter.Eventually.of_forall fun n => ?_) hsum0
  have hMpos : 0 < (radialPowerCutoff n : ℝ) :=
    lt_of_lt_of_le zero_lt_one (one_le_radialPowerCutoff n)
  have hRpos : 0 < R n := by
    dsimp [R]
    exact Real.sqrt_pos.2 hMpos
  have hRsq : R n ^ 2 = (radialPowerCutoff n : ℝ) := by
    dsimp [R]
    exact Real.sq_sqrt hMpos.le
  unfold processCutoffMassEnvelope
  rw [← hRsq, Real.sqrt_sq_eq_abs, abs_of_pos hRpos]
  field_simp [ne_of_gt hRpos]
  <;> ring

lemma tendsto_sqrt_part_clippingEnvelope (s : ℝ) :
    Tendsto (fun n : ℕ =>
      Real.sqrt (Real.sqrt (radialPowerCutoff n : ℝ)) *
        Real.sqrt (2 * processCutoffMassEnvelope s n)) atTop (𝓝 0) := by
  have hinside : Tendsto (fun n : ℕ =>
      Real.sqrt (radialPowerCutoff n : ℝ) *
        (2 * processCutoffMassEnvelope s n)) atTop (𝓝 0) := by
    convert (tendsto_sqrt_powerCutoff_mul_massEnvelope s).const_mul 2 using 1 <;> ring
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hinside
  simp only [Real.sqrt_zero] at hsqrt
  apply Tendsto.congr' (Filter.Eventually.of_forall fun n => ?_) hsqrt
  simp only [Function.comp_apply]
  rw [← Real.sqrt_mul (Real.sqrt_nonneg _)]

lemma tendsto_log_mul_powerCutoff_inv (k : ℕ) (hk : 0 < k) :
    Tendsto (fun n : ℕ => Real.log (radialPowerCutoff n : ℝ) *
      (radialPowerCutoff n : ℝ)⁻¹ ^ k) atTop (𝓝 0) := by
  have hr : (0 : ℝ) < k := by exact_mod_cast hk
  have h := (isLittleO_log_rpow_atTop hr).tendsto_div_nhds_zero.comp
    tendsto_radialPowerCutoff_coe
  apply Tendsto.congr' (Filter.Eventually.of_forall fun n => ?_) h
  simp only [Function.comp_apply, Real.rpow_natCast, div_eq_mul_inv, inv_pow]

lemma tendsto_log_mul_processCutoffMassEnvelope (s : ℝ) :
    Tendsto (fun n : ℕ => Real.log (radialPowerCutoff n : ℝ) *
      processCutoffMassEnvelope s n) atTop (𝓝 0) := by
  have h1 := (tendsto_log_mul_powerCutoff_inv 1 (by norm_num)).const_mul
    (powerSmallBallRateConstant s + 2)
  have ht := (tendsto_log_powerCutoff_mul_tail s).const_mul 4
  have h2 := tendsto_log_mul_powerCutoff_inv 2 (by norm_num)
  have hsum := h1.add (ht.add h2)
  have hsum0 : Tendsto (fun n =>
      (powerSmallBallRateConstant s + 2) *
          (Real.log (radialPowerCutoff n : ℝ) *
            (radialPowerCutoff n : ℝ)⁻¹ ^ 1) +
        (4 * (Real.log (radialPowerCutoff n : ℝ) * powerSmallBallTail s n) +
          Real.log (radialPowerCutoff n : ℝ) *
            (radialPowerCutoff n : ℝ)⁻¹ ^ 2)) atTop (𝓝 0) := by
    convert hsum using 1 <;> ring
  apply Tendsto.congr' (Filter.Eventually.of_forall fun n => ?_) hsum0
  unfold processCutoffMassEnvelope
  ring

/-- The explicit clipping-error envelope forced by the power-scale small-ball
rate and a `sqrt M_n` logarithmic second-moment bound vanishes. -/
theorem tendsto_processClippingErrorEnvelope (s : ℝ) :
    Tendsto (processClippingErrorEnvelope s) atTop (𝓝 0) := by
  unfold processClippingErrorEnvelope
  convert (tendsto_sqrt_part_clippingEnvelope s).add
    (tendsto_log_mul_processCutoffMassEnvelope s) using 1 <;> ring

lemma abs_centered_sub_clipped_le_envelope
    {Ω : Type*} (ξ : ℕ → Ω → Bool) (n : ℕ) (s : ℝ) (ω : Ω)
    (hlog : MeasureTheory.MemLp
      (circleParameterFunction
        (fun z => rawLog ((processRadialWeightedSignPolynomial ξ n s ω).eval z))) 2
      circleParameterMeasure)
    (hmoment : processPolynomialLogSecondMoment ξ n s ω ≤
      Real.sqrt (radialPowerCutoff n : ℝ))
    (hsmall : processPowerSmallBallStatistic ξ n s ω ≤
      (powerSmallBallRateConstant s + 2) *
          (radialPowerCutoff n : ℝ)⁻¹ + 4 * powerSmallBallTail s n) :
    |centeredRadialLogMahler (littlewoodPolynomial ξ n ω) n s -
        processPowerClippedStatistic ξ n s ω| ≤
      processClippingErrorEnvelope s n := by
  have hbase :=
    abs_centeredRadialLogMahler_sub_processPowerClippedStatistic_le
      ξ n s ω hlog
  have hD : processPowerSmallBallStatistic ξ n s ω +
      (radialPowerCutoff n : ℝ)⁻¹ ^ 2 ≤ processCutoffMassEnvelope s n := by
    unfold processCutoffMassEnvelope
    linarith
  have hY0 := processPolynomialLogSecondMoment_nonneg ξ n s ω
  have hD0 : 0 ≤ processPowerSmallBallStatistic ξ n s ω +
      (radialPowerCutoff n : ℝ)⁻¹ ^ 2 := by
    exact add_nonneg (processPowerSmallBallStatistic_nonneg ξ n s ω)
      (sq_nonneg _)
  calc
    |centeredRadialLogMahler (littlewoodPolynomial ξ n ω) n s -
        processPowerClippedStatistic ξ n s ω| ≤
      Real.sqrt (processPolynomialLogSecondMoment ξ n s ω) *
        Real.sqrt (2 * (processPowerSmallBallStatistic ξ n s ω +
          (radialPowerCutoff n : ℝ)⁻¹ ^ 2)) +
      Real.log (radialPowerCutoff n : ℝ) *
        (processPowerSmallBallStatistic ξ n s ω +
          (radialPowerCutoff n : ℝ)⁻¹ ^ 2) := hbase
    _ ≤ processClippingErrorEnvelope s n := by
      unfold processClippingErrorEnvelope
      apply add_le_add
      · exact mul_le_mul
          (Real.sqrt_le_sqrt hmoment)
          (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hD (by norm_num)))
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      · exact mul_le_mul_of_nonneg_left hD
          (Real.log_nonneg (one_le_radialPowerCutoff n))

end Erdos522

end AmalgamatedModule101


/-! ===== amalgamated from Research.UniformMomentPowerClipped ===== -/

section AmalgamatedModule102


open Filter Topology MeasureTheory

namespace Erdos522

noncomputable def annealedPowerCutoffMassEnvelope (s : ℝ) (n : ℕ) : ℝ :=
  powerSmallBallRateConstant s * (radialPowerCutoff n : ℝ)⁻¹ +
    (radialPowerCutoff n : ℝ)⁻¹ ^ 2

noncomputable def uniformMomentPowerError (C s : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt C * Real.sqrt (2 * annealedPowerCutoffMassEnvelope s n) +
    Real.log (radialPowerCutoff n : ℝ) * annealedPowerCutoffMassEnvelope s n

lemma annealedPowerCutoffMassEnvelope_nonneg (s : ℝ) (n : ℕ) :
    0 ≤ annealedPowerCutoffMassEnvelope s n := by
  unfold annealedPowerCutoffMassEnvelope
  exact add_nonneg
    (mul_nonneg (powerSmallBallRateConstant_nonneg s) (by positivity))
    (sq_nonneg _)

lemma tendsto_annealedPowerCutoffMassEnvelope (s : ℝ) :
    Tendsto (annealedPowerCutoffMassEnvelope s) atTop (𝓝 0) := by
  have h1 := tendsto_radialPowerCutoff_inv_pow 1 (by norm_num)
  have h2 := tendsto_radialPowerCutoff_inv_pow 2 (by norm_num)
  unfold annealedPowerCutoffMassEnvelope
  convert (h1.const_mul (powerSmallBallRateConstant s)).add h2 using 1 <;> ring

lemma tendsto_log_mul_annealedPowerCutoffMassEnvelope (s : ℝ) :
    Tendsto (fun n => Real.log (radialPowerCutoff n : ℝ) *
      annealedPowerCutoffMassEnvelope s n) atTop (𝓝 0) := by
  have h1 := (tendsto_log_mul_powerCutoff_inv 1 (by norm_num)).const_mul
    (powerSmallBallRateConstant s)
  have h2 := tendsto_log_mul_powerCutoff_inv 2 (by norm_num)
  have hsum := h1.add h2
  have hsum0 : Tendsto (fun n =>
      powerSmallBallRateConstant s *
          (Real.log (radialPowerCutoff n : ℝ) *
            (radialPowerCutoff n : ℝ)⁻¹) +
        Real.log (radialPowerCutoff n : ℝ) *
          (radialPowerCutoff n : ℝ)⁻¹ ^ 2) atTop (𝓝 0) := by
    convert hsum using 1
    · funext n
      ring
    · ring
  unfold annealedPowerCutoffMassEnvelope
  apply Tendsto.congr' (Filter.Eventually.of_forall fun n => by ring) hsum0

lemma tendsto_uniformMomentPowerError (C s : ℝ) (hC : 0 ≤ C) :
    Tendsto (uniformMomentPowerError C s) atTop (𝓝 0) := by
  have htwice : Tendsto (fun n => 2 * annealedPowerCutoffMassEnvelope s n)
      atTop (𝓝 0) := by
    convert (tendsto_annealedPowerCutoffMassEnvelope s).const_mul 2 using 1 <;> ring
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp htwice
  simp only [Real.sqrt_zero] at hsqrt
  have hsqrt0 : Tendsto (fun n =>
      Real.sqrt (2 * annealedPowerCutoffMassEnvelope s n)) atTop (𝓝 0) := by
    change Tendsto (fun n => Real.sqrt (2 * annealedPowerCutoffMassEnvelope s n))
      atTop (𝓝 0) at hsqrt
    exact hsqrt
  unfold uniformMomentPowerError
  convert (hsqrt0.const_mul (Real.sqrt C)).add
    (tendsto_log_mul_annealedPowerCutoffMassEnvelope s) using 1 <;> ring

lemma tendsto_annealedRaw_sub_powerClipped_of_uniform_moment
    (C s : ℝ) (hC : 0 ≤ C)
    (hlog : ∀ n (x : Fin (n + 1) → Bool),
      MemLp
        (circleParameterFunction
          (fun z => rawLog ((radialWeightedSignPolynomial n s x).eval z))) 2
        circleParameterMeasure)
    (hmoment : ∀ᶠ n : ℕ in atTop,
      cubeAverage (radialCubeLogSecondMoment n s) ≤ C) :
    Tendsto (fun n => annealedRawLogMean n s -
      cubeAverage (radialCubeClippedStatistic n s (radialPowerCutoff n)))
      atTop (𝓝 0) := by
  have hbound : ∀ᶠ n : ℕ in atTop,
      |annealedRawLogMean n s -
        cubeAverage (radialCubeClippedStatistic n s (radialPowerCutoff n))| ≤
      uniformMomentPowerError C s n := by
    filter_upwards [hmoment, eventually_ge_atTop 1] with n hY hn
    have hS := cubeAverage_radialCubeSmallBallStatistic_powerCutoff_le s n hn
    have hD : cubeAverage
          (radialCubeSmallBallStatistic n s (radialPowerCutoff n)) +
          (radialPowerCutoff n : ℝ)⁻¹ ^ 2 ≤
        annealedPowerCutoffMassEnvelope s n := by
      unfold annealedPowerCutoffMassEnvelope
      exact add_le_add hS (le_refl _)
    have hbase := abs_cubeAverage_raw_sub_clipped_le n s (radialPowerCutoff n)
      (by exact_mod_cast one_le_radialPowerCutoff n) (fun x => hlog n x)
    unfold annealedRawLogMean
    calc
      |cubeAverage (fun x : Fin (n + 1) → Bool =>
          (radialWeightedSignPolynomial n s x).logMahlerMeasure) -
          cubeAverage (radialCubeClippedStatistic n s (radialPowerCutoff n))| ≤
        Real.sqrt (cubeAverage (radialCubeLogSecondMoment n s)) *
          Real.sqrt (2 * (cubeAverage
            (radialCubeSmallBallStatistic n s (radialPowerCutoff n)) +
              (radialPowerCutoff n : ℝ)⁻¹ ^ 2)) +
        Real.log (radialPowerCutoff n : ℝ) *
          (cubeAverage (radialCubeSmallBallStatistic n s (radialPowerCutoff n)) +
            (radialPowerCutoff n : ℝ)⁻¹ ^ 2) := hbase
      _ ≤ uniformMomentPowerError C s n := by
        unfold uniformMomentPowerError
        apply add_le_add
        · exact mul_le_mul
            (Real.sqrt_le_sqrt hY)
            (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hD (by norm_num)))
            (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        · exact mul_le_mul_of_nonneg_left hD
            (Real.log_nonneg (one_le_radialPowerCutoff n))
  have habs : Tendsto (fun n => |annealedRawLogMean n s -
      cubeAverage (radialCubeClippedStatistic n s (radialPowerCutoff n))|)
      atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
      (tendsto_uniformMomentPowerError C s hC)
    · filter_upwards with n
      exact abs_nonneg _
    · exact hbound
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  simpa [Function.comp_def] using habs

/-- A single uniform annealed `L²` logarithmic-moment bound supplies the first
of F-065's two remaining inputs: all power-clipped means have one common
limit. -/
theorem exists_common_powerClipped_limit_of_uniform_moment
    (C : ℝ) (hC : 0 ≤ C)
    (hlog : ∀ n s (x : Fin (n + 1) → Bool),
      MemLp
        (circleParameterFunction
          (fun z => rawLog ((radialWeightedSignPolynomial n s x).eval z))) 2
        circleParameterMeasure)
    (hmoment : ∀ s : ℝ, ∀ᶠ n : ℕ in atTop,
      cubeAverage (radialCubeLogSecondMoment n s) ≤ C) :
    ∃ c : ℝ, ∀ s : ℝ,
      Tendsto (fun n => cubeAverage
        (radialCubeClippedStatistic n s (radialPowerCutoff n))) atTop (𝓝 c) := by
  obtain ⟨c, hraw, hgauss⟩ :=
    exists_common_limit_raw_and_gaussianClipped_of_uniform_moment
      C hC hlog hmoment
  refine ⟨c, fun s => ?_⟩
  have hdiff := tendsto_annealedRaw_sub_powerClipped_of_uniform_moment
    C s hC (fun n x => hlog n s x) (hmoment s)
  have h := (hraw s).sub hdiff
  convert h using 1 <;> ring

end Erdos522

end AmalgamatedModule102


/-! ===== amalgamated from Research.HighMomentBorel ===== -/

section AmalgamatedModule103


open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace Erdos522

lemma sqrt_radialPowerCutoff_pow_sixtyFour (n : ℕ) :
    (Real.sqrt (radialPowerCutoff n : ℝ)) ^ 64 =
      (radialPowerCutoff n : ℝ) ^ 32 := by
  have hsq : (Real.sqrt (radialPowerCutoff n : ℝ)) ^ 2 =
      (radialPowerCutoff n : ℝ) := Real.sq_sqrt (by positivity)
  calc
    (Real.sqrt (radialPowerCutoff n : ℝ)) ^ 64 =
        ((Real.sqrt (radialPowerCutoff n : ℝ)) ^ 2) ^ 32 := by ring
    _ = (radialPowerCutoff n : ℝ) ^ 32 := by rw [hsq]

lemma radialPowerCutoff_pow_thirtyTwo (n : ℕ) :
    (radialPowerCutoff n : ℝ) ^ 32 = ((n : ℝ) + 1) ^ 2 := by
  calc
    (radialPowerCutoff n : ℝ) ^ 32 =
        ((radialPowerCutoff n : ℝ) ^ 16) ^ 2 := by ring
    _ = ((n : ℝ) + 1) ^ 2 := by rw [radialPowerCutoff_pow_sixteen]

/-- Finite-cube Markov bound at exactly the coarse threshold needed for
clipping removal. -/
theorem cubeProbability_logSecondMoment_gt_sqrt_cutoff_le
    (K : ℝ) (hK : 0 ≤ K) (n : ℕ) (s : ℝ)
    (hmoment64 : cubeAverage (fun x : Fin (n + 1) → Bool =>
      (radialCubeLogSecondMoment n s x) ^ 64) ≤ K) :
    cubeProbability {x : Fin (n + 1) → Bool |
      Real.sqrt (radialPowerCutoff n : ℝ) < radialCubeLogSecondMoment n s x} ≤
      K / (((n : ℝ) + 1) ^ 2) := by
  have hMpos : 0 < (radialPowerCutoff n : ℝ) := by
    exact_mod_cast radialPowerCutoff_pos n
  have hM32 : 0 < (radialPowerCutoff n : ℝ) ^ 32 := pow_pos hMpos _
  have hpoint : ∀ x : Fin (n + 1) → Bool,
      (if x ∈ {x : Fin (n + 1) → Bool |
          Real.sqrt (radialPowerCutoff n : ℝ) <
            radialCubeLogSecondMoment n s x} then (1 : ℝ) else 0) ≤
        (radialCubeLogSecondMoment n s x) ^ 64 /
          (radialPowerCutoff n : ℝ) ^ 32 := by
    intro x
    by_cases hx : Real.sqrt (radialPowerCutoff n : ℝ) <
        radialCubeLogSecondMoment n s x
    · simp only [Set.mem_setOf_eq, hx, if_true]
      apply (le_div_iff₀ hM32).2
      rw [← sqrt_radialPowerCutoff_pow_sixtyFour]
      simpa using pow_le_pow_left₀ (Real.sqrt_nonneg _) (le_of_lt hx) 64
    · simp only [Set.mem_setOf_eq, hx, if_false]
      exact div_nonneg
        (pow_nonneg (radialCubeLogSecondMoment_nonneg n s x) 64) hM32.le
  calc
    cubeProbability {x : Fin (n + 1) → Bool |
        Real.sqrt (radialPowerCutoff n : ℝ) < radialCubeLogSecondMoment n s x} ≤
      cubeAverage (fun x => (radialCubeLogSecondMoment n s x) ^ 64 /
        (radialPowerCutoff n : ℝ) ^ 32) := by
      unfold cubeProbability
      exact cubeAverage_mono hpoint
    _ = cubeAverage (fun x => (radialCubeLogSecondMoment n s x) ^ 64) /
        (radialPowerCutoff n : ℝ) ^ 32 := by
      unfold cubeAverage
      rw [← Finset.sum_div]
      ring
    _ ≤ K / (radialPowerCutoff n : ℝ) ^ 32 :=
      div_le_div_of_nonneg_right hmoment64 hM32.le
    _ = K / (((n : ℝ) + 1) ^ 2) := by rw [radialPowerCutoff_pow_thirtyTwo]

lemma summable_inverse_nat_add_one_sq :
    Summable (fun n : ℕ => (((n : ℝ) + 1) ^ 2)⁻¹) := by
  have hbase : Summable (fun n : ℕ => (((n : ℝ) ^ (2 : ℝ)))⁻¹) :=
    Real.summable_nat_rpow_inv.mpr (by norm_num)
  have hshift := (summable_nat_add_iff 1).mpr hbase
  apply hshift.congr
  intro n
  simp only [Nat.cast_add, Nat.cast_one, Real.rpow_two]

lemma summable_logSecondMoment_bad_cubeProbability
    (K : ℝ) (hK : 0 ≤ K) (s : ℝ)
    (hmoment64 : ∀ n, cubeAverage (fun x : Fin (n + 1) → Bool =>
      (radialCubeLogSecondMoment n s x) ^ 64) ≤ K) :
    Summable (fun n => cubeProbability {x : Fin (n + 1) → Bool |
      Real.sqrt (radialPowerCutoff n : ℝ) < radialCubeLogSecondMoment n s x}) := by
  apply (summable_inverse_nat_add_one_sq.mul_left K).of_nonneg_of_le
  · intro n
    exact cubeProbability_nonneg' _
  · intro n
    simpa [div_eq_mul_inv] using
      cubeProbability_logSecondMoment_gt_sqrt_cutoff_le K hK n s (hmoment64 n)

lemma measure_processLogSecondMoment_bad_eq
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : ℕ → Ω → Bool) (hξ_meas : ∀ k, Measurable (ξ k))
    (hξ_indep : iIndepFun ξ μ)
    (hξ_fair : ∀ k, μ {ω | ξ k ω = true} = (1 : ENNReal) / 2)
    (s : ℝ) (n : ℕ) :
    μ {ω | Real.sqrt (radialPowerCutoff n : ℝ) <
      processPolynomialLogSecondMoment ξ n s ω} =
      ENNReal.ofReal (cubeProbability {x : Fin (n + 1) → Bool |
        Real.sqrt (radialPowerCutoff n : ℝ) < radialCubeLogSecondMoment n s x}) := by
  simpa [processPolynomialLogSecondMoment, processRadialWeightedSignPolynomial,
    radialCubeLogSecondMoment] using
    measure_prefix_event_eq_ofReal_cubeProbability μ ξ hξ_meas hξ_indep hξ_fair
      (n + 1) {x : Fin (n + 1) → Bool |
        Real.sqrt (radialPowerCutoff n : ℝ) < radialCubeLogSecondMoment n s x}

/-- A uniform 64th moment of the angular log second moment gives the almost-
sure coarse moment envelope required by F-064. -/
theorem ae_eventually_processLogSecondMoment_le_sqrt_cutoff
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : ℕ → Ω → Bool) (hξ_meas : ∀ k, Measurable (ξ k))
    (hξ_indep : iIndepFun ξ μ)
    (hξ_fair : ∀ k, μ {ω | ξ k ω = true} = (1 : ENNReal) / 2)
    (K : ℝ) (hK : 0 ≤ K) (s : ℝ)
    (hmoment64 : ∀ n, cubeAverage (fun x : Fin (n + 1) → Bool =>
      (radialCubeLogSecondMoment n s x) ^ 64) ≤ K) :
    ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop,
      processPolynomialLogSecondMoment ξ n s ω ≤
        Real.sqrt (radialPowerCutoff n : ℝ) := by
  let p : ℕ → ℝ := fun n => cubeProbability {x : Fin (n + 1) → Bool |
    Real.sqrt (radialPowerCutoff n : ℝ) < radialCubeLogSecondMoment n s x}
  let q : ℕ → NNReal := fun n => ⟨p n, cubeProbability_nonneg' _⟩
  have hp : Summable p :=
    summable_logSecondMoment_bad_cubeProbability K hK s hmoment64
  have hq : Summable q := by
    apply NNReal.summable_coe.mp
    have hcoe : (fun n => (q n : ℝ)) = p := by funext n; rfl
    rw [hcoe]
    exact hp
  have hsum : (∑' n : ℕ, μ {ω | Real.sqrt (radialPowerCutoff n : ℝ) <
      processPolynomialLogSecondMoment ξ n s ω}) ≠ ⊤ := by
    have heq : (fun n : ℕ => μ {ω | Real.sqrt (radialPowerCutoff n : ℝ) <
        processPolynomialLogSecondMoment ξ n s ω}) =
        fun n => (q n : ENNReal) := by
      funext n
      rw [measure_processLogSecondMoment_bad_eq μ ξ hξ_meas hξ_indep hξ_fair]
      exact ENNReal.ofReal_eq_coe_nnreal (cubeProbability_nonneg' _)
    rw [heq]
    exact ENNReal.tsum_coe_ne_top_iff_summable.mpr hq
  have hfinite := ae_eventually_notMem hsum
  filter_upwards [hfinite] with ω hω
  filter_upwards [hω] with n hn
  simpa only [Set.mem_setOf_eq, not_lt] using hn

end Erdos522

end AmalgamatedModule103


/-! ===== amalgamated from Research.ConditionalClippingRemoval ===== -/

section AmalgamatedModule104


open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace Erdos522

/-- The only missing input for almost-sure clipping removal is an eventual
sublinear logarithmic second-moment bound (together with the elementary `L²`
well-posedness of each logarithm). -/
theorem ae_tendsto_centered_sub_powerClipped_of_logSecondMoment
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : ℕ → Ω → Bool) (hξ_meas : ∀ k, Measurable (ξ k))
    (hξ_indep : iIndepFun ξ μ)
    (hξ_fair : ∀ k, μ {ω | ξ k ω = true} = (1 : ENNReal) / 2)
    (s : ℝ)
    (hlogMoment : ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop,
      MemLp
        (circleParameterFunction
          (fun z => rawLog ((processRadialWeightedSignPolynomial ξ n s ω).eval z))) 2
        circleParameterMeasure ∧
      processPolynomialLogSecondMoment ξ n s ω ≤
        Real.sqrt (radialPowerCutoff n : ℝ)) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ =>
        centeredRadialLogMahler (littlewoodPolynomial ξ n ω) n s -
          processPowerClippedStatistic ξ n s ω) atTop (𝓝 0) := by
  filter_upwards [hlogMoment,
    ae_eventually_processPowerSmallBallStatistic_le_explicit_rate
      μ ξ hξ_meas hξ_indep hξ_fair s] with ω hm hs
  have hbound : ∀ᶠ n : ℕ in atTop,
      |centeredRadialLogMahler (littlewoodPolynomial ξ n ω) n s -
          processPowerClippedStatistic ξ n s ω| ≤
        processClippingErrorEnvelope s n := by
    filter_upwards [hm, hs] with n hmn hsn
    exact abs_centered_sub_clipped_le_envelope ξ n s ω hmn.1 hmn.2 hsn
  have habs : Tendsto (fun n : ℕ =>
      |centeredRadialLogMahler (littlewoodPolynomial ξ n ω) n s -
        processPowerClippedStatistic ξ n s ω|) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
      (tendsto_processClippingErrorEnvelope s)
    · filter_upwards with n
      exact abs_nonneg _
    · exact hbound
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  simpa [Function.comp_def] using habs

end Erdos522

end AmalgamatedModule104


/-! ===== amalgamated from Research.LittlewoodReduction ===== -/

section AmalgamatedModule105


open scoped BigOperators Topology
open Filter MeasureTheory ProbabilityTheory

namespace Erdos522

lemma littlewoodPolynomial_coeff_zero {Ω : Type*}
    (ξ : ℕ → Ω → Bool) (n : ℕ) (ω : Ω) :
    (littlewoodPolynomial ξ n ω).coeff 0 = rademacherSign (ξ 0 ω) := by
  simp [littlewoodPolynomial]

lemma rademacherSign_ne_zero (b : Bool) : rademacherSign b ≠ 0 := by
  cases b <;> simp [rademacherSign]

lemma littlewoodPolynomial_natDegree {Ω : Type*}
    (ξ : ℕ → Ω → Bool) (n : ℕ) (ω : Ω) :
    (littlewoodPolynomial ξ n ω).natDegree = n := by
  apply le_antisymm
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    simp [littlewoodPolynomial]
    intro h
    omega
  · apply Polynomial.le_natDegree_of_ne_zero
    rw [show (littlewoodPolynomial ξ n ω).coeff n = rademacherSign (ξ n ω) by
      simp [littlewoodPolynomial]]
    exact rademacherSign_ne_zero _

lemma littlewoodPolynomial_leadingCoeff_norm {Ω : Type*}
    (ξ : ℕ → Ω → Bool) (n : ℕ) (ω : Ω) :
    ‖(littlewoodPolynomial ξ n ω).leadingCoeff‖ = 1 := by
  rw [← Polynomial.coeff_natDegree, littlewoodPolynomial_natDegree]
  rw [show (littlewoodPolynomial ξ n ω).coeff n = rademacherSign (ξ n ω) by
    simp [littlewoodPolynomial]]
  cases ξ n ω <;> simp [rademacherSign]

/-- The exact countable family of quenched centered-increment statements left
by F-008 for a nested Littlewood sequence. -/
def HasReciprocalCenteredIncrements {Ω : Type*}
    (ξ : ℕ → Ω → Bool) (ω : Ω) : Prop :=
  (∀ j : ℕ, Tendsto
    (fun m => centeredRadialLogMahler (littlewoodPolynomial ξ (m + 1) ω) (m + 1)
        ((1 : ℝ) / ((j : ℝ) + 1)) -
      centeredRadialLogMahler (littlewoodPolynomial ξ (m + 1) ω) (m + 1) 0)
    atTop (nhds 0)) ∧
  (∀ j : ℕ, Tendsto
    (fun m => centeredRadialLogMahler (littlewoodPolynomial ξ (m + 1) ω) (m + 1)
        (-((1 : ℝ) / ((j : ℝ) + 1))) -
      centeredRadialLogMahler (littlewoodPolynomial ξ (m + 1) ω) (m + 1) 0)
    atTop (nhds 0))

/-- A fully formal conditional closure of Erdős 522: the remaining countable
quenched log-Mahler increment property implies the exact target root ratio. -/
theorem erdos522_of_reciprocal_centered_increments
    {Ω : Type*} (ξ : ℕ → Ω → Bool) (ω : Ω)
    (h : HasReciprocalCenteredIncrements ξ ω) :
    Tendsto (fun n => (R ξ n ω : ℝ) / ((n : ℝ) / 2)) atTop (nhds 1) := by
  have hrShift : Tendsto
      (fun m => (polynomialClosedRootCount (littlewoodPolynomial ξ (m + 1) ω) : ℝ) /
        (m + 1 : ℝ)) atTop (nhds (1 / 2 : ℝ)) := by
    apply tendsto_closed_root_ratio_of_reciprocal_centered_increments
      (fun m => littlewoodPolynomial ξ (m + 1) ω)
    · intro m
      rw [littlewoodPolynomial_coeff_zero]
      exact rademacherSign_ne_zero _
    · intro m
      exact littlewoodPolynomial_leadingCoeff_norm _ _ _
    · exact h.1
    · exact h.2
  have hrShift' : Tendsto
      (fun m => (R ξ (m + 1) ω : ℝ) / (m + 1 : ℝ))
      atTop (nhds (1 / 2 : ℝ)) := by
    simpa [R, closedUnitRootCount, polynomialClosedRootCount] using hrShift
  have hr : Tendsto (fun n => (R ξ n ω : ℝ) / (n : ℝ))
      atTop (nhds (1 / 2 : ℝ)) :=
    (tendsto_add_atTop_iff_nat 1).mp (by simpa [Nat.add_comm] using hrShift')
  have htwo := hr.const_mul 2
  convert htwo using 1
  · funext n
    by_cases hn : n = 0
    · simp [hn]
    · field_simp
  · norm_num

end Erdos522

end AmalgamatedModule105


/-! ===== amalgamated from Research.ProbabilisticReduction ===== -/

section AmalgamatedModule106


open scoped BigOperators Topology
open Filter MeasureTheory ProbabilityTheory

namespace Erdos522

universe u

/-- The sole probabilistic assertion remaining after F-009 for a given
process: every fixed radial shift has the same almost-sure centered
log-Mahler limit. -/
def HasQuenchedCenteredLogMahlerLimit
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    (ξ : ℕ → Ω → Bool) : Prop :=
  ∃ c : ℝ, ∀ s : ℝ, ∀ᵐ ω ∂μ,
    Tendsto
      (fun n => centeredRadialLogMahler (littlewoodPolynomial ξ n ω) n s)
      atTop (nhds c)

/-- The quenched centered log-Mahler assertion implies exactly Erdős 522. -/
theorem erdos522_of_quenchedCenteredLogMahler
    {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : ℕ → Ω → Bool)
    (hξ_meas : ∀ k, Measurable (ξ k))
    (hξ_indep : iIndepFun ξ μ)
    (hξ_fair : ∀ k, μ {ω | ξ k ω = true} = (1 : ENNReal) / 2)
    (hQ : HasQuenchedCenteredLogMahlerLimit μ ξ) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n => (R ξ n ω : ℝ) / ((n : ℝ) / 2)) atTop (nhds 1) := by
  obtain ⟨c, hcenter⟩ := hQ
  have hzero := hcenter 0
  have hpos : ∀ j : ℕ, ∀ᵐ ω ∂μ, Tendsto
      (fun m => centeredRadialLogMahler (littlewoodPolynomial ξ (m + 1) ω) (m + 1)
          ((1 : ℝ) / ((j : ℝ) + 1)) -
        centeredRadialLogMahler (littlewoodPolynomial ξ (m + 1) ω) (m + 1) 0)
      atTop (nhds 0) := by
    intro j
    filter_upwards [hcenter ((1 : ℝ) / ((j : ℝ) + 1)), hzero] with ω hs h0
    have hs' : Tendsto
        (fun m => centeredRadialLogMahler (littlewoodPolynomial ξ (m + 1) ω) (m + 1)
          ((1 : ℝ) / ((j : ℝ) + 1))) atTop (nhds c) :=
      (tendsto_add_atTop_iff_nat 1).mpr hs
    have h0' : Tendsto
        (fun m => centeredRadialLogMahler (littlewoodPolynomial ξ (m + 1) ω) (m + 1) 0)
        atTop (nhds c) := (tendsto_add_atTop_iff_nat 1).mpr h0
    convert hs'.sub h0' using 1 <;> ring
  have hneg : ∀ j : ℕ, ∀ᵐ ω ∂μ, Tendsto
      (fun m => centeredRadialLogMahler (littlewoodPolynomial ξ (m + 1) ω) (m + 1)
          (-((1 : ℝ) / ((j : ℝ) + 1))) -
        centeredRadialLogMahler (littlewoodPolynomial ξ (m + 1) ω) (m + 1) 0)
      atTop (nhds 0) := by
    intro j
    filter_upwards [hcenter (-((1 : ℝ) / ((j : ℝ) + 1))), hzero] with ω hs h0
    have hs' : Tendsto
        (fun m => centeredRadialLogMahler (littlewoodPolynomial ξ (m + 1) ω) (m + 1)
          (-((1 : ℝ) / ((j : ℝ) + 1)))) atTop (nhds c) :=
      (tendsto_add_atTop_iff_nat 1).mpr hs
    have h0' : Tendsto
        (fun m => centeredRadialLogMahler (littlewoodPolynomial ξ (m + 1) ω) (m + 1) 0)
        atTop (nhds c) := (tendsto_add_atTop_iff_nat 1).mpr h0
    convert hs'.sub h0' using 1 <;> ring
  have hposAll : ∀ᵐ ω ∂μ, ∀ j : ℕ, Tendsto
      (fun m => centeredRadialLogMahler (littlewoodPolynomial ξ (m + 1) ω) (m + 1)
          ((1 : ℝ) / ((j : ℝ) + 1)) -
        centeredRadialLogMahler (littlewoodPolynomial ξ (m + 1) ω) (m + 1) 0)
      atTop (nhds 0) := MeasureTheory.ae_all_iff.mpr hpos
  have hnegAll : ∀ᵐ ω ∂μ, ∀ j : ℕ, Tendsto
      (fun m => centeredRadialLogMahler (littlewoodPolynomial ξ (m + 1) ω) (m + 1)
          (-((1 : ℝ) / ((j : ℝ) + 1))) -
        centeredRadialLogMahler (littlewoodPolynomial ξ (m + 1) ω) (m + 1) 0)
      atTop (nhds 0) := MeasureTheory.ae_all_iff.mpr hneg
  filter_upwards [hposAll, hnegAll] with ω hp hn
  exact erdos522_of_reciprocal_centered_increments ξ ω ⟨hp, hn⟩

end Erdos522

end AmalgamatedModule106


/-! ===== amalgamated from Research.PowerClippedFinalReduction ===== -/

section AmalgamatedModule107


open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace Erdos522

/-- Exact two-input analytic gate: convergence of the annealed power-clipped
means and a coarse quenched logarithmic moment bound imply the full quenched
centered log-Mahler assertion. -/
theorem hasQuenchedCenteredLogMahlerLimit_of_powerClipped
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : ℕ → Ω → Bool) (hξ_meas : ∀ k, Measurable (ξ k))
    (hξ_indep : iIndepFun ξ μ)
    (hξ_fair : ∀ k, μ {ω | ξ k ω = true} = (1 : ENNReal) / 2)
    (c : ℝ)
    (hmeans : ∀ s : ℝ,
      Tendsto (fun n => cubeAverage
        (radialCubeClippedStatistic n s (radialPowerCutoff n))) atTop (𝓝 c))
    (hlogMoments : ∀ s : ℝ, ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop,
      MemLp
        (circleParameterFunction
          (fun z => rawLog ((processRadialWeightedSignPolynomial ξ n s ω).eval z))) 2
        circleParameterMeasure ∧
      processPolynomialLogSecondMoment ξ n s ω ≤
        Real.sqrt (radialPowerCutoff n : ℝ)) :
    HasQuenchedCenteredLogMahlerLimit μ ξ := by
  refine ⟨c, fun s => ?_⟩
  filter_upwards [ae_tendsto_processPowerClippedStatistic_of_mean
      μ ξ hξ_meas hξ_indep hξ_fair s c (hmeans s),
    ae_tendsto_centered_sub_powerClipped_of_logSecondMoment
      μ ξ hξ_meas hξ_indep hξ_fair s (hlogMoments s)] with ω hclip hdiff
  have hsum := hdiff.add hclip
  convert hsum using 1 <;> ring

/-- Consequently the same two explicit analytic inputs imply Erdős 522. -/
theorem erdos522_of_powerClipped_means_and_logMoments
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : ℕ → Ω → Bool) (hξ_meas : ∀ k, Measurable (ξ k))
    (hξ_indep : iIndepFun ξ μ)
    (hξ_fair : ∀ k, μ {ω | ξ k ω = true} = (1 : ENNReal) / 2)
    (c : ℝ)
    (hmeans : ∀ s : ℝ,
      Tendsto (fun n => cubeAverage
        (radialCubeClippedStatistic n s (radialPowerCutoff n))) atTop (𝓝 c))
    (hlogMoments : ∀ s : ℝ, ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop,
      MemLp
        (circleParameterFunction
          (fun z => rawLog ((processRadialWeightedSignPolynomial ξ n s ω).eval z))) 2
        circleParameterMeasure ∧
      processPolynomialLogSecondMoment ξ n s ω ≤
        Real.sqrt (radialPowerCutoff n : ℝ)) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n => (R ξ n ω : ℝ) / ((n : ℝ) / 2)) atTop (𝓝 1) :=
  erdos522_of_quenchedCenteredLogMahler μ ξ hξ_meas hξ_indep hξ_fair
    (hasQuenchedCenteredLogMahlerLimit_of_powerClipped
      μ ξ hξ_meas hξ_indep hξ_fair c hmeans hlogMoments)

end Erdos522

end AmalgamatedModule107


/-! ===== amalgamated from Research.UniformMomentFinalReduction ===== -/

section AmalgamatedModule108


open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace Erdos522

/-- A fully explicit single analytic gate: two uniform annealed logarithmic
moment bounds (plus elementary per-polynomial `L²` well-posedness) imply the
complete Erdős 522 conclusion. -/
theorem erdos522_of_uniform_annealed_log_moments
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : ℕ → Ω → Bool) (hξ_meas : ∀ k, Measurable (ξ k))
    (hξ_indep : iIndepFun ξ μ)
    (hξ_fair : ∀ k, μ {ω | ξ k ω = true} = (1 : ENNReal) / 2)
    (C K : ℝ) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hlog : ∀ n s (x : Fin (n + 1) → Bool),
      MemLp
        (circleParameterFunction
          (fun z => rawLog ((radialWeightedSignPolynomial n s x).eval z))) 2
        circleParameterMeasure)
    (hsecond : ∀ s : ℝ, ∀ᶠ n : ℕ in atTop,
      cubeAverage (radialCubeLogSecondMoment n s) ≤ C)
    (hsixtyFour : ∀ n s, cubeAverage (fun x : Fin (n + 1) → Bool =>
      (radialCubeLogSecondMoment n s x) ^ 64) ≤ K) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n => (R ξ n ω : ℝ) / ((n : ℝ) / 2)) atTop (𝓝 1) := by
  obtain ⟨c, hmeans⟩ := exists_common_powerClipped_limit_of_uniform_moment
    C hC hlog hsecond
  have hlogMoments : ∀ s : ℝ, ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop,
      MemLp
        (circleParameterFunction
          (fun z => rawLog ((processRadialWeightedSignPolynomial ξ n s ω).eval z))) 2
        circleParameterMeasure ∧
      processPolynomialLogSecondMoment ξ n s ω ≤
        Real.sqrt (radialPowerCutoff n : ℝ) := by
    intro s
    filter_upwards [ae_eventually_processLogSecondMoment_le_sqrt_cutoff
      μ ξ hξ_meas hξ_indep hξ_fair K hK s (fun n => hsixtyFour n s)] with ω hm
    filter_upwards [hm] with n hmn
    constructor
    · simpa [processRadialWeightedSignPolynomial] using
        hlog n s (prefixVector ξ (n + 1) ω)
    · exact hmn
  exact erdos522_of_powerClipped_means_and_logMoments
    μ ξ hξ_meas hξ_indep hξ_fair c hmeans hlogMoments

end Erdos522

end AmalgamatedModule108


/-! ===== amalgamated from Research.NNSMomentFinalReduction ===== -/

section AmalgamatedModule109


open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace Erdos522

noncomputable def radialCubeLogPower128Moment
    (n : ℕ) (s : ℝ) (x : Fin (n + 1) → Bool) : ℝ :=
  Real.circleAverage
    (fun z => ((rawLog ((radialWeightedSignPolynomial n s x).eval z)) ^ 2) ^ 64)
    0 1

lemma radialCubeLogSecondMoment_pow_sixtyFour_le_power128Moment
    (n : ℕ) (s : ℝ) (x : Fin (n + 1) → Bool)
    (hlog : MemLp
      (circleParameterFunction
        (fun z => rawLog ((radialWeightedSignPolynomial n s x).eval z))) 2
      circleParameterMeasure)
    (hhigh : Integrable
      (fun θ => ((circleParameterFunction
        (fun z => rawLog ((radialWeightedSignPolynomial n s x).eval z)) θ) ^ 2) ^ 64)
      circleParameterMeasure) :
    (radialCubeLogSecondMoment n s x) ^ 64 ≤
      radialCubeLogPower128Moment n s x := by
  let f : ℝ → ℝ := fun θ =>
    (circleParameterFunction
      (fun z => rawLog ((radialWeightedSignPolynomial n s x).eval z)) θ) ^ 2
  have hf0 : ∀ᵐ θ ∂circleParameterMeasure, f θ ∈ Set.Ici (0 : ℝ) :=
    Filter.Eventually.of_forall fun θ => by
      change 0 ≤ f θ
      dsimp [f]
      exact sq_nonneg _
  have hfint : Integrable f circleParameterMeasure := by
    exact hlog.integrable_sq
  have hgint : Integrable ((fun y : ℝ => y ^ 64) ∘ f)
      circleParameterMeasure := by
    simpa [f, Function.comp_def] using hhigh
  have hj := (convexOn_pow 64 : ConvexOn ℝ (Set.Ici 0)
      (fun y : ℝ => y ^ 64)).map_integral_le
    (continuous_pow 64).continuousOn isClosed_Ici hf0 hfint hgint
  unfold radialCubeLogSecondMoment polynomialLogSecondMoment
    radialCubeLogPower128Moment
  rw [circleAverage_eq_integral_circleParameterMeasure,
    circleAverage_eq_integral_circleParameterMeasure]
  simpa [f, circleParameterFunction, Function.comp_def] using hj

lemma nonneg_le_one_add_pow_sixtyFour {y : ℝ} (hy : 0 ≤ y) :
    y ≤ 1 + y ^ 64 := by
  by_cases h : y ≤ 1
  · linarith [pow_nonneg hy 64]
  · have h1 : 1 ≤ y := le_of_not_ge h
    have hp : y ^ 1 ≤ y ^ 64 :=
      pow_le_pow_right₀ h1 (by norm_num : 1 ≤ 64)
    simpa using hp.trans (le_add_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1))

/-- NNS Corollary 1.2 at exponent 128 is now the sole deep input: its joint
cube--circle bound (with the associated integrability) implies Erdős 522. -/
theorem erdos522_of_uniform_joint_log_power128
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : ℕ → Ω → Bool) (hξ_meas : ∀ k, Measurable (ξ k))
    (hξ_indep : iIndepFun ξ μ)
    (hξ_fair : ∀ k, μ {ω | ξ k ω = true} = (1 : ENNReal) / 2)
    (K : ℝ) (hK : 0 ≤ K)
    (hlog : ∀ n s (x : Fin (n + 1) → Bool),
      MemLp
        (circleParameterFunction
          (fun z => rawLog ((radialWeightedSignPolynomial n s x).eval z))) 2
        circleParameterMeasure)
    (hhighInt : ∀ n s (x : Fin (n + 1) → Bool),
      Integrable
        (fun θ => ((circleParameterFunction
          (fun z => rawLog ((radialWeightedSignPolynomial n s x).eval z)) θ) ^ 2) ^ 64)
        circleParameterMeasure)
    (hjoint : ∀ n s,
      cubeAverage (radialCubeLogPower128Moment n s) ≤ K) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n => (R ξ n ω : ℝ) / ((n : ℝ) / 2)) atTop (𝓝 1) := by
  have h64 : ∀ n s, cubeAverage (fun x : Fin (n + 1) → Bool =>
      (radialCubeLogSecondMoment n s x) ^ 64) ≤ K := by
    intro n s
    exact (cubeAverage_mono fun x =>
      radialCubeLogSecondMoment_pow_sixtyFour_le_power128Moment
        n s x (hlog n s x) (hhighInt n s x)).trans (hjoint n s)
  have hsecond : ∀ s : ℝ, ∀ᶠ n : ℕ in atTop,
      cubeAverage (radialCubeLogSecondMoment n s) ≤ K + 1 := by
    intro s
    filter_upwards with n
    calc
      cubeAverage (radialCubeLogSecondMoment n s) ≤
          cubeAverage (fun x => 1 +
            (radialCubeLogSecondMoment n s x) ^ 64) := by
        apply cubeAverage_mono
        intro x
        exact nonneg_le_one_add_pow_sixtyFour
          (radialCubeLogSecondMoment_nonneg n s x)
      _ = 1 + cubeAverage (fun x =>
          (radialCubeLogSecondMoment n s x) ^ 64) := by
        unfold cubeAverage
        simp_rw [Finset.sum_add_distrib]
        simp [Fintype.card_bool, Fintype.card_fin]
        field_simp
        <;> ring
      _ ≤ K + 1 := by linarith [h64 n s]
  exact erdos522_of_uniform_annealed_log_moments
    μ ξ hξ_meas hξ_indep hξ_fair (K + 1) K (by linarith) hK
    hlog hsecond h64

end Erdos522

end AmalgamatedModule109


/-! ===== amalgamated from Research.AnnealedLogMomentBridge ===== -/

section AmalgamatedModule110


open MeasureTheory ProbabilityTheory

namespace Erdos522

lemma integrable_circleParameter_of_circleIntegrable
    (h : ℂ → ℝ) (hh : CircleIntegrable h 0 1) :
    Integrable (circleParameterFunction h) circleParameterMeasure := by
  have hi : IntervalIntegrable (fun θ : ℝ => h (circleMap 0 1 θ))
      volume 0 (2 * Real.pi) := (circleIntegrable_def h 0 1).mp hh
  have hbase : Integrable (fun θ : ℝ => h (circleMap 0 1 θ))
      (volume.restrict (Set.uIoc 0 (2 * Real.pi))) :=
    intervalIntegrable_iff.mp hi
  unfold circleParameterMeasure
  apply hbase.smul_measure
  rw [ENNReal.inv_ne_top]
  simp only [Measure.restrict_apply_univ, Real.volume_uIoc, sub_zero]
  exact ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))

lemma integral_norm_sq_radialAnnealedLaw_eq_one (n : ℕ) (s : ℝ) :
    (∫ z : ℂ, ‖z‖ ^ 2 ∂(radialAnnealedLaw n s : Measure ℂ)) = 1 := by
  have hang (x : Fin (n + 1) → Bool) : Integrable
      (circleParameterFunction
        (fun z => ‖(radialWeightedSignPolynomial n s x).eval z‖ ^ 2))
      circleParameterMeasure := by
    apply integrable_circleParameter_of_circleIntegrable
    apply ContinuousOn.circleIntegrable (by norm_num)
    fun_prop
  have hbridge := integral_radialAnnealedLaw_eq_cubeAverage_of_integrable
    n s (fun z : ℂ => ‖z‖ ^ 2) (by fun_prop) hang
  rw [hbridge]
  calc
    cubeAverage (radialCubeAngularStatistic n s (fun z : ℂ => ‖z‖ ^ 2)) =
        cubeAverage (fun _ : Fin (n + 1) → Bool => 1) := by
      apply congrArg cubeAverage
      funext x
      unfold radialCubeAngularStatistic angularStatistic
      exact weightedVectorPolynomial_circleAverage_sq_norm_eq_one
        (fun k : Fin (n + 1) => radialWeight n s k)
        (fun k => radialWeight_nonneg n s k)
        (sum_radialWeight_fin n s) x
    _ = 1 := cubeAverage_const 1

noncomputable def radialCubeLogPower256Moment
    (n : ℕ) (s : ℝ) (x : Fin (n + 1) → Bool) : ℝ :=
  Real.circleAverage
    (fun z => (absoluteRawLog ((radialWeightedSignPolynomial n s x).eval z)) ^ 256)
    0 1

lemma integral_absoluteRawLog_pow256_radialAnnealedLaw_eq
    (n : ℕ) (s : ℝ)
    (hhighInt : ∀ x : Fin (n + 1) → Bool,
      Integrable
        (fun θ => (absoluteRawLog
          ((radialWeightedSignPolynomial n s x).eval (circleMap 0 1 θ))) ^ 256)
        circleParameterMeasure) :
    (∫ z, (absoluteRawLog z) ^ 256
      ∂(radialAnnealedLaw n s : Measure ℂ)) =
      cubeAverage (radialCubeLogPower256Moment n s) := by
  have hang (x : Fin (n + 1) → Bool) : Integrable
      (circleParameterFunction
        (fun z => (absoluteRawLog ((radialWeightedSignPolynomial n s x).eval z)) ^ 256))
      circleParameterMeasure := by
    change Integrable
      (fun θ => (absoluteRawLog
        ((radialWeightedSignPolynomial n s x).eval (circleMap 0 1 θ))) ^ 256)
      circleParameterMeasure
    exact hhighInt x
  have h := integral_radialAnnealedLaw_eq_cubeAverage_of_integrable
    n s (fun z => (absoluteRawLog z) ^ 256)
    (measurable_absoluteRawLog.pow_const 256) hang
  rw [h]
  apply congrArg cubeAverage
  funext x
  rfl

lemma integral_absoluteRawLog_pow128_radialAnnealedLaw_eq
    (n : ℕ) (s : ℝ)
    (hhighInt : ∀ x : Fin (n + 1) → Bool,
      Integrable
        (fun θ => (absoluteRawLog
          ((radialWeightedSignPolynomial n s x).eval (circleMap 0 1 θ))) ^ 128)
        circleParameterMeasure) :
    (∫ z, (absoluteRawLog z) ^ 128
      ∂(radialAnnealedLaw n s : Measure ℂ)) =
      cubeAverage (radialCubeLogPower128Moment n s) := by
  have hang (x : Fin (n + 1) → Bool) : Integrable
      (circleParameterFunction
        (fun z => (absoluteRawLog ((radialWeightedSignPolynomial n s x).eval z)) ^ 128))
      circleParameterMeasure := by
    change Integrable
      (fun θ => (absoluteRawLog
        ((radialWeightedSignPolynomial n s x).eval (circleMap 0 1 θ))) ^ 128)
      circleParameterMeasure
    exact hhighInt x
  have h := integral_radialAnnealedLaw_eq_cubeAverage_of_integrable
    n s (fun z => (absoluteRawLog z) ^ 128)
    (measurable_absoluteRawLog.pow_const 128) hang
  have heq (z : ℂ) : (absoluteRawLog z) ^ 128 = ((rawLog z) ^ 2) ^ 64 := by
    unfold absoluteRawLog
    rw [show |rawLog z| ^ 128 = (|rawLog z| ^ 2) ^ 64 by ring, sq_abs]
  rw [h]
  apply congrArg cubeAverage
  funext x
  unfold radialCubeAngularStatistic angularStatistic radialCubeLogPower128Moment
  apply congrArg (fun f : ℂ → ℝ => Real.circleAverage f 0 1)
  funext z
  exact heq ((radialWeightedSignPolynomial n s x).eval z)

end Erdos522

end AmalgamatedModule110


/-! ===== amalgamated from Research.SymmetricClipLayer ===== -/

section AmalgamatedModule111


namespace Erdos522

noncomputable def realSymmetricClip (A y : ℝ) : ℝ :=
  max (-A) (min A y)

noncomputable def positivePart (y : ℝ) : ℝ := max y 0
noncomputable def negativePart (y : ℝ) : ℝ := max (-y) 0

lemma positivePart_nonneg (y : ℝ) : 0 ≤ positivePart y := le_max_right _ _
lemma negativePart_nonneg (y : ℝ) : 0 ≤ negativePart y := le_max_right _ _

lemma positivePart_sub_negativePart (y : ℝ) :
    positivePart y - negativePart y = y := by
  unfold positivePart negativePart
  rcases le_total y 0 with hy | hy <;>
    simp [max_eq_left, max_eq_right, hy] <;> linarith

lemma realSymmetricClip_of_nonneg {A y : ℝ} (hA : 0 ≤ A) (hy : 0 ≤ y) :
    realSymmetricClip A y = min A y := by
  unfold realSymmetricClip
  rw [max_eq_right]
  exact le_trans (neg_nonpos.mpr hA) (le_min hA hy)

lemma realSymmetricClip_of_nonpos {A y : ℝ} (hA : 0 ≤ A) (hy : y ≤ 0) :
    realSymmetricClip A y = max (-A) y := by
  unfold realSymmetricClip
  rw [min_eq_right]
  exact hy.trans hA

lemma positivePart_symmClip_of_nonneg {A y : ℝ} (hA : 0 ≤ A) (hy : 0 ≤ y) :
    positivePart (realSymmetricClip A y) = min A y := by
  rw [realSymmetricClip_of_nonneg hA hy]
  unfold positivePart
  rw [max_eq_left]
  exact le_min hA hy

lemma negativePart_symmClip_of_nonneg {A y : ℝ} (hA : 0 ≤ A) (hy : 0 ≤ y) :
    negativePart (realSymmetricClip A y) = 0 := by
  rw [realSymmetricClip_of_nonneg hA hy]
  unfold negativePart
  rw [max_eq_right]
  exact neg_nonpos.mpr (le_min hA hy)

lemma positivePart_symmClip_of_nonpos {A y : ℝ} (hA : 0 ≤ A) (hy : y ≤ 0) :
    positivePart (realSymmetricClip A y) = 0 := by
  rw [realSymmetricClip_of_nonpos hA hy]
  unfold positivePart
  rw [max_eq_right]
  exact max_le (neg_nonpos.mpr hA) hy

lemma negativePart_symmClip_of_nonpos {A y : ℝ} (hA : 0 ≤ A) (hy : y ≤ 0) :
    negativePart (realSymmetricClip A y) = min A (-y) := by
  rw [realSymmetricClip_of_nonpos hA hy]
  unfold negativePart
  have h : -(max (-A) y) = min A (-y) := by
    rcases le_total (-A) y with hle | hle
    · rw [max_eq_right hle, min_eq_right]
      linarith
    · rw [max_eq_left hle, min_eq_left] <;> linarith
  rw [h, max_eq_left]
  exact le_min hA (neg_nonneg.mpr hy)

lemma min_mono_right {A B y : ℝ} (hAB : A ≤ B) :
    min A y ≤ min B y := min_le_min_right y hAB

lemma positivePart_symmClip_mono {A B y : ℝ}
    (hA : 0 ≤ A) (hAB : A ≤ B) :
    positivePart (realSymmetricClip A y) ≤
      positivePart (realSymmetricClip B y) := by
  have hB : 0 ≤ B := hA.trans hAB
  by_cases hy : 0 ≤ y
  · rw [positivePart_symmClip_of_nonneg hA hy,
      positivePart_symmClip_of_nonneg hB hy]
    exact min_mono_right hAB
  · have hy' : y ≤ 0 := le_of_not_ge hy
    rw [positivePart_symmClip_of_nonpos hA hy',
      positivePart_symmClip_of_nonpos hB hy']

lemma negativePart_symmClip_mono {A B y : ℝ}
    (hA : 0 ≤ A) (hAB : A ≤ B) :
    negativePart (realSymmetricClip A y) ≤
      negativePart (realSymmetricClip B y) := by
  have hB : 0 ≤ B := hA.trans hAB
  by_cases hy : 0 ≤ y
  · rw [negativePart_symmClip_of_nonneg hA hy,
      negativePart_symmClip_of_nonneg hB hy]
  · have hy' : y ≤ 0 := le_of_not_ge hy
    rw [negativePart_symmClip_of_nonpos hA hy',
      negativePart_symmClip_of_nonpos hB hy']
    exact min_mono_right hAB

lemma positivePart_symmClip_layer {A B y t : ℝ}
    (hA : 0 ≤ A) (hAB : A ≤ B) (ht0 : 0 ≤ t)
    (ht : t < positivePart (realSymmetricClip B y) -
      positivePart (realSymmetricClip A y)) :
    A + t < y := by
  have hB : 0 ≤ B := hA.trans hAB
  by_cases hy : 0 ≤ y
  · rw [positivePart_symmClip_of_nonneg hB hy,
      positivePart_symmClip_of_nonneg hA hy] at ht
    have hmin : min B y ≤ y := min_le_right _ _
    by_cases hyA : y ≤ A
    · rw [min_eq_right hyA, min_eq_right (hyA.trans hAB)] at ht
      linarith
    · rw [min_eq_left (le_of_not_ge hyA)] at ht
      linarith
  · have hy' : y ≤ 0 := le_of_not_ge hy
    rw [positivePart_symmClip_of_nonpos hB hy',
      positivePart_symmClip_of_nonpos hA hy'] at ht
    linarith

lemma negativePart_symmClip_layer {A B y t : ℝ}
    (hA : 0 ≤ A) (hAB : A ≤ B) (ht0 : 0 ≤ t)
    (ht : t < negativePart (realSymmetricClip B y) -
      negativePart (realSymmetricClip A y)) :
    y < -(A + t) := by
  have hB : 0 ≤ B := hA.trans hAB
  by_cases hy : 0 ≤ y
  · rw [negativePart_symmClip_of_nonneg hB hy,
      negativePart_symmClip_of_nonneg hA hy] at ht
    linarith
  · have hy' : y ≤ 0 := le_of_not_ge hy
    rw [negativePart_symmClip_of_nonpos hB hy',
      negativePart_symmClip_of_nonpos hA hy'] at ht
    by_cases hyA : -y ≤ A
    · rw [min_eq_right hyA, min_eq_right (hyA.trans hAB)] at ht
      linarith
    · have hmin : min B (-y) ≤ -y := min_le_right _ _
      rw [min_eq_left (le_of_not_ge hyA)] at ht
      linarith

lemma positivePart_symmClip_layer_le {A B y t : ℝ}
    (hA : 0 ≤ A) (hAB : A ≤ B) (ht0 : 0 < t)
    (ht : t ≤ positivePart (realSymmetricClip B y) -
      positivePart (realSymmetricClip A y)) :
    A + t ≤ y := by
  have hB : 0 ≤ B := hA.trans hAB
  by_cases hy : 0 ≤ y
  · rw [positivePart_symmClip_of_nonneg hB hy,
      positivePart_symmClip_of_nonneg hA hy] at ht
    have hmin : min B y ≤ y := min_le_right _ _
    by_cases hyA : y ≤ A
    · rw [min_eq_right hyA, min_eq_right (hyA.trans hAB)] at ht
      linarith
    · rw [min_eq_left (le_of_not_ge hyA)] at ht
      linarith
  · have hy' : y ≤ 0 := le_of_not_ge hy
    rw [positivePart_symmClip_of_nonpos hB hy',
      positivePart_symmClip_of_nonpos hA hy'] at ht
    linarith

lemma negativePart_symmClip_layer_le {A B y t : ℝ}
    (hA : 0 ≤ A) (hAB : A ≤ B) (ht0 : 0 < t)
    (ht : t ≤ negativePart (realSymmetricClip B y) -
      negativePart (realSymmetricClip A y)) :
    y ≤ -(A + t) := by
  have hB : 0 ≤ B := hA.trans hAB
  by_cases hy : 0 ≤ y
  · rw [negativePart_symmClip_of_nonneg hB hy,
      negativePart_symmClip_of_nonneg hA hy] at ht
    linarith
  · have hy' : y ≤ 0 := le_of_not_ge hy
    rw [negativePart_symmClip_of_nonpos hB hy',
      negativePart_symmClip_of_nonpos hA hy'] at ht
    by_cases hyA : -y ≤ A
    · rw [min_eq_right hyA, min_eq_right (hyA.trans hAB)] at ht
      linarith
    · have hmin : min B (-y) ≤ -y := min_le_right _ _
      rw [min_eq_left (le_of_not_ge hyA)] at ht
      linarith

lemma positivePart_symmClip_diff_le {A B y : ℝ}
    (hA : 0 ≤ A) (hAB : A ≤ B) :
    positivePart (realSymmetricClip B y) -
      positivePart (realSymmetricClip A y) ≤ B - A := by
  have hB : 0 ≤ B := hA.trans hAB
  by_cases hy : 0 ≤ y
  · rw [positivePart_symmClip_of_nonneg hB hy,
      positivePart_symmClip_of_nonneg hA hy]
    by_cases hAy : A ≤ y
    · rw [min_eq_left hAy]
      linarith [min_le_left B y]
    · rw [min_eq_right (le_of_not_ge hAy)]
      linarith [min_le_right B y]
  · have hy' : y ≤ 0 := le_of_not_ge hy
    rw [positivePart_symmClip_of_nonpos hB hy',
      positivePart_symmClip_of_nonpos hA hy']
    linarith

lemma negativePart_symmClip_diff_le {A B y : ℝ}
    (hA : 0 ≤ A) (hAB : A ≤ B) :
    negativePart (realSymmetricClip B y) -
      negativePart (realSymmetricClip A y) ≤ B - A := by
  have hB : 0 ≤ B := hA.trans hAB
  by_cases hy : 0 ≤ y
  · rw [negativePart_symmClip_of_nonneg hB hy,
      negativePart_symmClip_of_nonneg hA hy]
    linarith
  · have hy' : y ≤ 0 := le_of_not_ge hy
    rw [negativePart_symmClip_of_nonpos hB hy',
      negativePart_symmClip_of_nonpos hA hy']
    by_cases hAy : A ≤ -y
    · rw [min_eq_left hAy]
      linarith [min_le_left B (-y)]
    · rw [min_eq_right (le_of_not_ge hAy)]
      linarith [min_le_right B (-y)]

lemma abs_symmClip_sub_le_parts {A B y : ℝ}
    (hA : 0 ≤ A) (hAB : A ≤ B) :
    |realSymmetricClip B y - realSymmetricClip A y| ≤
      (positivePart (realSymmetricClip B y) -
        positivePart (realSymmetricClip A y)) +
      (negativePart (realSymmetricClip B y) -
        negativePart (realSymmetricClip A y)) := by
  have hB : 0 ≤ B := hA.trans hAB
  by_cases hy : 0 ≤ y
  · rw [positivePart_symmClip_of_nonneg hB hy,
      positivePart_symmClip_of_nonneg hA hy,
      negativePart_symmClip_of_nonneg hB hy,
      negativePart_symmClip_of_nonneg hA hy,
      realSymmetricClip_of_nonneg hB hy,
      realSymmetricClip_of_nonneg hA hy]
    rw [abs_of_nonneg (sub_nonneg.mpr (min_mono_right hAB))]
    linarith
  · have hy' : y ≤ 0 := le_of_not_ge hy
    rw [positivePart_symmClip_of_nonpos hB hy',
      positivePart_symmClip_of_nonpos hA hy',
      negativePart_symmClip_of_nonpos hB hy',
      negativePart_symmClip_of_nonpos hA hy']
    have hcB := realSymmetricClip_of_nonpos hB hy'
    have hcA := realSymmetricClip_of_nonpos hA hy'
    have hn := min_mono_right (y := -y) hAB
    have hidB : realSymmetricClip B y = -min B (-y) := by
      rw [hcB]
      rcases le_total (-B) y with hle | hle
      · rw [max_eq_right hle, min_eq_right] <;> linarith
      · rw [max_eq_left hle, min_eq_left] <;> linarith
    have hidA : realSymmetricClip A y = -min A (-y) := by
      rw [hcA]
      rcases le_total (-A) y with hle | hle
      · rw [max_eq_right hle, min_eq_right] <;> linarith
      · rw [max_eq_left hle, min_eq_left] <;> linarith
    rw [hidB, hidA, abs_of_nonpos (by linarith)]
    linarith

end Erdos522

end AmalgamatedModule111


/-! ===== amalgamated from Research.ClippedLogLayers ===== -/

section AmalgamatedModule112


namespace Erdos522

noncomputable def clippedPositivePart (M : NNReal) (z : ℂ) : ℝ :=
  positivePart (clippedLog M z)

noncomputable def clippedNegativePart (M : NNReal) (z : ℂ) : ℝ :=
  negativePart (clippedLog M z)

lemma clippedLog_eq_realSymmetricClip (M : NNReal) (hM : 1 ≤ M)
    {z : ℂ} (hz : z ≠ 0) :
    clippedLog M z = realSymmetricClip (Real.log (M : ℝ)) (Real.log ‖z‖) := by
  have hMp : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one (by exact_mod_cast hM)
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hinv : 0 < 1 / (M : ℝ) := one_div_pos.mpr hMp
  have hlogM : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg (by exact_mod_cast hM)
  by_cases hlow : ‖z‖ ≤ 1 / (M : ℝ)
  · have hloglow : Real.log ‖z‖ ≤ -Real.log (M : ℝ) := by
      have h := (Real.strictMonoOn_log.le_iff_le hr hinv).mpr hlow
      rw [one_div, Real.log_inv] at h
      exact h
    have hinvM : 1 / (M : ℝ) ≤ (M : ℝ) := by
      apply (div_le_iff₀ hMp).2
      nlinarith [show (1 : ℝ) ≤ M by exact_mod_cast hM]
    unfold clippedLog clippedRadius realSymmetricClip
    rw [max_eq_left hlow, min_eq_right hinvM, one_div, Real.log_inv,
      min_eq_right (hloglow.trans (neg_le_self hlogM)), max_eq_left hloglow]
  · have hlow' : 1 / (M : ℝ) ≤ ‖z‖ := le_of_not_ge hlow
    by_cases hupp : ‖z‖ ≤ (M : ℝ)
    · rw [clippedLog_eq_log_norm M hlow' hupp]
      unfold realSymmetricClip
      have hloLog : -Real.log (M : ℝ) ≤ Real.log ‖z‖ := by
        have h := (Real.strictMonoOn_log.le_iff_le hinv hr).mpr hlow'
        rw [one_div, Real.log_inv] at h
        exact h
      have hupLog : Real.log ‖z‖ ≤ Real.log (M : ℝ) :=
        (Real.strictMonoOn_log.le_iff_le hr hMp).mpr hupp
      rw [min_eq_right hupLog, max_eq_right hloLog]
    · have hupp' : (M : ℝ) ≤ ‖z‖ := le_of_not_ge hupp
      have hlogupp : Real.log (M : ℝ) ≤ Real.log ‖z‖ :=
        (Real.strictMonoOn_log.le_iff_le hMp hr).mpr hupp'
      unfold clippedLog clippedRadius realSymmetricClip
      rw [max_eq_right hlow', min_eq_left hupp', min_eq_left hlogupp,
        max_eq_right]
      exact neg_le_self hlogM

lemma clippedLog_zero (M : NNReal) (hM : 1 ≤ M) :
    clippedLog M 0 = -Real.log (M : ℝ) := by
  have hMp : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one (by exact_mod_cast hM)
  have hinvM : 1 / (M : ℝ) ≤ (M : ℝ) := by
    apply (div_le_iff₀ hMp).2
    nlinarith [show (1 : ℝ) ≤ M by exact_mod_cast hM]
  unfold clippedLog clippedRadius
  simp only [norm_zero]
  rw [max_eq_left (by positivity : (0 : ℝ) ≤ 1 / (M : ℝ)),
    min_eq_right hinvM, one_div, Real.log_inv]

lemma clippedPositivePart_zero (M : NNReal) (hM : 1 ≤ M) :
    clippedPositivePart M 0 = 0 := by
  rw [clippedPositivePart, clippedLog_zero M hM]
  unfold positivePart
  rw [max_eq_right]
  exact neg_nonpos.mpr (Real.log_nonneg (by exact_mod_cast hM))

lemma clippedNegativePart_zero (M : NNReal) (hM : 1 ≤ M) :
    clippedNegativePart M 0 = Real.log (M : ℝ) := by
  rw [clippedNegativePart, clippedLog_zero M hM]
  unfold negativePart
  rw [neg_neg, max_eq_left]
  exact Real.log_nonneg (by exact_mod_cast hM)

lemma log_cutoff_mono {K M : NNReal} (hK : 1 ≤ K) (hKM : K ≤ M) :
    Real.log (K : ℝ) ≤ Real.log (M : ℝ) := by
  have hKp : (0 : ℝ) < K := lt_of_lt_of_le zero_lt_one (by exact_mod_cast hK)
  have hMp : (0 : ℝ) < M := lt_of_lt_of_le hKp (by exact_mod_cast hKM)
  exact (Real.strictMonoOn_log.le_iff_le hKp hMp).mpr (by exact_mod_cast hKM)

lemma clippedPositivePart_mono {K M : NNReal} (hK : 1 ≤ K) (hKM : K ≤ M)
    (z : ℂ) : clippedPositivePart K z ≤ clippedPositivePart M z := by
  by_cases hz : z = 0
  · subst z
    rw [clippedPositivePart_zero K hK,
      clippedPositivePart_zero M (hK.trans hKM)]
  · rw [clippedPositivePart, clippedPositivePart,
      clippedLog_eq_realSymmetricClip K hK hz,
      clippedLog_eq_realSymmetricClip M (hK.trans hKM) hz]
    exact positivePart_symmClip_mono (Real.log_nonneg (by exact_mod_cast hK))
      (log_cutoff_mono hK hKM)

lemma clippedNegativePart_mono {K M : NNReal} (hK : 1 ≤ K) (hKM : K ≤ M)
    (z : ℂ) : clippedNegativePart K z ≤ clippedNegativePart M z := by
  by_cases hz : z = 0
  · subst z
    rw [clippedNegativePart_zero K hK,
      clippedNegativePart_zero M (hK.trans hKM)]
    exact log_cutoff_mono hK hKM
  · rw [clippedNegativePart, clippedNegativePart,
      clippedLog_eq_realSymmetricClip K hK hz,
      clippedLog_eq_realSymmetricClip M (hK.trans hKM) hz]
    exact negativePart_symmClip_mono (Real.log_nonneg (by exact_mod_cast hK))
      (log_cutoff_mono hK hKM)

lemma clippedPositivePart_diff_le_log {K M : NNReal}
    (hK : 1 ≤ K) (hKM : K ≤ M) (z : ℂ) :
    clippedPositivePart M z - clippedPositivePart K z ≤
      Real.log (M : ℝ) - Real.log (K : ℝ) := by
  by_cases hz : z = 0
  · subst z
    rw [clippedPositivePart_zero K hK,
      clippedPositivePart_zero M (hK.trans hKM)]
    linarith [log_cutoff_mono hK hKM]
  · simp only [clippedPositivePart]
    rw [clippedLog_eq_realSymmetricClip K hK hz,
      clippedLog_eq_realSymmetricClip M (hK.trans hKM) hz]
    exact positivePart_symmClip_diff_le
      (Real.log_nonneg (by exact_mod_cast hK)) (log_cutoff_mono hK hKM)

lemma clippedNegativePart_diff_le_log {K M : NNReal}
    (hK : 1 ≤ K) (hKM : K ≤ M) (z : ℂ) :
    clippedNegativePart M z - clippedNegativePart K z ≤
      Real.log (M : ℝ) - Real.log (K : ℝ) := by
  by_cases hz : z = 0
  · subst z
    rw [clippedNegativePart_zero K hK,
      clippedNegativePart_zero M (hK.trans hKM)]
  · simp only [clippedNegativePart]
    rw [clippedLog_eq_realSymmetricClip K hK hz,
      clippedLog_eq_realSymmetricClip M (hK.trans hKM) hz]
    exact negativePart_symmClip_diff_le
      (Real.log_nonneg (by exact_mod_cast hK)) (log_cutoff_mono hK hKM)

lemma clippedPositivePart_layer {K M : NNReal} (hK : 1 ≤ K) (hKM : K ≤ M)
    (z : ℂ) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t < clippedPositivePart M z - clippedPositivePart K z) :
    Real.exp (Real.log (K : ℝ) + t) < ‖z‖ := by
  have hz : z ≠ 0 := by
    intro hz
    subst z
    rw [clippedPositivePart_zero K hK,
      clippedPositivePart_zero M (hK.trans hKM)] at ht
    linarith
  simp only [clippedPositivePart] at ht
  rw [clippedLog_eq_realSymmetricClip K hK hz,
    clippedLog_eq_realSymmetricClip M (hK.trans hKM) hz] at ht
  have hlog := positivePart_symmClip_layer
    (Real.log_nonneg (by exact_mod_cast hK)) (log_cutoff_mono hK hKM) ht0 ht
  have hnorm : 0 < ‖z‖ := norm_pos_iff.mpr hz
  rw [← Real.exp_log hnorm]
  exact Real.exp_lt_exp.mpr hlog

lemma clippedNegativePart_layer {K M : NNReal} (hK : 1 ≤ K) (hKM : K ≤ M)
    (z : ℂ) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t < clippedNegativePart M z - clippedNegativePart K z) :
    ‖z‖ < Real.exp (-(Real.log (K : ℝ) + t)) := by
  by_cases hz : z = 0
  · subst z
    simpa using (Real.exp_pos (-(Real.log (K : ℝ) + t)))
  · simp only [clippedNegativePart] at ht
    rw [clippedLog_eq_realSymmetricClip K hK hz,
      clippedLog_eq_realSymmetricClip M (hK.trans hKM) hz] at ht
    have hlog := negativePart_symmClip_layer
      (Real.log_nonneg (by exact_mod_cast hK)) (log_cutoff_mono hK hKM) ht0 ht
    have hnorm : 0 < ‖z‖ := norm_pos_iff.mpr hz
    rw [← Real.exp_log hnorm]
    exact Real.exp_lt_exp.mpr hlog

lemma clippedPositivePart_layer_le {K M : NNReal}
    (hK : 1 ≤ K) (hKM : K ≤ M) (z : ℂ) {t : ℝ} (ht0 : 0 < t)
    (ht : t ≤ clippedPositivePart M z - clippedPositivePart K z) :
    Real.exp (Real.log (K : ℝ) + t) ≤ ‖z‖ := by
  have hz : z ≠ 0 := by
    intro hz
    subst z
    rw [clippedPositivePart_zero K hK,
      clippedPositivePart_zero M (hK.trans hKM)] at ht
    linarith
  simp only [clippedPositivePart] at ht
  rw [clippedLog_eq_realSymmetricClip K hK hz,
    clippedLog_eq_realSymmetricClip M (hK.trans hKM) hz] at ht
  have hlog := positivePart_symmClip_layer_le
    (Real.log_nonneg (by exact_mod_cast hK)) (log_cutoff_mono hK hKM) ht0 ht
  have hnorm : 0 < ‖z‖ := norm_pos_iff.mpr hz
  rw [← Real.exp_log hnorm]
  exact Real.exp_le_exp.mpr hlog

lemma clippedNegativePart_layer_le {K M : NNReal}
    (hK : 1 ≤ K) (hKM : K ≤ M) (z : ℂ) {t : ℝ} (ht0 : 0 < t)
    (ht : t ≤ clippedNegativePart M z - clippedNegativePart K z) :
    ‖z‖ ≤ Real.exp (-(Real.log (K : ℝ) + t)) := by
  by_cases hz : z = 0
  · subst z
    simpa using (Real.exp_pos (-(Real.log (K : ℝ) + t))).le
  · simp only [clippedNegativePart] at ht
    rw [clippedLog_eq_realSymmetricClip K hK hz,
      clippedLog_eq_realSymmetricClip M (hK.trans hKM) hz] at ht
    have hlog := negativePart_symmClip_layer_le
      (Real.log_nonneg (by exact_mod_cast hK)) (log_cutoff_mono hK hKM) ht0 ht
    have hnorm : 0 < ‖z‖ := norm_pos_iff.mpr hz
    rw [← Real.exp_log hnorm]
    exact Real.exp_le_exp.mpr hlog

lemma abs_clippedLog_sub_le_parts {K M : NNReal}
    (hK : 1 ≤ K) (hKM : K ≤ M) (z : ℂ) :
    |clippedLog M z - clippedLog K z| ≤
      (clippedPositivePart M z - clippedPositivePart K z) +
      (clippedNegativePart M z - clippedNegativePart K z) := by
  by_cases hz : z = 0
  · subst z
    rw [clippedLog_zero K hK, clippedLog_zero M (hK.trans hKM),
      clippedPositivePart_zero K hK,
      clippedPositivePart_zero M (hK.trans hKM),
      clippedNegativePart_zero K hK,
      clippedNegativePart_zero M (hK.trans hKM),
      abs_of_nonpos (by linarith [log_cutoff_mono hK hKM])]
    linarith
  · simp only [clippedPositivePart, clippedNegativePart]
    rw [clippedLog_eq_realSymmetricClip K hK hz,
      clippedLog_eq_realSymmetricClip M (hK.trans hKM) hz]
    exact abs_symmClip_sub_le_parts (y := Real.log ‖z‖)
      (Real.log_nonneg (by exact_mod_cast hK)) (log_cutoff_mono hK hKM)

end Erdos522

end AmalgamatedModule112


/-! ===== amalgamated from Research.ClippedLayerCake ===== -/

section AmalgamatedModule113


open MeasureTheory Set

namespace Erdos522

noncomputable def clippedPositiveIncrement (K M : NNReal) (z : ℂ) : ℝ :=
  clippedPositivePart M z - clippedPositivePart K z

noncomputable def clippedNegativeIncrement (K M : NNReal) (z : ℂ) : ℝ :=
  clippedNegativePart M z - clippedNegativePart K z

lemma clippedPositiveIncrement_nonneg {K M : NNReal}
    (hK : 1 ≤ K) (hKM : K ≤ M) (z : ℂ) :
    0 ≤ clippedPositiveIncrement K M z :=
  sub_nonneg.mpr (clippedPositivePart_mono hK hKM z)

lemma clippedNegativeIncrement_nonneg {K M : NNReal}
    (hK : 1 ≤ K) (hKM : K ≤ M) (z : ℂ) :
    0 ≤ clippedNegativeIncrement K M z :=
  sub_nonneg.mpr (clippedNegativePart_mono hK hKM z)

lemma clippedPositiveIncrement_le {K M : NNReal}
    (hK : 1 ≤ K) (hKM : K ≤ M) (z : ℂ) :
    clippedPositiveIncrement K M z ≤
      Real.log (M : ℝ) - Real.log (K : ℝ) :=
  clippedPositivePart_diff_le_log hK hKM z

lemma clippedNegativeIncrement_le {K M : NNReal}
    (hK : 1 ≤ K) (hKM : K ≤ M) (z : ℂ) :
    clippedNegativeIncrement K M z ≤
      Real.log (M : ℝ) - Real.log (K : ℝ) :=
  clippedNegativePart_diff_le_log hK hKM z

lemma integrable_clippedPositiveIncrement
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (Z : α → ℂ) (hZ : AEStronglyMeasurable Z μ)
    {K M : NNReal} (hK : 1 ≤ K) (hKM : K ≤ M) :
    Integrable (fun x => clippedPositiveIncrement K M (Z x)) μ := by
  have hcont : Continuous (clippedPositiveIncrement K M) := by
    unfold clippedPositiveIncrement clippedPositivePart positivePart
    have hcM := (clippedLog_lipschitz M (hK.trans hKM)).continuous
    have hcK := (clippedLog_lipschitz K hK).continuous
    fun_prop
  apply Integrable.of_bound (hcont.aestronglyMeasurable.comp_aemeasurable
    hZ.aemeasurable) (Real.log (M : ℝ) - Real.log (K : ℝ))
  filter_upwards with x
  change |clippedPositiveIncrement K M (Z x)| ≤ _
  rw [abs_of_nonneg (clippedPositiveIncrement_nonneg hK hKM _)]
  exact clippedPositiveIncrement_le hK hKM _

lemma integrable_clippedNegativeIncrement
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (Z : α → ℂ) (hZ : AEStronglyMeasurable Z μ)
    {K M : NNReal} (hK : 1 ≤ K) (hKM : K ≤ M) :
    Integrable (fun x => clippedNegativeIncrement K M (Z x)) μ := by
  have hcont : Continuous (clippedNegativeIncrement K M) := by
    unfold clippedNegativeIncrement clippedNegativePart negativePart
    have hcM := (clippedLog_lipschitz M (hK.trans hKM)).continuous
    have hcK := (clippedLog_lipschitz K hK).continuous
    fun_prop
  apply Integrable.of_bound (hcont.aestronglyMeasurable.comp_aemeasurable
    hZ.aemeasurable) (Real.log (M : ℝ) - Real.log (K : ℝ))
  filter_upwards with x
  change |clippedNegativeIncrement K M (Z x)| ≤ _
  rw [abs_of_nonneg (clippedNegativeIncrement_nonneg hK hKM _)]
  exact clippedNegativeIncrement_le hK hKM _

/-- Layer-cake comparison for the positive clipping increment. -/
theorem integral_clippedPositiveIncrement_le_of_layers
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (Z : α → ℂ) (hZ : AEStronglyMeasurable Z μ)
    {K M : NNReal} (hK : 1 ≤ K) (hKM : K ≤ M)
    (g : ℝ → ℝ)
    (hg : IntegrableOn g (Ioc 0
      (Real.log (M : ℝ) - Real.log (K : ℝ))))
    (hlayer : ∀ t, 0 < t → t ≤ Real.log (M : ℝ) - Real.log (K : ℝ) →
      μ.real {x | Real.exp (Real.log (K : ℝ) + t) ≤ ‖Z x‖} ≤ g t) :
    (∫ x, clippedPositiveIncrement K M (Z x) ∂μ) ≤
      ∫ t in Ioc 0 (Real.log (M : ℝ) - Real.log (K : ℝ)), g t := by
  let f : α → ℝ := fun x => clippedPositiveIncrement K M (Z x)
  let L : ℝ := Real.log (M : ℝ) - Real.log (K : ℝ)
  have hfint : Integrable f μ :=
    integrable_clippedPositiveIncrement μ Z hZ hK hKM
  have hf0 : 0 ≤ᵐ[μ] f := Filter.Eventually.of_forall fun x =>
    clippedPositiveIncrement_nonneg hK hKM _
  have hfL : f ≤ᵐ[μ] (fun _ => L) := Filter.Eventually.of_forall fun x =>
    clippedPositiveIncrement_le hK hKM _
  rw [hfint.integral_eq_integral_Ioc_meas_le hf0 hfL]
  have hpoint : ∀ t ∈ Ioc (0 : ℝ) L,
      μ.real {x | t ≤ f x} ≤ g t := by
    intro t ht
    apply (measureReal_mono ?_).trans (hlayer t ht.1 ht.2)
    intro x hx
    exact clippedPositivePart_layer_le hK hKM (Z x) ht.1 hx
  have hleftMeas : AEStronglyMeasurable
      (fun t => μ.real {x | t ≤ f x}) (volume.restrict (Ioc 0 L)) := by
    apply Measurable.aestronglyMeasurable
    rw [show (fun t => μ.real {x | t ≤ f x}) =
      fun t => (μ {x | t ≤ f x}).toReal by
        funext t; exact measureReal_def μ _]
    apply Measurable.ennreal_toReal
    exact Antitone.measurable fun a b hab => measure_mono fun x hx => hab.trans hx
  have hleftInt : IntegrableOn (fun t => μ.real {x | t ≤ f x}) (Ioc 0 L) := by
    apply hg.mono' hleftMeas
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact hpoint t ht
  apply integral_mono_ae hleftInt hg
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact hpoint t ht

/-- Layer-cake comparison for the negative clipping increment. -/
theorem integral_clippedNegativeIncrement_le_of_layers
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (Z : α → ℂ) (hZ : AEStronglyMeasurable Z μ)
    {K M : NNReal} (hK : 1 ≤ K) (hKM : K ≤ M)
    (g : ℝ → ℝ)
    (hg : IntegrableOn g (Ioc 0
      (Real.log (M : ℝ) - Real.log (K : ℝ))))
    (hlayer : ∀ t, 0 < t → t ≤ Real.log (M : ℝ) - Real.log (K : ℝ) →
      μ.real {x | ‖Z x‖ ≤ Real.exp (-(Real.log (K : ℝ) + t))} ≤ g t) :
    (∫ x, clippedNegativeIncrement K M (Z x) ∂μ) ≤
      ∫ t in Ioc 0 (Real.log (M : ℝ) - Real.log (K : ℝ)), g t := by
  let f : α → ℝ := fun x => clippedNegativeIncrement K M (Z x)
  let L : ℝ := Real.log (M : ℝ) - Real.log (K : ℝ)
  have hfint : Integrable f μ :=
    integrable_clippedNegativeIncrement μ Z hZ hK hKM
  have hf0 : 0 ≤ᵐ[μ] f := Filter.Eventually.of_forall fun x =>
    clippedNegativeIncrement_nonneg hK hKM _
  have hfL : f ≤ᵐ[μ] (fun _ => L) := Filter.Eventually.of_forall fun x =>
    clippedNegativeIncrement_le hK hKM _
  rw [hfint.integral_eq_integral_Ioc_meas_le hf0 hfL]
  have hpoint : ∀ t ∈ Ioc (0 : ℝ) L,
      μ.real {x | t ≤ f x} ≤ g t := by
    intro t ht
    apply (measureReal_mono ?_).trans (hlayer t ht.1 ht.2)
    intro x hx
    exact clippedNegativePart_layer_le hK hKM (Z x) ht.1 hx
  have hleftMeas : AEStronglyMeasurable
      (fun t => μ.real {x | t ≤ f x}) (volume.restrict (Ioc 0 L)) := by
    apply Measurable.aestronglyMeasurable
    rw [show (fun t => μ.real {x | t ≤ f x}) =
      fun t => (μ {x | t ≤ f x}).toReal by
        funext t; exact measureReal_def μ _]
    apply Measurable.ennreal_toReal
    exact Antitone.measurable fun a b hab => measure_mono fun x hx => hab.trans hx
  have hleftInt : IntegrableOn (fun t => μ.real {x | t ≤ f x}) (Ioc 0 L) := by
    apply hg.mono' hleftMeas
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact hpoint t ht
  apply integral_mono_ae hleftInt hg
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact hpoint t ht

end Erdos522

end AmalgamatedModule113


/-! ===== amalgamated from Research.AnnealedRadialLayerBounds ===== -/

section AmalgamatedModule114


open MeasureTheory ProbabilityTheory

namespace Erdos522

noncomputable def exponentialLayerCutoff (K : NNReal) (t : ℝ) : NNReal :=
  K * ⟨Real.exp t, (Real.exp_pos t).le⟩

@[simp] lemma coe_exponentialLayerCutoff (K : NNReal) (t : ℝ) :
    (exponentialLayerCutoff K t : ℝ) = (K : ℝ) * Real.exp t := rfl

lemma exponentialLayerCutoff_pos {K : NNReal} (hK : 0 < K) (t : ℝ) :
    0 < exponentialLayerCutoff K t := mul_pos hK (by exact_mod_cast Real.exp_pos t)

lemma inv_exponentialLayerCutoff (K : NNReal) (hK : 0 < K) (t : ℝ) :
    1 / (exponentialLayerCutoff K t : ℝ) =
      Real.exp (-(Real.log (K : ℝ) + t)) := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  rw [coe_exponentialLayerCutoff, Real.exp_neg, Real.exp_add,
    Real.exp_log hKr]
  field_simp

lemma exponentialLayerCutoff_eq_exp_log (K : NNReal) (hK : 0 < K) (t : ℝ) :
    (exponentialLayerCutoff K t : ℝ) =
      Real.exp (Real.log (K : ℝ) + t) := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  rw [coe_exponentialLayerCutoff, Real.exp_add, Real.exp_log hKr]

lemma integral_smallBallCutoff_radialAnnealedLaw_eq
    (n : ℕ) (s : ℝ) (Q : NNReal) :
    (∫ z : ℂ, smallBallCutoff Q z
      ∂(radialAnnealedLaw n s : Measure ℂ)) =
      cubeAverage (radialCubeSmallBallStatistic n s Q) := by
  change (∫ z : ℂ, smallBallCutoff Q z
      ∂(radialAnnealedLaw n s : Measure ℂ)) =
    cubeAverage (radialCubeAngularStatistic n s (smallBallCutoff Q))
  exact integral_radialAnnealedLaw_eq_cubeAverage n s (smallBallCutoff Q)
    (smallBallCutoff_lipschitz Q).continuous 1
    (fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (smallBallCutoff_nonneg Q z)]
      exact smallBallCutoff_le_one Q z)

lemma measureReal_radialAnnealed_norm_le_inv_le_smallBall
    (n : ℕ) (s : ℝ) (Q : NNReal) (hQ : 0 < Q) :
    (radialAnnealedLaw n s : Measure ℂ).real
      {z | ‖z‖ ≤ 1 / (Q : ℝ)} ≤
      cubeAverage (radialCubeSmallBallStatistic n s Q) := by
  let μ : Measure ℂ := radialAnnealedLaw n s
  let f : ℂ → ℝ := smallBallCutoff Q
  have hfint : Integrable f μ := by
    apply Integrable.of_bound (smallBallCutoff_lipschitz Q).continuous.aestronglyMeasurable 1
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (smallBallCutoff_nonneg Q z)]
    exact smallBallCutoff_le_one Q z
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (f := f) (Filter.Eventually.of_forall fun z => smallBallCutoff_nonneg Q z)
    hfint 1
  have hsub : {z : ℂ | ‖z‖ ≤ 1 / (Q : ℝ)} ⊆ {z | (1 : ℝ) ≤ f z} := by
    intro z hz
    change (1 : ℝ) ≤ smallBallCutoff Q z
    rw [smallBallCutoff_eq_one_of_norm_le hQ hz]
  have hmono : μ.real {z : ℂ | ‖z‖ ≤ 1 / (Q : ℝ)} ≤
      μ.real {z | (1 : ℝ) ≤ f z} := measureReal_mono (μ := μ) hsub
  have hmark' : μ.real {z | (1 : ℝ) ≤ f z} ≤ ∫ z, f z ∂μ := by
    simpa using hmark
  calc
    (radialAnnealedLaw n s : Measure ℂ).real {z | ‖z‖ ≤ 1 / (Q : ℝ)} ≤
        μ.real {z | (1 : ℝ) ≤ f z} := hmono
    _ ≤ ∫ z, f z ∂μ := hmark'
    _ = cubeAverage (radialCubeSmallBallStatistic n s Q) := by
      simpa [μ, f] using integral_smallBallCutoff_radialAnnealedLaw_eq n s Q

/-- Quantitative lower radial-layer probability under the annealed law. -/
theorem measureReal_radialAnnealed_lowerLayer_le
    (n : ℕ) (hn : 0 < n) (s : ℝ) (K : NNReal) (hK : 0 < K) (t : ℝ) :
    (radialAnnealedLaw n s : Measure ℂ).real
      {z | ‖z‖ ≤ Real.exp (-(Real.log (K : ℝ) + t))} ≤
      Real.exp 1 *
        (2 * Real.sqrt Real.pi / (exponentialLayerCutoff K t : ℝ) +
          ((7 / 24 : ℝ) * (Real.exp (4 * |s|) / (n + 1 : ℝ)) +
            2 * (Real.exp (4 * |s|) / (n + 1 : ℝ)) ^ 2) *
              (exponentialLayerCutoff K t : ℝ) ^ 4 *
                circularGaussianFourthNormMoment +
          Real.sqrt (Real.exp (4 * |s|) / (n + 1 : ℝ)) / 4 *
              (exponentialLayerCutoff K t : ℝ) ^ 2 *
                circularGaussianSecondNormMoment) := by
  let Q := exponentialLayerCutoff K t
  rw [← inv_exponentialLayerCutoff K hK t]
  exact (measureReal_radialAnnealed_norm_le_inv_le_smallBall n s Q
    (exponentialLayerCutoff_pos hK t)).trans
      (cubeAverage_radialCubeSmallBallStatistic_le n hn s Q
        (exponentialLayerCutoff_pos hK t))

lemma integral_highBallCutoff_radialAnnealedLaw_eq
    (n : ℕ) (s : ℝ) (Q : NNReal) :
    (∫ z : ℂ, highBallCutoff Q z
      ∂(radialAnnealedLaw n s : Measure ℂ)) =
      cubeAverage (radialCubeAngularStatistic n s (highBallCutoff Q)) := by
  apply integral_radialAnnealedLaw_eq_cubeAverage n s (highBallCutoff Q)
    (by unfold highBallCutoff; fun_prop) 1
  intro z
  rw [Real.norm_eq_abs, abs_of_nonneg (highBallCutoff_nonneg Q z)]
  exact highBallCutoff_le_one Q z

lemma cubeAverage_radialHighBall_le
    (n : ℕ) (s : ℝ) (Q : NNReal) (hQ : 0 < Q) :
    cubeAverage (radialCubeAngularStatistic n s (highBallCutoff Q)) ≤
      1 / (Q : ℝ) ^ 2 := by
  calc
    cubeAverage (radialCubeAngularStatistic n s (highBallCutoff Q)) ≤
        cubeAverage (fun _ : Fin (n + 1) → Bool => 1 / (Q : ℝ) ^ 2) := by
      apply cubeAverage_mono
      intro x
      exact weightedVectorPolynomial_highBall_circleAverage_le
        (fun k : Fin (n + 1) => radialWeight n s k)
        (fun k => radialWeight_nonneg n s k)
        (sum_radialWeight_fin n s) x Q hQ
    _ = 1 / (Q : ℝ) ^ 2 := cubeAverage_const _

lemma measureReal_radialAnnealed_norm_ge_le_highBall
    (n : ℕ) (s : ℝ) (Q : NNReal) (hQ : 0 < Q) :
    (radialAnnealedLaw n s : Measure ℂ).real
      {z | (Q : ℝ) ≤ ‖z‖} ≤ 1 / (Q : ℝ) ^ 2 := by
  let μ : Measure ℂ := radialAnnealedLaw n s
  let f : ℂ → ℝ := highBallCutoff Q
  have hfint : Integrable f μ := by
    apply Integrable.of_bound (by
      dsimp [f]
      unfold highBallCutoff
      fun_prop) 1
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (highBallCutoff_nonneg Q z)]
    exact highBallCutoff_le_one Q z
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (f := f) (Filter.Eventually.of_forall fun z => highBallCutoff_nonneg Q z)
    hfint 1
  have hsub : {z : ℂ | (Q : ℝ) ≤ ‖z‖} ⊆ {z | (1 : ℝ) ≤ f z} := by
    intro z hz
    change (1 : ℝ) ≤ highBallCutoff Q z
    rw [highBallCutoff_eq_one_of_le_norm hQ hz]
  have hmono : μ.real {z : ℂ | (Q : ℝ) ≤ ‖z‖} ≤
      μ.real {z | (1 : ℝ) ≤ f z} := measureReal_mono (μ := μ) hsub
  have hmark' : μ.real {z | (1 : ℝ) ≤ f z} ≤ ∫ z, f z ∂μ := by
    simpa using hmark
  calc
    (radialAnnealedLaw n s : Measure ℂ).real {z | (Q : ℝ) ≤ ‖z‖} ≤
        μ.real {z | (1 : ℝ) ≤ f z} := hmono
    _ ≤ ∫ z, f z ∂μ := hmark'
    _ = cubeAverage (radialCubeAngularStatistic n s (highBallCutoff Q)) := by
      simpa [μ, f] using integral_highBallCutoff_radialAnnealedLaw_eq n s Q
    _ ≤ 1 / (Q : ℝ) ^ 2 := cubeAverage_radialHighBall_le n s Q hQ

/-- Quantitative upper radial-layer probability under the annealed law. -/
theorem measureReal_radialAnnealed_upperLayer_le
    (n : ℕ) (s : ℝ) (K : NNReal) (hK : 0 < K) (t : ℝ) :
    (radialAnnealedLaw n s : Measure ℂ).real
      {z | Real.exp (Real.log (K : ℝ) + t) ≤ ‖z‖} ≤
      (K : ℝ)⁻¹ ^ 2 * Real.exp (-2 * t) := by
  let Q := exponentialLayerCutoff K t
  rw [← exponentialLayerCutoff_eq_exp_log K hK t]
  have h := measureReal_radialAnnealed_norm_ge_le_highBall n s Q
    (exponentialLayerCutoff_pos hK t)
  calc
    (radialAnnealedLaw n s : Measure ℂ).real {z | (Q : ℝ) ≤ ‖z‖} ≤
        1 / (Q : ℝ) ^ 2 := h
    _ = (K : ℝ)⁻¹ ^ 2 * Real.exp (-2 * t) := by
      rw [coe_exponentialLayerCutoff,
        show Real.exp (-2 * t) = (Real.exp t)⁻¹ ^ 2 by
          rw [show -2 * t = -t + -t by ring, Real.exp_add, Real.exp_neg]
          ring]
      field_simp

end Erdos522

end AmalgamatedModule114


/-! ===== amalgamated from Research.AnnealedClippedIncrementBound ===== -/

section AmalgamatedModule115


open MeasureTheory ProbabilityTheory Set

namespace Erdos522

lemma integral_Ioc_exp_neg_le_one (L : ℝ) :
    (∫ t : ℝ in Ioc 0 L, Real.exp (-t)) ≤ 1 := by
  by_cases hL : 0 ≤ L
  · have hres : volume.restrict (Ioc (0 : ℝ) L) ≤ volume.restrict (Ioi 0) :=
      Measure.restrict_mono Ioc_subset_Ioi_self (le_refl _)
    calc
      (∫ t : ℝ in Ioc 0 L, Real.exp (-t)) ≤
          ∫ t : ℝ in Ioi 0, Real.exp (-t) :=
        integral_mono_measure hres
          (Filter.Eventually.of_forall fun t => (Real.exp_pos _).le)
          (integrableOn_exp_neg_Ioi 0)
      _ = 1 := integral_exp_neg_Ioi_zero
  · have hempty : Ioc (0 : ℝ) L = ∅ := by
      rw [Ioc_eq_empty]
      exact fun h => hL h.le
    simp [hempty]

lemma integral_Ioc_const (L c : ℝ) (hL : 0 ≤ L) :
    (∫ _t : ℝ in Ioc 0 L, c) = L * c := by
  rw [setIntegral_const]
  simp [measureReal_def, Real.volume_Ioc, hL]

noncomputable def annealedLayerError (n : ℕ) (s : ℝ) (M : NNReal) : ℝ :=
  (((7 / 24 : ℝ) * (Real.exp (4 * |s|) / (n + 1 : ℝ)) +
      2 * (Real.exp (4 * |s|) / (n + 1 : ℝ)) ^ 2) *
        (M : ℝ) ^ 4 * circularGaussianFourthNormMoment) +
    (Real.sqrt (Real.exp (4 * |s|) / (n + 1 : ℝ)) / 4 *
      (M : ℝ) ^ 2 * circularGaussianSecondNormMoment)

lemma annealedLayerError_nonneg (n : ℕ) (s : ℝ) (M : NNReal) :
    0 ≤ annealedLayerError n s M := by
  unfold annealedLayerError
  have h2 := circularGaussianSecondNormMoment_nonneg
  have h4 := circularGaussianFourthNormMoment_nonneg
  positivity

noncomputable def annealedLowerLayerMajorant
    (n : ℕ) (s : ℝ) (K M : NNReal) (t : ℝ) : ℝ :=
  Real.exp 1 * (2 * Real.sqrt Real.pi * (K : ℝ)⁻¹ * Real.exp (-t) +
    annealedLayerError n s M)

lemma integrableOn_annealedLowerLayerMajorant
    (n : ℕ) (s : ℝ) (K M : NNReal) (L : ℝ) :
    IntegrableOn (annealedLowerLayerMajorant n s K M) (Ioc 0 L) := by
  apply (ContinuousOn.integrableOn_Icc (by
    unfold annealedLowerLayerMajorant
    fun_prop)).mono_set
  exact Ioc_subset_Icc_self

lemma lowerLayerMajorant_integral_le
    (n : ℕ) (s : ℝ) (K M : NNReal)
    (hK : 1 ≤ K) (hKM : K ≤ M) :
    (∫ t : ℝ in Ioc 0 (Real.log (M : ℝ) - Real.log (K : ℝ)),
      annealedLowerLayerMajorant n s K M t) ≤
      Real.exp 1 *
        (2 * Real.sqrt Real.pi * (K : ℝ)⁻¹ +
          (Real.log (M : ℝ) - Real.log (K : ℝ)) *
            annealedLayerError n s M) := by
  let L := Real.log (M : ℝ) - Real.log (K : ℝ)
  let a := 2 * Real.sqrt Real.pi * (K : ℝ)⁻¹
  let E := annealedLayerError n s M
  have hL : 0 ≤ L := sub_nonneg.mpr (log_cutoff_mono hK hKM)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hE : 0 ≤ E := by exact annealedLayerError_nonneg n s M
  have hexpInt : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioc 0 L) := by
    apply (integrableOn_exp_neg_Ioi 0).mono_set
    exact Ioc_subset_Ioi_self
  have hconstInt : IntegrableOn (fun _t : ℝ => E) (Ioc 0 L) := by
    exact integrableOn_const (by simp [Real.volume_Ioc]) (by simp)
  have heq :
      (∫ t : ℝ in Ioc 0 L, annealedLowerLayerMajorant n s K M t) =
        Real.exp 1 *
          (a * (∫ t : ℝ in Ioc 0 L, Real.exp (-t)) + L * E) := by
    unfold annealedLowerLayerMajorant
    dsimp [L, a, E]
    rw [integral_const_mul,
      integral_add (hexpInt.const_mul _) hconstInt,
      integral_const_mul, integral_Ioc_const L E hL]
  rw [heq]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  have haI : a * (∫ t : ℝ in Ioc 0 L, Real.exp (-t)) ≤ a := by
    simpa using mul_le_mul_of_nonneg_left (integral_Ioc_exp_neg_le_one L) ha
  have hinner : a * (∫ t : ℝ in Ioc 0 L, Real.exp (-t)) + L * E ≤
      a + L * E := add_le_add haI (le_refl _)
  simpa [L, a, E] using hinner

lemma exponentialLayerCutoff_le {K M : NNReal} (hK : 1 ≤ K) (hKM : K ≤ M)
    {t : ℝ} (ht : t ≤ Real.log (M : ℝ) - Real.log (K : ℝ)) :
    (exponentialLayerCutoff K t : ℝ) ≤ (M : ℝ) := by
  have hMp : (0 : ℝ) < M := by
    exact_mod_cast lt_of_lt_of_le (show (0 : NNReal) < 1 by norm_num) (hK.trans hKM)
  rw [exponentialLayerCutoff_eq_exp_log K
    (lt_of_lt_of_le (show (0 : NNReal) < 1 by norm_num) hK) t,
    ← Real.exp_log hMp]
  apply Real.exp_le_exp.mpr
  linarith

lemma measureReal_lowerLayer_le_majorant
    (n : ℕ) (hn : 0 < n) (s : ℝ) (K M : NNReal)
    (hK : 1 ≤ K) (hKM : K ≤ M) {t : ℝ}
    (ht : t ≤ Real.log (M : ℝ) - Real.log (K : ℝ)) :
    (radialAnnealedLaw n s : Measure ℂ).real
      {z | ‖z‖ ≤ Real.exp (-(Real.log (K : ℝ) + t))} ≤
      annealedLowerLayerMajorant n s K M t := by
  have hKp : 0 < K := lt_of_lt_of_le (by norm_num) hK
  have hQ := measureReal_radialAnnealed_lowerLayer_le n hn s K hKp t
  have hQM := exponentialLayerCutoff_le hK hKM ht
  have hA : 0 ≤ (7 / 24 : ℝ) * (Real.exp (4 * |s|) / (n + 1 : ℝ)) +
      2 * (Real.exp (4 * |s|) / (n + 1 : ℝ)) ^ 2 := by positivity
  have hC2 := circularGaussianSecondNormMoment_nonneg
  have hC4 := circularGaussianFourthNormMoment_nonneg
  have hmain : 2 * Real.sqrt Real.pi / (exponentialLayerCutoff K t : ℝ) =
      2 * Real.sqrt Real.pi * (K : ℝ)⁻¹ * Real.exp (-t) := by
    rw [coe_exponentialLayerCutoff, Real.exp_neg]
    field_simp
  calc
    (radialAnnealedLaw n s : Measure ℂ).real
        {z | ‖z‖ ≤ Real.exp (-(Real.log (K : ℝ) + t))} ≤
      Real.exp 1 *
        (2 * Real.sqrt Real.pi / (exponentialLayerCutoff K t : ℝ) +
          ((7 / 24 : ℝ) * (Real.exp (4 * |s|) / (n + 1 : ℝ)) +
            2 * (Real.exp (4 * |s|) / (n + 1 : ℝ)) ^ 2) *
              (exponentialLayerCutoff K t : ℝ) ^ 4 *
                circularGaussianFourthNormMoment +
          Real.sqrt (Real.exp (4 * |s|) / (n + 1 : ℝ)) / 4 *
              (exponentialLayerCutoff K t : ℝ) ^ 2 *
                circularGaussianSecondNormMoment) := hQ
    _ ≤ annealedLowerLayerMajorant n s K M t := by
      unfold annealedLowerLayerMajorant annealedLayerError
      rw [hmain]
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      have hb4 :
          ((7 / 24 : ℝ) * (Real.exp (4 * |s|) / (n + 1 : ℝ)) +
              2 * (Real.exp (4 * |s|) / (n + 1 : ℝ)) ^ 2) *
              (exponentialLayerCutoff K t : ℝ) ^ 4 *
                circularGaussianFourthNormMoment ≤
          ((7 / 24 : ℝ) * (Real.exp (4 * |s|) / (n + 1 : ℝ)) +
              2 * (Real.exp (4 * |s|) / (n + 1 : ℝ)) ^ 2) *
              (M : ℝ) ^ 4 * circularGaussianFourthNormMoment :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hQM 4) hA) hC4
      have hb2 :
          Real.sqrt (Real.exp (4 * |s|) / (n + 1 : ℝ)) / 4 *
              (exponentialLayerCutoff K t : ℝ) ^ 2 *
                circularGaussianSecondNormMoment ≤
          Real.sqrt (Real.exp (4 * |s|) / (n + 1 : ℝ)) / 4 *
              (M : ℝ) ^ 2 * circularGaussianSecondNormMoment :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hQM 2)
            (by positivity)) hC2
      linarith

noncomputable def annealedUpperLayerMajorant (K : NNReal) (t : ℝ) : ℝ :=
  (K : ℝ)⁻¹ ^ 2 * Real.exp (-t)

lemma integrableOn_annealedUpperLayerMajorant (K : NNReal) (L : ℝ) :
    IntegrableOn (annealedUpperLayerMajorant K) (Ioc 0 L) := by
  apply (integrableOn_exp_neg_Ioi 0).mono_set Ioc_subset_Ioi_self |>.const_mul

lemma upperLayerMajorant_integral_le (K : NNReal) (L : ℝ) :
    (∫ t : ℝ in Ioc 0 L, annealedUpperLayerMajorant K t) ≤
      (K : ℝ)⁻¹ ^ 2 := by
  unfold annealedUpperLayerMajorant
  rw [integral_const_mul]
  exact mul_le_of_le_one_right (by positivity) (integral_Ioc_exp_neg_le_one L)

lemma measureReal_upperLayer_le_majorant
    (n : ℕ) (s : ℝ) (K : NNReal) (hK : 1 ≤ K) {t : ℝ} (ht : 0 ≤ t) :
    (radialAnnealedLaw n s : Measure ℂ).real
      {z | Real.exp (Real.log (K : ℝ) + t) ≤ ‖z‖} ≤
      annealedUpperLayerMajorant K t := by
  have h := measureReal_radialAnnealed_upperLayer_le n s K
    (lt_of_lt_of_le (by norm_num) hK) t
  apply h.trans
  unfold annealedUpperLayerMajorant
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith))
  positivity

/-- Explicit integrated bounds for both clipping increments. -/
theorem integral_annealed_clippedNegativeIncrement_le
    (n : ℕ) (hn : 0 < n) (s : ℝ) (K M : NNReal)
    (hK : 1 ≤ K) (hKM : K ≤ M) :
    (∫ z : ℂ, clippedNegativeIncrement K M z
      ∂(radialAnnealedLaw n s : Measure ℂ)) ≤
      Real.exp 1 *
        (2 * Real.sqrt Real.pi * (K : ℝ)⁻¹ +
          (Real.log (M : ℝ) - Real.log (K : ℝ)) *
            annealedLayerError n s M) := by
  exact (integral_clippedNegativeIncrement_le_of_layers
    (radialAnnealedLaw n s : Measure ℂ) id continuous_id.aestronglyMeasurable
    hK hKM (annealedLowerLayerMajorant n s K M)
    (integrableOn_annealedLowerLayerMajorant n s K M _)
    (fun t ht0 ht => measureReal_lowerLayer_le_majorant n hn s K M hK hKM ht)).trans
      (lowerLayerMajorant_integral_le n s K M hK hKM)

theorem integral_annealed_clippedPositiveIncrement_le
    (n : ℕ) (s : ℝ) (K M : NNReal)
    (hK : 1 ≤ K) (hKM : K ≤ M) :
    (∫ z : ℂ, clippedPositiveIncrement K M z
      ∂(radialAnnealedLaw n s : Measure ℂ)) ≤ (K : ℝ)⁻¹ ^ 2 := by
  let L := Real.log (M : ℝ) - Real.log (K : ℝ)
  exact (integral_clippedPositiveIncrement_le_of_layers
    (radialAnnealedLaw n s : Measure ℂ) id continuous_id.aestronglyMeasurable
    hK hKM (annealedUpperLayerMajorant K)
    (integrableOn_annealedUpperLayerMajorant K L)
    (fun t ht0 ht => measureReal_upperLayer_le_majorant n s K hK ht0.le)).trans
      (upperLayerMajorant_integral_le K L)

/-- The full annealed clipped-log expectation changes by at most the sum of the
explicit upper- and lower-layer envelopes. -/
theorem abs_integral_annealed_clippedLog_sub_le
    (n : ℕ) (hn : 0 < n) (s : ℝ) (K M : NNReal)
    (hK : 1 ≤ K) (hKM : K ≤ M) :
    |(∫ z : ℂ, clippedLog M z ∂(radialAnnealedLaw n s : Measure ℂ)) -
      ∫ z : ℂ, clippedLog K z ∂(radialAnnealedLaw n s : Measure ℂ)| ≤
      (K : ℝ)⁻¹ ^ 2 + Real.exp 1 *
        (2 * Real.sqrt Real.pi * (K : ℝ)⁻¹ +
          (Real.log (M : ℝ) - Real.log (K : ℝ)) *
            annealedLayerError n s M) := by
  let μ : Measure ℂ := radialAnnealedLaw n s
  have hM : 1 ≤ M := hK.trans hKM
  have hclipM : Integrable (clippedLog M) μ := by
    apply Integrable.of_bound (clippedLog_lipschitz M hM).continuous.aestronglyMeasurable
      (Real.log (M : ℝ))
    filter_upwards with z
    simpa [Real.norm_eq_abs] using abs_clippedLog_le_log M hM z
  have hclipK : Integrable (clippedLog K) μ := by
    apply Integrable.of_bound (clippedLog_lipschitz K hK).continuous.aestronglyMeasurable
      (Real.log (K : ℝ))
    filter_upwards with z
    simpa [Real.norm_eq_abs] using abs_clippedLog_le_log K hK z
  have hpint : Integrable (clippedPositiveIncrement K M) μ :=
    integrable_clippedPositiveIncrement μ id continuous_id.aestronglyMeasurable hK hKM
  have hnint : Integrable (clippedNegativeIncrement K M) μ :=
    integrable_clippedNegativeIncrement μ id continuous_id.aestronglyMeasurable hK hKM
  calc
    |(∫ z : ℂ, clippedLog M z ∂μ) - ∫ z : ℂ, clippedLog K z ∂μ| =
        |∫ z : ℂ, (clippedLog M z - clippedLog K z) ∂μ| := by
      rw [integral_sub hclipM hclipK]
    _ ≤ ∫ z : ℂ, |clippedLog M z - clippedLog K z| ∂μ :=
      abs_integral_le_integral_abs
    _ ≤ ∫ z : ℂ, (clippedPositiveIncrement K M z +
        clippedNegativeIncrement K M z) ∂μ := by
      apply integral_mono (hclipM.sub hclipK).abs (hpint.add hnint)
      intro z
      exact abs_clippedLog_sub_le_parts hK hKM z
    _ = (∫ z : ℂ, clippedPositiveIncrement K M z ∂μ) +
        ∫ z : ℂ, clippedNegativeIncrement K M z ∂μ :=
      integral_add hpint hnint
    _ ≤ (K : ℝ)⁻¹ ^ 2 + Real.exp 1 *
        (2 * Real.sqrt Real.pi * (K : ℝ)⁻¹ +
          (Real.log (M : ℝ) - Real.log (K : ℝ)) *
            annealedLayerError n s M) :=
      add_le_add
        (integral_annealed_clippedPositiveIncrement_le n s K M hK hKM)
        (integral_annealed_clippedNegativeIncrement_le n hn s K M hK hKM)

end Erdos522

end AmalgamatedModule115


/-! ===== amalgamated from Research.PowerClippedAnnealedLimit ===== -/

section AmalgamatedModule116


open Filter Topology MeasureTheory ProbabilityTheory

namespace Erdos522

lemma annealedLayerError_power_exact (n : ℕ) (s : ℝ) :
    annealedLayerError n s (radialPowerCutoff n) =
      ((((7 / 24 : ℝ) * Real.exp (4 * |s|)) *
          ((radialPowerCutoff n : ℝ)⁻¹) ^ 12 +
        (2 * (Real.exp (4 * |s|)) ^ 2) *
          ((radialPowerCutoff n : ℝ)⁻¹) ^ 28) *
            circularGaussianFourthNormMoment) +
      (Real.sqrt (Real.exp (4 * |s|)) / 4 *
          circularGaussianSecondNormMoment) *
        ((radialPowerCutoff n : ℝ)⁻¹) ^ 6 := by
  let E : ℝ := Real.exp (4 * |s|)
  have hA := radialPowerCutoff_div_mul_pow_four E n
  have hB := radialPowerCutoff_div_sq_mul_pow_four E n
  have hC := sqrt_div_mul_radialPowerCutoff_sq E (by positivity) n
  unfold annealedLayerError
  change (((7 / 24 : ℝ) * (E / ((n : ℝ) + 1)) +
      2 * (E / ((n : ℝ) + 1)) ^ 2) *
        (radialPowerCutoff n : ℝ) ^ 4 * circularGaussianFourthNormMoment) +
    (Real.sqrt (E / ((n : ℝ) + 1)) / 4 *
      (radialPowerCutoff n : ℝ) ^ 2 * circularGaussianSecondNormMoment) = _
  rw [show ((7 / 24 : ℝ) * (E / ((n : ℝ) + 1)) +
      2 * (E / ((n : ℝ) + 1)) ^ 2) *
        (radialPowerCutoff n : ℝ) ^ 4 =
      (7 / 24 : ℝ) *
          (E / ((n : ℝ) + 1) * (radialPowerCutoff n : ℝ) ^ 4) +
        2 * ((E / ((n : ℝ) + 1)) ^ 2 *
          (radialPowerCutoff n : ℝ) ^ 4) by ring,
    hA, hB, show Real.sqrt (E / ((n : ℝ) + 1)) / 4 *
        (radialPowerCutoff n : ℝ) ^ 2 =
      (Real.sqrt (E / ((n : ℝ) + 1)) *
        (radialPowerCutoff n : ℝ) ^ 2) / 4 by ring,
    hC]
  ring

lemma tendsto_logRatio_mul_radialPowerCutoff_inv_pow
    (K : NNReal) (k : ℕ) (hk : 0 < k) :
    Tendsto (fun n =>
      (Real.log (radialPowerCutoff n : ℝ) - Real.log (K : ℝ)) *
        ((radialPowerCutoff n : ℝ)⁻¹) ^ k) atTop (𝓝 0) := by
  have hlog := tendsto_log_mul_powerCutoff_inv k hk
  have hinv := tendsto_radialPowerCutoff_inv_pow k hk
  have hconst := hinv.const_mul (Real.log (K : ℝ))
  have h := hlog.sub hconst
  convert h using 1
  · funext n
    ring
  · ring

lemma tendsto_logRatio_mul_annealedLayerError (s : ℝ) (K : NNReal) :
    Tendsto (fun n =>
      (Real.log (radialPowerCutoff n : ℝ) - Real.log (K : ℝ)) *
        annealedLayerError n s (radialPowerCutoff n)) atTop (𝓝 0) := by
  let a : ℝ := (7 / 24 : ℝ) * Real.exp (4 * |s|)
  let b : ℝ := 2 * (Real.exp (4 * |s|)) ^ 2
  let d : ℝ := Real.sqrt (Real.exp (4 * |s|)) / 4 *
    circularGaussianSecondNormMoment
  let c4 : ℝ := circularGaussianFourthNormMoment
  have h12 := (tendsto_logRatio_mul_radialPowerCutoff_inv_pow K 12 (by norm_num)).const_mul a
  have h28 := (tendsto_logRatio_mul_radialPowerCutoff_inv_pow K 28 (by norm_num)).const_mul b
  have h6 := (tendsto_logRatio_mul_radialPowerCutoff_inv_pow K 6 (by norm_num)).const_mul d
  have h := ((h12.add h28).mul_const c4).add h6
  have h0 : Tendsto (fun n =>
      (a * ((Real.log (radialPowerCutoff n : ℝ) - Real.log (K : ℝ)) *
          ((radialPowerCutoff n : ℝ)⁻¹) ^ 12) +
       b * ((Real.log (radialPowerCutoff n : ℝ) - Real.log (K : ℝ)) *
          ((radialPowerCutoff n : ℝ)⁻¹) ^ 28)) * c4 +
       d * ((Real.log (radialPowerCutoff n : ℝ) - Real.log (K : ℝ)) *
          ((radialPowerCutoff n : ℝ)⁻¹) ^ 6)) atTop (𝓝 0) := by
    convert h using 1 <;> ring
  apply Tendsto.congr' (Filter.Eventually.of_forall fun n => ?_) h0
  rw [annealedLayerError_power_exact]
  dsimp [a, b, d, c4]
  ring

lemma eventually_fixedCutoff_le_powerCutoff (K : NNReal) :
    ∀ᶠ n : ℕ in atTop, K ≤ radialPowerCutoff n := by
  have h := tendsto_radialPowerCutoff_coe.eventually_ge_atTop (K : ℝ)
  filter_upwards [h] with n hn
  exact_mod_cast hn

noncomputable def layerIntegerCutoff (k : ℕ) : NNReal := (k + 1 : ℕ)

@[simp] lemma coe_layerIntegerCutoff (k : ℕ) :
    (layerIntegerCutoff k : ℝ) = (k : ℝ) + 1 := by
  simp [layerIntegerCutoff]

lemma one_le_layerIntegerCutoff (k : ℕ) : (1 : NNReal) ≤ layerIntegerCutoff k := by
  simp [layerIntegerCutoff]

noncomputable def powerToFixedClippingError (k : ℕ) : ℝ :=
  (layerIntegerCutoff k : ℝ)⁻¹ ^ 2 +
    Real.exp 1 * ((2 * Real.sqrt Real.pi + 1) *
      (layerIntegerCutoff k : ℝ)⁻¹)

lemma tendsto_powerToFixedClippingError :
    Tendsto powerToFixedClippingError atTop (𝓝 0) := by
  have hbase : Tendsto (fun k => (layerIntegerCutoff k : ℝ)) atTop atTop := by
    apply Tendsto.congr' (Filter.Eventually.of_forall fun k =>
      (coe_layerIntegerCutoff k).symm)
    exact tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hinv : Tendsto (fun k => (layerIntegerCutoff k : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hbase
  unfold powerToFixedClippingError
  convert (hinv.pow 2).add
    ((hinv.const_mul (2 * Real.sqrt Real.pi + 1)).const_mul (Real.exp 1))
    using 1 <;> ring

lemma integral_clippedLog_radialAnnealedLaw_eq_cubeAverage
    (n : ℕ) (s : ℝ) (M : NNReal) (hM : 1 ≤ M) :
    (∫ z : ℂ, clippedLog M z ∂(radialAnnealedLaw n s : Measure ℂ)) =
      cubeAverage (radialCubeClippedStatistic n s M) := by
  change (∫ z : ℂ, clippedLog M z
      ∂(radialAnnealedLaw n s : Measure ℂ)) =
    cubeAverage (radialCubeAngularStatistic n s (clippedLog M))
  exact integral_radialAnnealedLaw_eq_cubeAverage n s (clippedLog M)
    (clippedLog_lipschitz M hM).continuous (Real.log (M : ℝ))
    (fun z => by simpa [Real.norm_eq_abs] using abs_clippedLog_le_log M hM z)

lemma eventually_powerClipped_close_fixed
    (s : ℝ) (k : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      |cubeAverage (radialCubeClippedStatistic n s (radialPowerCutoff n)) -
        cubeAverage (radialCubeClippedStatistic n s (layerIntegerCutoff k))| ≤
      powerToFixedClippingError k := by
  let K := layerIntegerCutoff k
  have hK : (1 : NNReal) ≤ K := one_le_layerIntegerCutoff k
  have hKp : 0 < (K : ℝ)⁻¹ := by positivity
  have hres := tendsto_logRatio_mul_annealedLayerError s K
  have hsmall := hres.eventually (Metric.ball_mem_nhds 0 hKp)
  filter_upwards [eventually_fixedCutoff_le_powerCutoff K,
    eventually_ge_atTop 1, hsmall] with n hKM hn hs
  rw [Real.dist_eq, sub_zero] at hs
  have hlayer :
      (Real.log (radialPowerCutoff n : ℝ) - Real.log (K : ℝ)) *
        annealedLayerError n s (radialPowerCutoff n) ≤ (K : ℝ)⁻¹ := by
    exact (le_abs_self _).trans hs.le
  have hbound := abs_integral_annealed_clippedLog_sub_le
    n (Nat.zero_lt_of_lt hn) s K (radialPowerCutoff n) hK hKM
  rw [integral_clippedLog_radialAnnealedLaw_eq_cubeAverage n s K hK,
    integral_clippedLog_radialAnnealedLaw_eq_cubeAverage n s
      (radialPowerCutoff n) (hK.trans hKM)] at hbound
  unfold powerToFixedClippingError
  dsimp [K] at hbound hlayer ⊢
  nlinarith [Real.exp_pos 1, Real.sqrt_nonneg Real.pi]

noncomputable def layerGaussianClippedMean (k : ℕ) : ℝ :=
  ∫ z : ℂ, clippedLog (layerIntegerCutoff k) z
    ∂(circularGaussianLaw : ProbabilityMeasure ℂ)

lemma tendsto_layer_fixedClippedMean (s : ℝ) (k : ℕ) :
    Tendsto (fun n => cubeAverage
      (radialCubeClippedStatistic n s (layerIntegerCutoff k))) atTop
      (𝓝 (layerGaussianClippedMean k)) :=
  tendsto_cubeAverage_radialCubeClippedStatistic s (layerIntegerCutoff k)
    (one_le_layerIntegerCutoff k)

/-- Quantitative layer cake removes the moving-test gap: the power-scale
annealed clipped means converge to one common limit for every radial shift,
without any logarithmic-moment input. -/
theorem exists_common_powerClipped_limit_unconditional :
    ∃ c : ℝ, ∀ s : ℝ,
      Tendsto (fun n => cubeAverage
        (radialCubeClippedStatistic n s (radialPowerCutoff n))) atTop (𝓝 c) := by
  obtain ⟨c, hzero, hgauss⟩ :=
    exists_common_tendsto_of_triangular_approximation
      (fun n => cubeAverage
        (radialCubeClippedStatistic n 0 (radialPowerCutoff n)))
      (fun n k => cubeAverage
        (radialCubeClippedStatistic n 0 (layerIntegerCutoff k)))
      layerGaussianClippedMean powerToFixedClippingError
      tendsto_powerToFixedClippingError (tendsto_layer_fixedClippedMean 0)
      (eventually_powerClipped_close_fixed 0)
  refine ⟨c, fun s => ?_⟩
  obtain ⟨cs, hs, hgausss⟩ :=
    exists_common_tendsto_of_triangular_approximation
      (fun n => cubeAverage
        (radialCubeClippedStatistic n s (radialPowerCutoff n)))
      (fun n k => cubeAverage
        (radialCubeClippedStatistic n s (layerIntegerCutoff k)))
      layerGaussianClippedMean powerToFixedClippingError
      tendsto_powerToFixedClippingError (tendsto_layer_fixedClippedMean s)
      (eventually_powerClipped_close_fixed s)
  have hcs : cs = c := tendsto_nhds_unique hgausss hgauss
  simpa [hcs] using hs

end Erdos522

end AmalgamatedModule116


/-! ===== amalgamated from Research.SummableLogMomentFinalReduction ===== -/

section AmalgamatedModule117


open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace Erdos522

lemma summable_logSecondMoment_bad_of_budget
    (b : ℕ → ℝ) (hb0 : ∀ n, 0 ≤ b n) (hb : Summable b) (s : ℝ)
    (hmoment : ∀ n,
      cubeAverage (fun x : Fin (n + 1) → Bool =>
        (radialCubeLogSecondMoment n s x) ^ 64) ≤
        b n * (((n : ℝ) + 1) ^ 2)) :
    Summable (fun n => cubeProbability {x : Fin (n + 1) → Bool |
      Real.sqrt (radialPowerCutoff n : ℝ) < radialCubeLogSecondMoment n s x}) := by
  apply hb.of_nonneg_of_le
  · intro n
    exact cubeProbability_nonneg' _
  · intro n
    have h := cubeProbability_logSecondMoment_gt_sqrt_cutoff_le
      (b n * (((n : ℝ) + 1) ^ 2)) (mul_nonneg (hb0 n) (sq_nonneg _))
      n s (hmoment n)
    have hden : (0 : ℝ) < ((n : ℝ) + 1) ^ 2 := by positivity
    calc
      cubeProbability {x : Fin (n + 1) → Bool |
          Real.sqrt (radialPowerCutoff n : ℝ) < radialCubeLogSecondMoment n s x} ≤
        b n * (((n : ℝ) + 1) ^ 2) / (((n : ℝ) + 1) ^ 2) := h
      _ = b n := by field_simp

/-- A summable high-log-moment budget gives the quenched coarse envelope. -/
theorem ae_eventually_processLogSecondMoment_le_of_summable_budget
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : ℕ → Ω → Bool) (hξ_meas : ∀ k, Measurable (ξ k))
    (hξ_indep : iIndepFun ξ μ)
    (hξ_fair : ∀ k, μ {ω | ξ k ω = true} = (1 : ENNReal) / 2)
    (b : ℕ → ℝ) (hb0 : ∀ n, 0 ≤ b n) (hb : Summable b) (s : ℝ)
    (hmoment : ∀ n,
      cubeAverage (fun x : Fin (n + 1) → Bool =>
        (radialCubeLogSecondMoment n s x) ^ 64) ≤
        b n * (((n : ℝ) + 1) ^ 2)) :
    ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop,
      processPolynomialLogSecondMoment ξ n s ω ≤
        Real.sqrt (radialPowerCutoff n : ℝ) := by
  let p : ℕ → ℝ := fun n => cubeProbability {x : Fin (n + 1) → Bool |
    Real.sqrt (radialPowerCutoff n : ℝ) < radialCubeLogSecondMoment n s x}
  let q : ℕ → NNReal := fun n => ⟨p n, cubeProbability_nonneg' _⟩
  have hp : Summable p := summable_logSecondMoment_bad_of_budget b hb0 hb s hmoment
  have hq : Summable q := by
    apply NNReal.summable_coe.mp
    have hcoe : (fun n => (q n : ℝ)) = p := by funext n; rfl
    rw [hcoe]
    exact hp
  have hsum : (∑' n : ℕ, μ {ω | Real.sqrt (radialPowerCutoff n : ℝ) <
      processPolynomialLogSecondMoment ξ n s ω}) ≠ ⊤ := by
    have heq : (fun n : ℕ => μ {ω | Real.sqrt (radialPowerCutoff n : ℝ) <
        processPolynomialLogSecondMoment ξ n s ω}) =
        fun n => (q n : ENNReal) := by
      funext n
      rw [measure_processLogSecondMoment_bad_eq μ ξ hξ_meas hξ_indep hξ_fair]
      exact ENNReal.ofReal_eq_coe_nnreal (cubeProbability_nonneg' _)
    rw [heq]
    exact ENNReal.tsum_coe_ne_top_iff_summable.mpr hq
  have hfinite := ae_eventually_notMem hsum
  filter_upwards [hfinite] with ω hω
  filter_upwards [hω] with n hn
  simpa only [Set.mem_setOf_eq, not_lt] using hn

/-- With F-080, the only remaining input is now a summable budget for the 64th
moment of the angular log second moment. -/
theorem erdos522_of_summable_logMoment_budget
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : ℕ → Ω → Bool) (hξ_meas : ∀ k, Measurable (ξ k))
    (hξ_indep : iIndepFun ξ μ)
    (hξ_fair : ∀ k, μ {ω | ξ k ω = true} = (1 : ENNReal) / 2)
    (b : ℕ → ℝ) (hb0 : ∀ n, 0 ≤ b n) (hb : Summable b)
    (hlog : ∀ n s (x : Fin (n + 1) → Bool),
      MemLp
        (circleParameterFunction
          (fun z => rawLog ((radialWeightedSignPolynomial n s x).eval z))) 2
        circleParameterMeasure)
    (hmoment : ∀ n s,
      cubeAverage (fun x : Fin (n + 1) → Bool =>
        (radialCubeLogSecondMoment n s x) ^ 64) ≤
        b n * (((n : ℝ) + 1) ^ 2)) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n => (R ξ n ω : ℝ) / ((n : ℝ) / 2)) atTop (𝓝 1) := by
  obtain ⟨c, hmeans⟩ := exists_common_powerClipped_limit_unconditional
  have hlogMoments : ∀ s : ℝ, ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop,
      MemLp
        (circleParameterFunction
          (fun z => rawLog ((processRadialWeightedSignPolynomial ξ n s ω).eval z))) 2
        circleParameterMeasure ∧
      processPolynomialLogSecondMoment ξ n s ω ≤
        Real.sqrt (radialPowerCutoff n : ℝ) := by
    intro s
    filter_upwards [ae_eventually_processLogSecondMoment_le_of_summable_budget
      μ ξ hξ_meas hξ_indep hξ_fair b hb0 hb s (fun n => hmoment n s)] with ω hm
    filter_upwards [hm] with n hmn
    constructor
    · simpa [processRadialWeightedSignPolynomial] using
        hlog n s (prefixVector ξ (n + 1) ω)
    · exact hmn
  exact erdos522_of_powerClipped_means_and_logMoments
    μ ξ hξ_meas hξ_indep hξ_fair c hmeans hlogMoments

end Erdos522

end AmalgamatedModule117


/-! ===== amalgamated from Research.SubpolynomialLogMomentFinalReduction ===== -/

section AmalgamatedModule118


open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace Erdos522

noncomputable def sqrtGrowthBudget (C : ℝ) (n : ℕ) : ℝ :=
  C * (((n : ℝ) + 1) ^ (-(3 / 2 : ℝ)))

lemma sqrtGrowthBudget_nonneg (C : ℝ) (hC : 0 ≤ C) (n : ℕ) :
    0 ≤ sqrtGrowthBudget C n := by
  unfold sqrtGrowthBudget
  exact mul_nonneg hC (Real.rpow_nonneg (by positivity) _)

lemma summable_sqrtGrowthBudget (C : ℝ) : Summable (sqrtGrowthBudget C) := by
  have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-(3 / 2 : ℝ))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hshift := (summable_nat_add_iff 1).mpr hbase
  apply hshift.mul_left C |>.congr
  intro n
  simp only [sqrtGrowthBudget, Nat.cast_add, Nat.cast_one]

lemma sqrtGrowthBudget_mul_sq (C : ℝ) (n : ℕ) :
    sqrtGrowthBudget C n * (((n : ℝ) + 1) ^ 2) =
      C * Real.sqrt ((n : ℝ) + 1) := by
  let x : ℝ := (n : ℝ) + 1
  have hx : 0 < x := by dsimp [x]; positivity
  unfold sqrtGrowthBudget
  change C * (x ^ (-(3 / 2 : ℝ))) * x ^ 2 = C * Real.sqrt x
  rw [← Real.rpow_natCast]
  rw [mul_assoc]
  rw [← Real.rpow_add hx]
  rw [Real.sqrt_eq_rpow]
  congr 1
  norm_num

/-- It suffices that the joint exponent-128 log moment grow no faster than
`sqrt(n+1)`; in particular any polylogarithmic bound is more than enough. -/
theorem erdos522_of_joint_log_power128_sqrt_growth
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : ℕ → Ω → Bool) (hξ_meas : ∀ k, Measurable (ξ k))
    (hξ_indep : iIndepFun ξ μ)
    (hξ_fair : ∀ k, μ {ω | ξ k ω = true} = (1 : ENNReal) / 2)
    (C : ℝ) (hC : 0 ≤ C)
    (hlog : ∀ n s (x : Fin (n + 1) → Bool),
      MemLp
        (circleParameterFunction
          (fun z => rawLog ((radialWeightedSignPolynomial n s x).eval z))) 2
        circleParameterMeasure)
    (hhighInt : ∀ n s (x : Fin (n + 1) → Bool),
      Integrable
        (fun θ => ((circleParameterFunction
          (fun z => rawLog ((radialWeightedSignPolynomial n s x).eval z)) θ) ^ 2) ^ 64)
        circleParameterMeasure)
    (hjoint : ∀ n s,
      cubeAverage (radialCubeLogPower128Moment n s) ≤
        C * Real.sqrt ((n : ℝ) + 1)) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n => (R ξ n ω : ℝ) / ((n : ℝ) / 2)) atTop (𝓝 1) := by
  have h64 : ∀ n s,
      cubeAverage (fun x : Fin (n + 1) → Bool =>
        (radialCubeLogSecondMoment n s x) ^ 64) ≤
        sqrtGrowthBudget C n * (((n : ℝ) + 1) ^ 2) := by
    intro n s
    rw [sqrtGrowthBudget_mul_sq]
    exact (cubeAverage_mono fun x =>
      radialCubeLogSecondMoment_pow_sixtyFour_le_power128Moment
        n s x (hlog n s x) (hhighInt n s x)).trans (hjoint n s)
  exact erdos522_of_summable_logMoment_budget
    μ ξ hξ_meas hξ_indep hξ_fair (sqrtGrowthBudget C)
    (sqrtGrowthBudget_nonneg C hC) (summable_sqrtGrowthBudget C)
    hlog h64

end Erdos522

end AmalgamatedModule118


/-! ===== amalgamated from Research.SDependentLogMomentFinalReduction ===== -/

section AmalgamatedModule119


open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace Erdos522

/-- The summable log-moment budget may depend on the fixed radial parameter:
quenched convergence is asserted separately for each `s`, so no uniformity in
`s` is needed. -/
theorem erdos522_of_sDependent_summable_logMoment_budget
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : ℕ → Ω → Bool) (hξ_meas : ∀ k, Measurable (ξ k))
    (hξ_indep : iIndepFun ξ μ)
    (hξ_fair : ∀ k, μ {ω | ξ k ω = true} = (1 : ENNReal) / 2)
    (b : ℝ → ℕ → ℝ) (hb0 : ∀ s n, 0 ≤ b s n)
    (hb : ∀ s, Summable (b s))
    (hlog : ∀ n s (x : Fin (n + 1) → Bool),
      MemLp
        (circleParameterFunction
          (fun z => rawLog ((radialWeightedSignPolynomial n s x).eval z))) 2
        circleParameterMeasure)
    (hmoment : ∀ n s,
      cubeAverage (fun x : Fin (n + 1) → Bool =>
        (radialCubeLogSecondMoment n s x) ^ 64) ≤
        b s n * (((n : ℝ) + 1) ^ 2)) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n => (R ξ n ω : ℝ) / ((n : ℝ) / 2)) atTop (𝓝 1) := by
  obtain ⟨c, hmeans⟩ := exists_common_powerClipped_limit_unconditional
  have hlogMoments : ∀ s : ℝ, ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop,
      MemLp
        (circleParameterFunction
          (fun z => rawLog ((processRadialWeightedSignPolynomial ξ n s ω).eval z))) 2
        circleParameterMeasure ∧
      processPolynomialLogSecondMoment ξ n s ω ≤
        Real.sqrt (radialPowerCutoff n : ℝ) := by
    intro s
    filter_upwards [ae_eventually_processLogSecondMoment_le_of_summable_budget
      μ ξ hξ_meas hξ_indep hξ_fair (b s) (hb0 s) (hb s) s
      (fun n => hmoment n s)] with ω hm
    filter_upwards [hm] with n hmn
    constructor
    · simpa [processRadialWeightedSignPolynomial] using
        hlog n s (prefixVector ξ (n + 1) ω)
    · exact hmn
  exact erdos522_of_powerClipped_means_and_logMoments
    μ ξ hξ_meas hξ_indep hξ_fair c hmeans hlogMoments

/-- Accordingly, the `O(sqrt n)` joint 128th-log-moment constant may depend on
`s`; only degree-uniformity for each fixed radial parameter is needed. -/
theorem erdos522_of_sDependent_joint_log_power128_sqrt_growth
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : ℕ → Ω → Bool) (hξ_meas : ∀ k, Measurable (ξ k))
    (hξ_indep : iIndepFun ξ μ)
    (hξ_fair : ∀ k, μ {ω | ξ k ω = true} = (1 : ENNReal) / 2)
    (C : ℝ → ℝ) (hC : ∀ s, 0 ≤ C s)
    (hlog : ∀ n s (x : Fin (n + 1) → Bool),
      MemLp
        (circleParameterFunction
          (fun z => rawLog ((radialWeightedSignPolynomial n s x).eval z))) 2
        circleParameterMeasure)
    (hhighInt : ∀ n s (x : Fin (n + 1) → Bool),
      Integrable
        (fun θ => ((circleParameterFunction
          (fun z => rawLog ((radialWeightedSignPolynomial n s x).eval z)) θ) ^ 2) ^ 64)
        circleParameterMeasure)
    (hjoint : ∀ n s,
      cubeAverage (radialCubeLogPower128Moment n s) ≤
        C s * Real.sqrt ((n : ℝ) + 1)) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n => (R ξ n ω : ℝ) / ((n : ℝ) / 2)) atTop (𝓝 1) := by
  have h64 : ∀ n s,
      cubeAverage (fun x : Fin (n + 1) → Bool =>
        (radialCubeLogSecondMoment n s x) ^ 64) ≤
        sqrtGrowthBudget (C s) n * (((n : ℝ) + 1) ^ 2) := by
    intro n s
    rw [sqrtGrowthBudget_mul_sq]
    exact (cubeAverage_mono fun x =>
      radialCubeLogSecondMoment_pow_sixtyFour_le_power128Moment
        n s x (hlog n s x) (hhighInt n s x)).trans (hjoint n s)
  exact erdos522_of_sDependent_summable_logMoment_budget
    μ ξ hξ_meas hξ_indep hξ_fair
    (fun s => sqrtGrowthBudget (C s))
    (fun s => sqrtGrowthBudget_nonneg (C s) (hC s))
    (fun s => summable_sqrtGrowthBudget (C s)) hlog h64

end Erdos522

end AmalgamatedModule119


/-! ===== amalgamated from Research.LogMomentSmallBallFinalReduction ===== -/

section AmalgamatedModule120


open MeasureTheory ProbabilityTheory Filter Topology

namespace Erdos522

noncomputable def logMomentTruncationScale (n : ℕ) : ℝ :=
  ((n + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 256)

lemma truncationScale_pow128 (n : ℕ) :
    (logMomentTruncationScale n) ^ 128 = Real.sqrt (n + 1 : ℕ) := by
  unfold logMomentTruncationScale
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (by positivity : 0 ≤ ((n + 1 : ℕ) : ℝ))]
  norm_num
  exact (Real.sqrt_eq_rpow _).symm

lemma power_product_le_one (n : ℕ) :
    (((n + 1 : ℕ) : ℝ) ^ (256 : ℝ)) *
      (((n + 1 : ℕ) : ℝ) ^ (-600 : ℝ)) ≤ 1 := by
  let X : ℝ := ((n + 1 : ℕ) : ℝ)
  have hX : 1 ≤ X := by simp [X]
  have hmono : X ^ (-600 : ℝ) ≤ X ^ (-256 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hX (by norm_num)
  calc
    X ^ (256 : ℝ) * X ^ (-600 : ℝ) ≤ X ^ (256 : ℝ) * X ^ (-256 : ℝ) :=
      mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = X ^ ((256 : ℝ) + (-256 : ℝ)) := by
      rw [Real.rpow_add (by positivity)]
    _ = 1 := by norm_num

lemma sqrt_moment_probability_product_le
    (n : ℕ) (D : ℝ) (hD : 0 ≤ D) :
    Real.sqrt (D * (((n + 1 : ℕ) : ℝ) ^ (256 : ℝ))) *
      Real.sqrt (D * (((n + 1 : ℕ) : ℝ) ^ (-600 : ℝ))) ≤ D := by
  have hA : 0 ≤ D * (((n + 1 : ℕ) : ℝ) ^ (256 : ℝ)) := mul_nonneg hD (by positivity)
  rw [← Real.sqrt_mul hA]
  calc
    Real.sqrt ((D * (((n + 1 : ℕ) : ℝ) ^ (256 : ℝ))) *
        (D * (((n + 1 : ℕ) : ℝ) ^ (-600 : ℝ)))) ≤
        Real.sqrt (D ^ 2) := by
      apply Real.sqrt_le_sqrt
      calc
        (D * (((n + 1 : ℕ) : ℝ) ^ (256 : ℝ))) *
            (D * (((n + 1 : ℕ) : ℝ) ^ (-600 : ℝ))) =
            D ^ 2 * ((((n + 1 : ℕ) : ℝ) ^ (256 : ℝ)) *
              (((n + 1 : ℕ) : ℝ) ^ (-600 : ℝ))) := by ring
        _ ≤ D ^ 2 * 1 := mul_le_mul_of_nonneg_left
          (power_product_le_one n) (sq_nonneg D)
        _ = D ^ 2 := mul_one _
    _ = D := Real.sqrt_sq hD

lemma integrable_abslog_pow128_of_pow256
    (n : ℕ) (s : ℝ) (x : Fin (n + 1) → Bool)
    (h256 : Integrable
      (fun θ => (absoluteRawLog
        ((radialWeightedSignPolynomial n s x).eval (circleMap 0 1 θ))) ^ 256)
      circleParameterMeasure) :
    Integrable
      (fun θ => (absoluteRawLog
        ((radialWeightedSignPolynomial n s x).eval (circleMap 0 1 θ))) ^ 128)
      circleParameterMeasure := by
  let a : ℝ → ℝ := fun θ => absoluteRawLog
    ((radialWeightedSignPolynomial n s x).eval (circleMap 0 1 θ))
  have hmeas : Measurable a := by
    unfold a absoluteRawLog rawLog
    fun_prop
  have hg : Integrable (fun θ => 1 + (a θ) ^ 256) circleParameterMeasure :=
    (integrable_const 1).add (by simpa [a] using h256)
  apply hg.mono' (hmeas.pow_const 128).aestronglyMeasurable
  filter_upwards with θ
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (absoluteRawLog_nonneg _) _)]
  have ha : 0 ≤ a θ := absoluteRawLog_nonneg _
  have hy : 0 ≤ (a θ) ^ 128 := pow_nonneg ha _
  have hs := sq_nonneg ((a θ) ^ 128 - 1)
  norm_num [show (a θ) ^ 256 = ((a θ) ^ 128) ^ 2 by ring] at hs ⊢
  nlinarith

lemma integrable_rawlog_sq_of_pow256
    (n : ℕ) (s : ℝ) (x : Fin (n + 1) → Bool)
    (h256 : Integrable
      (fun θ => (absoluteRawLog
        ((radialWeightedSignPolynomial n s x).eval (circleMap 0 1 θ))) ^ 256)
      circleParameterMeasure) :
    Integrable
      (fun θ => (rawLog
        ((radialWeightedSignPolynomial n s x).eval (circleMap 0 1 θ))) ^ 2)
      circleParameterMeasure := by
  let a : ℝ → ℝ := fun θ => absoluteRawLog
    ((radialWeightedSignPolynomial n s x).eval (circleMap 0 1 θ))
  have hmeas : Measurable (fun θ => (rawLog
      ((radialWeightedSignPolynomial n s x).eval (circleMap 0 1 θ))) ^ 2) := by
    unfold rawLog
    fun_prop
  have hg : Integrable (fun θ => 1 + (a θ) ^ 256) circleParameterMeasure :=
    (integrable_const 1).add (by simpa [a] using h256)
  apply hg.mono' hmeas.aestronglyMeasurable
  filter_upwards with θ
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have heq : (rawLog
      ((radialWeightedSignPolynomial n s x).eval (circleMap 0 1 θ))) ^ 2 =
      (a θ) ^ 2 := by simp [a, absoluteRawLog, sq_abs]
  rw [heq]
  have ha : 0 ≤ a θ := absoluteRawLog_nonneg _
  have hy : 0 ≤ (a θ) ^ 2 := pow_nonneg ha _
  have hs := sq_nonneg ((a θ) ^ 127 - 1)
  norm_num [show (a θ) ^ 256 = ((a θ) ^ 128) ^ 2 by ring] at hs ⊢
  by_cases hle : a θ ≤ 1
  · nlinarith [sq_nonneg (a θ)]
  · have hpow : (a θ) ^ 2 ≤ (a θ) ^ 256 := by
      exact pow_le_pow_right₀ (by linarith) (by norm_num)
    linarith

/-- A polynomial 256th-moment bound together with a sufficiently strong
annealed lower-tail estimate implies Erdős #522. -/
theorem erdos522_of_polynomial_logMoment_and_smallBall
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : ℕ → Ω → Bool) (hξ_meas : ∀ k, Measurable (ξ k))
    (hξ_indep : iIndepFun ξ μ)
    (hξ_fair : ∀ k, μ {ω | ξ k ω = true} = (1 : ENNReal) / 2)
    (D : ℝ) (hD : 1 ≤ D)
    (hInt256 : ∀ (n : ℕ) (s : ℝ) (x : Fin (n + 1) → Bool),
      Integrable
        (fun θ => (absoluteRawLog
          ((radialWeightedSignPolynomial n s x).eval (circleMap 0 1 θ))) ^ 256)
        circleParameterMeasure)
    (hMoment256 : ∀ (n : ℕ) (s : ℝ),
      cubeAverage (radialCubeLogPower256Moment n s) ≤
        D * (((n + 1 : ℕ) : ℝ) ^ (256 : ℝ)))
    (hSmall : ∀ (n : ℕ) (s : ℝ),
      (radialAnnealedLaw n s : Measure ℂ)
        {z | ‖z‖ ≤ Real.exp (-(logMomentTruncationScale n))} ≤
      ENNReal.ofReal (D * (((n + 1 : ℕ) : ℝ) ^ (-600 : ℝ)))) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n => (R ξ n ω : ℝ) / ((n : ℝ) / 2)) atTop (𝓝 1) := by
  let C : ℝ := 1 + 64 ^ 128 + D
  have hC : 0 < C := by dsimp [C]; positivity
  apply erdos522_of_joint_log_power128_sqrt_growth
    μ ξ hξ_meas hξ_indep hξ_fair C (le_of_lt hC)
  · intro n s x
    have hmeas : Measurable (circleParameterFunction
        (fun z => rawLog ((radialWeightedSignPolynomial n s x).eval z))) := by
      unfold circleParameterFunction rawLog
      fun_prop
    rw [memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable]
    exact integrable_rawlog_sq_of_pow256 n s x (hInt256 n s x)
  · intro n s x
    have h128 := integrable_abslog_pow128_of_pow256 n s x (hInt256 n s x)
    apply h128.congr
    filter_upwards with θ
    unfold absoluteRawLog
    rw [show |rawLog ((radialWeightedSignPolynomial n s x).eval
      (circleMap 0 1 θ))| ^ 128 =
      (|rawLog ((radialWeightedSignPolynomial n s x).eval
        (circleMap 0 1 θ))| ^ 2) ^ 64 by ring, sq_abs]
    rfl
  · intro n s
    have h128Int : ∀ x : Fin (n + 1) → Bool, Integrable
        (fun θ => (absoluteRawLog
          ((radialWeightedSignPolynomial n s x).eval (circleMap 0 1 θ))) ^ 128)
        circleParameterMeasure := fun x =>
      integrable_abslog_pow128_of_pow256 n s x (hInt256 n s x)
    rw [← integral_absoluteRawLog_pow128_radialAnnealedLaw_eq n s h128Int]
    have hLaw256 : Integrable (fun z : ℂ => (absoluteRawLog z) ^ 256)
        (radialAnnealedLaw n s : Measure ℂ) := by
      apply integrable_radialAnnealedLaw_of_angular n s
        (fun z : ℂ => (absoluteRawLog z) ^ 256)
        (measurable_absoluteRawLog.pow_const 256)
      intro x
      change Integrable
        (fun θ => (absoluteRawLog
          ((radialWeightedSignPolynomial n s x).eval (circleMap 0 1 θ))) ^ 256)
        circleParameterMeasure
      exact hInt256 n s x
    have hLaw256Bound : (∫ z, (absoluteRawLog z) ^ 256
          ∂(radialAnnealedLaw n s : Measure ℂ)) ≤
        D * (((n + 1 : ℕ) : ℝ) ^ (256 : ℝ)) := by
      rw [integral_absoluteRawLog_pow256_radialAnnealedLaw_eq n s (hInt256 n s)]
      exact hMoment256 n s
    have hT : 0 ≤ logMomentTruncationScale n := by
      unfold logMomentTruncationScale
      positivity
    have hMomNonneg : 0 ≤ D * (((n + 1 : ℕ) : ℝ) ^ (256 : ℝ)) :=
      mul_nonneg (le_trans zero_le_one hD) (by positivity)
    have hpNonneg : 0 ≤ D * (((n + 1 : ℕ) : ℝ) ^ (-600 : ℝ)) :=
      mul_nonneg (le_trans zero_le_one hD) (Real.rpow_nonneg (by positivity) _)
    have hNormInt : Integrable (fun z : ℂ => ‖z‖ ^ 2)
        (radialAnnealedLaw n s : Measure ℂ) := by
      apply integrable_radialAnnealedLaw_of_angular n s
        (fun z : ℂ => ‖z‖ ^ 2) (by fun_prop)
      intro x
      apply integrable_circleParameter_of_circleIntegrable
      apply ContinuousOn.circleIntegrable (by norm_num)
      fun_prop
    have hSmallReal : (radialAnnealedLaw n s : Measure ℂ).real
        {z | ‖z‖ ≤ Real.exp (-(logMomentTruncationScale n))} ≤
        D * (((n + 1 : ℕ) : ℝ) ^ (-600 : ℝ)) := by
      unfold Measure.real
      calc
        ((radialAnnealedLaw n s : Measure ℂ)
          {z | ‖z‖ ≤ Real.exp (-(logMomentTruncationScale n))}).toReal ≤
            (ENNReal.ofReal (D * (((n + 1 : ℕ) : ℝ) ^ (-600 : ℝ)))).toReal :=
          ENNReal.toReal_mono (by simp) (hSmall n s)
        _ = D * (((n + 1 : ℕ) : ℝ) ^ (-600 : ℝ)) :=
          ENNReal.toReal_ofReal hpNonneg
    have htrunc := integral_absoluteRawLog_pow_128_le_of_truncation
      (radialAnnealedLaw n s : Measure ℂ)
      (logMomentTruncationScale n)
      (D * (((n + 1 : ℕ) : ℝ) ^ (256 : ℝ)))
      (D * (((n + 1 : ℕ) : ℝ) ^ (-600 : ℝ)))
      hT hMomNonneg hpNonneg hLaw256 hLaw256Bound hNormInt
      (by rw [integral_norm_sq_radialAnnealedLaw_eq_one]) hSmallReal
    calc
      (∫ z, (absoluteRawLog z) ^ 128
          ∂(radialAnnealedLaw n s : Measure ℂ)) ≤
          (logMomentTruncationScale n) ^ 128 + 64 ^ 128 +
            Real.sqrt (D * (((n + 1 : ℕ) : ℝ) ^ (256 : ℝ))) *
            Real.sqrt (D * (((n + 1 : ℕ) : ℝ) ^ (-600 : ℝ))) := htrunc
      _ ≤ Real.sqrt (n + 1 : ℕ) + 64 ^ 128 + D := by
        rw [truncationScale_pow128]
        gcongr
        exact sqrt_moment_probability_product_le n D (le_trans zero_le_one hD)
      _ ≤ C * Real.sqrt (n + 1 : ℕ) := by
        have hsqrt : 1 ≤ Real.sqrt (n + 1 : ℕ) := by
          rw [← Real.sqrt_one]
          exact Real.sqrt_le_sqrt (by simp)
        dsimp [C]
        nlinarith [show 0 ≤ (64 : ℝ) ^ 128 by positivity]
      _ = C * Real.sqrt ((n : ℝ) + 1) := by norm_num

end Erdos522

end AmalgamatedModule120


/-! ===== amalgamated from Research.SDependentMomentSmallBallFinalReduction ===== -/

section AmalgamatedModule121


open MeasureTheory ProbabilityTheory Filter Topology

namespace Erdos522

/-- Radial-parameter-dependent version of F-086.  The constants in the
polynomial moment and small-ball estimates need not be uniform in `s`. -/
theorem erdos522_of_sDependent_polynomial_logMoment_and_smallBall
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : ℕ → Ω → Bool) (hξ_meas : ∀ k, Measurable (ξ k))
    (hξ_indep : iIndepFun ξ μ)
    (hξ_fair : ∀ k, μ {ω | ξ k ω = true} = (1 : ENNReal) / 2)
    (D : ℝ → ℝ) (hD : ∀ s, 1 ≤ D s)
    (hInt256 : ∀ (n : ℕ) (s : ℝ) (x : Fin (n + 1) → Bool),
      Integrable
        (fun θ => (absoluteRawLog
          ((radialWeightedSignPolynomial n s x).eval (circleMap 0 1 θ))) ^ 256)
        circleParameterMeasure)
    (hMoment256 : ∀ (n : ℕ) (s : ℝ),
      cubeAverage (radialCubeLogPower256Moment n s) ≤
        D s * (((n + 1 : ℕ) : ℝ) ^ (256 : ℝ)))
    (hSmall : ∀ (n : ℕ) (s : ℝ),
      (radialAnnealedLaw n s : Measure ℂ)
        {z | ‖z‖ ≤ Real.exp (-(logMomentTruncationScale n))} ≤
      ENNReal.ofReal (D s * (((n + 1 : ℕ) : ℝ) ^ (-600 : ℝ)))) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n => (R ξ n ω : ℝ) / ((n : ℝ) / 2)) atTop (𝓝 1) := by
  let C : ℝ → ℝ := fun s => 1 + 64 ^ 128 + D s
  have hC : ∀ s, 0 ≤ C s := by
    intro s
    dsimp [C]
    nlinarith [hD s, show 0 ≤ (64 : ℝ) ^ 128 by positivity]
  apply erdos522_of_sDependent_joint_log_power128_sqrt_growth
    μ ξ hξ_meas hξ_indep hξ_fair C hC
  · intro n s x
    have hmeas : Measurable (circleParameterFunction
        (fun z => rawLog ((radialWeightedSignPolynomial n s x).eval z))) := by
      unfold circleParameterFunction rawLog
      fun_prop
    rw [memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable]
    exact integrable_rawlog_sq_of_pow256 n s x (hInt256 n s x)
  · intro n s x
    have h128 := integrable_abslog_pow128_of_pow256 n s x (hInt256 n s x)
    apply h128.congr
    filter_upwards with θ
    unfold absoluteRawLog
    rw [show |rawLog ((radialWeightedSignPolynomial n s x).eval
      (circleMap 0 1 θ))| ^ 128 =
      (|rawLog ((radialWeightedSignPolynomial n s x).eval
        (circleMap 0 1 θ))| ^ 2) ^ 64 by ring, sq_abs]
    rfl
  · intro n s
    have h128Int : ∀ x : Fin (n + 1) → Bool, Integrable
        (fun θ => (absoluteRawLog
          ((radialWeightedSignPolynomial n s x).eval (circleMap 0 1 θ))) ^ 128)
        circleParameterMeasure := fun x =>
      integrable_abslog_pow128_of_pow256 n s x (hInt256 n s x)
    rw [← integral_absoluteRawLog_pow128_radialAnnealedLaw_eq n s h128Int]
    have hLaw256 : Integrable (fun z : ℂ => (absoluteRawLog z) ^ 256)
        (radialAnnealedLaw n s : Measure ℂ) := by
      apply integrable_radialAnnealedLaw_of_angular n s
        (fun z : ℂ => (absoluteRawLog z) ^ 256)
        (measurable_absoluteRawLog.pow_const 256)
      intro x
      change Integrable
        (fun θ => (absoluteRawLog
          ((radialWeightedSignPolynomial n s x).eval (circleMap 0 1 θ))) ^ 256)
        circleParameterMeasure
      exact hInt256 n s x
    have hLaw256Bound : (∫ z, (absoluteRawLog z) ^ 256
          ∂(radialAnnealedLaw n s : Measure ℂ)) ≤
        D s * (((n + 1 : ℕ) : ℝ) ^ (256 : ℝ)) := by
      rw [integral_absoluteRawLog_pow256_radialAnnealedLaw_eq n s (hInt256 n s)]
      exact hMoment256 n s
    have hT : 0 ≤ logMomentTruncationScale n := by
      unfold logMomentTruncationScale
      positivity
    have hMomNonneg : 0 ≤ D s * (((n + 1 : ℕ) : ℝ) ^ (256 : ℝ)) :=
      mul_nonneg (le_trans zero_le_one (hD s)) (Real.rpow_nonneg (by positivity) _)
    have hpNonneg : 0 ≤ D s * (((n + 1 : ℕ) : ℝ) ^ (-600 : ℝ)) :=
      mul_nonneg (le_trans zero_le_one (hD s)) (Real.rpow_nonneg (by positivity) _)
    have hNormInt : Integrable (fun z : ℂ => ‖z‖ ^ 2)
        (radialAnnealedLaw n s : Measure ℂ) := by
      apply integrable_radialAnnealedLaw_of_angular n s
        (fun z : ℂ => ‖z‖ ^ 2) (by fun_prop)
      intro x
      apply integrable_circleParameter_of_circleIntegrable
      apply ContinuousOn.circleIntegrable (by norm_num)
      fun_prop
    have hSmallReal : (radialAnnealedLaw n s : Measure ℂ).real
        {z | ‖z‖ ≤ Real.exp (-(logMomentTruncationScale n))} ≤
        D s * (((n + 1 : ℕ) : ℝ) ^ (-600 : ℝ)) := by
      unfold Measure.real
      calc
        ((radialAnnealedLaw n s : Measure ℂ)
          {z | ‖z‖ ≤ Real.exp (-(logMomentTruncationScale n))}).toReal ≤
            (ENNReal.ofReal (D s * (((n + 1 : ℕ) : ℝ) ^ (-600 : ℝ)))).toReal :=
          ENNReal.toReal_mono (by simp) (hSmall n s)
        _ = D s * (((n + 1 : ℕ) : ℝ) ^ (-600 : ℝ)) :=
          ENNReal.toReal_ofReal hpNonneg
    have htrunc := integral_absoluteRawLog_pow_128_le_of_truncation
      (radialAnnealedLaw n s : Measure ℂ)
      (logMomentTruncationScale n)
      (D s * (((n + 1 : ℕ) : ℝ) ^ (256 : ℝ)))
      (D s * (((n + 1 : ℕ) : ℝ) ^ (-600 : ℝ)))
      hT hMomNonneg hpNonneg hLaw256 hLaw256Bound hNormInt
      (by rw [integral_norm_sq_radialAnnealedLaw_eq_one]) hSmallReal
    calc
      (∫ z, (absoluteRawLog z) ^ 128
          ∂(radialAnnealedLaw n s : Measure ℂ)) ≤
          (logMomentTruncationScale n) ^ 128 + 64 ^ 128 +
            Real.sqrt (D s * (((n + 1 : ℕ) : ℝ) ^ (256 : ℝ))) *
            Real.sqrt (D s * (((n + 1 : ℕ) : ℝ) ^ (-600 : ℝ))) := htrunc
      _ ≤ Real.sqrt (n + 1 : ℕ) + 64 ^ 128 + D s := by
        rw [truncationScale_pow128]
        gcongr
        exact sqrt_moment_probability_product_le n (D s)
          (le_trans zero_le_one (hD s))
      _ ≤ C s * Real.sqrt (n + 1 : ℕ) := by
        have hsqrt : 1 ≤ Real.sqrt (n + 1 : ℕ) := by
          rw [← Real.sqrt_one]
          exact Real.sqrt_le_sqrt (by simp)
        dsimp [C]
        nlinarith [hD s, show 0 ≤ (64 : ℝ) ^ 128 by positivity]
      _ = C s * Real.sqrt ((n : ℝ) + 1) := by norm_num

end Erdos522

end AmalgamatedModule121


/-! ===== amalgamated from Research.InverseCircleKernel ===== -/

section AmalgamatedModule122


open MeasureTheory
open scoped Interval

namespace Erdos522

noncomputable def inverseCircleMajorant (θ : ℝ) : ℝ :=
  2 + 2 * (θ ^ (-(1 : ℝ) / 2) +
    (2 * Real.pi - θ) ^ (-(1 : ℝ) / 2))

lemma intervalIntegrable_inverseCircleMajorant :
    IntervalIntegrable inverseCircleMajorant volume 0 (2 * Real.pi) := by
  have hp : IntervalIntegrable (fun θ : ℝ => θ ^ (-(1 : ℝ) / 2))
      volume 0 (2 * Real.pi) := by
    apply intervalIntegral.intervalIntegrable_rpow'
    norm_num
  have hr : IntervalIntegrable
      (fun θ : ℝ => (2 * Real.pi - θ) ^ (-(1 : ℝ) / 2))
      volume 0 (2 * Real.pi) := by
    have h := hp.comp_sub_left (2 * Real.pi)
    norm_num at h ⊢
    exact h.symm
  unfold inverseCircleMajorant
  have hc : IntervalIntegrable (fun _ : ℝ => (2 : ℝ))
      volume 0 (2 * Real.pi) := intervalIntegrable_const
  exact hc.add ((hp.add hr).const_mul 2)

lemma inverseCircleMajorant_nonneg {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ2 : θ ≤ 2 * Real.pi) :
    0 ≤ inverseCircleMajorant θ := by
  unfold inverseCircleMajorant
  positivity

private lemma radial_circle_norm_sq (r θ : ℝ) :
    ‖circleMap 0 1 θ - (r : ℂ)‖ ^ 2 =
      (1 - r) ^ 2 + 2 * r * (1 - Real.cos θ) := by
  rw [Complex.sq_norm]
  simp [circleMap, Complex.normSq_apply, Complex.exp_mul_I]
  ring_nf
  rw [Complex.cos_ofReal_re, Complex.sin_ofReal_re, Real.sin_sq]
  ring

private lemma rpow_neg_half_antitone {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    b ^ (-(1 : ℝ) / 2) ≤ a ^ (-(1 : ℝ) / 2) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hp := Real.rpow_le_rpow ha.le hab (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [show (-(1 : ℝ) / 2) = -((1 : ℝ) / 2) by ring,
    Real.rpow_neg hb.le, Real.rpow_neg ha.le]
  exact (inv_le_inv₀ (Real.rpow_pos_of_pos hb _) (Real.rpow_pos_of_pos ha _)).2 hp

private lemma div_four_rpow_neg_half (x : ℝ) (hx : 0 < x) :
    (x / 4) ^ (-(1 : ℝ) / 2) = 2 * x ^ (-(1 : ℝ) / 2) := by
  rw [div_eq_mul_inv, Real.mul_rpow (le_of_lt hx) (by positivity)]
  have hfour : (4⁻¹ : ℝ) ^ (-(1 : ℝ) / 2) = 2 := by
    rw [show (-(1 : ℝ) / 2) = -((1 : ℝ) / 2) by ring]
    rw [Real.rpow_neg (by norm_num)]
    rw [← Real.sqrt_eq_rpow]
    norm_num
  rw [hfour]
  ring

private lemma radial_inverse_kernel_le_left
    {r θ : ℝ} (hr0 : 1 / 2 ≤ r) (hr2 : r ≤ 2)
    (hθ0 : 0 < θ) (hθπ : θ ≤ Real.pi) :
    ‖circleMap 0 1 θ - (r : ℂ)‖ ^ (-(1 : ℝ) / 2) ≤
      2 * θ ^ (-(1 : ℝ) / 2) := by
  have hθhalf0 : 0 ≤ θ / 2 := by positivity
  have hθhalfπ : θ / 2 ≤ Real.pi / 2 := by linarith
  have hsin := Real.mul_le_sin hθhalf0 hθhalfπ
  have hpi4 : Real.pi ≤ 4 := Real.pi_le_four
  have hθpi : θ / 4 ≤ θ / Real.pi := by
    exact (div_le_div_iff_of_pos_left hθ0 (by norm_num) Real.pi_pos).2 hpi4
  have hsin' : θ / 4 ≤ Real.sin (θ / 2) := by
    calc
      θ / 4 ≤ θ / Real.pi := hθpi
      _ = 2 / Real.pi * (θ / 2) := by ring
      _ ≤ Real.sin (θ / 2) := hsin
  have hsin0 : 0 ≤ Real.sin (θ / 2) := le_trans (by positivity) hsin'
  have hcos : (θ / 4) ^ 2 ≤ 1 - Real.cos θ := by
    rw [show 1 - Real.cos θ = 2 * (Real.sin (θ / 2)) ^ 2 by
      rw [show θ = 2 * (θ / 2) by ring, Real.cos_two_mul, Real.sin_sq]
      ring]
    nlinarith [sq_nonneg (Real.sin (θ / 2) - θ / 4)]
  have hnormsq : (θ / 4) ^ 2 ≤ ‖circleMap 0 1 θ - (r : ℂ)‖ ^ 2 := by
    rw [radial_circle_norm_sq]
    have hmul : 1 - Real.cos θ ≤ 2 * r * (1 - Real.cos θ) := by
      have hc : 0 ≤ 1 - Real.cos θ := sub_nonneg.mpr (Real.cos_le_one θ)
      nlinarith
    nlinarith [sq_nonneg (1 - r)]
  have hnorm : θ / 4 ≤ ‖circleMap 0 1 θ - (r : ℂ)‖ := by
    have hleft : 0 ≤ θ / 4 := by positivity
    have hright : 0 ≤ ‖circleMap 0 1 θ - (r : ℂ)‖ := norm_nonneg _
    nlinarith [sq_nonneg (‖circleMap 0 1 θ - (r : ℂ)‖ - θ / 4)]
  calc
    ‖circleMap 0 1 θ - (r : ℂ)‖ ^ (-(1 : ℝ) / 2) ≤
        (θ / 4) ^ (-(1 : ℝ) / 2) :=
      rpow_neg_half_antitone (by positivity) hnorm
    _ = 2 * θ ^ (-(1 : ℝ) / 2) := div_four_rpow_neg_half θ hθ0

private lemma radial_circle_norm_two_pi_sub (r θ : ℝ) :
    ‖circleMap 0 1 (2 * Real.pi - θ) - (r : ℂ)‖ =
      ‖circleMap 0 1 θ - (r : ℂ)‖ := by
  have h1 := radial_circle_norm_sq r (2 * Real.pi - θ)
  have h2 := radial_circle_norm_sq r θ
  rw [Real.cos_two_pi_sub] at h1
  have hsq : ‖circleMap 0 1 (2 * Real.pi - θ) - (r : ℂ)‖ ^ 2 =
      ‖circleMap 0 1 θ - (r : ℂ)‖ ^ 2 := h1.trans h2.symm
  nlinarith [norm_nonneg (circleMap 0 1 (2 * Real.pi - θ) - (r : ℂ)),
    norm_nonneg (circleMap 0 1 θ - (r : ℂ))]

private lemma radial_inverse_kernel_le_majorant
    {r θ : ℝ} (hr0 : 1 / 2 ≤ r) (hr2 : r ≤ 2)
    (hθ0 : 0 < θ) (hθ2 : θ < 2 * Real.pi) :
    ‖circleMap 0 1 θ - (r : ℂ)‖ ^ (-(1 : ℝ) / 2) ≤
      inverseCircleMajorant θ := by
  unfold inverseCircleMajorant
  by_cases hθπ : θ ≤ Real.pi
  · have h := radial_inverse_kernel_le_left hr0 hr2 hθ0 hθπ
    have hother : 0 ≤ (2 * Real.pi - θ) ^ (-(1 : ℝ) / 2) :=
      Real.rpow_nonneg (by positivity) _
    nlinarith
  · let u := 2 * Real.pi - θ
    have hu0 : 0 < u := by dsimp [u]; linarith
    have huπ : u ≤ Real.pi := by dsimp [u]; nlinarith [Real.pi_pos]
    have h := radial_inverse_kernel_le_left hr0 hr2 hu0 huπ
    rw [radial_circle_norm_two_pi_sub r θ] at h
    have hfirst : 0 ≤ θ ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg (le_of_lt hθ0) _
    dsimp [u] at h
    nlinarith

private lemma rpow_neg_half_le_two_of_half_le {d : ℝ} (hd : 1 / 2 ≤ d) :
    d ^ (-(1 : ℝ) / 2) ≤ 2 := by
  calc
    d ^ (-(1 : ℝ) / 2) ≤ (1 / 2 : ℝ) ^ (-(1 : ℝ) / 2) :=
      rpow_neg_half_antitone (by norm_num) hd
    _ ≤ (1 / 4 : ℝ) ^ (-(1 : ℝ) / 2) :=
      rpow_neg_half_antitone (by norm_num) (by norm_num)
    _ = 2 := by
      rw [show (-(1 : ℝ) / 2) = -((1 : ℝ) / 2) by ring]
      rw [Real.rpow_neg (by norm_num)]
      rw [← Real.sqrt_eq_rpow]
      norm_num

private lemma radial_inverse_kernel_le_majorant_all
    {r θ : ℝ} (hr : 0 ≤ r) (hθ0 : 0 < θ) (hθ2 : θ < 2 * Real.pi) :
    ‖circleMap 0 1 θ - (r : ℂ)‖ ^ (-(1 : ℝ) / 2) ≤
      inverseCircleMajorant θ := by
  by_cases hr0 : 1 / 2 ≤ r
  · by_cases hr2 : r ≤ 2
    · exact radial_inverse_kernel_le_majorant hr0 hr2 hθ0 hθ2
    · have hdist : 1 / 2 ≤ ‖circleMap 0 1 θ - (r : ℂ)‖ := by
        have hrev := norm_sub_norm_le (r : ℂ) (circleMap 0 1 θ)
        rw [Complex.norm_real, Real.norm_of_nonneg hr, norm_circleMap_zero,
          abs_one, norm_sub_rev] at hrev
        linarith
      have hk := rpow_neg_half_le_two_of_half_le hdist
      have hmaj : 2 ≤ inverseCircleMajorant θ := by
        unfold inverseCircleMajorant
        have h1 : 0 ≤ θ ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg (le_of_lt hθ0) _
        have h2 : 0 ≤ (2 * Real.pi - θ) ^ (-(1 : ℝ) / 2) :=
          Real.rpow_nonneg (by linarith) _
        linarith
      exact hk.trans hmaj
  · have hdist : 1 / 2 ≤ ‖circleMap 0 1 θ - (r : ℂ)‖ := by
      have hrev := norm_sub_norm_le (circleMap 0 1 θ) (r : ℂ)
      rw [norm_circleMap_zero, abs_one, Complex.norm_real,
        Real.norm_of_nonneg hr] at hrev
      linarith
    have hk := rpow_neg_half_le_two_of_half_le hdist
    have hmaj : 2 ≤ inverseCircleMajorant θ := by
      unfold inverseCircleMajorant
      have h1 : 0 ≤ θ ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg (le_of_lt hθ0) _
      have h2 : 0 ≤ (2 * Real.pi - θ) ^ (-(1 : ℝ) / 2) :=
        Real.rpow_nonneg (by linarith) _
      linarith
    exact hk.trans hmaj

private lemma circle_rotation_norm (β : ℂ) (θ : ℝ) :
    ‖circleMap 0 1 (θ + β.arg) - β‖ =
      ‖circleMap 0 1 θ - (‖β‖ : ℂ)‖ := by
  let φ : ℝ := β.arg
  let r : ℝ := ‖β‖
  have hβ : (r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I) = β := by
    simpa [r, φ] using Complex.norm_mul_exp_arg_mul_I β
  change ‖circleMap 0 1 (θ + φ) - β‖ = ‖circleMap 0 1 θ - (r : ℂ)‖
  rw [← hβ]
  simp only [circleMap_zero, Complex.ofReal_one, one_mul, Complex.ofReal_add,
    add_mul, Complex.exp_add]
  rw [← sub_mul, Complex.norm_mul, Complex.norm_exp]
  simp

private lemma intervalIntegrable_radial_inverse_kernel (r : ℝ) (hr : 0 ≤ r) :
    IntervalIntegrable
      (fun θ => ‖circleMap 0 1 θ - (r : ℂ)‖ ^ (-(1 : ℝ) / 2))
      volume 0 (2 * Real.pi) := by
  let f : ℝ → ℝ := fun θ =>
    ‖circleMap 0 1 θ - (r : ℂ)‖ ^ (-(1 : ℝ) / 2)
  let g : ℝ → ℝ := inverseCircleMajorant
  have hg : Integrable g (volume.restrict (Set.Ioc 0 (2 * Real.pi))) := by
    simpa [g, IntegrableOn, Set.uIoc_of_le
      (by positivity : (0 : ℝ) ≤ 2 * Real.pi)] using
      (intervalIntegrable_iff.mp intervalIntegrable_inverseCircleMajorant)
  have hfmeas : AEStronglyMeasurable f
      (volume.restrict (Set.Ioc 0 (2 * Real.pi))) := by
    apply Measurable.aestronglyMeasurable
    dsimp [f]
    fun_prop
  have hne_global : ∀ᵐ θ : ℝ ∂volume, θ ≠ 2 * Real.pi := by
    rw [ae_iff]
    simpa using (Real.volume_singleton (a := 2 * Real.pi))
  have hne : ∀ᵐ θ : ℝ ∂volume.restrict (Set.Ioc 0 (2 * Real.pi)),
      θ ≠ 2 * Real.pi :=
    (ae_restrict_le : ae (volume.restrict (Set.Ioc 0 (2 * Real.pi))) ≤ ae volume)
      hne_global
  have hle : ∀ᵐ θ : ℝ ∂volume.restrict (Set.Ioc 0 (2 * Real.pi)),
      f θ ≤ g θ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc, hne] with θ hθ hneθ
    exact radial_inverse_kernel_le_majorant_all hr hθ.1 (lt_of_le_of_ne hθ.2 hneθ)
  have hf : Integrable f (volume.restrict (Set.Ioc 0 (2 * Real.pi))) := by
    apply hg.mono' hfmeas
    filter_upwards [hle] with θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact hθ
  apply intervalIntegrable_iff.mpr
  simpa [f, IntegrableOn, Set.uIoc_of_le
    (by positivity : (0 : ℝ) ≤ 2 * Real.pi)] using hf

private lemma intervalIntegral_radial_inverse_kernel_le (r : ℝ) (hr : 0 ≤ r) :
    (∫ θ in 0..2 * Real.pi,
      ‖circleMap 0 1 θ - (r : ℂ)‖ ^ (-(1 : ℝ) / 2)) ≤
      ∫ θ in 0..2 * Real.pi, inverseCircleMajorant θ := by
  let f : ℝ → ℝ := fun θ =>
    ‖circleMap 0 1 θ - (r : ℂ)‖ ^ (-(1 : ℝ) / 2)
  let g : ℝ → ℝ := inverseCircleMajorant
  have hfI := intervalIntegrable_radial_inverse_kernel r hr
  have hgI := intervalIntegrable_inverseCircleMajorant
  have hf : Integrable f (volume.restrict (Set.Ioc 0 (2 * Real.pi))) := by
    simpa [f, IntegrableOn, Set.uIoc_of_le
      (by positivity : (0 : ℝ) ≤ 2 * Real.pi)] using
      (intervalIntegrable_iff.mp hfI)
  have hg : Integrable g (volume.restrict (Set.Ioc 0 (2 * Real.pi))) := by
    simpa [g, IntegrableOn, Set.uIoc_of_le
      (by positivity : (0 : ℝ) ≤ 2 * Real.pi)] using
      (intervalIntegrable_iff.mp hgI)
  have hne_global : ∀ᵐ θ : ℝ ∂volume, θ ≠ 2 * Real.pi := by
    rw [ae_iff]
    simpa using (Real.volume_singleton (a := 2 * Real.pi))
  have hne : ∀ᵐ θ : ℝ ∂volume.restrict (Set.Ioc 0 (2 * Real.pi)),
      θ ≠ 2 * Real.pi :=
    (ae_restrict_le : ae (volume.restrict (Set.Ioc 0 (2 * Real.pi))) ≤ ae volume)
      hne_global
  have hle : f ≤ᵐ[volume.restrict (Set.Ioc 0 (2 * Real.pi))] g := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc, hne] with θ hθ hneθ
    exact radial_inverse_kernel_le_majorant_all hr hθ.1 (lt_of_le_of_ne hθ.2 hneθ)
  rw [intervalIntegral.integral_of_le (by positivity),
    intervalIntegral.integral_of_le (by positivity)]
  exact integral_mono_ae hf hg hle

noncomputable def inverseCircleKernelBound : ℝ :=
  (2 * Real.pi)⁻¹ *
    ∫ θ in 0..2 * Real.pi, inverseCircleMajorant θ

lemma inverseCircleKernelBound_nonneg : 0 ≤ inverseCircleKernelBound := by
  unfold inverseCircleKernelBound
  apply mul_nonneg (inv_nonneg.mpr (by positivity))
  apply intervalIntegral.integral_nonneg (by positivity)
  intro θ hθ
  exact inverseCircleMajorant_nonneg hθ.1 hθ.2

lemma circleIntegrable_inverse_sqrt_distance (β : ℂ) :
    CircleIntegrable (fun z => ‖z - β‖ ^ (-(1 : ℝ) / 2)) 0 1 := by
  let q : ℝ → ℝ := fun θ =>
    ‖circleMap 0 1 θ - β‖ ^ (-(1 : ℝ) / 2)
  have hshift : IntervalIntegrable (fun θ => q (θ + β.arg))
      volume 0 (2 * Real.pi) := by
    have hr := intervalIntegrable_radial_inverse_kernel ‖β‖ (norm_nonneg β)
    apply hr.congr
    intro θ hθ
    dsimp [q]
    rw [circle_rotation_norm]
  have hperiodic : Function.Periodic q (2 * Real.pi) := by
    have h := (periodic_circleMap 0 1).comp
      (fun z : ℂ => ‖z - β‖ ^ (-(1 : ℝ) / 2))
    simpa [q, Function.comp_def] using h
  have hqshift : IntervalIntegrable q volume β.arg (β.arg + 2 * Real.pi) := by
    have h := hshift.comp_sub_right β.arg
    convert h using 1
    · funext θ
      dsimp [q]
      congr 3
      ring
    · ring
    · ring
  rw [circleIntegrable_def]
  apply hperiodic.intervalIntegrable (by positivity) hqshift

lemma circleAverage_inverse_sqrt_distance_le (β : ℂ) :
    Real.circleAverage (fun z => ‖z - β‖ ^ (-(1 : ℝ) / 2)) 0 1 ≤
      inverseCircleKernelBound := by
  rw [Real.circleAverage_eq_integral_add (η := β.arg)]
  unfold inverseCircleKernelBound
  simp only [smul_eq_mul]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (by positivity))
  have hrad := intervalIntegral_radial_inverse_kernel_le ‖β‖ (norm_nonneg β)
  calc
    (∫ θ in 0..2 * Real.pi,
        ‖circleMap 0 1 (θ + β.arg) - β‖ ^ (-(1 : ℝ) / 2)) =
        ∫ θ in 0..2 * Real.pi,
          ‖circleMap 0 1 θ - (‖β‖ : ℂ)‖ ^ (-(1 : ℝ) / 2) := by
      apply intervalIntegral.integral_congr
      intro θ hθ
      dsimp
      rw [circle_rotation_norm]
    _ ≤ ∫ θ in 0..2 * Real.pi, inverseCircleMajorant θ := hrad

end Erdos522

end AmalgamatedModule122


/-! ===== amalgamated from Research.FiniteHolderProduct ===== -/

section AmalgamatedModule123


open MeasureTheory
open scoped BigOperators ENNReal

namespace Erdos522

lemma lintegral_fin_product_rpow_inv_le
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (N : ℕ) (hN : 0 < N)
    (f : Fin N → α → ℝ≥0∞)
    (hf : ∀ i, AEMeasurable (f i) μ)
    (K : ℝ≥0∞) (hK : ∀ i, ∫⁻ x, f i x ∂μ ≤ K) :
    (∫⁻ x, ∏ i : Fin N, (f i x) ^ ((N : ℝ)⁻¹) ∂μ) ≤ K := by
  have hsum : ∑ i : Fin N, ((N : ℝ)⁻¹) = 1 := by
    simp [hN.ne']
  have hh := ENNReal.lintegral_prod_norm_pow_le
    (Finset.univ : Finset (Fin N))
    (fun i hi => hf i) hsum (fun i hi => by positivity)
  calc
    (∫⁻ x, ∏ i : Fin N, (f i x) ^ ((N : ℝ)⁻¹) ∂μ) ≤
        ∏ i : Fin N, (∫⁻ x, f i x ∂μ) ^ ((N : ℝ)⁻¹) := by
      simpa using hh
    _ ≤ ∏ _i : Fin N, K ^ ((N : ℝ)⁻¹) := by
      gcongr with i
      exact hK i
    _ = K := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [← ENNReal.rpow_natCast]
      rw [← ENNReal.rpow_mul]
      simp [hN.ne']

lemma lintegral_fin_product_rpow_inv_le_of_card_le
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (N d : ℕ) (hN : 0 < N) (hd : d ≤ N)
    (f : Fin d → α → ℝ≥0∞) (hf : ∀ i, AEMeasurable (f i) μ)
    (K : ℝ≥0∞) (hK1 : 1 ≤ K) (hK : ∀ i, ∫⁻ x, f i x ∂μ ≤ K) :
    (∫⁻ x, ∏ i : Fin d, (f i x) ^ ((N : ℝ)⁻¹) ∂μ) ≤ K := by
  let q : ℝ := 1 - (d : ℝ) / N
  have hsum : q + ∑ i : Fin d, ((N : ℝ)⁻¹) = 1 := by
    dsimp [q]
    simp
    field_simp
    ring
  have hq : 0 ≤ q := by
    dsimp [q]
    rw [sub_nonneg, div_le_one (by positivity)]
    exact_mod_cast hd
  have hh := ENNReal.lintegral_mul_prod_norm_pow_le
    (Finset.univ : Finset (Fin d))
    (g := fun _ => 1) (f := f)
    (by fun_prop) (fun i hi => hf i) q hsum hq (fun i hi => by positivity)
  have hmain : (∫⁻ x, ∏ i : Fin d, (f i x) ^ ((N : ℝ)⁻¹) ∂μ) ≤
      ∏ i : Fin d, (∫⁻ x, f i x ∂μ) ^ ((N : ℝ)⁻¹) := by
    simpa using hh
  calc
    _ ≤ ∏ i : Fin d, (∫⁻ x, f i x ∂μ) ^ ((N : ℝ)⁻¹) := hmain
    _ ≤ ∏ _i : Fin d, K ^ ((N : ℝ)⁻¹) := by
      gcongr with i
      exact hK i
    _ = K ^ ((d : ℝ) / N) := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      congr 1
      field_simp
    _ ≤ K := by
      have he : (d : ℝ) / N ≤ 1 := by
        rw [div_le_one (by positivity)]
        exact_mod_cast hd
      have hh := ENNReal.rpow_le_rpow_of_exponent_le hK1 he
      simpa only [ENNReal.rpow_one] using hh

end Erdos522

end AmalgamatedModule123


/-! ===== amalgamated from Research.ListInverseCircleProduct ===== -/

section AmalgamatedModule124


open MeasureTheory
open scoped BigOperators ENNReal

namespace Erdos522

lemma integrable_circleParameter_inverse_sqrt_distance (β : ℂ) :
    Integrable
      (fun θ => ‖circleMap 0 1 θ - β‖ ^ (-(1 : ℝ) / 2))
      circleParameterMeasure := by
  have hi := circleIntegrable_inverse_sqrt_distance β
  rw [circleIntegrable_def, intervalIntegrable_iff] at hi
  unfold circleParameterMeasure
  apply hi.smul_measure
  rw [ENNReal.inv_ne_top]
  simp only [Measure.restrict_apply_univ, Real.volume_uIoc, sub_zero]
  exact ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))

lemma integral_circleParameter_inverse_sqrt_distance_le (β : ℂ) :
    (∫ θ, ‖circleMap 0 1 θ - β‖ ^ (-(1 : ℝ) / 2)
      ∂circleParameterMeasure) ≤ inverseCircleKernelBound := by
  change (∫ θ, circleParameterFunction
    (fun z => ‖z - β‖ ^ (-(1 : ℝ) / 2)) θ ∂circleParameterMeasure) ≤ _
  rw [← circleAverage_eq_integral_circleParameterMeasure]
  exact circleAverage_inverse_sqrt_distance_le β

noncomputable def inverseCircleKernelENNBound : ℝ≥0∞ :=
  ENNReal.ofReal (max 1 inverseCircleKernelBound)

lemma one_le_inverseCircleKernelENNBound : 1 ≤ inverseCircleKernelENNBound := by
  unfold inverseCircleKernelENNBound
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (le_max_left _ _)

lemma lintegral_circleParameter_inverse_sqrt_distance_le (β : ℂ) :
    (∫⁻ θ, ENNReal.ofReal
      (‖circleMap 0 1 θ - β‖ ^ (-(1 : ℝ) / 2))
      ∂circleParameterMeasure) ≤ inverseCircleKernelENNBound := by
  have hi := integrable_circleParameter_inverse_sqrt_distance β
  have hnonneg : 0 ≤ᵐ[circleParameterMeasure]
      (fun θ => ‖circleMap 0 1 θ - β‖ ^ (-(1 : ℝ) / 2)) := by
    filter_upwards with θ
    exact Real.rpow_nonneg (norm_nonneg _) _
  rw [← ofReal_integral_eq_lintegral_ofReal hi hnonneg]
  unfold inverseCircleKernelENNBound
  apply ENNReal.ofReal_le_ofReal
  exact (integral_circleParameter_inverse_sqrt_distance_le β).trans
    (le_max_right _ _)

noncomputable def listCircleDistanceProduct (l : List ℂ) (θ : ℝ) : ℝ :=
  (l.map fun β => ‖circleMap 0 1 θ - β‖).prod

lemma listCircleDistanceProduct_nonneg (l : List ℂ) (θ : ℝ) :
    0 ≤ listCircleDistanceProduct l θ := by
  induction l with
  | nil => simp [listCircleDistanceProduct]
  | cons β l ih =>
      simp only [listCircleDistanceProduct, List.map_cons, List.prod_cons]
      exact mul_nonneg (norm_nonneg _) (by simpa [listCircleDistanceProduct] using ih)

lemma measurable_listCircleDistanceProduct (l : List ℂ) :
    Measurable (listCircleDistanceProduct l) := by
  unfold listCircleDistanceProduct
  induction l with
  | nil => simp
  | cons β l ih =>
      simp only [List.map_cons, List.prod_cons]
      exact (by fun_prop : Measurable (fun θ => ‖circleMap 0 1 θ - β‖)).mul ih

lemma measurable_rpow_of_measurable_nonneg
    {α : Type*} [MeasurableSpace α] (f : α → ℝ) (p : ℝ)
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) :
    Measurable (fun x => (f x) ^ p) := by
  by_cases hp : p = 0
  · subst p
    simp
  · have heq : (fun x => (f x) ^ p) = fun x =>
        if f x = 0 then 0 else Real.exp (Real.log (f x) * p) := by
      funext x
      rw [Real.rpow_def_of_nonneg (hf0 x)]
      simp [hp]
    rw [heq]
    exact Measurable.ite (measurableSet_eq_fun hf measurable_const)
      measurable_const ((Real.measurable_log.comp hf).mul measurable_const).exp

lemma listCircleDistanceProduct_rpow_eq
    (l : List ℂ) (N : ℕ) (hN : 0 < N) (θ : ℝ) :
    (listCircleDistanceProduct l θ) ^ (-(1 : ℝ) / (2 * N)) =
      ∏ i : Fin l.length,
        (‖circleMap 0 1 θ - l.get i‖ ^ (-(1 : ℝ) / 2)) ^ ((N : ℝ)⁻¹) := by
  let d : Fin l.length → ℝ := fun i => ‖circleMap 0 1 θ - l.get i‖
  have hd (i : Fin l.length) : 0 ≤ d i := norm_nonneg _
  have hprod : listCircleDistanceProduct l θ = ∏ i : Fin l.length, d i := by
    unfold listCircleDistanceProduct
    rw [← List.prod_ofFn]
    congr 1
    calc
      List.map (fun β => ‖circleMap 0 1 θ - β‖) l =
          List.map (fun β => ‖circleMap 0 1 θ - β‖) (List.ofFn l.get) := by
        rw [List.ofFn_get]
      _ = List.ofFn d := by rw [List.map_ofFn]; rfl
  rw [hprod]
  rw [Real.finset_prod_rpow Finset.univ (fun i => d i ^ (-(1 : ℝ) / 2))
      (fun i hi => Real.rpow_nonneg (hd i) _) ((N : ℝ)⁻¹)]
  rw [Real.finset_prod_rpow Finset.univ d (fun i hi => hd i) (-(1 : ℝ) / 2)]
  rw [← Real.rpow_mul (Finset.prod_nonneg (fun i hi => hd i))]
  congr 1
  field_simp

private lemma ofReal_listCircleDistanceProduct_rpow
    (l : List ℂ) (N : ℕ) (hN : 0 < N) (θ : ℝ) :
    ENNReal.ofReal ((listCircleDistanceProduct l θ) ^
      (-(1 : ℝ) / (2 * N))) =
      ∏ i : Fin l.length,
        (ENNReal.ofReal
          (‖circleMap 0 1 θ - l.get i‖ ^ (-(1 : ℝ) / 2))) ^ ((N : ℝ)⁻¹) := by
  rw [listCircleDistanceProduct_rpow_eq l N hN θ]
  rw [ENNReal.ofReal_prod_of_nonneg]
  · apply Finset.prod_congr rfl
    intro i hi
    exact (ENNReal.ofReal_rpow_of_nonneg
      (Real.rpow_nonneg (norm_nonneg _) _)
      (inv_nonneg.mpr (Nat.cast_nonneg N))).symm
  · intro i hi
    exact Real.rpow_nonneg (Real.rpow_nonneg (norm_nonneg _) _) _

/-- Uniform integrability of the inverse tiny power of a product of at most
`N` circle-distance factors. -/
theorem integrable_listCircleDistanceProduct_rpow
    (l : List ℂ) (N : ℕ) (hN : 0 < N) (hlen : l.length ≤ N) :
    Integrable (fun θ => (listCircleDistanceProduct l θ) ^
      (-(1 : ℝ) / (2 * N))) circleParameterMeasure ∧
    (∫ θ, (listCircleDistanceProduct l θ) ^
      (-(1 : ℝ) / (2 * N)) ∂circleParameterMeasure) ≤
      max 1 inverseCircleKernelBound := by
  let F : Fin l.length → ℝ → ℝ≥0∞ := fun i θ =>
    ENNReal.ofReal
      (‖circleMap 0 1 θ - l.get i‖ ^ (-(1 : ℝ) / 2))
  have hFmeas (i : Fin l.length) : AEMeasurable (F i) circleParameterMeasure := by
    apply Measurable.aemeasurable
    dsimp [F]
    fun_prop
  have hFbound (i : Fin l.length) :
      (∫⁻ θ, F i θ ∂circleParameterMeasure) ≤ inverseCircleKernelENNBound := by
    exact lintegral_circleParameter_inverse_sqrt_distance_le (l.get i)
  have hholder := lintegral_fin_product_rpow_inv_le_of_card_le
    circleParameterMeasure N l.length hN hlen F hFmeas
    inverseCircleKernelENNBound one_le_inverseCircleKernelENNBound hFbound
  have hlin : (∫⁻ θ, ENNReal.ofReal
      ((listCircleDistanceProduct l θ) ^ (-(1 : ℝ) / (2 * N)))
      ∂circleParameterMeasure) ≤ inverseCircleKernelENNBound := by
    simpa only [ofReal_listCircleDistanceProduct_rpow l N hN] using hholder
  have hbase : Measurable (listCircleDistanceProduct l) :=
    measurable_listCircleDistanceProduct l
  have hmeas : AEStronglyMeasurable
      (fun θ => (listCircleDistanceProduct l θ) ^ (-(1 : ℝ) / (2 * N)))
      circleParameterMeasure :=
    (measurable_rpow_of_measurable_nonneg _ _ hbase
      (listCircleDistanceProduct_nonneg l)).aestronglyMeasurable
  have hnonneg : 0 ≤ᵐ[circleParameterMeasure]
      (fun θ => (listCircleDistanceProduct l θ) ^ (-(1 : ℝ) / (2 * N))) := by
    filter_upwards with θ
    exact Real.rpow_nonneg (listCircleDistanceProduct_nonneg l θ) _
  have hint : Integrable
      (fun θ => (listCircleDistanceProduct l θ) ^ (-(1 : ℝ) / (2 * N)))
      circleParameterMeasure := by
    refine ⟨hmeas, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal hnonneg]
    exact lt_of_le_of_lt hlin (by simp [inverseCircleKernelENNBound])
  constructor
  · exact hint
  · apply (ENNReal.ofReal_le_ofReal_iff
      (le_trans zero_le_one (le_max_left 1 inverseCircleKernelBound))).mp
    rw [ofReal_integral_eq_lintegral_ofReal hint hnonneg]
    exact hlin

end Erdos522

end AmalgamatedModule124


/-! ===== amalgamated from Research.ExponentialMomentToPower ===== -/

section AmalgamatedModule125


open MeasureTheory

namespace Erdos522

lemma abs_pow_le_inv_pow_mul_factorial_mul_exp_add_exp
    (t x : ℝ) (ht : 0 < t) (m : ℕ) :
    |x| ^ m ≤ (t⁻¹) ^ m * (m.factorial : ℝ) *
      (Real.exp (t * x) + Real.exp (-t * x)) := by
  have hy : 0 ≤ t * |x| := mul_nonneg ht.le (abs_nonneg x)
  have hseries := Real.pow_div_factorial_le_exp (t * |x|) hy m
  have hfact : 0 < (m.factorial : ℝ) := by positivity
  have hpow : (t * |x|) ^ m ≤ (m.factorial : ℝ) * Real.exp (t * |x|) := by
    calc
      (t * |x|) ^ m ≤ Real.exp (t * |x|) * (m.factorial : ℝ) :=
        (div_le_iff₀ hfact).mp hseries
      _ = (m.factorial : ℝ) * Real.exp (t * |x|) := mul_comm _ _
  have hexp : Real.exp (t * |x|) ≤
      Real.exp (t * x) + Real.exp (-t * x) := by
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx]
      linarith [Real.exp_pos (-t * x)]
    · rw [abs_of_neg (lt_of_not_ge hx)]
      have heq : t * -x = -t * x := by ring
      rw [heq]
      linarith [Real.exp_pos (t * x)]
  have hcomb : (t * |x|) ^ m ≤ (m.factorial : ℝ) *
      (Real.exp (t * x) + Real.exp (-t * x)) :=
    hpow.trans (mul_le_mul_of_nonneg_left hexp (Nat.cast_nonneg _))
  calc
    |x| ^ m = (t⁻¹) ^ m * (t * |x|) ^ m := by
      rw [← mul_pow]
      field_simp [ht.ne']
    _ ≤ (t⁻¹) ^ m * ((m.factorial : ℝ) *
        (Real.exp (t * x) + Real.exp (-t * x))) :=
      mul_le_mul_of_nonneg_left hcomb (pow_nonneg (inv_nonneg.mpr ht.le) _)
    _ = (t⁻¹) ^ m * (m.factorial : ℝ) *
        (Real.exp (t * x) + Real.exp (-t * x)) := by ring

/-- Quantitative form of the standard fact that two-sided exponential moments
control every absolute power moment. -/
theorem integral_abs_pow_le_of_two_sided_exp
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (X : α → ℝ) (t A B : ℝ) (ht : 0 < t)
    (hposInt : Integrable (fun a => Real.exp (t * X a)) μ)
    (hnegInt : Integrable (fun a => Real.exp (-t * X a)) μ)
    (hpos : (∫ a, Real.exp (t * X a) ∂μ) ≤ A)
    (hneg : (∫ a, Real.exp (-t * X a) ∂μ) ≤ B)
    (m : ℕ) :
    Integrable (fun a => |X a| ^ m) μ ∧
    (∫ a, |X a| ^ m ∂μ) ≤
      (t⁻¹) ^ m * (m.factorial : ℝ) * (A + B) := by
  have hmInt := ProbabilityTheory.integrable_pow_abs_of_integrable_exp_mul
    (μ := μ) (X := X) ht.ne' hposInt (by simpa only [neg_mul] using hnegInt) m
  constructor
  · exact hmInt
  · calc
      (∫ a, |X a| ^ m ∂μ) ≤
          ∫ a, (t⁻¹) ^ m * (m.factorial : ℝ) *
            (Real.exp (t * X a) + Real.exp (-t * X a)) ∂μ := by
        apply integral_mono_ae hmInt
        · exact ((hposInt.add hnegInt).const_mul
            ((t⁻¹) ^ m * (m.factorial : ℝ)))
        · filter_upwards with a
          exact abs_pow_le_inv_pow_mul_factorial_mul_exp_add_exp t (X a) ht m
      _ = (t⁻¹) ^ m * (m.factorial : ℝ) *
          ((∫ a, Real.exp (t * X a) ∂μ) +
            ∫ a, Real.exp (-t * X a) ∂μ) := by
        rw [integral_const_mul, integral_add hposInt hnegInt]
      _ ≤ (t⁻¹) ^ m * (m.factorial : ℝ) * (A + B) := by
        gcongr

end Erdos522

end AmalgamatedModule125


/-! ===== amalgamated from Research.PolynomialLogExponentialMoments ===== -/

section AmalgamatedModule126


open MeasureTheory
open scoped BigOperators ENNReal

namespace Erdos522

noncomputable def multisetCircleDistanceProduct (m : Multiset ℂ) (θ : ℝ) : ℝ :=
  (m.map fun β => ‖circleMap 0 1 θ - β‖).prod

lemma multisetCircleDistanceProduct_nonneg (m : Multiset ℂ) (θ : ℝ) :
    0 ≤ multisetCircleDistanceProduct m θ := by
  refine Quotient.inductionOn m ?_
  intro l
  change 0 ≤ listCircleDistanceProduct l θ
  exact listCircleDistanceProduct_nonneg l θ

lemma measurable_multisetCircleDistanceProduct (m : Multiset ℂ) :
    Measurable (multisetCircleDistanceProduct m) := by
  refine Quotient.inductionOn m ?_
  intro l
  change Measurable (listCircleDistanceProduct l)
  exact measurable_listCircleDistanceProduct l

lemma integrable_multisetCircleDistanceProduct_rpow
    (m : Multiset ℂ) (N : ℕ) (hN : 0 < N) (hcard : m.card ≤ N) :
    Integrable (fun θ => (multisetCircleDistanceProduct m θ) ^
      (-(1 : ℝ) / (2 * N))) circleParameterMeasure ∧
    (∫ θ, (multisetCircleDistanceProduct m θ) ^
      (-(1 : ℝ) / (2 * N)) ∂circleParameterMeasure) ≤
      max 1 inverseCircleKernelBound := by
  revert hcard
  refine Quotient.inductionOn m ?_
  intro l hcard
  change Integrable (fun θ => (listCircleDistanceProduct l θ) ^
      (-(1 : ℝ) / (2 * N))) circleParameterMeasure ∧
    (∫ θ, (listCircleDistanceProduct l θ) ^
      (-(1 : ℝ) / (2 * N)) ∂circleParameterMeasure) ≤
      max 1 inverseCircleKernelBound
  apply integrable_listCircleDistanceProduct_rpow l N hN
  simpa using hcard

lemma polynomial_eval_circle_norm_eq
    (p : Polynomial ℂ) (θ : ℝ) :
    ‖p.eval (circleMap 0 1 θ)‖ =
      ‖p.leadingCoeff‖ * multisetCircleDistanceProduct p.roots θ := by
  have hs : p.Splits := IsAlgClosed.splits p
  rw [hs.eval_eq_prod_roots, norm_mul]
  unfold multisetCircleDistanceProduct
  congr 1
  have hnormprod (m : Multiset ℂ) :
      ‖m.prod‖ = (m.map norm).prod := by
    induction m using Multiset.induction_on with
    | empty => simp
    | @cons z m ih => simp [ih, norm_mul]
  rw [hnormprod]
  simp only [Multiset.map_map, Function.comp_apply]

lemma countable_polynomial_circle_zero_set {p : Polynomial ℂ} (hp : p ≠ 0) :
    Set.Countable {θ : ℝ | p.eval (circleMap 0 1 θ) = 0} := by
  have heq : {θ : ℝ | p.eval (circleMap 0 1 θ) = 0} =
      circleMap 0 1 ⁻¹' (↑p.roots.toFinset : Set ℂ) := by
    ext θ
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    constructor
    · intro h
      exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp).mpr h)
    · intro h
      exact (Polynomial.mem_roots hp).mp (Multiset.mem_toFinset.mp h)
  rw [heq]
  exact (p.roots.toFinset.finite_toSet.countable).preimage_circleMap 0 (by norm_num)

lemma ae_polynomial_eval_circle_ne_zero {p : Polynomial ℂ} (hp : p ≠ 0) :
    ∀ᵐ θ ∂circleParameterMeasure, p.eval (circleMap 0 1 θ) ≠ 0 := by
  let Z : Set ℝ := {θ : ℝ | p.eval (circleMap 0 1 θ) = 0}
  have hZvol : volume Z = 0 :=
    (countable_polynomial_circle_zero_set hp).measure_zero volume
  have hZrestrict :
      (volume.restrict (Set.uIoc 0 (2 * Real.pi))) Z = 0 := by
    exact le_antisymm
      ((Measure.restrict_le_self : volume.restrict
        (Set.uIoc 0 (2 * Real.pi)) ≤ volume) Z |>.trans_eq hZvol)
      bot_le
  rw [ae_iff]
  have hset : {a : ℝ | ¬p.eval (circleMap 0 1 a) ≠ 0} = Z := by
    ext a
    simp [Z]
  rw [hset]
  unfold circleParameterMeasure
  rw [Measure.smul_apply, hZrestrict, smul_zero]

lemma exp_mul_rawLog_eq_rpow_ae
    {p : Polynomial ℂ} (hp : p ≠ 0) (t : ℝ) :
    (fun θ => Real.exp (t * rawLog (p.eval (circleMap 0 1 θ)))) =ᵐ[
      circleParameterMeasure]
      (fun θ => ‖p.eval (circleMap 0 1 θ)‖ ^ t) := by
  filter_upwards [ae_polynomial_eval_circle_ne_zero hp] with θ hθ
  unfold rawLog
  rw [Real.rpow_def_of_pos (norm_pos_iff.mpr hθ)]
  congr 1
  ring

lemma exp_neg_mul_rawLog_eq_rpow_ae
    {p : Polynomial ℂ} (hp : p ≠ 0) (t : ℝ) :
    (fun θ => Real.exp (-t * rawLog (p.eval (circleMap 0 1 θ)))) =ᵐ[
      circleParameterMeasure]
      (fun θ => ‖p.eval (circleMap 0 1 θ)‖ ^ (-t)) := by
  simpa only [neg_mul] using exp_mul_rawLog_eq_rpow_ae hp (-t)

lemma polynomial_norm_rpow_neg_eq
    (p : Polynomial ℂ) (N : ℕ) (hN : 0 < N) (θ : ℝ) :
    ‖p.eval (circleMap 0 1 θ)‖ ^ (-(1 : ℝ) / (2 * N)) =
      ‖p.leadingCoeff‖ ^ (-(1 : ℝ) / (2 * N)) *
        (multisetCircleDistanceProduct p.roots θ) ^
          (-(1 : ℝ) / (2 * N)) := by
  rw [polynomial_eval_circle_norm_eq]
  exact Real.mul_rpow (norm_nonneg _) (multisetCircleDistanceProduct_nonneg _ _)

/-- The inverse exponential moment of a polynomial logarithm at scale
`1/(2N)` is controlled by its leading coefficient and the universal root
kernel, provided its degree is less than `N`. -/
theorem integrable_exp_neg_rawLog_polynomial
    (p : Polynomial ℂ) (hp : p ≠ 0) (N : ℕ) (hN : 0 < N)
    (hdeg : p.natDegree < N) :
    Integrable
      (fun θ => Real.exp (-(1 / (2 * N : ℝ)) *
        rawLog (p.eval (circleMap 0 1 θ)))) circleParameterMeasure ∧
    (∫ θ, Real.exp (-(1 / (2 * N : ℝ)) *
      rawLog (p.eval (circleMap 0 1 θ))) ∂circleParameterMeasure) ≤
      ‖p.leadingCoeff‖ ^ (-(1 : ℝ) / (2 * N)) *
        max 1 inverseCircleKernelBound := by
  have hcard : p.roots.card ≤ N := by
    rw [IsAlgClosed.card_roots_eq_natDegree]
    exact Nat.le_of_lt hdeg
  have hroot := integrable_multisetCircleDistanceProduct_rpow
    p.roots N hN hcard
  have hconst0 : 0 ≤ ‖p.leadingCoeff‖ ^ (-(1 : ℝ) / (2 * N)) :=
    Real.rpow_nonneg (norm_nonneg _) _
  have hnormInt : Integrable
      (fun θ => ‖p.eval (circleMap 0 1 θ)‖ ^ (-(1 : ℝ) / (2 * N)))
      circleParameterMeasure := by
    apply (hroot.1.const_mul
      (‖p.leadingCoeff‖ ^ (-(1 : ℝ) / (2 * N)))).congr
    filter_upwards with θ
    exact (polynomial_norm_rpow_neg_eq p N hN θ).symm
  have hae := exp_neg_mul_rawLog_eq_rpow_ae hp (1 / (2 * N : ℝ))
  have hae' : (fun θ => Real.exp (-(1 / (2 * N : ℝ)) *
        rawLog (p.eval (circleMap 0 1 θ)))) =ᵐ[circleParameterMeasure]
      (fun θ => ‖p.eval (circleMap 0 1 θ)‖ ^
        (-(1 : ℝ) / (2 * N))) := by
    filter_upwards [hae] with θ hθ
    convert hθ using 1 <;> ring
  have hexpInt := hnormInt.congr hae'.symm
  constructor
  · exact hexpInt
  · rw [integral_congr_ae hae']
    calc
      (∫ θ, ‖p.eval (circleMap 0 1 θ)‖ ^ (-(1 : ℝ) / (2 * N))
          ∂circleParameterMeasure) =
          ‖p.leadingCoeff‖ ^ (-(1 : ℝ) / (2 * N)) *
            ∫ θ, (multisetCircleDistanceProduct p.roots θ) ^
              (-(1 : ℝ) / (2 * N)) ∂circleParameterMeasure := by
        simp_rw [polynomial_norm_rpow_neg_eq p N hN]
        rw [integral_const_mul]
      _ ≤ ‖p.leadingCoeff‖ ^ (-(1 : ℝ) / (2 * N)) *
          max 1 inverseCircleKernelBound :=
        mul_le_mul_of_nonneg_left hroot.2 hconst0

lemma rpow_le_one_add_sq {u t : ℝ} (hu : 0 ≤ u) (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    u ^ t ≤ 1 + u ^ 2 := by
  by_cases hu1 : u ≤ 1
  · exact (Real.rpow_le_one hu hu1 ht0).trans (by nlinarith [sq_nonneg u])
  · have hpow : u ^ t ≤ u ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hu1) ht2
    have hpow' : u ^ t ≤ u ^ (2 : ℕ) :=
      hpow.trans_eq (Real.rpow_natCast u 2)
    exact hpow'.trans (le_add_of_nonneg_left zero_le_one)

/-- The positive exponential moment at the same tiny scale is bounded by two
whenever the polynomial is normalized in angular `L²`. -/
theorem integrable_exp_pos_rawLog_polynomial
    (p : Polynomial ℂ) (hp : p ≠ 0) (N : ℕ) (hN : 0 < N)
    (hnormInt : Integrable
      (fun θ => ‖p.eval (circleMap 0 1 θ)‖ ^ 2) circleParameterMeasure)
    (hnorm : (∫ θ, ‖p.eval (circleMap 0 1 θ)‖ ^ 2
      ∂circleParameterMeasure) ≤ 1) :
    Integrable
      (fun θ => Real.exp ((1 / (2 * N : ℝ)) *
        rawLog (p.eval (circleMap 0 1 θ)))) circleParameterMeasure ∧
    (∫ θ, Real.exp ((1 / (2 * N : ℝ)) *
      rawLog (p.eval (circleMap 0 1 θ))) ∂circleParameterMeasure) ≤ 2 := by
  let t : ℝ := 1 / (2 * N : ℝ)
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have ht2 : t ≤ 2 := by
    dsimp [t]
    have hcast : (1 : ℝ) ≤ N := by exact_mod_cast hN
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * N)).2
    nlinarith
  let g : ℝ → ℝ := fun θ => ‖p.eval (circleMap 0 1 θ)‖ ^ t
  have hgmeas : AEStronglyMeasurable g circleParameterMeasure := by
    apply Measurable.aestronglyMeasurable
    apply measurable_rpow_of_measurable_nonneg
    · fun_prop
    · intro θ
      exact norm_nonneg _
  have hg : Integrable g circleParameterMeasure := by
    apply ((integrable_const 1).add hnormInt).mono' hgmeas
    filter_upwards with θ
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact rpow_le_one_add_sq (norm_nonneg _) ht0 ht2
  have hge : (∫ θ, g θ ∂circleParameterMeasure) ≤ 2 := by
    calc
      (∫ θ, g θ ∂circleParameterMeasure) ≤
          ∫ θ, (1 + ‖p.eval (circleMap 0 1 θ)‖ ^ 2)
            ∂circleParameterMeasure := by
        apply integral_mono_ae hg ((integrable_const 1).add hnormInt)
        filter_upwards with θ
        exact rpow_le_one_add_sq (norm_nonneg _) ht0 ht2
      _ = 1 + ∫ θ, ‖p.eval (circleMap 0 1 θ)‖ ^ 2
          ∂circleParameterMeasure := by
        rw [integral_add (integrable_const 1) hnormInt, integral_const]
        norm_num
      _ ≤ 2 := by linarith
  have hae := exp_mul_rawLog_eq_rpow_ae hp t
  have hexp : Integrable
      (fun θ => Real.exp (t * rawLog (p.eval (circleMap 0 1 θ))))
      circleParameterMeasure := hg.congr hae.symm
  constructor
  · simpa [t] using hexp
  · simpa [t] using (integral_congr_ae hae).trans_le hge

/-- A degree-`<N`, angularly `L²`-normalized polynomial has a quantitative
256th logarithmic moment bound in terms of only its leading coefficient and
the universal inverse-root kernel. -/
theorem integral_abs_rawLog_pow256_polynomial_le
    (p : Polynomial ℂ) (hp : p ≠ 0) (N : ℕ) (hN : 0 < N)
    (hdeg : p.natDegree < N)
    (hnormInt : Integrable
      (fun θ => ‖p.eval (circleMap 0 1 θ)‖ ^ 2) circleParameterMeasure)
    (hnorm : (∫ θ, ‖p.eval (circleMap 0 1 θ)‖ ^ 2
      ∂circleParameterMeasure) ≤ 1) :
    Integrable
      (fun θ => |rawLog (p.eval (circleMap 0 1 θ))| ^ 256)
      circleParameterMeasure ∧
    (∫ θ, |rawLog (p.eval (circleMap 0 1 θ))| ^ 256
      ∂circleParameterMeasure) ≤
      ((2 * N : ℕ) : ℝ) ^ 256 * (Nat.factorial 256 : ℝ) *
        (2 + ‖p.leadingCoeff‖ ^ (-(1 : ℝ) / (2 * N)) *
          max 1 inverseCircleKernelBound) := by
  have hpExp := integrable_exp_pos_rawLog_polynomial p hp N hN hnormInt hnorm
  have hnExp := integrable_exp_neg_rawLog_polynomial p hp N hN hdeg
  have ht : 0 < (1 / (2 * N : ℝ)) := by positivity
  have h := integral_abs_pow_le_of_two_sided_exp circleParameterMeasure
    (fun θ => rawLog (p.eval (circleMap 0 1 θ)))
    (1 / (2 * N : ℝ)) 2
    (‖p.leadingCoeff‖ ^ (-(1 : ℝ) / (2 * N)) *
      max 1 inverseCircleKernelBound)
    ht hpExp.1 hnExp.1 hpExp.2 hnExp.2 256
  convert h using 1 <;> norm_num [hN.ne']

end Erdos522

end AmalgamatedModule126


/-! ===== amalgamated from Research.RadialPolynomialLogMoment ===== -/

section AmalgamatedModule127


open MeasureTheory
open scoped BigOperators

namespace Erdos522

lemma radialWeight_pos (n : ℕ) (s : ℝ) (k : ℕ) :
    0 < radialWeight n s k := by
  unfold radialWeight
  exact div_pos (Real.exp_pos _) (radialVariance_pos n s)

lemma radialVariance_upper_exp (n : ℕ) (s : ℝ) :
    radialVariance n s ≤ Real.exp ((n + 1 : ℕ) + 2 * |s|) := by
  have hterm : ∀ k ∈ Finset.range (n + 1),
      Real.exp (2 * s * ((k : ℝ) / n)) ≤ Real.exp (2 * |s|) := by
    intro k hk
    by_cases hn : n = 0
    · subst n
      simp
    · exact radialWeight_numerator_upper (Nat.pos_of_ne_zero hn)
        (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) s
  have hsum : radialVariance n s ≤ (n + 1 : ℝ) * Real.exp (2 * |s|) := by
    unfold radialVariance
    calc
      (∑ k ∈ Finset.range (n + 1),
        Real.exp (2 * s * ((k : ℝ) / n))) ≤
          ∑ k ∈ Finset.range (n + 1), Real.exp (2 * |s|) := by
        exact Finset.sum_le_sum fun k hk => hterm k hk
      _ = (n + 1 : ℝ) * Real.exp (2 * |s|) := by simp
  have hnexp : (n + 1 : ℝ) ≤ Real.exp (n + 1 : ℝ) := by
    have := Real.add_one_le_exp ((n + 1 : ℕ) : ℝ)
    norm_num at this ⊢
    linarith
  calc
    radialVariance n s ≤ (n + 1 : ℝ) * Real.exp (2 * |s|) := hsum
    _ ≤ Real.exp (n + 1 : ℝ) * Real.exp (2 * |s|) :=
      mul_le_mul_of_nonneg_right hnexp (Real.exp_nonneg _)
    _ = Real.exp ((n + 1 : ℕ) + 2 * |s|) := by
      rw [← Real.exp_add]
      norm_num

lemma radialWeight_last_lower_exp (n : ℕ) (s : ℝ) :
    Real.exp (-((n + 1 : ℕ) : ℝ) - 4 * |s|) ≤ radialWeight n s n := by
  have hnum : Real.exp (-2 * |s|) ≤
      Real.exp (2 * s * ((n : ℝ) / n)) := by
    by_cases hn : n = 0
    · subst n
      simp
    · apply Real.exp_le_exp.mpr
      have hunit := mul_div_mem_unitInterval (Nat.pos_of_ne_zero hn) (le_refl n)
      have h := (abs_bound_mul_unitInterval s ((n : ℝ) / n) hunit.1 hunit.2).1
      linarith
  have hvar := radialVariance_upper_exp n s
  have hdiv : Real.exp (-2 * |s|) /
      Real.exp (((n + 1 : ℕ) : ℝ) + 2 * |s|) ≤
      Real.exp (2 * s * ((n : ℝ) / n)) / radialVariance n s := by
    exact div_le_div₀ (Real.exp_nonneg _) hnum (radialVariance_pos n s) hvar
  unfold radialWeight
  calc
    Real.exp (-((n + 1 : ℕ) : ℝ) - 4 * |s|) =
        Real.exp (-2 * |s|) /
          Real.exp (((n + 1 : ℕ) : ℝ) + 2 * |s|) := by
      rw [← Real.exp_sub]
      congr 1
      ring
    _ ≤ _ := hdiv

lemma radialWeightedSignPolynomial_coeff_last_ne_zero
    (n : ℕ) (s : ℝ) (x : Fin (n + 1) → Bool) :
    (radialWeightedSignPolynomial n s x).coeff n ≠ 0 := by
  have hcoeff := coeff_weightedVectorPolynomial
    (fun k : Fin (n + 1) => radialWeight n s k)
    (fun k => realRademacherSign (x k)) (Fin.last n)
  change (radialWeightedSignPolynomial n s x).coeff (Fin.last n : ℕ) ≠ 0
  rw [radialWeightedSignPolynomial]
  rw [hcoeff]
  rw [Complex.ofReal_ne_zero]
  apply mul_ne_zero (Real.sqrt_ne_zero'.mpr (radialWeight_pos n s n))
  cases h : x (Fin.last n) <;> simp [realRademacherSign, h]

lemma radialWeightedSignPolynomial_natDegree
    (n : ℕ) (s : ℝ) (x : Fin (n + 1) → Bool) :
    (radialWeightedSignPolynomial n s x).natDegree = n := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro j hj
    unfold radialWeightedSignPolynomial
    exact coeff_weightedVectorPolynomial_eq_zero_of_ge _ _ (by omega)
  · exact radialWeightedSignPolynomial_coeff_last_ne_zero n s x

lemma norm_leadingCoeff_radialWeightedSignPolynomial
    (n : ℕ) (s : ℝ) (x : Fin (n + 1) → Bool) :
    ‖(radialWeightedSignPolynomial n s x).leadingCoeff‖ =
      Real.sqrt (radialWeight n s n) := by
  rw [← Polynomial.coeff_natDegree,
    radialWeightedSignPolynomial_natDegree n s x]
  unfold radialWeightedSignPolynomial
  change ‖(weightedVectorPolynomial
    (fun k : Fin (n + 1) => radialWeight n s k)
    (fun k => realRademacherSign (x k))).coeff (Fin.last n : ℕ)‖ = _
  rw [coeff_weightedVectorPolynomial]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  have hs : |realRademacherSign (x (Fin.last n))| = 1 := by
    cases h : x (Fin.last n) <;> simp [realRademacherSign, h]
  rw [hs, mul_one, Fin.val_last]

lemma tiny_inverse_leadingCoeff_radial_le
    (n : ℕ) (s : ℝ) (x : Fin (n + 1) → Bool) :
    ‖(radialWeightedSignPolynomial n s x).leadingCoeff‖ ^
      (-(1 : ℝ) / (2 * (n + 1 : ℕ))) ≤ Real.exp (1 + |s|) := by
  let N : ℝ := ((n + 1 : ℕ) : ℝ)
  let L : ℝ := Real.exp ((-N - 4 * |s|) / 2)
  have hN : 1 ≤ N := by simp [N]
  have hweight := radialWeight_last_lower_exp n s
  have hsqrt : L ≤ Real.sqrt (radialWeight n s n) := by
    dsimp [L, N]
    rw [Real.exp_half]
    exact Real.sqrt_le_sqrt hweight
  rw [norm_leadingCoeff_radialWeightedSignPolynomial]
  have hL : 0 < L := by dsimp [L]; positivity
  have hsqrtPos : 0 < Real.sqrt (radialWeight n s n) := by
    exact Real.sqrt_pos.2 (radialWeight_pos n s n)
  have hbase := Real.rpow_le_rpow hL.le hsqrt
    (show 0 ≤ (1 : ℝ) / (2 * (n + 1 : ℕ)) by positivity)
  have hinv : (Real.sqrt (radialWeight n s n)) ^
      (-(1 : ℝ) / (2 * (n + 1 : ℕ))) ≤
      L ^ (-(1 : ℝ) / (2 * (n + 1 : ℕ))) := by
    rw [show (-(1 : ℝ) / (2 * (n + 1 : ℕ))) =
      -((1 : ℝ) / (2 * (n + 1 : ℕ))) by ring,
      Real.rpow_neg hsqrtPos.le, Real.rpow_neg hL.le]
    exact (inv_le_inv₀ (Real.rpow_pos_of_pos hsqrtPos _)
      (Real.rpow_pos_of_pos hL _)).2 hbase
  refine hinv.trans ?_
  have hLeq : L ^ (-(1 : ℝ) / (2 * (n + 1 : ℕ))) =
      Real.exp ((N + 4 * |s|) / (4 * N)) := by
    rw [Real.rpow_def_of_pos hL]
    dsimp [L]
    rw [Real.log_exp]
    congr 1
    dsimp [N]
    field_simp
    ring
  rw [hLeq]
  apply Real.exp_le_exp.mpr
  have habsN : |s| / N ≤ |s| := by
    exact (div_le_iff₀ (by positivity : 0 < N)).2
      (by nlinarith [abs_nonneg s])
  have : (N + 4 * |s|) / (4 * N) = 1 / 4 + |s| / N := by
    field_simp
  rw [this]
  linarith [abs_nonneg s]

lemma radialPolynomial_normSq_integrable
    (n : ℕ) (s : ℝ) (x : Fin (n + 1) → Bool) :
    Integrable
      (fun θ => ‖(radialWeightedSignPolynomial n s x).eval
        (circleMap 0 1 θ)‖ ^ 2) circleParameterMeasure := by
  change Integrable (circleParameterFunction
    (fun z => ‖(radialWeightedSignPolynomial n s x).eval z‖ ^ 2))
    circleParameterMeasure
  apply integrable_circleParameter_of_circleIntegrable
  apply ContinuousOn.circleIntegrable (by norm_num)
  fun_prop

lemma radialPolynomial_integral_normSq_eq_one
    (n : ℕ) (s : ℝ) (x : Fin (n + 1) → Bool) :
    (∫ θ, ‖(radialWeightedSignPolynomial n s x).eval
      (circleMap 0 1 θ)‖ ^ 2 ∂circleParameterMeasure) = 1 := by
  change (∫ θ, circleParameterFunction
    (fun z => ‖(radialWeightedSignPolynomial n s x).eval z‖ ^ 2) θ
    ∂circleParameterMeasure) = 1
  rw [← circleAverage_eq_integral_circleParameterMeasure]
  unfold radialWeightedSignPolynomial
  exact weightedVectorPolynomial_circleAverage_sq_norm_eq_one
    (fun k : Fin (n + 1) => radialWeight n s k)
    (fun k => radialWeight_nonneg n s k)
    (sum_radialWeight_fin n s) x

noncomputable def radialLogMomentConstant (s : ℝ) : ℝ :=
  max 1 ((2 : ℝ) ^ 256 * (Nat.factorial 256 : ℝ) *
    (2 + Real.exp (1 + |s|) * max 1 inverseCircleKernelBound))

lemma one_le_radialLogMomentConstant (s : ℝ) :
    1 ≤ radialLogMomentConstant s := le_max_left _ _

/-- Deterministic degree-scale bound for every normalized radial sign
polynomial; in particular no random log-integrability theorem is needed for
the high moment. -/
theorem radialPolynomial_absLog_pow256_integrable_bound
    (n : ℕ) (s : ℝ) (x : Fin (n + 1) → Bool) :
    Integrable
      (fun θ => (absoluteRawLog
        ((radialWeightedSignPolynomial n s x).eval (circleMap 0 1 θ))) ^ 256)
      circleParameterMeasure ∧
    (∫ θ, (absoluteRawLog
      ((radialWeightedSignPolynomial n s x).eval (circleMap 0 1 θ))) ^ 256
      ∂circleParameterMeasure) ≤
      radialLogMomentConstant s * (((n + 1 : ℕ) : ℝ) ^ (256 : ℝ)) := by
  let p := radialWeightedSignPolynomial n s x
  have hp : p ≠ 0 := by
    intro hz
    have hc := radialWeightedSignPolynomial_coeff_last_ne_zero n s x
    exact hc (by simp [p, hz])
  have hdeg : p.natDegree < n + 1 := by
    rw [show p.natDegree = n from radialWeightedSignPolynomial_natDegree n s x]
    omega
  have hgeneric := integral_abs_rawLog_pow256_polynomial_le p hp (n + 1)
    (by omega) hdeg (radialPolynomial_normSq_integrable n s x)
    (by rw [radialPolynomial_integral_normSq_eq_one])
  have htiny := tiny_inverse_leadingCoeff_radial_le n s x
  constructor
  · simpa [absoluteRawLog, p] using hgeneric.1
  · change (∫ θ, |rawLog (p.eval (circleMap 0 1 θ))| ^ 256
        ∂circleParameterMeasure) ≤ _
    calc
      _ ≤ (((2 * (n + 1) : ℕ) : ℝ) ^ 256) *
          (Nat.factorial 256 : ℝ) *
          (2 + ‖p.leadingCoeff‖ ^ (-(1 : ℝ) / (2 * (n + 1 : ℕ))) *
            max 1 inverseCircleKernelBound) := hgeneric.2
      _ ≤ ((2 : ℝ) ^ 256 * (Nat.factorial 256 : ℝ) *
          (2 + Real.exp (1 + |s|) * max 1 inverseCircleKernelBound)) *
          (((n + 1 : ℕ) : ℝ) ^ 256) := by
        rw [show (((2 * (n + 1) : ℕ) : ℝ) ^ 256) =
          (2 : ℝ) ^ 256 * (((n + 1 : ℕ) : ℝ) ^ 256) by
            push_cast; rw [mul_pow]]
        have hK : 0 ≤ max 1 inverseCircleKernelBound :=
          le_trans zero_le_one (le_max_left _ _)
        have hinner : 2 + ‖p.leadingCoeff‖ ^
            (-(1 : ℝ) / (2 * (n + 1 : ℕ))) *
              max 1 inverseCircleKernelBound ≤
            2 + Real.exp (1 + |s|) * max 1 inverseCircleKernelBound := by
          gcongr
        have hfac : 0 ≤ (2 : ℝ) ^ 256 * (Nat.factorial 256 : ℝ) := by positivity
        calc
          (2 : ℝ) ^ 256 * (((n + 1 : ℕ) : ℝ) ^ 256) *
              (Nat.factorial 256 : ℝ) *
              (2 + ‖p.leadingCoeff‖ ^ (-(1 : ℝ) / (2 * (n + 1 : ℕ))) *
                max 1 inverseCircleKernelBound) =
              ((2 : ℝ) ^ 256 * (Nat.factorial 256 : ℝ)) *
                (2 + ‖p.leadingCoeff‖ ^ (-(1 : ℝ) / (2 * (n + 1 : ℕ))) *
                  max 1 inverseCircleKernelBound) *
                (((n + 1 : ℕ) : ℝ) ^ 256) := by ring
          _ ≤ ((2 : ℝ) ^ 256 * (Nat.factorial 256 : ℝ)) *
                (2 + Real.exp (1 + |s|) * max 1 inverseCircleKernelBound) *
                (((n + 1 : ℕ) : ℝ) ^ 256) := by gcongr
          _ = _ := by ring
      _ ≤ radialLogMomentConstant s *
          (((n + 1 : ℕ) : ℝ) ^ (256 : ℝ)) := by
        unfold radialLogMomentConstant
        gcongr
        · exact le_max_right _ _
        · exact le_of_eq (Real.rpow_natCast ((n + 1 : ℕ) : ℝ) 256).symm

lemma cubeAverage_radialLogPower256_le
    (n : ℕ) (s : ℝ) :
    cubeAverage (radialCubeLogPower256Moment n s) ≤
      radialLogMomentConstant s * (((n + 1 : ℕ) : ℝ) ^ (256 : ℝ)) := by
  calc
    cubeAverage (radialCubeLogPower256Moment n s) ≤
        cubeAverage (fun _ : Fin (n + 1) → Bool =>
          radialLogMomentConstant s * (((n + 1 : ℕ) : ℝ) ^ (256 : ℝ))) := by
      apply cubeAverage_mono
      intro x
      unfold radialCubeLogPower256Moment
      rw [circleAverage_eq_integral_circleParameterMeasure]
      exact (radialPolynomial_absLog_pow256_integrable_bound n s x).2
    _ = radialLogMomentConstant s *
        (((n + 1 : ℕ) : ℝ) ^ (256 : ℝ)) := cubeAverage_const _

end Erdos522

end AmalgamatedModule127


/-! ===== amalgamated from Research.SmallBallOnlyFinalReduction ===== -/

section AmalgamatedModule128


open MeasureTheory ProbabilityTheory Filter Topology

namespace Erdos522

/-- All logarithmic-integrability hypotheses have now been discharged
deterministically.  The sole remaining analytic input is the stated annealed
small-ball estimate, with a shift-dependent constant. -/
theorem erdos522_of_radial_annealed_smallBall
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : ℕ → Ω → Bool) (hξ_meas : ∀ k, Measurable (ξ k))
    (hξ_indep : iIndepFun ξ μ)
    (hξ_fair : ∀ k, μ {ω | ξ k ω = true} = (1 : ENNReal) / 2)
    (D : ℝ → ℝ) (hD1 : ∀ s, 1 ≤ D s)
    (hDmoment : ∀ s, radialLogMomentConstant s ≤ D s)
    (hSmall : ∀ (n : ℕ) (s : ℝ),
      (radialAnnealedLaw n s : Measure ℂ)
        {z | ‖z‖ ≤ Real.exp (-(logMomentTruncationScale n))} ≤
      ENNReal.ofReal (D s * (((n + 1 : ℕ) : ℝ) ^ (-600 : ℝ)))) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n => (R ξ n ω : ℝ) / ((n : ℝ) / 2)) atTop (𝓝 1) := by
  apply erdos522_of_sDependent_polynomial_logMoment_and_smallBall
    μ ξ hξ_meas hξ_indep hξ_fair D hD1
  · intro n s x
    exact (radialPolynomial_absLog_pow256_integrable_bound n s x).1
  · intro n s
    exact (cubeAverage_radialLogPower256_le n s).trans
      (mul_le_mul_of_nonneg_right (hDmoment s)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  · exact hSmall

end Erdos522

end AmalgamatedModule128


/-! ===== amalgamated from Research.TinyFractionalCosineMomentFinalReduction ===== -/

section AmalgamatedModule129


open MeasureTheory ProbabilityTheory Filter Topology

namespace Erdos522

/-- A fixed positive fractional-frequency decay in the high angular moment
estimate implies the required annealed lower-tail rate eventually. -/
theorem eventually_radialAnnealedLaw_smallBall_of_tinyFractionalCosineMoment
    (s C : ℝ) (A : ℕ) (hC : 0 ≤ C)
    (hmom : ∀ (n : ℕ) (t : ℂ), t ≠ 0 →
      (2 / ((n + 1 : ℕ) : ℝ)) ^ (2 * 1024) *
          radialCosineSumMoment n s t 1024 ≤
        C * (((((n + 1 : ℕ) : ℝ)⁻¹) ^ 1024) +
          (((n + 1 : ℕ) : ℝ) ^ A) * (‖t‖⁻¹) ^ ((1 : ℝ) / 8192))) :
    ∀ᶠ n : ℕ in atTop,
      (radialAnnealedLaw n s : Measure ℂ).real
          {z | ‖z‖ ≤ Real.exp (-(logMomentTruncationScale n))} ≤
        ((((n + 1 : ℕ) : ℝ)⁻¹) ^ 600) := by
  let X : ℕ → ℝ := fun n => ((n + 1 : ℕ) : ℝ)
  let M : ℕ → NNReal := fun n =>
    ⟨Real.exp (logMomentTruncationScale n), (Real.exp_pos _).le⟩
  let L : ℕ → ℝ := fun n => (X n) ^ (8192 * (A + 1024))
  have hgauss : ∀ᶠ n : ℕ in atTop,
      Real.exp 1 * (Real.exp 1 * Real.sqrt Real.pi) *
          (X n) ^ (8192 * (A + 1024)) /
            Real.exp ((X n) ^ ((1 : ℝ) / 256)) ≤
        (X n)⁻¹ ^ 603 := by
    simpa [X] using
      eventually_const_mul_pow_div_exp_rpow_le_inv_pow
        (Real.exp 1 * (Real.exp 1 * Real.sqrt Real.pi))
        (by positivity) (8192 * (A + 1024)) 603 ((1 : ℝ) / 256) (by norm_num)
  have hexp : ∀ᶠ n : ℕ in atTop,
      Real.exp 1 * Real.exp (-(X n) / 8) ≤ (X n)⁻¹ ^ 603 := by
    have h := eventually_const_mul_pow_div_exp_mul_rpow_le_inv_pow
      (Real.exp 1) (1 / 8 : ℝ) (Real.exp_pos 1).le (by norm_num)
      0 603 (1 : ℝ) (by norm_num)
    filter_upwards [h] with n hn
    calc
      Real.exp 1 * Real.exp (-(X n) / 8) =
          Real.exp 1 / Real.exp ((1 / 8 : ℝ) * (X n) ^ (1 : ℝ)) := by
        simp only [div_eq_mul_inv]
        rw [← Real.exp_neg]
        congr 2
        rw [Real.rpow_one]
        ring
      _ ≤ (X n)⁻¹ ^ 603 := by simpa [X] using hn
  have hpow : ∀ᶠ n : ℕ in atTop,
      (Real.exp 1 * C) * ((X n)⁻¹ ^ 1024) ≤ (X n)⁻¹ ^ 603 := by
    simpa [X] using eventually_const_mul_inv_pow_le_inv_pow
      (Real.exp 1 * C) (mul_nonneg (Real.exp_pos 1).le hC) 1024 603 (by omega)
  filter_upwards [hgauss, hexp, hpow, hpow, eventually_ge_atTop 1]
    with n hga hlin hp₁ hp₂ hn
  have hX : 0 < X n := by dsimp [X]; positivity
  have hM : 0 < M n := by
    dsimp [M]
    exact_mod_cast Real.exp_pos (logMomentTruncationScale n)
  have hL : 0 < L n := by dsimp [L]; positivity
  have hchar := integral_norm_radialAnnealedCharacteristic_smul_le_of_fractionalMoment
    n 1024 A ((1 : ℝ) / 8192) s C (M n : ℝ) (L n)
      (by norm_num) (by norm_num) hC hM hL (hmom n)
  have hsb := radialAnnealedLaw_smallBall_le_characteristicIntegral
    n s (M n) hM
  have hradius : ((M n : ℝ)⁻¹) =
      Real.exp (-(logMomentTruncationScale n)) := by
    change (Real.exp (logMomentTruncationScale n))⁻¹ = _
    exact (Real.exp_neg _).symm
  rw [hradius] at hsb
  have hraw := hsb.trans (mul_le_mul_of_nonneg_left hchar (Real.exp_pos 1).le)
  have hLratio :
      Real.exp 1 * (Real.exp 1 * Real.sqrt Real.pi * ((L n) / (M n : ℝ))) =
        Real.exp 1 * (Real.exp 1 * Real.sqrt Real.pi) *
          (X n) ^ (8192 * (A + 1024)) /
            Real.exp ((X n) ^ ((1 : ℝ) / 256)) := by
    have hMval : (M n : ℝ) = Real.exp (logMomentTruncationScale n) := rfl
    rw [hMval]
    dsimp [L, X, logMomentTruncationScale]
    ring
  have hNA : (X n) ^ A * ((L n)⁻¹) ^ ((1 : ℝ) / 8192) =
      (X n)⁻¹ ^ 1024 := by
    dsimp [L]
    have hbase : 0 ≤ (X n) ^ (8192 * (A + 1024)) := by positivity
    rw [Real.inv_rpow hbase]
    have hp : ((X n) ^ (8192 * (A + 1024))) ^ ((1 : ℝ) / 8192) =
        (X n) ^ (A + 1024) := by
      calc
        ((X n) ^ (8192 * (A + 1024))) ^ ((1 : ℝ) / 8192) =
            ((X n) ^ ((8192 * (A + 1024) : ℕ) : ℝ)) ^
              ((1 : ℝ) / 8192) := by rw [Real.rpow_natCast]
        _ = (X n) ^ (((8192 * (A + 1024) : ℕ) : ℝ) *
              ((1 : ℝ) / 8192)) := (Real.rpow_mul hX.le _ _).symm
        _ = (X n) ^ ((A + 1024 : ℕ) : ℝ) := by
          congr 1
          push_cast
          ring
        _ = (X n) ^ (A + 1024) := Real.rpow_natCast _ _
    rw [hp, inv_pow]
    rw [show A + 1024 = 1024 + A by omega, pow_add]
    field_simp
  have hraw' :
      (radialAnnealedLaw n s : Measure ℂ).real
          {z | ‖z‖ ≤ Real.exp (-(logMomentTruncationScale n))} ≤
        (X n)⁻¹ ^ 603 + (X n)⁻¹ ^ 603 +
          (X n)⁻¹ ^ 603 + (X n)⁻¹ ^ 603 := by
    calc
      _ ≤ Real.exp 1 *
          (Real.exp 1 * Real.sqrt Real.pi * ((L n) / (M n : ℝ)) +
            (Real.exp (-(X n) / 8) +
              C * ((X n)⁻¹ ^ 1024 +
                (X n) ^ A * ((L n)⁻¹) ^ ((1 : ℝ) / 8192)))) := by
        simpa [X] using hraw
      _ = Real.exp 1 * (Real.exp 1 * Real.sqrt Real.pi * ((L n) / (M n : ℝ))) +
            Real.exp 1 * Real.exp (-(X n) / 8) +
            (Real.exp 1 * C) * ((X n)⁻¹ ^ 1024) +
            (Real.exp 1 * C) *
              ((X n) ^ A * ((L n)⁻¹) ^ ((1 : ℝ) / 8192)) := by ring
      _ ≤ (X n)⁻¹ ^ 603 + (X n)⁻¹ ^ 603 +
            (X n)⁻¹ ^ 603 + (X n)⁻¹ ^ 603 := by
        rw [hLratio, hNA]
        gcongr
  have hfour :
      (X n)⁻¹ ^ 603 + (X n)⁻¹ ^ 603 +
          (X n)⁻¹ ^ 603 + (X n)⁻¹ ^ 603 ≤ (X n)⁻¹ ^ 600 := by
    have hX2 : (2 : ℝ) ≤ X n := by
      dsimp [X]
      exact_mod_cast Nat.succ_le_succ hn
    have hX3 : (4 : ℝ) ≤ (X n) ^ 3 := by nlinarith [sq_nonneg (X n - 2)]
    rw [show 603 = 600 + 3 by omega, pow_add]
    calc
      _ = 4 * ((X n)⁻¹ ^ 600 * (X n)⁻¹ ^ 3) := by ring
      _ = ((X n)⁻¹ ^ 600) * (4 * (X n)⁻¹ ^ 3) := by ring
      _ ≤ ((X n)⁻¹ ^ 600) * 1 := by
        gcongr
        rw [inv_pow]
        apply (div_le_one (by positivity)).2
        exact hX3
      _ = _ := by ring
  exact hraw'.trans hfour

/-- It is enough to prove the displayed angular moment estimate with the tiny
fixed frequency-decay exponent `1/8192`. -/
theorem erdos522_of_tinyFractional_radialCosineSumMoment
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : ℕ → Ω → Bool) (hξ_meas : ∀ k, Measurable (ξ k))
    (hξ_indep : iIndepFun ξ μ)
    (hξ_fair : ∀ k, μ {ω | ξ k ω = true} = (1 : ENNReal) / 2)
    (hmom : ∀ s : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∃ A : ℕ,
      ∀ (n : ℕ) (t : ℂ), t ≠ 0 →
        (2 / ((n + 1 : ℕ) : ℝ)) ^ (2 * 1024) *
            radialCosineSumMoment n s t 1024 ≤
          C * (((((n + 1 : ℕ) : ℝ)⁻¹) ^ 1024) +
            (((n + 1 : ℕ) : ℝ) ^ A) * (‖t‖⁻¹) ^ ((1 : ℝ) / 8192))) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n => (R ξ n ω : ℝ) / ((n : ℝ) / 2)) atTop (𝓝 1) := by
  let C : ℝ → ℝ := fun s => Classical.choose (hmom s)
  have hC : ∀ s, 0 ≤ C s := fun s => (Classical.choose_spec (hmom s)).1
  let A : ℝ → ℕ := fun s => Classical.choose (Classical.choose_spec (hmom s)).2
  have hmomS : ∀ s (n : ℕ) (t : ℂ), t ≠ 0 →
      (2 / ((n + 1 : ℕ) : ℝ)) ^ (2 * 1024) *
          radialCosineSumMoment n s t 1024 ≤
        C s * (((((n + 1 : ℕ) : ℝ)⁻¹) ^ 1024) +
          (((n + 1 : ℕ) : ℝ) ^ A s) * (‖t‖⁻¹) ^ ((1 : ℝ) / 8192)) := by
    intro s
    exact Classical.choose_spec (Classical.choose_spec (hmom s)).2
  have hev (s : ℝ) : ∀ᶠ n : ℕ in atTop,
      (radialAnnealedLaw n s : Measure ℂ).real
          {z | ‖z‖ ≤ Real.exp (-(logMomentTruncationScale n))} ≤
        ((((n + 1 : ℕ) : ℝ)⁻¹) ^ 600) :=
    eventually_radialAnnealedLaw_smallBall_of_tinyFractionalCosineMoment
      s (C s) (A s) (hC s) (hmomS s)
  have hex (s : ℝ) : ∃ N : ℕ, ∀ n, N ≤ n →
      (radialAnnealedLaw n s : Measure ℂ).real
          {z | ‖z‖ ≤ Real.exp (-(logMomentTruncationScale n))} ≤
        ((((n + 1 : ℕ) : ℝ)⁻¹) ^ 600) := eventually_atTop.mp (hev s)
  let N : ℝ → ℕ := fun s => Classical.choose (hex s)
  have hN (s : ℝ) : ∀ n, N s ≤ n →
      (radialAnnealedLaw n s : Measure ℂ).real
          {z | ‖z‖ ≤ Real.exp (-(logMomentTruncationScale n))} ≤
        ((((n + 1 : ℕ) : ℝ)⁻¹) ^ 600) := Classical.choose_spec (hex s)
  let D : ℝ → ℝ := fun s =>
    max 1 (max (radialLogMomentConstant s) ((((N s + 1 : ℕ) : ℝ) ^ 600)))
  have hD1 : ∀ s, 1 ≤ D s := fun s => le_max_left _ _
  have hDmom : ∀ s, radialLogMomentConstant s ≤ D s := by
    intro s
    exact (le_max_left _ _).trans (le_max_right _ _)
  apply erdos522_of_radial_annealed_smallBall μ ξ hξ_meas hξ_indep hξ_fair
    D hD1 hDmom
  intro n s
  have hX : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hrpow : (((n + 1 : ℕ) : ℝ) ^ (-600 : ℝ)) =
      ((((n + 1 : ℕ) : ℝ)⁻¹) ^ 600) := by
    rw [Real.rpow_neg hX.le]
    rw [show (((n + 1 : ℕ) : ℝ) ^ (600 : ℝ)) =
      (((n + 1 : ℕ) : ℝ) ^ (600 : ℕ)) by
        exact Real.rpow_natCast _ 600]
    exact (inv_pow _ 600).symm
  rw [hrpow]
  have htarget0 : 0 ≤ D s * ((((n + 1 : ℕ) : ℝ)⁻¹) ^ 600) := by
    exact mul_nonneg (le_trans zero_le_one (hD1 s)) (by positivity)
  apply (ENNReal.toReal_le_toReal
    (measure_ne_top (radialAnnealedLaw n s : Measure ℂ) _)
    ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal htarget0]
  by_cases hn : N s ≤ n
  · have hmul := mul_le_mul_of_nonneg_right (hD1 s)
        (show 0 ≤ ((((n + 1 : ℕ) : ℝ)⁻¹) ^ 600) by positivity)
    exact (hN s n hn).trans (by simpa using hmul)
  · have hnle : n + 1 ≤ N s + 1 := by omega
    have hpowle : ((((n + 1 : ℕ) : ℝ) ^ 600)) ≤
        (((N s + 1 : ℕ) : ℝ) ^ 600) := by
      exact_mod_cast Nat.pow_le_pow_left hnle 600
    have hDpow : (((N s + 1 : ℕ) : ℝ) ^ 600) ≤ D s :=
      (le_max_right _ _).trans (le_max_right _ _)
    have hprod : 1 ≤ D s * ((((n + 1 : ℕ) : ℝ)⁻¹) ^ 600) := by
      rw [inv_pow]
      apply (le_div_iff₀ (by positivity)).2
      simpa [one_mul] using hpowle.trans hDpow
    have hmeasure :
        (radialAnnealedLaw n s : Measure ℂ).real
          {z | ‖z‖ ≤ Real.exp (-(logMomentTruncationScale n))} ≤ 1 := by
      unfold Measure.real
      rw [← ENNReal.toReal_one]
      apply ENNReal.toReal_mono (by simp)
      calc
        (radialAnnealedLaw n s : Measure ℂ)
            {z | ‖z‖ ≤ Real.exp (-(logMomentTruncationScale n))} ≤
            (radialAnnealedLaw n s : Measure ℂ) Set.univ :=
          measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    exact hmeasure.trans hprod

end Erdos522

end AmalgamatedModule129


/-! ===== amalgamated from Research.RadialCosineMomentFinal ===== -/

section AmalgamatedModule130


open MeasureTheory

namespace Erdos522

noncomputable def radialCosineMomentCombinedConstant
    (q H : ℕ) (s : ℝ) : ℝ :=
  (2 : ℝ) ^ (4 * q) *
    (((((q + 1) ^ (2 * q + 1) : ℕ) : ℝ)) +
      radialOscillationPolynomialConstant q H s + 1)

lemma radialCosineMomentCombinedConstant_nonneg (q H : ℕ) (s : ℝ) :
    0 ≤ radialCosineMomentCombinedConstant q H s := by
  unfold radialCosineMomentCombinedConstant
  have hc := radialOscillationPolynomialConstant_nonneg q H s
  positivity

/-- Package the exceptional and oscillatory coefficients into one constant;
the harmless degree-zero case is covered by the trivial integral bound. -/
theorem normalized_radialCosineSumMoment_le_combined
    (q H n : ℕ) (hH : 4 * q + 1 ≤ H)
    (s : ℝ) {t : ℂ} (ht : t ≠ 0) :
    (2 / ((n + 1 : ℕ) : ℝ)) ^ (2 * q) *
        radialCosineSumMoment n s t q ≤
      radialCosineMomentCombinedConstant q H s *
        (((((n + 1 : ℕ) : ℝ)⁻¹) ^ q) +
          (((n + 1 : ℕ) : ℝ) ^
              (radialOscillationPolynomialExponent H)) *
            (‖t‖⁻¹) ^ ((1 : ℝ) / H)) := by
  let X : ℝ := ((((n + 1 : ℕ) : ℝ)⁻¹) ^ q)
  let Y : ℝ := (((n + 1 : ℕ) : ℝ) ^
      (radialOscillationPolynomialExponent H)) *
        (‖t‖⁻¹) ^ ((1 : ℝ) / H)
  let C₀ : ℝ := ((((q + 1) ^ (2 * q + 1) : ℕ) : ℝ))
  let C₁ : ℝ := radialOscillationPolynomialConstant q H s
  let P : ℝ := (2 : ℝ) ^ (4 * q)
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hY : 0 ≤ Y := by dsimp [Y]; positivity
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  have hC₁ : 0 ≤ C₁ := by
    dsimp [C₁]
    exact radialOscillationPolynomialConstant_nonneg q H s
  have hP : 0 ≤ P := by dsimp [P]; positivity
  by_cases hn : 0 < n
  · have hraw := normalized_radialCosineSumMoment_le_polynomial
      q H n hn hH s ht
    have hinside : C₀ * X + C₁ * Y ≤ (C₀ + C₁ + 1) * (X + Y) := by
      calc
        C₀ * X + C₁ * Y ≤ (C₀ + C₁ + 1) * X +
            (C₀ + C₁ + 1) * Y := by
          gcongr <;> linarith
        _ = _ := by ring
    calc
      _ ≤ P * (C₀ * X + C₁ * Y) := by
        simpa [P, C₀, C₁, X, Y, Nat.cast_add, Nat.cast_one, inv_pow,
          mul_assoc] using hraw
      _ ≤ P * ((C₀ + C₁ + 1) * (X + Y)) :=
        mul_le_mul_of_nonneg_left hinside hP
      _ = _ := by
        unfold radialCosineMomentCombinedConstant
        dsimp [P, C₀, C₁, X, Y]
        ring
  · have hn0 : n = 0 := by omega
    subst n
    have hraw := normalized_radialCosineSumMoment_le_exceptional_add
      q 0 s t 1 (by norm_num) (by
        intro K hK σ
        exact oscillatoryIntegralNorm_le_one circleParameterMeasure
          (fun k θ => 2 * radialCharacteristicPhase 0 s t
            (circleMap 0 1 θ) k) K σ)
    have hsmall : C₀ + 1 ≤ C₀ + C₁ + 1 := by linarith
    have hXone : X = 1 := by simp [X]
    have hXY : 1 ≤ X + Y := by linarith
    calc
      _ ≤ P * (C₀ + 1) := by
        simpa [P, C₀, X, Nat.cast_add, Nat.cast_one] using hraw
      _ ≤ P * (C₀ + C₁ + 1) := mul_le_mul_of_nonneg_left hsmall hP
      _ ≤ P * (C₀ + C₁ + 1) * (X + Y) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hXY
          (mul_nonneg hP (by linarith))
      _ = _ := by
        unfold radialCosineMomentCombinedConstant
        dsimp [P, C₀, C₁, X, Y]

noncomputable def radialCosineMomentFinalConstant (s : ℝ) : ℝ :=
  radialCosineMomentCombinedConstant 1024 8192 s

lemma radialCosineMomentFinalConstant_nonneg (s : ℝ) :
    0 ≤ radialCosineMomentFinalConstant s := by
  exact radialCosineMomentCombinedConstant_nonneg 1024 8192 s

/-- The exact tiny-fractional high-moment hypothesis required by F-118 holds
with explicit constants. -/
theorem radialCosineSumMoment_tinyFractionalBound
    (s : ℝ) (n : ℕ) {t : ℂ} (ht : t ≠ 0) :
    (2 / ((n + 1 : ℕ) : ℝ)) ^ (2 * 1024) *
        radialCosineSumMoment n s t 1024 ≤
      radialCosineMomentFinalConstant s *
        (((((n + 1 : ℕ) : ℝ)⁻¹) ^ 1024) +
          (((n + 1 : ℕ) : ℝ) ^
              (radialOscillationPolynomialExponent 8192)) *
            (‖t‖⁻¹) ^ ((1 : ℝ) / 8192)) := by
  exact normalized_radialCosineSumMoment_le_combined
    1024 8192 n (by norm_num) s ht

end Erdos522

end AmalgamatedModule130


/-! ===== amalgamated from Research.Erdos522Final ===== -/

section AmalgamatedModule131


open scoped BigOperators Topology
open Filter MeasureTheory ProbabilityTheory

namespace Erdos522

universe u_erdos_final

/-- Erdős Problem 522: the normalized number of zeros in the closed unit disk
converges almost surely to one for every i.i.d. fair Rademacher sequence. -/
theorem erdos_522_final :
    ∀ {Ω : Type u_erdos_final} [MeasurableSpace Ω]
      (μ : Measure Ω) [IsProbabilityMeasure μ]
      (ξ : ℕ → Ω → Bool),
      (∀ k, Measurable (ξ k)) →
      iIndepFun ξ μ →
      (∀ k, μ {ω | ξ k ω = true} = (1 : ENNReal) / 2) →
      ∀ᵐ ω ∂μ,
        Tendsto (fun n => (R ξ n ω : ℝ) / ((n : ℝ) / 2)) atTop (𝓝 1) := by
  intro Ω _ μ _ ξ hξ_meas hξ_indep hξ_fair
  apply erdos522_of_tinyFractional_radialCosineSumMoment
    μ ξ hξ_meas hξ_indep hξ_fair
  intro s
  exact ⟨radialCosineMomentFinalConstant s,
    radialCosineMomentFinalConstant_nonneg s,
    radialOscillationPolynomialExponent 8192,
    fun n t ht => radialCosineSumMoment_tinyFractionalBound s n ht⟩

end Erdos522

end AmalgamatedModule131


namespace Erdos522

universe u_erdos_proof

/-- The proof-gate theorem at its exact pinned, universe-polymorphic type. -/
theorem erdos_522 : Erdos522Claim.{u_erdos_proof} :=
  erdos_522_final

end Erdos522
