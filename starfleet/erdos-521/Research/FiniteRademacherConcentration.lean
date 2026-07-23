import Research.RademacherCharacteristic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Tactic

open scoped BigOperators

namespace Erdos521

noncomputable local instance finiteRademacherConcentrationDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

noncomputable def finiteRademacherRealSum {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (e : ι → Bool) : ℝ :=
  ∑ i, sign (e i) * a i

noncomputable def finiteRademacherVariance {ι : Type*} [Fintype ι]
    (a : ι → ℝ) : ℝ :=
  ∑ i, (a i) ^ 2

lemma sum_bool_rexp_sign (x : ℝ) :
    (∑ b : Bool, Real.exp (sign b * x)) = 2 * Real.cosh x := by
  rw [Fintype.sum_bool]
  rw [show sign true = (1 : ℝ) by simp [sign],
    show sign false = (-1 : ℝ) by simp [sign]]
  rw [Real.cosh_eq]
  ring

lemma sum_rexp_finiteRademacherRealSum {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (lam : ℝ) :
    (∑ e : ι → Bool, Real.exp (lam * finiteRademacherRealSum a e)) =
      ∏ i : ι, 2 * Real.cosh (lam * a i) := by
  have hpoint (e : ι → Bool) :
      Real.exp (lam * finiteRademacherRealSum a e) =
        ∏ i : ι, Real.exp (sign (e i) * (lam * a i)) := by
    rw [← Real.exp_sum]
    congr 1
    unfold finiteRademacherRealSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  calc
    (∑ e : ι → Bool, Real.exp (lam * finiteRademacherRealSum a e)) =
        ∑ e : ι → Bool, ∏ i : ι,
          Real.exp (sign (e i) * (lam * a i)) := by
      apply Finset.sum_congr rfl
      intro e he
      exact hpoint e
    _ = ∏ i : ι, ∑ b : Bool, Real.exp (sign b * (lam * a i)) := by
      exact (Fintype.prod_sum
        (fun i : ι ↦ fun b : Bool ↦ Real.exp (sign b * (lam * a i)))).symm
    _ = ∏ i : ι, 2 * Real.cosh (lam * a i) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact sum_bool_rexp_sign (lam * a i)

lemma finiteRademacher_mgf_bound {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (lam : ℝ) :
    (∑ e : ι → Bool, Real.exp (lam * finiteRademacherRealSum a e)) ≤
      (2 : ℝ) ^ Fintype.card ι *
        Real.exp (lam ^ 2 * finiteRademacherVariance a / 2) := by
  rw [sum_rexp_finiteRademacherRealSum]
  calc
    (∏ i : ι, 2 * Real.cosh (lam * a i)) ≤
        ∏ i : ι, 2 * Real.exp ((lam * a i) ^ 2 / 2) := by
      apply Finset.prod_le_prod
      · intro i hi
        positivity
      · intro i hi
        exact mul_le_mul_of_nonneg_left (Real.cosh_le_exp_half_sq _) (by norm_num)
    _ = (2 : ℝ) ^ Fintype.card ι *
        Real.exp (lam ^ 2 * finiteRademacherVariance a / 2) := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Finset.card_univ]
      rw [← Real.exp_sum]
      congr 1
      unfold finiteRademacherVariance
      rw [Finset.mul_sum, Finset.sum_div]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      ring

noncomputable def finiteRademacherUpperTailProbability {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (T : ℝ) : ℝ :=
  (∑ e : ι → Bool,
    if T ≤ finiteRademacherRealSum a e then (1 : ℝ) else 0) /
      (2 : ℝ) ^ Fintype.card ι

lemma finiteRademacherUpperTailProbability_le_mgf {ι : Type*} [Fintype ι]
    (a : ι → ℝ) {T lam : ℝ} (hlam : 0 ≤ lam) :
    finiteRademacherUpperTailProbability a T ≤
      Real.exp (-lam * T + lam ^ 2 * finiteRademacherVariance a / 2) := by
  let D : ℝ := (2 : ℝ) ^ Fintype.card ι
  have hD : 0 < D := by dsimp [D]; positivity
  have hpoint (e : ι → Bool) :
      (if T ≤ finiteRademacherRealSum a e then (1 : ℝ) else 0) ≤
        Real.exp (-lam * T) *
          Real.exp (lam * finiteRademacherRealSum a e) := by
    by_cases he : T ≤ finiteRademacherRealSum a e
    · rw [if_pos he, ← Real.exp_add]
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      nlinarith
    · rw [if_neg he]
      positivity
  unfold finiteRademacherUpperTailProbability
  change (∑ e : ι → Bool,
    if T ≤ finiteRademacherRealSum a e then (1 : ℝ) else 0) / D ≤ _
  apply (div_le_iff₀ hD).2
  calc
    (∑ e : ι → Bool,
      if T ≤ finiteRademacherRealSum a e then (1 : ℝ) else 0) ≤
        ∑ e : ι → Bool,
          Real.exp (-lam * T) * Real.exp (lam * finiteRademacherRealSum a e) := by
      exact Finset.sum_le_sum fun e he ↦ hpoint e
    _ = Real.exp (-lam * T) *
        ∑ e : ι → Bool, Real.exp (lam * finiteRademacherRealSum a e) := by
      rw [Finset.mul_sum]
    _ ≤ Real.exp (-lam * T) *
        (D * Real.exp (lam ^ 2 * finiteRademacherVariance a / 2)) := by
      exact mul_le_mul_of_nonneg_left (by simpa [D] using finiteRademacher_mgf_bound a lam)
        (Real.exp_pos _).le
    _ = Real.exp (-lam * T + lam ^ 2 * finiteRademacherVariance a / 2) * D := by
      rw [Real.exp_add]
      ring

lemma finiteRademacherUpperTailProbability_le {ι : Type*} [Fintype ι]
    (a : ι → ℝ) {T : ℝ} (hT : 0 ≤ T) (hV : 0 < finiteRademacherVariance a) :
    finiteRademacherUpperTailProbability a T ≤
      Real.exp (-(T ^ 2) / (2 * finiteRademacherVariance a)) := by
  have h := finiteRademacherUpperTailProbability_le_mgf a
    (T := T) (lam := T / finiteRademacherVariance a) (div_nonneg hT hV.le)
  convert h using 1
  field_simp
  ring

noncomputable def finiteRademacherAbsTailProbability {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (T : ℝ) : ℝ :=
  (∑ e : ι → Bool,
    if T ≤ |finiteRademacherRealSum a e| then (1 : ℝ) else 0) /
      (2 : ℝ) ^ Fintype.card ι

lemma finiteRademacherAbsTailProbability_le {ι : Type*} [Fintype ι]
    (a : ι → ℝ) {T : ℝ} (hT : 0 ≤ T) (hV : 0 < finiteRademacherVariance a) :
    finiteRademacherAbsTailProbability a T ≤
      2 * Real.exp (-(T ^ 2) / (2 * finiteRademacherVariance a)) := by
  let D : ℝ := (2 : ℝ) ^ Fintype.card ι
  have hD : 0 < D := by dsimp [D]; positivity
  have hneg (e : ι → Bool) :
      finiteRademacherRealSum (fun i ↦ -a i) e =
        -finiteRademacherRealSum a e := by
    unfold finiteRademacherRealSum
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hVneg : finiteRademacherVariance (fun i ↦ -a i) =
      finiteRademacherVariance a := by
    unfold finiteRademacherVariance
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hpoint (e : ι → Bool) :
      (if T ≤ |finiteRademacherRealSum a e| then (1 : ℝ) else 0) ≤
        (if T ≤ finiteRademacherRealSum a e then (1 : ℝ) else 0) +
          (if T ≤ finiteRademacherRealSum (fun i ↦ -a i) e then (1 : ℝ) else 0) := by
    rw [hneg]
    by_cases hp : 0 ≤ finiteRademacherRealSum a e
    · rw [abs_of_nonneg hp]
      split_ifs <;> norm_num
    · rw [abs_of_neg (lt_of_not_ge hp)]
      split_ifs <;> norm_num
  have hplus := finiteRademacherUpperTailProbability_le a hT hV
  have hminus := finiteRademacherUpperTailProbability_le (fun i ↦ -a i) hT (by simpa [hVneg] using hV)
  rw [hVneg] at hminus
  unfold finiteRademacherAbsTailProbability
  change (∑ e : ι → Bool,
    if T ≤ |finiteRademacherRealSum a e| then (1 : ℝ) else 0) / D ≤ _
  calc
    _ ≤ ((∑ e : ι → Bool,
          if T ≤ finiteRademacherRealSum a e then (1 : ℝ) else 0) +
        (∑ e : ι → Bool,
          if T ≤ finiteRademacherRealSum (fun i ↦ -a i) e then (1 : ℝ) else 0)) / D := by
      apply div_le_div_of_nonneg_right _ hD.le
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun e he ↦ hpoint e
    _ = finiteRademacherUpperTailProbability a T +
        finiteRademacherUpperTailProbability (fun i ↦ -a i) T := by
      unfold finiteRademacherUpperTailProbability
      ring
    _ ≤ Real.exp (-(T ^ 2) / (2 * finiteRademacherVariance a)) +
        Real.exp (-(T ^ 2) / (2 * finiteRademacherVariance a)) :=
      add_le_add hplus hminus
    _ = _ := by ring

end Erdos521
