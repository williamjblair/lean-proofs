import Research.Benchmark

/-! # Unstopped iterated-log products on a high domain -/

namespace Research

noncomputable def iteratedLog : ℕ → ℝ → ℝ
  | 0, x => x
  | k + 1, x => iteratedLog k (Real.log x)

noncomputable def iteratedLogProduct (k : ℕ) (x : ℝ) : ℝ :=
  ∏ j ∈ Finset.range k, iteratedLog (j + 1) x

@[simp] theorem iteratedLog_zero (x : ℝ) : iteratedLog 0 x = x := rfl
@[simp] theorem iteratedLog_succ (k : ℕ) (x : ℝ) :
    iteratedLog (k + 1) x = iteratedLog k (Real.log x) := rfl
@[simp] theorem iteratedLogProduct_zero (x : ℝ) :
    iteratedLogProduct 0 x = 1 := by simp [iteratedLogProduct]

/-- Append the last factor in the finite product. -/
theorem iteratedLogProduct_succ_last (k : ℕ) (x : ℝ) :
    iteratedLogProduct (k + 1) x =
      iteratedLogProduct k x * iteratedLog (k + 1) x := by
  unfold iteratedLogProduct
  rw [Finset.prod_range_succ]

/-- Recursive form of the finite product. -/
theorem iteratedLogProduct_succ (k : ℕ) (x : ℝ) :
    iteratedLogProduct (k + 1) x =
      Real.log x * iteratedLogProduct k (Real.log x) := by
  induction k with
  | zero => simp [iteratedLogProduct, iteratedLog]
  | succ k ih =>
      rw [iteratedLogProduct_succ_last (k + 1) x, ih]
      rw [show iteratedLog (k + 1 + 1) x =
        iteratedLog (k + 1) (Real.log x) by rfl]
      rw [iteratedLogProduct_succ_last k (Real.log x)]
      ring

/-- A renewal product splits after any fully active initial segment. -/
theorem renewalProduct_add_eq_iteratedLogProduct_mul
    (k l : ℕ) (x : ℝ)
    (hactive : ∀ j, j < k → renewalThreshold < iteratedLog j x) :
    renewalProduct (k + l) x =
      iteratedLogProduct k x * renewalProduct l (iteratedLog k x) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
      have hx : renewalThreshold < x := by
        simpa using hactive 0 (by omega)
      rw [show k + 1 + l = (k + l) + 1 by omega,
        renewalProduct_of_lt (k + l) hx,
        iteratedLogProduct_succ, iteratedLog_succ]
      rw [ih (Real.log x)]
      · ring
      · intro j hj
        simpa using hactive (j + 1) (by omega)

/-- Composition law for iterated logarithms. -/
theorem iteratedLog_add (j k : ℕ) (x : ℝ) :
    iteratedLog (j + k) x = iteratedLog k (iteratedLog j x) := by
  induction j generalizing x with
  | zero => simp
  | succ j ih =>
      rw [Nat.succ_add, iteratedLog_succ, iteratedLog_succ]
      exact ih (Real.log x)

/-- Iterating one additional logarithm can also be viewed at the end. -/
theorem iteratedLog_succ_last (k : ℕ) (x : ℝ) :
    iteratedLog (k + 1) x = Real.log (iteratedLog k x) := by
  simpa [iteratedLog] using iteratedLog_add k 1 x

/-- Elementary lower estimate for `log(1-e)`. -/
theorem neg_two_mul_le_log_one_sub {e : ℝ} (he0 : 0 ≤ e)
    (he2 : e ≤ 1 / 2) :
    -2 * e ≤ Real.log (1 - e) := by
  have hone : 0 < 1 - e := by linarith
  have hinv : 0 < (1 - e)⁻¹ := inv_pos.mpr hone
  have hlog := Real.log_le_sub_one_of_pos hinv
  rw [Real.log_inv] at hlog
  have hfrac : (1 - e)⁻¹ - 1 = e / (1 - e) := by field_simp; ring
  rw [hfrac] at hlog
  have hden : 1 / 2 ≤ 1 - e := by linarith
  have hefrac : e / (1 - e) ≤ 2 * e := by
    rw [div_le_iff₀ hone]
    nlinarith
  linarith

/-- One logarithm preserves a common multiplicative comparison once the
smaller reference logarithm is at least two. -/
theorem log_scale_lower {a b e : ℝ} (he0 : 0 ≤ e) (he2 : e ≤ 1 / 2)
    (hb : 0 < b) (hlogb : 2 ≤ Real.log b)
    (hab : (1 - e) * b ≤ a) :
    (1 - e) * Real.log b ≤ Real.log a := by
  have hone : 0 < 1 - e := by linarith
  have hscaled : 0 < (1 - e) * b := mul_pos hone hb
  have hloga : Real.log ((1 - e) * b) ≤ Real.log a :=
    Real.log_le_log hscaled hab
  rw [Real.log_mul (ne_of_gt hone) (ne_of_gt hb)] at hloga
  have hsub := neg_two_mul_le_log_one_sub he0 he2
  nlinarith

/-- The multiplicative comparison propagates through every iterated log as
long as the reference orbit remains at least two. -/
theorem iteratedLog_scale_lower {x t e : ℝ} (k : ℕ)
    (he0 : 0 ≤ e) (he2 : e ≤ 1 / 2)
    (hx : 0 < x) (htx : (1 - e) * x ≤ t)
    (horbit : ∀ j, 1 ≤ j → j ≤ k → 2 ≤ iteratedLog j x) :
    (1 - e) * iteratedLog k x ≤ iteratedLog k t := by
  induction k generalizing x t with
  | zero => simpa using htx
  | succ k ih =>
      rw [iteratedLog_succ, iteratedLog_succ]
      have hlogx2 : 2 ≤ Real.log x := by
        simpa using horbit 1 (by omega) (by omega)
      have hlogComp : (1 - e) * Real.log x ≤ Real.log t :=
        log_scale_lower he0 he2 hx hlogx2 htx
      have hlogxPos : 0 < Real.log x := lt_of_lt_of_le (by norm_num) hlogx2
      apply ih hlogxPos hlogComp
      intro j hj1 hjk
      simpa [iteratedLog_add] using horbit (j + 1) (by omega) (by omega)

/-- Consequently the whole `k`-factor product loses at most
`(1-e)^k` under the same scaling. -/
theorem iteratedLogProduct_scale_lower {x t e : ℝ} (k : ℕ)
    (he0 : 0 ≤ e) (he2 : e ≤ 1 / 2)
    (hx : 0 < x) (htx : (1 - e) * x ≤ t)
    (horbit : ∀ j, 1 ≤ j → j ≤ k → 2 ≤ iteratedLog j x) :
    (1 - e) ^ k * iteratedLogProduct k x ≤ iteratedLogProduct k t := by
  rw [iteratedLogProduct]
  have hfac (j : ℕ) (hj : j ∈ Finset.range k) :
      (1 - e) * iteratedLog (j + 1) x ≤ iteratedLog (j + 1) t := by
    apply iteratedLog_scale_lower (j + 1) he0 he2 hx htx
    intro i hi1 hij
    exact horbit i hi1 (by have := Finset.mem_range.mp hj; omega)
  calc
    (1 - e) ^ k * ∏ j ∈ Finset.range k, iteratedLog (j + 1) x =
        ∏ j ∈ Finset.range k, ((1 - e) * iteratedLog (j + 1) x) := by
      rw [Finset.prod_mul_distrib]
      simp
    _ ≤ ∏ j ∈ Finset.range k, iteratedLog (j + 1) t := by
      apply Finset.prod_le_prod
      · intro j hj
        have hjpos : 0 ≤ iteratedLog (j + 1) x :=
          le_trans (by norm_num) (horbit (j + 1) (by omega)
            (by have := Finset.mem_range.mp hj; omega))
        exact mul_nonneg (by linarith) hjpos
      · intro j hj
        exact hfac j hj

/-- Applying the preceding comparison after the first logarithm handles the
power-tail point `x^(1-e)`. -/
theorem iteratedLog_rpow_scale_lower {x e : ℝ} (j : ℕ)
    (he0 : 0 ≤ e) (he2 : e ≤ 1 / 2) (hx : 1 < x)
    (horbit : ∀ i, 1 ≤ i → i ≤ j + 1 → 2 ≤ iteratedLog i x) :
    (1 - e) * iteratedLog (j + 1) x ≤
      iteratedLog (j + 1) (x ^ (1 - e)) := by
  rw [iteratedLog_succ, iteratedLog_succ, Real.log_rpow (lt_trans zero_lt_one hx)]
  apply iteratedLog_scale_lower j he0 he2
  · exact Real.log_pos hx
  · rfl
  · intro i hi1 hij
    simpa using horbit (i + 1) (by omega) (by omega)

/-- Product comparison at the power-tail point. -/
theorem iteratedLogProduct_rpow_scale_lower {x e : ℝ} (k : ℕ)
    (he0 : 0 ≤ e) (he2 : e ≤ 1 / 2) (hx : 1 < x)
    (horbit : ∀ j, 1 ≤ j → j ≤ k → 2 ≤ iteratedLog j x) :
    (1 - e) ^ k * iteratedLogProduct k x ≤
      iteratedLogProduct k (x ^ (1 - e)) := by
  rw [iteratedLogProduct]
  have hfac (j : ℕ) (hj : j ∈ Finset.range k) :
      (1 - e) * iteratedLog (j + 1) x ≤
        iteratedLog (j + 1) (x ^ (1 - e)) := by
    apply iteratedLog_rpow_scale_lower j he0 he2 hx
    intro i hi1 hij
    exact horbit i hi1 (by have := Finset.mem_range.mp hj; omega)
  calc
    (1 - e) ^ k * ∏ j ∈ Finset.range k, iteratedLog (j + 1) x =
        ∏ j ∈ Finset.range k, ((1 - e) * iteratedLog (j + 1) x) := by
      rw [Finset.prod_mul_distrib]
      simp
    _ ≤ ∏ j ∈ Finset.range k,
        iteratedLog (j + 1) (x ^ (1 - e)) := by
      apply Finset.prod_le_prod
      · intro j hj
        have hjpos : 0 ≤ iteratedLog (j + 1) x :=
          le_trans (by norm_num) (horbit (j + 1) (by omega)
            (by have := Finset.mem_range.mp hj; omega))
        exact mul_nonneg (by linarith) hjpos
      · intro j hj
        exact hfac j hj

/-- Exponential tower with prescribed bottom value. -/
noncomputable def realTower (b : ℝ) : ℕ → ℝ
  | 0 => b
  | k + 1 => Real.exp (realTower b k)

@[simp] theorem realTower_zero (b : ℝ) : realTower b 0 = b := rfl
@[simp] theorem realTower_succ (b : ℝ) (k : ℕ) :
    realTower b (k + 1) = Real.exp (realTower b k) := rfl

/-- Matching logarithm and tower heights cancel. -/
theorem iteratedLog_realTower_same (b : ℝ) (k : ℕ) :
    iteratedLog k (realTower b k) = b := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [realTower_succ, iteratedLog_succ, Real.log_exp]
      exact ih

/-- Towers above two increase with their height. -/
theorem realTower_le_succ (k : ℕ) : realTower 2 k ≤ realTower 2 (k + 1) := by
  rw [realTower_succ]
  have hnonneg : 0 ≤ realTower 2 k := by
    cases k with
    | zero => norm_num [realTower]
    | succ k => simp [realTower]; positivity
  have h := Real.add_one_le_exp (realTower 2 k)
  linarith

theorem realTower_mono : Monotone (realTower 2) :=
  monotone_nat_of_le_succ realTower_le_succ

/-- Towers with nonnegative base increase in height. -/
theorem realTower_mono_height_of_nonneg {b : ℝ} (hb : 0 ≤ b) :
    Monotone (realTower b) := by
  apply monotone_nat_of_le_succ
  intro k
  rw [realTower_succ]
  have h := Real.add_one_le_exp (realTower b k)
  have hk0 : 0 ≤ realTower b k := by
    cases k with
    | zero => exact hb
    | succ k => rw [realTower_succ]; positivity
  linarith

/-- The height-two tower dominates the linear height. -/
theorem nat_add_two_le_realTower (k : ℕ) :
    (k + 2 : ℕ) ≤ realTower 2 k := by
  induction k with
  | zero => norm_num [realTower]
  | succ k ih =>
      rw [realTower_succ]
      have h := Real.add_one_le_exp (realTower 2 k)
      norm_num only [Nat.cast_add, Nat.cast_ofNat] at ih ⊢
      nlinarith

/-- Iterated logarithms are monotone once their arguments lie above the
corresponding height tower. -/
theorem iteratedLog_mono_on {k : ℕ} {x y : ℝ}
    (hx : realTower 2 k ≤ x) (hxy : x ≤ y) :
    iteratedLog k x ≤ iteratedLog k y := by
  induction k generalizing x y with
  | zero => simpa using hxy
  | succ k ih =>
      rw [iteratedLog_succ, iteratedLog_succ]
      have hfloorPos : 0 < realTower 2 (k + 1) := by
        rw [realTower_succ]
        positivity
      have hxPos : 0 < x := lt_of_lt_of_le hfloorPos hx
      have hlogxy : Real.log x ≤ Real.log y := Real.log_le_log hxPos hxy
      apply ih ?_ hlogxy
      rw [realTower_succ] at hx
      rw [← Real.log_exp (realTower 2 k)]
      exact Real.log_le_log (by positivity) hx

/-- Every factor is at least two above the corresponding tower. -/
theorem two_le_iteratedLog_of_tower_le {k : ℕ} {x : ℝ}
    (hx : realTower 2 k ≤ x) :
    ∀ j, j ≤ k → 2 ≤ iteratedLog j x := by
  intro j hj
  have hfloor : realTower 2 j ≤ x := le_trans (realTower_mono hj) hx
  have hmono := iteratedLog_mono_on (k := j)
    (x := realTower 2 j) (y := x) le_rfl hfloor
  rw [iteratedLog_realTower_same] at hmono
  exact hmono

/-- The finite product is monotone on its high domain. -/
theorem iteratedLogProduct_mono_on {k : ℕ} {x y : ℝ}
    (hx : realTower 2 k ≤ x) (hxy : x ≤ y) :
    iteratedLogProduct k x ≤ iteratedLogProduct k y := by
  rw [iteratedLogProduct, iteratedLogProduct]
  apply Finset.prod_le_prod
  · intro j hj
    have hjk : j + 1 ≤ k := by
      have := Finset.mem_range.mp hj
      omega
    have hfloor : realTower 2 (j + 1) ≤ x :=
      le_trans (realTower_mono hjk) hx
    have hval : 2 ≤ iteratedLog (j + 1) x := by
      have hmono := iteratedLog_mono_on (k := j + 1)
        (x := realTower 2 (j + 1)) (y := x) le_rfl hfloor
      rw [iteratedLog_realTower_same] at hmono
      exact hmono
    linarith
  · intro j hj
    have hjk : j + 1 ≤ k := by
      have := Finset.mem_range.mp hj
      omega
    exact iteratedLog_mono_on
      (le_trans (realTower_mono hjk) hx) hxy

/-- Globally monotone clamped version of the high-domain product. -/
noncomputable def clampedIteratedLogProduct (k : ℕ) (x : ℝ) : ℝ :=
  iteratedLogProduct k (max (realTower 2 k) x)

theorem monotone_clampedIteratedLogProduct (k : ℕ) :
    Monotone (clampedIteratedLogProduct k) := by
  intro x y hxy
  apply iteratedLogProduct_mono_on
  · exact le_max_left _ _
  · exact max_le_max le_rfl hxy

/-- The clamped product is nonnegative everywhere. -/
theorem clampedIteratedLogProduct_nonneg (k : ℕ) (x : ℝ) :
    0 ≤ clampedIteratedLogProduct k x := by
  rw [clampedIteratedLogProduct]
  have h := iteratedLogProduct_mono_on (k := k)
    (x := realTower 2 k) (y := max (realTower 2 k) x)
    le_rfl (le_max_left _ _)
  have hbase : 0 ≤ iteratedLogProduct k (realTower 2 k) := by
    rw [iteratedLogProduct]
    apply Finset.prod_nonneg
    intro j hj
    have hjk : j + 1 ≤ k := by
      have := Finset.mem_range.mp hj
      omega
    have hmono := iteratedLog_mono_on (k := j + 1)
      (x := realTower 2 (j + 1)) (y := realTower 2 k)
      le_rfl (realTower_mono hjk)
    rw [iteratedLog_realTower_same] at hmono
    linarith
  exact le_trans hbase h

/-- Above the tower floor clamping does nothing. -/
theorem clampedIteratedLogProduct_eq {k : ℕ} {x : ℝ}
    (hx : realTower 2 k ≤ x) :
    clampedIteratedLogProduct k x = iteratedLogProduct k x := by
  rw [clampedIteratedLogProduct, max_eq_right hx]

/-- Cancelling an initial segment of a tower by logarithms. -/
theorem iteratedLog_realTower_add (b : ℝ) (j r : ℕ) :
    iteratedLog j (realTower b (j + r)) = realTower b r := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Nat.succ_add, realTower_succ, iteratedLog_succ, Real.log_exp]
      exact ih

/-- Towers are monotone in their bottom value. -/
theorem realTower_mono_base (k : ℕ) : Monotone (fun b => realTower b k) := by
  intro a b hab
  induction k with
  | zero => simpa using hab
  | succ k ih =>
      simp only [realTower_succ]
      exact Real.exp_le_exp.mpr ih

/-- Product cut off below a prescribed high tower. -/
noncomputable def cutoffIteratedLogProduct (H : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  if realTower H k ≤ x then iteratedLogProduct k x else 0

/-- On the active side the cutoff disappears. -/
theorem cutoffIteratedLogProduct_eq {H : ℝ} {k : ℕ} {x : ℝ}
    (hx : realTower H k ≤ x) :
    cutoffIteratedLogProduct H k x = iteratedLogProduct k x := by
  rw [cutoffIteratedLogProduct, if_pos hx]

/-- Below the cutoff the product vanishes. -/
theorem cutoffIteratedLogProduct_eq_zero {H : ℝ} {k : ℕ} {x : ℝ}
    (hx : x < realTower H k) :
    cutoffIteratedLogProduct H k x = 0 := by
  rw [cutoffIteratedLogProduct, if_neg (not_le.mpr hx)]

/-- The high-cutoff product is globally monotone. -/
theorem monotone_cutoffIteratedLogProduct {H : ℝ} (hH : 2 ≤ H) (k : ℕ) :
    Monotone (cutoffIteratedLogProduct H k) := by
  intro x y hxy
  by_cases hx : realTower H k ≤ x
  · have hy : realTower H k ≤ y := le_trans hx hxy
    rw [cutoffIteratedLogProduct_eq hx, cutoffIteratedLogProduct_eq hy]
    apply iteratedLogProduct_mono_on ?_ hxy
    exact le_trans (realTower_mono_base k hH) hx
  · rw [cutoffIteratedLogProduct, if_neg hx]
    by_cases hy : realTower H k ≤ y
    · rw [cutoffIteratedLogProduct_eq hy]
      have hfloor : realTower 2 k ≤ y :=
        le_trans (realTower_mono_base k hH) hy
      have hnonneg := clampedIteratedLogProduct_nonneg k y
      rw [clampedIteratedLogProduct_eq hfloor] at hnonneg
      exact hnonneg
    · rw [cutoffIteratedLogProduct, if_neg hy]

/-- The high-cutoff product is nonnegative. -/
theorem cutoffIteratedLogProduct_nonneg {H : ℝ} (hH : 2 ≤ H)
    (k : ℕ) (x : ℝ) :
    0 ≤ cutoffIteratedLogProduct H k x := by
  by_cases hx : realTower H k ≤ x
  · rw [cutoffIteratedLogProduct_eq hx]
    have hfloor : realTower 2 k ≤ x :=
      le_trans (realTower_mono_base k hH) hx
    have h := clampedIteratedLogProduct_nonneg k x
    rw [clampedIteratedLogProduct_eq hfloor] at h
    exact h
  · rw [cutoffIteratedLogProduct, if_neg hx]

/-- Cutoff at an arbitrary argument threshold. -/
noncomputable def cutoffAtIteratedLogProduct (A : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  if A ≤ x then iteratedLogProduct k x else 0

theorem cutoffAtIteratedLogProduct_eq {A : ℝ} {k : ℕ} {x : ℝ}
    (hx : A ≤ x) :
    cutoffAtIteratedLogProduct A k x = iteratedLogProduct k x := by
  rw [cutoffAtIteratedLogProduct, if_pos hx]

theorem monotone_cutoffAtIteratedLogProduct {A : ℝ} {k : ℕ}
    (hfloor : realTower 2 k ≤ A) :
    Monotone (cutoffAtIteratedLogProduct A k) := by
  intro x y hxy
  by_cases hx : A ≤ x
  · have hy : A ≤ y := le_trans hx hxy
    rw [cutoffAtIteratedLogProduct_eq hx, cutoffAtIteratedLogProduct_eq hy]
    exact iteratedLogProduct_mono_on (le_trans hfloor hx) hxy
  · rw [cutoffAtIteratedLogProduct, if_neg hx]
    by_cases hy : A ≤ y
    · rw [cutoffAtIteratedLogProduct_eq hy]
      have h := clampedIteratedLogProduct_nonneg k y
      rw [clampedIteratedLogProduct_eq (le_trans hfloor hy)] at h
      exact h
    · rw [cutoffAtIteratedLogProduct, if_neg hy]

theorem cutoffAtIteratedLogProduct_nonneg {A : ℝ} {k : ℕ}
    (hfloor : realTower 2 k ≤ A) (x : ℝ) :
    0 ≤ cutoffAtIteratedLogProduct A k x := by
  by_cases hx : A ≤ x
  · rw [cutoffAtIteratedLogProduct_eq hx]
    have h := clampedIteratedLogProduct_nonneg k x
    rw [clampedIteratedLogProduct_eq (le_trans hfloor hx)] at h
    exact h
  · rw [cutoffAtIteratedLogProduct, if_neg hx]

/-- Once an argument is bounded, every renewal height is bounded by one
fixed finite height at the endpoint. -/
theorem renewalProduct_le_fixed_of_le {u U : ℝ} (hU : 0 ≤ U)
    (hu : u ≤ U) (n : ℕ) :
    renewalProduct n u ≤
      renewalProduct (Nat.ceil U + 1) U := by
  let H := Nat.ceil U + 1
  have hUH : U < (H : ℕ) := by
    dsimp [H]
    have hceil : U ≤ (Nat.ceil U : ℕ) := Nat.le_ceil U
    exact lt_of_le_of_lt hceil (by exact_mod_cast (Nat.lt_succ_self (Nat.ceil U)))
  have harg : renewalArgument H u ≤ renewalThreshold := by
    by_contra hnot
    have hactive : renewalThreshold < renewalArgument H u := lt_of_not_ge hnot
    have hheight := renewalThreshold_add_le_of_lt_argument H u hactive
    have hHle : (H : ℕ) ≤ u := by
      have hT0 : 0 ≤ renewalThreshold := by
        rw [renewalThreshold]
        positivity
      exact le_trans (by linarith) hheight
    nlinarith
  have hheightBound : renewalProduct n u ≤ renewalProduct H u := by
    by_cases hn : n ≤ H
    · exact renewalProduct_mono_height u hn
    · have hHn : H ≤ n := by omega
      rw [renewalProduct_stable_of_argument_le H u harg n hHn]
  exact le_trans hheightBound (monotone_renewalProduct H hu)

end Research
