import Research.LowerProduct

/-! # Right-endpoint lower mesh estimates -/

namespace Research

/-- A right-endpoint Riemann sum over a monotone mesh dominates a monotone
power-tail rectangle.  The explicit crossing index avoids any continuous
integration or discretization error. -/
theorem power_tail_le_right_mesh_sum
    (f : ℝ → ℝ) (w : ℕ → ℝ) (hf : Monotone f) (hw : Monotone w)
    {t : ℝ} {a y : ℕ} (ha2 : 2 ≤ a) (hay : a < y)
    (hwa : w a ≤ t) (htnext : t ≤ w (a + 1))
    (hft : 0 ≤ f t)
    (hnonneg : ∀ i ∈ Finset.Ico 2 y, 0 ≤ f (w (i + 1))) :
    f t * (w y - t) ≤
      ∑ i ∈ Finset.Ico 2 y, f (w (i + 1)) * (w (i + 1) - w i) := by
  have htailSubset : Finset.Ico a y ⊆ Finset.Ico 2 y := by
    intro i hi
    rw [Finset.mem_Ico] at hi ⊢
    omega
  have htailLe :
      ∑ i ∈ Finset.Ico a y, f (w (i + 1)) * (w (i + 1) - w i) ≤
        ∑ i ∈ Finset.Ico 2 y, f (w (i + 1)) * (w (i + 1) - w i) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg htailSubset
    intro i hiBig hiTail
    exact mul_nonneg (hnonneg i hiBig)
      (sub_nonneg.mpr (hw (by omega)))
  have hrect : f t * (w y - w a) ≤
      ∑ i ∈ Finset.Ico a y, f (w (i + 1)) * (w (i + 1) - w i) := by
    rw [← Finset.sum_Ico_sub w (le_of_lt hay), Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hai : a ≤ i := (Finset.mem_Ico.mp hi).1
    have htwi : t ≤ w (i + 1) :=
      le_trans htnext (hw (by omega))
    exact mul_le_mul_of_nonneg_right (hf htwi)
      (sub_nonneg.mpr (hw (by omega)))
  have hlength : f t * (w y - t) ≤ f t * (w y - w a) :=
    mul_le_mul_of_nonneg_left (sub_le_sub_left hwa (w y)) hft
  exact le_trans hlength (le_trans hrect htailLe)

/-- Specialization to a power-tail point. -/
theorem rpow_tail_le_right_mesh_sum
    (f : ℝ → ℝ) (w : ℕ → ℝ) (hf : Monotone f) (hw : Monotone w)
    {x e : ℝ} {a y : ℕ} (ha2 : 2 ≤ a) (hay : a < y)
    (hwa : w a ≤ x ^ (1 - e)) (htnext : x ^ (1 - e) ≤ w (a + 1))
    (hft : 0 ≤ f (x ^ (1 - e)))
    (hnonneg : ∀ i ∈ Finset.Ico 2 y, 0 ≤ f (w (i + 1))) :
    f (x ^ (1 - e)) * (w y - x ^ (1 - e)) ≤
      ∑ i ∈ Finset.Ico 2 y, f (w (i + 1)) * (w (i + 1) - w i) :=
  power_tail_le_right_mesh_sum f w hf hw ha2 hay hwa htnext hft hnonneg

/-- The logarithmic mesh has a cell crossing every point strictly between
its value at two and its endpoint. -/
theorem exists_logLogNat_crossing {t : ℝ} {y : ℕ}
    (hy : 3 ≤ y) (htlow : logLogNat 2 ≤ t) (htop : t < logLogNat y) :
    ∃ a : ℕ, 2 ≤ a ∧ a < y ∧ logLogNat a ≤ t ∧
      t ≤ logLogNat (a + 1) := by
  let r : ℝ := Real.exp (Real.exp t)
  let a : ℕ := ⌊r⌋₊
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hr2 : (2 : ℝ) ≤ r := by
    have h1 := Real.exp_le_exp.mpr htlow
    dsimp [logLogNat] at h1
    rw [Real.exp_log hlog2] at h1
    have h2 := Real.exp_le_exp.mpr h1
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h2
    exact h2
  have ha2 : 2 ≤ a := by
    apply Nat.le_floor
    exact hr2
  have har : (a : ℝ) ≤ r := Nat.floor_le (by positivity)
  have hrSucc : r < (a : ℝ) + 1 := Nat.lt_floor_add_one r
  have hrY : r < (y : ℝ) := by
    have h1 := Real.exp_lt_exp.mpr htop
    dsimp [logLogNat] at h1
    have hlogy : 0 < Real.log (y : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < y by omega))
    rw [Real.exp_log hlogy] at h1
    have h2 := Real.exp_lt_exp.mpr h1
    rw [Real.exp_log (by positivity : (0 : ℝ) < y)] at h2
    exact h2
  have hay : a < y := by
    rw [Nat.floor_lt (by positivity : 0 ≤ r)]
    exact hrY
  have hwa : logLogNat a ≤ t := by
    have haPos : (0 : ℝ) < a := by positivity
    have hlogA : Real.log (a : ℝ) ≤ Real.exp t := by
      have := Real.log_le_log haPos har
      dsimp [r] at this
      rw [Real.log_exp] at this
      exact this
    have hlogAPos : 0 < Real.log (a : ℝ) :=
      Real.log_pos (by exact_mod_cast ha2)
    have := Real.log_le_log hlogAPos hlogA
    rw [Real.log_exp] at this
    exact this
  have hnext : t ≤ logLogNat (a + 1) := by
    have ha1Pos : (0 : ℝ) < (a + 1 : ℕ) := by positivity
    have hfirst : Real.exp t < Real.log (a + 1 : ℕ) := by
      have := Real.log_lt_log (by positivity : (0 : ℝ) < r) hrSucc
      dsimp [r] at this
      rw [Real.log_exp] at this
      norm_num only [Nat.cast_add, Nat.cast_one]
      exact this
    have hlogNextPos : 0 < Real.log (a + 1 : ℕ) :=
      Real.log_pos (by exact_mod_cast (show 1 < a + 1 by omega))
    have := Real.log_le_log (by positivity : (0 : ℝ) < Real.exp t) hfirst.le
    rw [Real.log_exp] at this
    exact this
  exact ⟨a, ha2, hay, hwa, hnext⟩

/-- Globally monotone extension of the natural double-log mesh. -/
noncomputable def clampedLogLogNat (n : ℕ) : ℝ := logLogNat (max 2 n)

theorem monotone_clampedLogLogNat : Monotone clampedLogLogNat := by
  intro a b hab
  apply logLogNat_mono (le_max_left 2 a)
  exact max_le_max le_rfl hab

@[simp] theorem clampedLogLogNat_eq {n : ℕ} (hn : 2 ≤ n) :
    clampedLogLogNat n = logLogNat n := by
  rw [clampedLogLogNat, max_eq_right hn]

/-- Quantitative lower transform for a high iterated-log product.  All losses
are exposed in the single parameter `e`; later `e=e_k` is chosen summably. -/
theorem iteratedLogProduct_right_mesh_lower
    (k y : ℕ) (e : ℝ) (hy : 3 ≤ y)
    (he0 : 0 < e) (he2 : e ≤ 1 / 2)
    (hx1 : 1 < logLogNat y)
    (htlow : logLogNat 2 ≤ logLogNat y ^ (1 - e))
    (htower : realTower 2 k ≤ logLogNat y ^ (1 - e))
    (hratio : logLogNat y ^ (1 - e) ≤ e * logLogNat y)
    (horbit : ∀ j, 1 ≤ j → j ≤ k →
      2 ≤ iteratedLog j (logLogNat y)) :
    (1 - e) ^ (k + 1) * logLogNat y *
        iteratedLogProduct k (logLogNat y) ≤
      ∑ i ∈ Finset.Ico 2 y,
        clampedIteratedLogProduct k (logLogNat (i + 1)) *
          (logLogNat (i + 1) - logLogNat i) := by
  let x := logLogNat y
  let t := x ^ (1 - e)
  have htlt : t < x := by
    dsimp [t, x]
    exact Real.rpow_lt_self_of_one_lt hx1 (by linarith)
  obtain ⟨a, ha2, hay, hwa, hnext⟩ :=
    exists_logLogNat_crossing hy htlow htlt
  have hmesh := power_tail_le_right_mesh_sum
    (clampedIteratedLogProduct k) clampedLogLogNat
    (monotone_clampedIteratedLogProduct k) monotone_clampedLogLogNat
    ha2 hay (by simpa [clampedLogLogNat_eq ha2] using hwa)
    (by simpa [clampedLogLogNat_eq (show 2 ≤ a + 1 by omega)] using hnext)
    (clampedIteratedLogProduct_nonneg k t)
    (fun i hi => clampedIteratedLogProduct_nonneg k (clampedLogLogNat (i + 1)))
  have hsumEq :
      (∑ i ∈ Finset.Ico 2 y,
        clampedIteratedLogProduct k (clampedLogLogNat (i + 1)) *
          (clampedLogLogNat (i + 1) - clampedLogLogNat i)) =
      ∑ i ∈ Finset.Ico 2 y,
        clampedIteratedLogProduct k (logLogNat (i + 1)) *
          (logLogNat (i + 1) - logLogNat i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [clampedLogLogNat_eq (show 2 ≤ i by
      have := (Finset.mem_Ico.mp hi).1; omega),
      clampedLogLogNat_eq (show 2 ≤ i + 1 by
        have := (Finset.mem_Ico.mp hi).1
        omega)]
  rw [hsumEq, clampedLogLogNat_eq (show 2 ≤ y by omega)] at hmesh
  have htower' : realTower 2 k ≤ t := by simpa [t, x] using htower
  rw [clampedIteratedLogProduct_eq htower'] at hmesh
  change iteratedLogProduct k t * (x - t) ≤ _ at hmesh
  have htx : realTower 2 k ≤ x :=
    le_trans htower' (le_of_lt htlt)
  have hprod := iteratedLogProduct_rpow_scale_lower k he0.le he2 hx1 horbit
  have hlength : (1 - e) * x ≤ x - t := by
    dsimp [t, x] at hratio ⊢
    linarith
  have hnonnegP : 0 ≤ iteratedLogProduct k x := by
    have hclamp := clampedIteratedLogProduct_nonneg k x
    rw [clampedIteratedLogProduct_eq htx] at hclamp
    exact hclamp
  have hnonnegT : 0 ≤ iteratedLogProduct k t := by
    have hclamp := clampedIteratedLogProduct_nonneg k t
    rw [clampedIteratedLogProduct_eq htower'] at hclamp
    exact hclamp
  have hfactor : 0 ≤ (1 - e) * x :=
    mul_nonneg (by linarith) (le_trans (by norm_num) hx1.le)
  have hmul := mul_le_mul hprod hlength hfactor hnonnegT
  change ((1 - e) ^ k * iteratedLogProduct k x) * ((1 - e) * x) ≤
    iteratedLogProduct k t * (x - t) at hmul
  have hcombine : (1 - e) ^ (k + 1) * x * iteratedLogProduct k x ≤
      iteratedLogProduct k t * (x - t) := by
    calc
      (1 - e) ^ (k + 1) * x * iteratedLogProduct k x =
          ((1 - e) ^ k * iteratedLogProduct k x) * ((1 - e) * x) := by
        rw [pow_succ]
        ring
      _ ≤ iteratedLogProduct k t * (x - t) := hmul
  exact le_trans hcombine hmesh

/-- High-cutoff counterpart of `iteratedLogProduct_right_mesh_lower`. -/
theorem iteratedLogProduct_cutoff_right_mesh_lower
    (H : ℝ) (k y : ℕ) (e : ℝ) (hH : 2 ≤ H) (hy : 3 ≤ y)
    (he0 : 0 < e) (he2 : e ≤ 1 / 2)
    (hx1 : 1 < logLogNat y)
    (htlow : logLogNat 2 ≤ logLogNat y ^ (1 - e))
    (htower : realTower H k ≤ logLogNat y ^ (1 - e))
    (hratio : logLogNat y ^ (1 - e) ≤ e * logLogNat y)
    (horbit : ∀ j, 1 ≤ j → j ≤ k →
      2 ≤ iteratedLog j (logLogNat y)) :
    (1 - e) ^ (k + 1) * logLogNat y *
        iteratedLogProduct k (logLogNat y) ≤
      ∑ i ∈ Finset.Ico 2 y,
        cutoffIteratedLogProduct H k (logLogNat (i + 1)) *
          (logLogNat (i + 1) - logLogNat i) := by
  let x := logLogNat y
  let t := x ^ (1 - e)
  have htlt : t < x := by
    dsimp [t, x]
    exact Real.rpow_lt_self_of_one_lt hx1 (by linarith)
  obtain ⟨a, ha2, hay, hwa, hnext⟩ :=
    exists_logLogNat_crossing hy htlow htlt
  have hmesh := power_tail_le_right_mesh_sum
    (cutoffIteratedLogProduct H k) clampedLogLogNat
    (monotone_cutoffIteratedLogProduct hH k) monotone_clampedLogLogNat
    ha2 hay (by simpa [clampedLogLogNat_eq ha2] using hwa)
    (by simpa [clampedLogLogNat_eq (show 2 ≤ a + 1 by omega)] using hnext)
    (cutoffIteratedLogProduct_nonneg hH k t)
    (fun i hi => cutoffIteratedLogProduct_nonneg hH k (clampedLogLogNat (i + 1)))
  have hsumEq :
      (∑ i ∈ Finset.Ico 2 y,
        cutoffIteratedLogProduct H k (clampedLogLogNat (i + 1)) *
          (clampedLogLogNat (i + 1) - clampedLogLogNat i)) =
      ∑ i ∈ Finset.Ico 2 y,
        cutoffIteratedLogProduct H k (logLogNat (i + 1)) *
          (logLogNat (i + 1) - logLogNat i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [clampedLogLogNat_eq (show 2 ≤ i by
      have := (Finset.mem_Ico.mp hi).1
      omega),
      clampedLogLogNat_eq (show 2 ≤ i + 1 by
        have := (Finset.mem_Ico.mp hi).1
        omega)]
  rw [hsumEq, clampedLogLogNat_eq (show 2 ≤ y by omega)] at hmesh
  have htower' : realTower H k ≤ t := by simpa [t, x] using htower
  rw [cutoffIteratedLogProduct_eq htower'] at hmesh
  change iteratedLogProduct k t * (x - t) ≤ _ at hmesh
  have hprod := iteratedLogProduct_rpow_scale_lower k he0.le he2 hx1 horbit
  have hlength : (1 - e) * x ≤ x - t := by
    dsimp [t, x] at hratio ⊢
    linarith
  have hnonnegT : 0 ≤ iteratedLogProduct k t := by
    have h := cutoffIteratedLogProduct_nonneg hH k t
    rw [cutoffIteratedLogProduct_eq htower'] at h
    exact h
  have hfactor : 0 ≤ (1 - e) * x :=
    mul_nonneg (by linarith) (le_trans (by norm_num) hx1.le)
  have hmul := mul_le_mul hprod hlength hfactor hnonnegT
  change ((1 - e) ^ k * iteratedLogProduct k x) * ((1 - e) * x) ≤
    iteratedLogProduct k t * (x - t) at hmul
  apply le_trans ?_ hmesh
  calc
    (1 - e) ^ (k + 1) * logLogNat y *
        iteratedLogProduct k (logLogNat y) =
      ((1 - e) ^ k * iteratedLogProduct k x) * ((1 - e) * x) := by
        dsimp [x]
        rw [pow_succ]
        ring
    _ ≤ iteratedLogProduct k t * (x - t) := hmul


/-- Arbitrary-cutoff counterpart used by adaptive thresholds. -/
theorem iteratedLogProduct_cutoffAt_right_mesh_lower
    (A : ℝ) (k y : ℕ) (e : ℝ)
    (hfloor : realTower 2 k ≤ A) (hy : 3 ≤ y)
    (he0 : 0 < e) (he2 : e ≤ 1 / 2)
    (hx1 : 1 < logLogNat y)
    (htlow : logLogNat 2 ≤ logLogNat y ^ (1 - e))
    (htower : A ≤ logLogNat y ^ (1 - e))
    (hratio : logLogNat y ^ (1 - e) ≤ e * logLogNat y)
    (horbit : ∀ j, 1 ≤ j → j ≤ k →
      2 ≤ iteratedLog j (logLogNat y)) :
    (1 - e) ^ (k + 1) * logLogNat y *
        iteratedLogProduct k (logLogNat y) ≤
      ∑ i ∈ Finset.Ico 2 y,
        cutoffAtIteratedLogProduct A k (logLogNat (i + 1)) *
          (logLogNat (i + 1) - logLogNat i) := by
  let x := logLogNat y
  let t := x ^ (1 - e)
  have htlt : t < x := by
    dsimp [t, x]
    exact Real.rpow_lt_self_of_one_lt hx1 (by linarith)
  obtain ⟨a, ha2, hay, hwa, hnext⟩ :=
    exists_logLogNat_crossing hy htlow htlt
  have hmesh := power_tail_le_right_mesh_sum
    (cutoffAtIteratedLogProduct A k) clampedLogLogNat
    (monotone_cutoffAtIteratedLogProduct hfloor) monotone_clampedLogLogNat
    ha2 hay (by simpa [clampedLogLogNat_eq ha2] using hwa)
    (by simpa [clampedLogLogNat_eq (show 2 ≤ a + 1 by omega)] using hnext)
    (cutoffAtIteratedLogProduct_nonneg hfloor t)
    (fun i hi => cutoffAtIteratedLogProduct_nonneg hfloor (clampedLogLogNat (i + 1)))
  have hsumEq :
      (∑ i ∈ Finset.Ico 2 y,
        cutoffAtIteratedLogProduct A k (clampedLogLogNat (i + 1)) *
          (clampedLogLogNat (i + 1) - clampedLogLogNat i)) =
      ∑ i ∈ Finset.Ico 2 y,
        cutoffAtIteratedLogProduct A k (logLogNat (i + 1)) *
          (logLogNat (i + 1) - logLogNat i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [clampedLogLogNat_eq (show 2 ≤ i by
      have := (Finset.mem_Ico.mp hi).1
      omega),
      clampedLogLogNat_eq (show 2 ≤ i + 1 by
        have := (Finset.mem_Ico.mp hi).1
        omega)]
  rw [hsumEq, clampedLogLogNat_eq (show 2 ≤ y by omega)] at hmesh
  have htower' : A ≤ t := by simpa [t, x] using htower
  rw [cutoffAtIteratedLogProduct_eq htower'] at hmesh
  change iteratedLogProduct k t * (x - t) ≤ _ at hmesh
  have hprod := iteratedLogProduct_rpow_scale_lower k he0.le he2 hx1 horbit
  have hlength : (1 - e) * x ≤ x - t := by
    dsimp [t, x] at hratio ⊢
    linarith
  have hnonnegT : 0 ≤ iteratedLogProduct k t := by
    have h := cutoffAtIteratedLogProduct_nonneg hfloor t
    rw [cutoffAtIteratedLogProduct_eq htower'] at h
    exact h
  have hfactor : 0 ≤ (1 - e) * x :=
    mul_nonneg (by linarith) (le_trans (by norm_num) hx1.le)
  have hmul := mul_le_mul hprod hlength hfactor hnonnegT
  change ((1 - e) ^ k * iteratedLogProduct k x) * ((1 - e) * x) ≤
    iteratedLogProduct k t * (x - t) at hmul
  apply le_trans ?_ hmesh
  calc
    (1 - e) ^ (k + 1) * logLogNat y *
        iteratedLogProduct k (logLogNat y) =
      ((1 - e) ^ k * iteratedLogProduct k x) * ((1 - e) * x) := by
        dsimp [x]
        rw [pow_succ]
        ring
    _ ≤ iteratedLogProduct k t * (x - t) := hmul

end Research
