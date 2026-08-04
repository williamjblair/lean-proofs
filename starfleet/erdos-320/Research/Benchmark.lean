import Mathlib

/-!
# The full-depth iterated-log benchmark

A finite height parameter makes the stopped iterated-log product easy to use in
Lean. Once the logarithmic orbit has crossed the threshold, increasing the
height no longer changes the value.
-/

namespace Research

/-- Fixed stopping threshold for the renewal product. -/
noncomputable def renewalThreshold : ℝ := Real.exp 3

/-- `renewalProduct k x` multiplies successive logarithms until either `k`
factors have been used or the current argument is at most `exp 3`. -/
noncomputable def renewalProduct : ℕ → ℝ → ℝ
  | 0, _ => 1
  | k + 1, x =>
      if x ≤ renewalThreshold then 1
      else Real.log x * renewalProduct k (Real.log x)

/-- Argument remaining after at most `k` stopped logarithm steps. -/
noncomputable def renewalArgument : ℕ → ℝ → ℝ
  | 0, x => x
  | k + 1, x =>
      if x ≤ renewalThreshold then x else renewalArgument k (Real.log x)

@[simp]
theorem renewalArgument_zero (x : ℝ) : renewalArgument 0 x = x := rfl

@[simp]
theorem renewalArgument_of_le (k : ℕ) {x : ℝ}
    (hx : x ≤ renewalThreshold) : renewalArgument k x = x := by
  cases k with
  | zero => rfl
  | succ k => rw [renewalArgument, if_pos hx]

@[simp]
theorem renewalArgument_succ_of_lt (k : ℕ) {x : ℝ}
    (hx : renewalThreshold < x) :
    renewalArgument (k + 1) x = renewalArgument k (Real.log x) := by
  rw [renewalArgument, if_neg (not_le.mpr hx)]

@[simp]
theorem renewalProduct_zero (x : ℝ) : renewalProduct 0 x = 1 := rfl

@[simp]
theorem renewalProduct_of_le (k : ℕ) {x : ℝ}
    (hx : x ≤ renewalThreshold) : renewalProduct (k + 1) x = 1 := by
  rw [renewalProduct, if_pos hx]

@[simp]
theorem renewalProduct_of_lt (k : ℕ) {x : ℝ}
    (hx : renewalThreshold < x) :
    renewalProduct (k + 1) x =
      Real.log x * renewalProduct k (Real.log x) := by
  rw [renewalProduct, if_neg (not_le.mpr hx)]

/-- Every stopped product is at least one. -/
theorem one_le_renewalProduct (k : ℕ) (x : ℝ) :
    1 ≤ renewalProduct k x := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
      by_cases hx : x ≤ renewalThreshold
      · simp [renewalProduct_of_le k hx]
      · rw [renewalProduct_of_lt k (lt_of_not_ge hx)]
        have hlog : 3 < Real.log x := by
          rw [← Real.log_exp 3]
          exact Real.strictMonoOn_log
            (by positivity : (0 : ℝ) < Real.exp 3)
            (lt_trans (by positivity : (0 : ℝ) < Real.exp 3) (lt_of_not_ge hx))
            (lt_of_not_ge hx)
        have hone := ih (Real.log x)
        nlinarith

/-- Adding one permitted logarithmic factor can only increase the stopped
product. -/
theorem renewalProduct_le_succ (k : ℕ) (x : ℝ) :
    renewalProduct k x ≤ renewalProduct (k + 1) x := by
  induction k generalizing x with
  | zero => exact one_le_renewalProduct 1 x
  | succ k ih =>
      by_cases hx : x ≤ renewalThreshold
      · simp [renewalProduct_of_le k hx, renewalProduct_of_le (k + 1) hx]
      · have hTx : renewalThreshold < x := lt_of_not_ge hx
        rw [renewalProduct_of_lt k hTx, renewalProduct_of_lt (k + 1) hTx]
        have hlog : 0 ≤ Real.log x := by
          have : 3 < Real.log x := by
            rw [← Real.log_exp 3]
            exact Real.strictMonoOn_log
              (by positivity : (0 : ℝ) < Real.exp 3)
              (lt_trans (by positivity : (0 : ℝ) < Real.exp 3) hTx) hTx
          linarith
        exact mul_le_mul_of_nonneg_left (ih (Real.log x)) hlog

/-- The stopped products are monotone in their height parameter. -/
theorem renewalProduct_mono_height (x : ℝ) :
    Monotone (fun k => renewalProduct k x) :=
  monotone_nat_of_le_succ (fun k => renewalProduct_le_succ k x)

/-- Once the stopped logarithmic orbit reaches the threshold, increasing
the product height does not change its value. -/
theorem renewalProduct_stable_of_argument_le (k : ℕ) (x : ℝ)
    (hstop : renewalArgument k x ≤ renewalThreshold) :
    ∀ l, k ≤ l → renewalProduct l x = renewalProduct k x := by
  induction k generalizing x with
  | zero =>
      intro l _
      have hx : x ≤ renewalThreshold := by simpa using hstop
      cases l with
      | zero => rfl
      | succ l => simp [renewalProduct_of_le l hx]
  | succ k ih =>
      intro l hkl
      by_cases hx : x ≤ renewalThreshold
      · have hlPos : 0 < l := by omega
        obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hlPos)
        simp [renewalProduct_of_le k hx, renewalProduct_of_le j hx]
      · have hTx : renewalThreshold < x := lt_of_not_ge hx
        have hstop' : renewalArgument k (Real.log x) ≤ renewalThreshold := by
          simpa [renewalArgument_succ_of_lt k hTx] using hstop
        have hlPos : 0 < l := by omega
        obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hlPos)
        have hkj : k ≤ j := by omega
        rw [renewalProduct_of_lt k hTx, renewalProduct_of_lt j hTx]
        rw [ih (Real.log x) hstop' j hkj]

/-- If the orbit remains above threshold for `k` steps, its initial argument
must exceed the threshold by at least `k`. -/
theorem renewalThreshold_add_le_of_lt_argument (k : ℕ) (x : ℝ)
    (hactive : renewalThreshold < renewalArgument k x) :
    renewalThreshold + k ≤ x := by
  induction k generalizing x with
  | zero => simpa using hactive.le
  | succ k ih =>
      by_cases hx : x ≤ renewalThreshold
      · rw [renewalArgument_of_le (k + 1) hx] at hactive
        exact False.elim (not_lt_of_ge hx hactive)
      · have hTx : renewalThreshold < x := lt_of_not_ge hx
        have hnext : renewalThreshold < renewalArgument k (Real.log x) := by
          simpa [renewalArgument_succ_of_lt k hTx] using hactive
        have hih := ih (Real.log x) hnext
        have hlog : Real.log x ≤ x - 1 :=
          Real.log_le_sub_one_of_pos (lt_trans (by
            rw [renewalThreshold]
            positivity) hTx)
        norm_num at hih ⊢
        linarith

/-- For fixed height, the stopped product is monotone in its argument. -/
theorem monotone_renewalProduct (k : ℕ) :
    Monotone (renewalProduct k) := by
  induction k with
  | zero => intro x y hxy; simp
  | succ k ih =>
      intro x y hxy
      by_cases hx : x ≤ renewalThreshold
      · rw [renewalProduct_of_le k hx]
        exact one_le_renewalProduct (k + 1) y
      · have hTx : renewalThreshold < x := lt_of_not_ge hx
        have hTy : renewalThreshold < y := lt_of_lt_of_le hTx hxy
        rw [renewalProduct_of_lt k hTx, renewalProduct_of_lt k hTy]
        have hTpos : (0 : ℝ) < renewalThreshold := by
          rw [renewalThreshold]
          positivity
        have hxpos : 0 < x := lt_trans hTpos hTx
        have hlogxy : Real.log x ≤ Real.log y := Real.log_le_log hxpos hxy
        exact mul_le_mul hlogxy (ih hlogxy)
          (by exact le_trans (by norm_num) (one_le_renewalProduct k (Real.log x)))
          (by
            have : 3 < Real.log y := by
              rw [← Real.log_exp 3]
              exact Real.strictMonoOn_log
                (by positivity : (0 : ℝ) < Real.exp 3)
                (lt_trans (by positivity : (0 : ℝ) < Real.exp 3) hTy) hTy
            linarith)

/-- A monotone Riemann sum against monotone mesh increments is bounded by
the endpoint value times the total mesh length. This is the discrete renewal
estimate used for the logarithmic mesh `w_m = log(log m)`. -/
theorem sum_mul_succ_sub_le_endpoint
    (f : ℝ → ℝ) (w : ℕ → ℝ) (hf : Monotone f) (hw : Monotone w)
    {a b : ℕ} (hab : a ≤ b) :
    ∑ i ∈ Finset.Ico a b, f (w i) * (w (i + 1) - w i) ≤
      f (w b) * (w b - w a) := by
  calc
    ∑ i ∈ Finset.Ico a b, f (w i) * (w (i + 1) - w i) ≤
        ∑ i ∈ Finset.Ico a b, f (w b) * (w (i + 1) - w i) := by
      apply Finset.sum_le_sum
      intro i hi
      have hib : i ≤ b := by
        have := (Finset.mem_Ico.mp hi).2
        omega
      exact mul_le_mul_of_nonneg_right (hf (hw hib))
        (sub_nonneg.mpr (hw (by omega)))
    _ = f (w b) * (∑ i ∈ Finset.Ico a b, (w (i + 1) - w i)) := by
      rw [Finset.mul_sum]
    _ = f (w b) * (w b - w a) := by
      rw [Finset.sum_Ico_sub w hab]

/-- Specialization of the telescoping estimate to the stopped renewal
product. -/
theorem renewalProduct_mesh_sum_le (k : ℕ)
    (w : ℕ → ℝ) (hw : Monotone w) {a b : ℕ} (hab : a ≤ b) :
    ∑ i ∈ Finset.Ico a b,
        renewalProduct k (w i) * (w (i + 1) - w i) ≤
      renewalProduct k (w b) * (w b - w a) :=
  sum_mul_succ_sub_le_endpoint _ _ (monotone_renewalProduct k) hw hab

/-- Natural logarithm iterated twice on a natural argument. -/
noncomputable def logLogNat (n : ℕ) : ℝ :=
  Real.log (Real.log (n : ℝ))

/-- `logLogNat` is monotone once its natural arguments are at least two. -/
theorem logLogNat_mono {a b : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) :
    logLogNat a ≤ logLogNat b := by
  have haPos : (0 : ℝ) < a := by positivity
  have hlogPos : 0 < Real.log (a : ℝ) :=
    Real.log_pos (by exact_mod_cast ha)
  have hlogLe : Real.log (a : ℝ) ≤ Real.log (b : ℝ) :=
    Real.log_le_log haPos (by exact_mod_cast hab)
  exact Real.log_le_log hlogPos hlogLe

/-- Height `N` is already beyond the stopping depth for the benchmark argument
`log(log N)`. -/
theorem renewalArgument_self_le_threshold (N : ℕ) (hN : 3 ≤ N) :
    renewalArgument N (logLogNat N) ≤ renewalThreshold := by
  by_contra h
  have hactive : renewalThreshold < renewalArgument N (logLogNat N) :=
    lt_of_not_ge h
  have hlower := renewalThreshold_add_le_of_lt_argument N (logLogNat N) hactive
  have hNpos : (0 : ℝ) < N := by positivity
  have hlogNpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hll : logLogNat N ≤ Real.log (N : ℝ) := by
    have h := Real.log_le_sub_one_of_pos hlogNpos
    dsimp [logLogNat]
    linarith
  have hlogN : Real.log (N : ℝ) ≤ (N : ℝ) := by
    have h := Real.log_le_sub_one_of_pos hNpos
    linarith
  have hTpos : 0 < renewalThreshold := by
    rw [renewalThreshold]
    positivity
  norm_num at hlower
  linarith

/-- Hence all heights at least `N` give the same fully stopped product. -/
theorem renewalProduct_stable_at_self (N l : ℕ) (hN : 3 ≤ N) (hNl : N ≤ l) :
    renewalProduct l (logLogNat N) = renewalProduct N (logLogNat N) :=
  renewalProduct_stable_of_argument_le N (logLogNat N)
    (renewalArgument_self_le_threshold N hN) l hNl

/-- Interval-local form of the monotone-mesh telescope. -/
theorem sum_mul_succ_sub_le_endpoint_of_interval
    (f : ℝ → ℝ) (w : ℕ → ℝ) (hf : Monotone f)
    {a b : ℕ} (hab : a ≤ b)
    (hwb : ∀ i ∈ Finset.Ico a b, w i ≤ w b)
    (hstep : ∀ i ∈ Finset.Ico a b, w i ≤ w (i + 1)) :
    ∑ i ∈ Finset.Ico a b, f (w i) * (w (i + 1) - w i) ≤
      f (w b) * (w b - w a) := by
  calc
    ∑ i ∈ Finset.Ico a b, f (w i) * (w (i + 1) - w i) ≤
        ∑ i ∈ Finset.Ico a b, f (w b) * (w (i + 1) - w i) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_right (hf (hwb i hi))
        (sub_nonneg.mpr (hstep i hi))
    _ = f (w b) * (∑ i ∈ Finset.Ico a b, (w (i + 1) - w i)) := by
      rw [Finset.mul_sum]
    _ = f (w b) * (w b - w a) := by
      rw [Finset.sum_Ico_sub w hab]

/-- A quantitative lower bound for one increment of the double-logarithm
mesh. -/
theorem one_div_mul_log_succ_le_logLogNat_sub (n : ℕ) (hn : 2 ≤ n) :
    1 / (((n + 1 : ℕ) : ℝ) * Real.log (n + 1 : ℕ)) ≤
      logLogNat (n + 1) - logLogNat n := by
  have hnpos : (0 : ℝ) < n := by positivity
  have hspos : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have hlogn : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast hn)
  have hlogs : 0 < Real.log ((n + 1 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n + 1 by omega))
  have hratio : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) / n := div_pos hspos hnpos
  have hd0 := Real.one_sub_inv_le_log_of_pos hratio
  have hd : 1 / ((n + 1 : ℕ) : ℝ) ≤
      Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ) := by
    calc
      1 / ((n + 1 : ℕ) : ℝ) =
          1 - ((((n + 1 : ℕ) : ℝ) / n)⁻¹) := by
        field_simp
        norm_num
      _ ≤ Real.log (((n + 1 : ℕ) : ℝ) / n) := hd0
      _ = Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ) := by
        rw [Real.log_div hspos.ne' hnpos.ne']
  have hdiv := div_le_div_of_nonneg_right hd hlogs.le
  have hout := Real.one_sub_inv_le_log_of_pos (div_pos hlogs hlogn)
  dsimp [logLogNat]
  calc
    1 / (((n + 1 : ℕ) : ℝ) * Real.log (n + 1 : ℕ)) =
        (1 / ((n + 1 : ℕ) : ℝ)) / Real.log (n + 1 : ℕ) := by ring
    _ ≤ (Real.log (n + 1 : ℕ) - Real.log (n : ℝ)) /
        Real.log (n + 1 : ℕ) := hdiv
    _ = 1 - ((Real.log (n + 1 : ℕ) / Real.log (n : ℝ))⁻¹) := by
      field_simp
    _ ≤ Real.log (Real.log (n + 1 : ℕ) / Real.log (n : ℝ)) := hout
    _ = Real.log (Real.log (n + 1 : ℕ)) -
        Real.log (Real.log (n : ℝ)) := by
      rw [Real.log_div hlogs.ne' hlogn.ne']

/-- A matching upper bound for one increment of the double-logarithm
mesh. -/
theorem logLogNat_sub_le_one_div_mul_log (n : ℕ) (hn : 2 ≤ n) :
    logLogNat (n + 1) - logLogNat n ≤
      1 / ((n : ℝ) * Real.log n) := by
  have hnpos : (0 : ℝ) < n := by positivity
  have hspos : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have hlogn : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast hn)
  have hlogs : 0 < Real.log ((n + 1 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n + 1 by omega))
  have hd0 := Real.log_le_sub_one_of_pos (div_pos hspos hnpos)
  have hd : Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ) ≤
      1 / (n : ℝ) := by
    calc
      Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ) =
          Real.log (((n + 1 : ℕ) : ℝ) / n) := by
        rw [Real.log_div hspos.ne' hnpos.ne']
      _ ≤ (((n + 1 : ℕ) : ℝ) / n) - 1 := hd0
      _ = 1 / (n : ℝ) := by
        field_simp
        norm_num
  have hout := Real.log_le_sub_one_of_pos (div_pos hlogs hlogn)
  dsimp [logLogNat]
  calc
    Real.log (Real.log (n + 1 : ℕ)) - Real.log (Real.log (n : ℝ)) =
        Real.log (Real.log (n + 1 : ℕ) / Real.log (n : ℝ)) := by
      rw [Real.log_div hlogs.ne' hlogn.ne']
    _ ≤ Real.log (n + 1 : ℕ) / Real.log (n : ℝ) - 1 := hout
    _ = (Real.log (n + 1 : ℕ) - Real.log (n : ℝ)) /
        Real.log n := by
      field_simp
    _ ≤ (1 / (n : ℝ)) / Real.log n :=
      div_le_div_of_nonneg_right hd hlogn.le
    _ = 1 / ((n : ℝ) * Real.log n) := by ring

/-- A discrete benchmark whose renewal weights telescope exactly. -/
noncomputable def discreteRenewalBenchmark (k n : ℕ) : ℝ :=
  (n : ℝ) * (n + 1) * renewalProduct k (logLogNat n) *
    (logLogNat (n + 1) - logLogNat n)

/-- The discrete benchmark is monotone in its height parameter on the
intended natural range. -/
theorem discreteRenewalBenchmark_mono_height (n : ℕ) (hn : 2 ≤ n) :
    Monotone (fun k => discreteRenewalBenchmark k n) := by
  intro k l hkl
  change (n : ℝ) * (n + 1) * renewalProduct k (logLogNat n) *
      (logLogNat (n + 1) - logLogNat n) ≤
    (n : ℝ) * (n + 1) * renewalProduct l (logLogNat n) *
      (logLogNat (n + 1) - logLogNat n)
  have hP := renewalProduct_mono_height (logLogNat n) hkl
  have hmesh : 0 ≤ logLogNat (n + 1) - logLogNat n :=
    sub_nonneg.mpr (logLogNat_mono hn (by omega))
  have hfactor : 0 ≤ (n : ℝ) * (n + 1) := by positivity
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hP hfactor) hmesh

/-- The discrete renewal benchmark is nonnegative on its intended range. -/
theorem discreteRenewalBenchmark_nonneg (k n : ℕ) (hn : 2 ≤ n) :
    0 ≤ discreteRenewalBenchmark k n := by
  rw [discreteRenewalBenchmark]
  have hmesh : 0 ≤ logLogNat (n + 1) - logLogNat n :=
    sub_nonneg.mpr (logLogNat_mono hn (by omega))
  have hP : 0 ≤ renewalProduct k (logLogNat n) :=
    le_trans (by norm_num) (one_le_renewalProduct k (logLogNat n))
  positivity

/-- The discrete benchmark is at least its continuous-scale counterpart
with `log(n+1)` in the denominator. -/
theorem div_log_succ_mul_renewalProduct_le_discrete (k n : ℕ)
    (hn : 2 ≤ n) :
    (n : ℝ) / Real.log (n + 1 : ℕ) * renewalProduct k (logLogNat n) ≤
      discreteRenewalBenchmark k n := by
  have hmesh := one_div_mul_log_succ_le_logLogNat_sub n hn
  have hPnonneg : 0 ≤ renewalProduct k (logLogNat n) :=
    le_trans (by norm_num) (one_le_renewalProduct k (logLogNat n))
  have hlogne : Real.log ((n + 1 : ℕ) : ℝ) ≠ 0 := by
    have : 0 < Real.log ((n + 1 : ℕ) : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < n + 1 by omega))
    exact this.ne'
  let F : ℝ := (n : ℝ) * (n + 1) * renewalProduct k (logLogNat n)
  have hFnonneg : 0 ≤ F := by
    dsimp [F]
    positivity
  calc
    (n : ℝ) / Real.log (n + 1 : ℕ) * renewalProduct k (logLogNat n) =
        F * (1 / (((n + 1 : ℕ) : ℝ) * Real.log (n + 1 : ℕ))) := by
      dsimp [F]
      field_simp [hlogne]
      norm_num
    _ ≤ F * (logLogNat (n + 1) - logLogNat n) :=
      mul_le_mul_of_nonneg_left hmesh hFnonneg
    _ = discreteRenewalBenchmark k n := by
      rw [discreteRenewalBenchmark]

/-- The discrete benchmark is at most the corresponding continuous-scale
quantity with `n+1` in the numerator. -/
theorem discreteRenewalBenchmark_le_succ_div_log (k n : ℕ)
    (hn : 2 ≤ n) :
    discreteRenewalBenchmark k n ≤
      ((n + 1 : ℕ) : ℝ) / Real.log n * renewalProduct k (logLogNat n) := by
  have hmesh := logLogNat_sub_le_one_div_mul_log n hn
  have hPnonneg : 0 ≤ renewalProduct k (logLogNat n) :=
    le_trans (by norm_num) (one_le_renewalProduct k (logLogNat n))
  let F : ℝ := (n : ℝ) * (n + 1) * renewalProduct k (logLogNat n)
  have hFnonneg : 0 ≤ F := by dsimp [F]; positivity
  have hlogne : Real.log (n : ℝ) ≠ 0 := by
    exact (Real.log_pos (by exact_mod_cast hn)).ne'
  calc
    discreteRenewalBenchmark k n =
        F * (logLogNat (n + 1) - logLogNat n) := by
      rw [discreteRenewalBenchmark]
    _ ≤ F * (1 / ((n : ℝ) * Real.log n)) :=
      mul_le_mul_of_nonneg_left hmesh hFnonneg
    _ = ((n + 1 : ℕ) : ℝ) / Real.log n *
        renewalProduct k (logLogNat n) := by
      dsimp [F]
      field_simp [hlogne]
      norm_num
      ring

/-- The principal renewal transform of the discrete benchmark is bounded by
one endpoint value times the logarithmic mesh length. -/
theorem sum_discreteRenewalBenchmark_div_le (k M y : ℕ)
    (hM : 2 ≤ M) (hMy : M ≤ y) :
    ∑ m ∈ Finset.Ico M y,
        discreteRenewalBenchmark k m / ((m : ℝ) * (m + 1)) ≤
      renewalProduct k (logLogNat y) * (logLogNat y - logLogNat M) := by
  calc
    ∑ m ∈ Finset.Ico M y,
        discreteRenewalBenchmark k m / ((m : ℝ) * (m + 1)) =
      ∑ m ∈ Finset.Ico M y,
        renewalProduct k (logLogNat m) *
          (logLogNat (m + 1) - logLogNat m) := by
      apply Finset.sum_congr rfl
      intro m hm
      have hmPos : (0 : ℝ) < m := by
        exact_mod_cast (lt_of_lt_of_le (by omega : 0 < M)
          (Finset.mem_Ico.mp hm).1)
      simp only [discreteRenewalBenchmark]
      field_simp [ne_of_gt hmPos]
    _ ≤ renewalProduct k (logLogNat y) *
        (logLogNat y - logLogNat M) := by
      apply sum_mul_succ_sub_le_endpoint_of_interval
        (renewalProduct k) logLogNat (monotone_renewalProduct k) hMy
      · intro i hi
        exact logLogNat_mono
          (le_trans hM (Finset.mem_Ico.mp hi).1)
          (le_of_lt (Finset.mem_Ico.mp hi).2)
      · intro i hi
        exact logLogNat_mono
          (le_trans hM (Finset.mem_Ico.mp hi).1) (by omega)

/-- A coarse endpoint bound for the unweighted sum of discrete benchmark
values. It is deliberately simple; choosing the base cutoff `M` later makes
it sufficient for both error terms in the renewal induction. -/
theorem sum_discreteRenewalBenchmark_le (k M y : ℕ)
    (hM : 2 ≤ M) (hMy : M ≤ y) :
    ∑ m ∈ Finset.Ico M y, discreteRenewalBenchmark k m ≤
      (y : ℝ) ^ 2 / Real.log M * renewalProduct k (logLogNat y) := by
  have hy2 : 2 ≤ y := le_trans hM hMy
  have hlogM : 0 < Real.log (M : ℝ) :=
    Real.log_pos (by exact_mod_cast hM)
  let R : ℝ := (y : ℝ) / Real.log M * renewalProduct k (logLogNat y)
  have hterm : ∀ m ∈ Finset.Ico M y, discreteRenewalBenchmark k m ≤ R := by
    intro m hm
    have hmBounds := Finset.mem_Ico.mp hm
    have hm2 : 2 ≤ m := le_trans hM hmBounds.1
    have hsucc : m + 1 ≤ y := Nat.succ_le_iff.mpr hmBounds.2
    have hlogm : 0 < Real.log (m : ℝ) :=
      Real.log_pos (by exact_mod_cast hm2)
    have hlogle : Real.log (M : ℝ) ≤ Real.log (m : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast hmBounds.1)
    have hquot : ((m + 1 : ℕ) : ℝ) / Real.log m ≤
        (y : ℝ) / Real.log M :=
      div_le_div₀ (by positivity) (by exact_mod_cast hsucc) hlogM hlogle
    have hPle : renewalProduct k (logLogNat m) ≤
        renewalProduct k (logLogNat y) :=
      monotone_renewalProduct k
        (logLogNat_mono hm2 (le_of_lt hmBounds.2))
    calc
      discreteRenewalBenchmark k m ≤
          ((m + 1 : ℕ) : ℝ) / Real.log m *
            renewalProduct k (logLogNat m) :=
        discreteRenewalBenchmark_le_succ_div_log k m hm2
      _ ≤ (y : ℝ) / Real.log M * renewalProduct k (logLogNat y) :=
        mul_le_mul hquot hPle
          (le_trans (by norm_num) (one_le_renewalProduct k (logLogNat m)))
          (by positivity)
      _ = R := rfl
  calc
    ∑ m ∈ Finset.Ico M y, discreteRenewalBenchmark k m ≤
        ∑ _m ∈ Finset.Ico M y, R := Finset.sum_le_sum hterm
    _ = ((Finset.Ico M y).card : ℝ) * R := by simp
    _ ≤ (y : ℝ) * R := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast (by simp [Nat.card_Ico] : (Finset.Ico M y).card ≤ y)
      · dsimp [R]
        exact mul_nonneg
          (div_nonneg (by exact_mod_cast (Nat.zero_le y)) hlogM.le)
          (le_trans (by norm_num) (one_le_renewalProduct k (logLogNat y)))
    _ = (y : ℝ) ^ 2 / Real.log M *
        renewalProduct k (logLogNat y) := by
      dsimp [R]
      ring

/-- Once the argument is below threshold, every positive remaining height is
frozen at one. -/
theorem renewalProduct_frozen (k : ℕ) {x : ℝ}
    (hx : x ≤ renewalThreshold) : renewalProduct k x = 1 := by
  cases k with
  | zero => rfl
  | succ k => exact renewalProduct_of_le k hx

end Research
