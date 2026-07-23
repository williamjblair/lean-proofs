import Research.AnalyticLower

open Filter Asymptotics MeasureTheory intervalIntegral Real
open scoped BigOperators

namespace Erdos796

/-- The weight whose prime sum is the correction to the reciprocal-prime
baseline in the large-semiprime main term. -/
noncomputable def correctionWeight (N t : ℝ) : ℝ :=
  Real.log t / (t * (Real.log N - Real.log t))

/-- The simpler quotient appearing after partial summation. -/
noncomputable def correctionKernel (N t : ℝ) : ℝ :=
  1 / (t * (Real.log N - Real.log t))

lemma correctionWeight_div_log {N t : ℝ} (ht : 1 < t) :
    correctionWeight N t / Real.log t = correctionKernel N t := by
  unfold correctionWeight correctionKernel
  have hlog : Real.log t ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
  field_simp

lemma hasDerivAt_correctionKernel {N t : ℝ} (ht : 0 < t)
    (hNt : Real.log N ≠ Real.log t) :
    HasDerivAt (correctionKernel N)
      ((1 + Real.log t - Real.log N) /
        (t ^ 2 * (Real.log N - Real.log t) ^ 2)) t := by
  unfold correctionKernel
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hden : t * (Real.log N - Real.log t) ≠ 0 :=
    mul_ne_zero ht0 (sub_ne_zero.mpr hNt)
  have hdlog : HasDerivAt (fun s : ℝ => Real.log N - Real.log s) (-1 / t) t := by
    simpa [div_eq_mul_inv] using
      (Real.hasDerivAt_log ht0).const_sub (Real.log N)
  have hp := (hasDerivAt_id t).mul hdlog
  have heq : 1 * (Real.log N - Real.log t) + t * (-1 / t) =
      Real.log N - Real.log t - 1 := by
    field_simp
    ring
  simp only [one_div]
  change HasDerivAt
    (fun s : ℝ => (s * (Real.log N - Real.log s))⁻¹)
    ((1 + Real.log t - Real.log N) /
      (t ^ 2 * (Real.log N - Real.log t) ^ 2)) t
  have hi := hp.inv hden
  have hcoef : -(1 * (Real.log N - Real.log t) + t * (-1 / t)) /
      (t * (Real.log N - Real.log t)) ^ 2 =
      (1 + Real.log t - Real.log N) /
        (t ^ 2 * (Real.log N - Real.log t) ^ 2) := by
    rw [heq]
    field_simp
    ring
  rw [← hcoef]
  exact hi

/-- Prime-weight correction through the real square-root cutoff. -/
noncomputable def correctionPrimeSum (N : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Iic ⌊Real.sqrt N⌋₊).filter Nat.Prime,
    correctionWeight N p

lemma deriv_correctionWeight_div_log {N t : ℝ} (ht : 1 < t)
    (hNt : Real.log N ≠ Real.log t) :
    deriv (fun s => correctionWeight N s / Real.log s) t =
      (1 + Real.log t - Real.log N) /
        (t ^ 2 * (Real.log N - Real.log t) ^ 2) := by
  have heq : Set.EqOn
      (fun s => correctionWeight N s / Real.log s)
      (correctionKernel N) (Set.Ioi 1) := by
    intro s hs
    exact correctionWeight_div_log hs
  exact (heq.deriv isOpen_Ioi ht).trans
    (hasDerivAt_correctionKernel (lt_trans (by norm_num) ht) hNt).deriv

/-- Exact elementary evaluation of the main integral in the correction
partial summation. -/
theorem integral_correctionKernel (N : ℝ) (hN : 16 ≤ N) :
    (∫ y in 2..Real.sqrt N, correctionKernel N y) =
      Real.log (Real.log N - Real.log 2) -
        Real.log (Real.log N / 2) := by
  have hNpos : 0 < N := by linarith
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  have hsqrt : 2 ≤ Real.sqrt N := by
    calc
      (2 : ℝ) = Real.sqrt 4 := by norm_num
      _ ≤ Real.sqrt N := Real.sqrt_le_sqrt (by linarith)
  have hgap {y : ℝ} (hy : y ∈ Set.Icc 2 (Real.sqrt N)) :
      0 < Real.log N - Real.log y := by
    have hypos : 0 < y := by linarith [hy.1]
    have hlogle : Real.log y ≤ Real.log (Real.sqrt N) :=
      Real.log_le_log hypos hy.2
    rw [Real.log_sqrt hNpos.le] at hlogle
    linarith
  have hint : IntervalIntegrable (correctionKernel N) volume 2 (Real.sqrt N) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hsqrt]
    intro y hy
    have hy0 : y ≠ 0 := by linarith [hy.1]
    have hgap0 : Real.log N - Real.log y ≠ 0 := ne_of_gt (hgap hy)
    have hden : y * (Real.log N - Real.log y) ≠ 0 :=
      mul_ne_zero hy0 hgap0
    unfold correctionKernel
    exact ContinuousAt.continuousWithinAt (by fun_prop)
  have hderiv : ∀ y ∈ Set.uIcc 2 (Real.sqrt N),
      HasDerivAt (fun z => -Real.log (Real.log N - Real.log z))
        (correctionKernel N y) y := by
    intro y hy
    rw [Set.uIcc_of_le hsqrt] at hy
    have hy0 : y ≠ 0 := by linarith [hy.1]
    have hg := (Real.hasDerivAt_log hy0).const_sub (Real.log N)
    have hh := (hg.log (ne_of_gt (hgap hy))).neg
    have heq : y⁻¹ * (Real.log N - Real.log y)⁻¹ = correctionKernel N y := by
      unfold correctionKernel
      rw [one_div, mul_inv_rev]
      ring
    rw [← heq]
    change HasDerivAt (- fun z => Real.log (Real.log N - Real.log z))
      (y⁻¹ * (Real.log N - Real.log y)⁻¹) y
    simpa [div_eq_mul_inv] using hh
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  rw [Real.log_sqrt hNpos.le]
  ring

/-- The elementary main integral tends to `log 2`. -/
theorem tendsto_integral_correctionKernel :
    Tendsto (fun N : ℝ => ∫ y in 2..Real.sqrt N, correctionKernel N y)
      atTop (nhds (Real.log 2)) := by
  have hL : Tendsto (fun N : ℝ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop
  have hsmall : Tendsto (fun N : ℝ => Real.log 2 / Real.log N)
      atTop (nhds 0) := hL.const_div_atTop _
  have hratio : Tendsto (fun N : ℝ =>
      (Real.log N - Real.log 2) / (Real.log N / 2))
      atTop (nhds 2) := by
    have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    have h := (hone.sub hsmall).const_mul (2 : ℝ)
    have h' : Tendsto (fun N : ℝ =>
        2 * (1 - Real.log 2 / Real.log N)) atTop (nhds 2) := by
      simpa using h
    apply h'.congr'
    filter_upwards [eventually_gt_atTop 1] with N hN
    have hlog : Real.log N ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith) (ne_of_gt hN)
    field_simp
  have hlogratio := hratio.log (by norm_num : (2 : ℝ) ≠ 0)
  apply hlogratio.congr'
  filter_upwards [eventually_ge_atTop 16] with N hN
  rw [integral_correctionKernel N hN]
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  have hleft : Real.log N - Real.log 2 ≠ 0 := by
    apply ne_of_gt
    have hlt := Real.strictMonoOn_log
      (Set.mem_Ioi.mpr (by norm_num : (0 : ℝ) < 2))
      (Set.mem_Ioi.mpr (by linarith : (0 : ℝ) < N))
      (by linarith : (2 : ℝ) < N)
    linarith
  have hright : Real.log N / 2 ≠ 0 := div_ne_zero (ne_of_gt hlogN) (by norm_num)
  rw [Real.log_div hleft hright]

/-- The lower-end boundary term in partial summation vanishes. -/
theorem tendsto_correction_boundary :
    Tendsto (fun N : ℝ =>
      2 * correctionWeight N 2 / Real.log 2) atTop (nhds 0) := by
  have hden : Tendsto (fun N : ℝ => Real.log N - Real.log 2) atTop atTop := by
    have h := tendsto_atTop_add_const_right atTop (-Real.log 2)
      Real.tendsto_log_atTop
    simpa [sub_eq_add_neg] using h
  have hinv := hden.inv_tendsto_atTop
  apply hinv.congr'
  filter_upwards [eventually_gt_atTop 2] with N hN
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hgap : Real.log N - Real.log 2 ≠ 0 := by
    apply sub_ne_zero.mpr
    exact ne_of_gt (Real.strictMonoOn_log
      (Set.mem_Ioi.mpr (by norm_num : (0 : ℝ) < 2))
      (Set.mem_Ioi.mpr (by linarith : (0 : ℝ) < N)) hN)
  unfold correctionWeight
  field_simp
  simp [hgap]

/-- Quantitative bound for the upper-end boundary term. -/
lemma correction_endpoint_bound {C N : ℝ} (hC : 0 ≤ C) (hN : 16 ≤ N)
    (hθ : |Chebyshev.theta (Real.sqrt N) - Real.sqrt N| ≤
      C * Real.sqrt N / Real.log (Real.sqrt N) ^ 2) :
    |correctionWeight N (Real.sqrt N) *
        (Chebyshev.theta (Real.sqrt N) - Real.sqrt N) /
        Real.log (Real.sqrt N)| ≤
      8 * C / Real.log N ^ 3 := by
  have hNpos : 0 < N := by linarith
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have hX : 0 < Real.sqrt N := Real.sqrt_pos.2 hNpos
  have hlogX : 0 < Real.log (Real.sqrt N) := by
    rw [Real.log_sqrt hNpos.le]
    linarith
  have hgap : 0 < Real.log N - Real.log (Real.sqrt N) := by
    rw [Real.log_sqrt hNpos.le]
    linarith
  have hre : correctionWeight N (Real.sqrt N) *
        (Chebyshev.theta (Real.sqrt N) - Real.sqrt N) /
        Real.log (Real.sqrt N) =
      correctionKernel N (Real.sqrt N) *
        (Chebyshev.theta (Real.sqrt N) - Real.sqrt N) := by
    rw [← correctionWeight_div_log ((Real.log_pos_iff hX.le).mp hlogX)]
    ring
  rw [hre, abs_mul, abs_of_pos (by
    unfold correctionKernel
    exact div_pos (by norm_num) (mul_pos hX hgap))]
  rw [show correctionKernel N (Real.sqrt N) =
      2 / (Real.sqrt N * Real.log N) by
    unfold correctionKernel
    rw [Real.log_sqrt hNpos.le]
    field_simp
    ring]
  calc
    (2 / (Real.sqrt N * Real.log N)) *
        |Chebyshev.theta (Real.sqrt N) - Real.sqrt N|
      ≤ (2 / (Real.sqrt N * Real.log N)) *
          (C * Real.sqrt N / Real.log (Real.sqrt N) ^ 2) := by gcongr
    _ = 8 * C / Real.log N ^ 3 := by
      rw [Real.log_sqrt hNpos.le]
      field_simp
      ring

/-- The upper-end boundary term in partial summation vanishes. -/
theorem tendsto_correction_endpoint :
    Tendsto (fun N : ℝ => correctionWeight N (Real.sqrt N) *
      (Chebyshev.theta (Real.sqrt N) - Real.sqrt N) /
      Real.log (Real.sqrt N)) atTop (nhds 0) := by
  obtain ⟨C, hC, htheta⟩ := RS_prime.pnt
  have hinv : Tendsto (fun N : ℝ => (Real.log N)⁻¹) atTop (nhds 0) :=
    Real.tendsto_log_atTop.inv_tendsto_atTop
  have hbound : Tendsto (fun N : ℝ => 8 * C / Real.log N ^ 3)
      atTop (nhds 0) := by
    have h := (hinv.pow 3).const_mul (8 * C)
    convert h using 1
    · funext N
      field_simp
    · simp
  apply squeeze_zero_norm' (a := fun N : ℝ => 8 * C / Real.log N ^ 3)
  · filter_upwards [eventually_ge_atTop 16] with N hN
    rw [Real.norm_eq_abs]
    exact correction_endpoint_bound hC hN
      (htheta (Real.sqrt N) (by
        calc
          (2 : ℝ) = Real.sqrt 4 := by norm_num
          _ ≤ Real.sqrt N := Real.sqrt_le_sqrt (by linarith)))
  · exact hbound

/-- Uniform derivative bound for the correction kernel. -/
lemma correction_deriv_bound {N y : ℝ} (hN : 16 ≤ N)
    (hy : y ∈ Set.Icc 2 (Real.sqrt N)) :
    |deriv (fun s => correctionWeight N s / Real.log s) y| ≤
      4 * (1 + 2 * Real.log N) /
        (y ^ 2 * Real.log N ^ 2) := by
  have hNpos : 0 < N := by linarith
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have hypos : 0 < y := by linarith [hy.1]
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg (by linarith [hy.1])
  have hlogle : Real.log y ≤ Real.log N / 2 := by
    calc
      Real.log y ≤ Real.log (Real.sqrt N) := Real.log_le_log hypos hy.2
      _ = Real.log N / 2 := Real.log_sqrt hNpos.le
  have hgap : 0 < Real.log N - Real.log y := by linarith
  have hlogne : Real.log N ≠ Real.log y :=
    ne_of_gt (by linarith : Real.log y < Real.log N)
  rw [deriv_correctionWeight_div_log (by linarith [hy.1]) hlogne]
  rw [abs_div, abs_of_pos (mul_pos (sq_pos_of_pos hypos) (sq_pos_of_pos hgap))]
  have hnum : |1 + Real.log y - Real.log N| ≤ 1 + 2 * Real.log N := by
    calc
      _ ≤ |(1 : ℝ)| + |Real.log y| + |Real.log N| := by
        rw [show 1 + Real.log y - Real.log N =
          1 + Real.log y + (-Real.log N) by ring]
        grw [abs_add_three]
        simp
      _ = 1 + Real.log y + Real.log N := by
        rw [abs_of_nonneg hlogy, abs_of_pos hL]
        norm_num
      _ ≤ _ := by linarith
  calc
    |1 + Real.log y - Real.log N| /
        (y ^ 2 * (Real.log N - Real.log y) ^ 2)
      ≤ (1 + 2 * Real.log N) /
        (y ^ 2 * (Real.log N / 2) ^ 2) := by
        apply div_le_div₀ (by positivity) hnum
        · positivity
        · apply mul_le_mul_of_nonneg_left _ (sq_nonneg y)
          gcongr
          linarith
    _ = _ := by field_simp; ring

/-- Uniform pointwise bound for the integrated theta error. -/
lemma correction_error_integrand_bound {C N y : ℝ} (hC : 0 ≤ C)
    (hN : 16 ≤ N) (hy : y ∈ Set.Icc 2 (Real.sqrt N))
    (hθ : |Chebyshev.theta y - y| ≤ C * y / Real.log y ^ 2) :
    |(Chebyshev.theta y - y) *
      deriv (fun s => correctionWeight N s / Real.log s) y| ≤
      (4 * C * (1 + 2 * Real.log N) / Real.log N ^ 2) *
        (1 / (y * Real.log y ^ 2)) := by
  have hNpos : 0 < N := by linarith
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have hypos : 0 < y := by linarith [hy.1]
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith [hy.1])
  rw [abs_mul]
  calc
    |Chebyshev.theta y - y| *
        |deriv (fun s => correctionWeight N s / Real.log s) y|
      ≤ (C * y / Real.log y ^ 2) *
        (4 * (1 + 2 * Real.log N) / (y ^ 2 * Real.log N ^ 2)) := by
          gcongr
          exact correction_deriv_bound hN hy
    _ = _ := by field_simp

/-- Elementary integral bound used for the theta-error remainder. -/
lemma integral_one_div_mul_log_sq_le {X : ℝ} (hX : 2 ≤ X) :
    (∫ y in 2..X, 1 / (y * Real.log y ^ 2)) ≤ 1 / Real.log 2 := by
  have hint : IntervalIntegrable (fun y : ℝ => 1 / (y * Real.log y ^ 2))
      volume 2 X := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hX]
    intro y hy
    have hy0 : y ≠ 0 := by linarith [hy.1]
    have hly : Real.log y ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith [hy.1]) (by linarith [hy.1])
    have hden : y * Real.log y ^ 2 ≠ 0 :=
      mul_ne_zero hy0 (pow_ne_zero 2 hly)
    exact ContinuousAt.continuousWithinAt (by fun_prop)
  have hderiv : ∀ y ∈ Set.uIcc 2 X,
      HasDerivAt (fun z => (1 / Real.log 2) - (Real.log z)⁻¹)
        (1 / (y * Real.log y ^ 2)) y := by
    intro y hy
    rw [Set.uIcc_of_le hX] at hy
    have hy0 : y ≠ 0 := by linarith [hy.1]
    have hly : Real.log y ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith [hy.1]) (by linarith [hy.1])
    have hh := ((Real.hasDerivAt_log hy0).inv hly).const_sub
      (1 / Real.log 2)
    simpa [one_div, div_eq_mul_inv, mul_comm] using hh
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hinv : 0 ≤ (Real.log X)⁻¹ := inv_nonneg.mpr hlogX.le
  simp only [one_div]
  linarith

/-- Rosser--Schoenfeld partial summation specialized to the correction
weight. -/
theorem correctionPrimeSum_eq (N : ℝ) (hN : 16 ≤ N) :
    correctionPrimeSum N =
      (∫ y in 2..Real.sqrt N, correctionKernel N y) +
      2 * correctionWeight N 2 / Real.log 2 +
      correctionWeight N (Real.sqrt N) *
          (Chebyshev.theta (Real.sqrt N) - Real.sqrt N) /
          Real.log (Real.sqrt N) -
      ∫ y in 2..Real.sqrt N,
        (Chebyshev.theta y - y) *
          deriv (fun s => correctionWeight N s / Real.log s) y := by
  have hNpos : 0 < N := by linarith
  have hsqrt : 2 ≤ Real.sqrt N := by
    calc
      (2 : ℝ) = Real.sqrt 4 := by norm_num
      _ ≤ Real.sqrt N := Real.sqrt_le_sqrt (by linarith)
  have hltN {t : ℝ} (ht : t ∈ Set.Icc 2 (Real.sqrt N)) : t < N := by
    have hsqrt_lt : Real.sqrt N < N := by
      exact (Real.sqrt_lt' hNpos).mpr (by nlinarith)
    exact ht.2.trans_lt hsqrt_lt
  have hdiff : ∀ t ∈ Set.Icc 2 (Real.sqrt N),
      DifferentiableAt ℝ (correctionWeight N) t := by
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hlogne : Real.log N - Real.log t ≠ 0 := by
      apply sub_ne_zero.mpr
      exact ne_of_gt (Real.strictMonoOn_log
        (by exact Set.mem_Ioi.mpr (by linarith [ht.1]))
        (Set.mem_Ioi.mpr hNpos) (hltN ht))
    have hden : t * (Real.log N - Real.log t) ≠ 0 :=
      mul_ne_zero ht0 hlogne
    unfold correctionWeight
    fun_prop
  have hderivInt : IntervalIntegrable
      (fun t => deriv (fun s => correctionWeight N s / Real.log s) t)
      volume 2 (Real.sqrt N) := by
    let d : ℝ → ℝ := fun t =>
      (1 + Real.log t - Real.log N) /
        (t ^ 2 * (Real.log N - Real.log t) ^ 2)
    have hdcont : ContinuousOn d (Set.Icc 2 (Real.sqrt N)) := by
      intro t ht
      have ht0 : t ≠ 0 := by linarith [ht.1]
      have hlogne : Real.log N - Real.log t ≠ 0 := by
        apply sub_ne_zero.mpr
        exact ne_of_gt (Real.strictMonoOn_log
          (by exact Set.mem_Ioi.mpr (by linarith [ht.1]))
          (Set.mem_Ioi.mpr hNpos) (hltN ht))
      have hden : t ^ 2 * (Real.log N - Real.log t) ^ 2 ≠ 0 :=
        mul_ne_zero (pow_ne_zero 2 ht0) (pow_ne_zero 2 hlogne)
      unfold d
      exact ContinuousAt.continuousWithinAt (by fun_prop)
    have hdint : IntervalIntegrable d volume 2 (Real.sqrt N) := by
      apply ContinuousOn.intervalIntegrable
      simpa only [Set.uIcc_of_le hsqrt] using hdcont
    apply hdint.congr
    intro t ht
    have ht' : t ∈ Set.Icc 2 (Real.sqrt N) := by
      rw [Set.uIoc_of_le hsqrt] at ht
      exact ⟨le_of_lt ht.1, ht.2⟩
    have hlogne : Real.log N ≠ Real.log t := by
      exact ne_of_gt (Real.strictMonoOn_log
        (by exact Set.mem_Ioi.mpr (by linarith [ht'.1]))
        (Set.mem_Ioi.mpr hNpos) (hltN ht'))
    exact (deriv_correctionWeight_div_log (by linarith [ht'.1]) hlogne).symm
  have h := RS_prime.eq_414 (f := correctionWeight N) hsqrt hdiff hderivInt
  unfold correctionPrimeSum
  rw [h]
  congr 3
  apply intervalIntegral.integral_congr
  intro y hy
  have hy' : y ∈ Set.Icc 2 (Real.sqrt N) := by
    simpa [Set.uIcc_of_le hsqrt] using hy
  exact correctionWeight_div_log (by linarith [hy'.1])

/-- The integrated theta-error remainder in correction partial summation
vanishes. -/
theorem tendsto_correction_error_integral :
    Tendsto (fun N : ℝ =>
      ∫ y in 2..Real.sqrt N,
        (Chebyshev.theta y - y) *
          deriv (fun s => correctionWeight N s / Real.log s) y)
      atTop (nhds 0) := by
  obtain ⟨C, hC, htheta⟩ := RS_prime.pnt
  let A : ℝ → ℝ := fun N =>
    4 * C * (1 + 2 * Real.log N) / Real.log N ^ 2
  let B : ℝ → ℝ := fun N => A N * (1 / Real.log 2)
  have hinv : Tendsto (fun N : ℝ => (Real.log N)⁻¹) atTop (nhds 0) :=
    Real.tendsto_log_atTop.inv_tendsto_atTop
  have hB : Tendsto B atTop (nhds 0) := by
    have hpoly : Tendsto (fun N : ℝ =>
        (Real.log N)⁻¹ ^ 2 + 2 * (Real.log N)⁻¹) atTop (nhds 0) := by
      simpa using (hinv.pow 2).add (hinv.const_mul 2)
    have h := hpoly.const_mul (4 * C / Real.log 2)
    have h' : Tendsto (fun N : ℝ =>
        (4 * C / Real.log 2) *
          ((Real.log N)⁻¹ ^ 2 + 2 * (Real.log N)⁻¹))
        atTop (nhds 0) := by simpa using h
    apply h'.congr'
    filter_upwards [eventually_gt_atTop 1] with N hN
    have hlog : Real.log N ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith) (ne_of_gt hN)
    unfold B A
    field_simp
  apply squeeze_zero_norm' (a := B)
  · filter_upwards [eventually_ge_atTop 16] with N hN
    have hNpos : 0 < N := by linarith
    have hsqrt : 2 ≤ Real.sqrt N := by
      calc
        (2 : ℝ) = Real.sqrt 4 := by norm_num
        _ ≤ Real.sqrt N := Real.sqrt_le_sqrt (by linarith)
    have hL : 0 < Real.log N := Real.log_pos (by linarith)
    have hA : 0 ≤ A N := by unfold A; positivity
    have hbase : IntervalIntegrable
        (fun y : ℝ => 1 / (y * Real.log y ^ 2)) volume 2 (Real.sqrt N) := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hsqrt]
      intro y hy
      have hy0 : y ≠ 0 := by linarith [hy.1]
      have hly : Real.log y ≠ 0 :=
        Real.log_ne_zero_of_pos_of_ne_one (by linarith [hy.1]) (by linarith [hy.1])
      have hden : y * Real.log y ^ 2 ≠ 0 :=
        mul_ne_zero hy0 (pow_ne_zero 2 hly)
      exact ContinuousAt.continuousWithinAt (by fun_prop)
    have hgbound : IntervalIntegrable
        (fun y : ℝ => A N * (1 / (y * Real.log y ^ 2)))
        volume 2 (Real.sqrt N) := hbase.const_mul (A N)
    calc
      ‖∫ y in 2..Real.sqrt N,
          (Chebyshev.theta y - y) *
            deriv (fun s => correctionWeight N s / Real.log s) y‖
        ≤ ∫ y in 2..Real.sqrt N,
            A N * (1 / (y * Real.log y ^ 2)) := by
          apply intervalIntegral.norm_integral_le_of_norm_le hsqrt
          · filter_upwards with y hy
            rw [Real.norm_eq_abs]
            have hy' : y ∈ Set.Icc 2 (Real.sqrt N) :=
              ⟨le_of_lt hy.1, hy.2⟩
            exact correction_error_integrand_bound hC hN hy'
              (htheta y hy'.1)
          · exact hgbound
      _ = A N * (∫ y in 2..Real.sqrt N,
          1 / (y * Real.log y ^ 2)) := intervalIntegral.integral_const_mul _ _
      _ ≤ A N * (1 / Real.log 2) := by
        gcongr
        exact integral_one_div_mul_log_sq_le hsqrt
      _ = B N := rfl
  · exact hB

/-- Reciprocal primes through `sqrt N`, normalized against `log log N`. -/
noncomputable def primeReciprocalSqrtResidual (N : ℝ) : ℝ :=
  (∑ p ∈ Finset.Ioc 0 ⌊Real.sqrt N⌋₊ with p.Prime, (1 : ℝ) / p) -
    Real.log (Real.log N)

/-- Mertens at the square-root cutoff contributes `M - log 2`. -/
theorem tendsto_primeReciprocalSqrtResidual :
    Tendsto primeReciprocalSqrtResidual atTop
      (nhds (Mertens.M - Real.log 2)) := by
  have hsqrt := tendsto_primeReciprocalResidual.comp Real.tendsto_sqrt_atTop
  have h := hsqrt.sub_const (Real.log 2)
  apply h.congr'
  filter_upwards [eventually_gt_atTop 1] with N hN
  have hNpos : 0 < N := by linarith
  have hlogN : 0 < Real.log N := Real.log_pos hN
  have hlog2 : Real.log (2 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  unfold primeReciprocalSqrtResidual primeReciprocalResidual
  simp only [Function.comp_apply]
  rw [Real.log_sqrt hNpos.le, Real.log_div (ne_of_gt hlogN) (by norm_num : (2 : ℝ) ≠ 0)]
  ring

/-- The reciprocal-prime mass through `sqrt N` is negligible compared with
`log N`. -/
theorem tendsto_primeReciprocalSqrt_div_log :
    Tendsto (fun N : ℝ =>
      (∑ p ∈ Finset.Ioc 0 ⌊Real.sqrt N⌋₊ with p.Prime, (1 : ℝ) / p) /
        Real.log N) atTop (nhds 0) := by
  have hinv : Tendsto (fun N : ℝ => (Real.log N)⁻¹) atTop (nhds 0) :=
    Real.tendsto_log_atTop.inv_tendsto_atTop
  have hres := tendsto_primeReciprocalSqrtResidual.mul hinv
  have hres' : Tendsto (fun N : ℝ =>
      primeReciprocalSqrtResidual N / Real.log N) atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using hres
  have hloglog : Tendsto (fun N : ℝ =>
      Real.log (Real.log N) / Real.log N) atTop (nhds 0) := by
    have h := (Real.tendsto_pow_log_div_pow_atTop 1 1 (by norm_num)).comp
      Real.tendsto_log_atTop
    simpa [Function.comp_def] using h
  have hsum : Tendsto (fun N : ℝ =>
      primeReciprocalSqrtResidual N / Real.log N +
        Real.log (Real.log N) / Real.log N) atTop (nhds 0) := by
    simpa using hres'.add hloglog
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop 1] with N hN
  unfold primeReciprocalSqrtResidual
  ring

/-- The correction in the large-semiprime main term converges to `log 2`. -/
theorem tendsto_correctionPrimeSum :
    Tendsto correctionPrimeSum atTop (nhds (Real.log 2)) := by
  have h := ((tendsto_integral_correctionKernel.add
      tendsto_correction_boundary).add tendsto_correction_endpoint).sub
      tendsto_correction_error_integral
  have h' : Tendsto (fun N : ℝ =>
      (∫ y in 2..Real.sqrt N, correctionKernel N y) +
      2 * correctionWeight N 2 / Real.log 2 +
      correctionWeight N (Real.sqrt N) *
          (Chebyshev.theta (Real.sqrt N) - Real.sqrt N) /
          Real.log (Real.sqrt N) -
      ∫ y in 2..Real.sqrt N,
        (Chebyshev.theta y - y) *
          deriv (fun s => correctionWeight N s / Real.log s) y)
      atTop (nhds (Real.log 2)) := by simpa using h
  apply h'.congr'
  filter_upwards [eventually_ge_atTop 16] with N hN
  exact (correctionPrimeSum_eq N hN).symm

/-- The normalized main term for large semiprimes, with `log log` removed. -/
noncomputable def semiprimeMainResidual (N : ℝ) : ℝ :=
  (∑ p ∈ (Finset.Iic ⌊Real.sqrt N⌋₊).filter Nat.Prime,
    Real.log N / ((p : ℝ) * (Real.log N - Real.log p))) -
      Real.log (Real.log N)

/-- Exact split of the semiprime main residual into Mertens baseline and the
`log 2` correction. -/
theorem semiprimeMainResidual_eq (N : ℝ) (hN : 16 ≤ N) :
    semiprimeMainResidual N =
      primeReciprocalSqrtResidual N + correctionPrimeSum N := by
  have hNpos : 0 < N := by linarith
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  have hpbound : ∀ p ∈ (Finset.Iic ⌊Real.sqrt N⌋₊).filter Nat.Prime,
      Real.log N - Real.log p ≠ 0 := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hple : (p : ℝ) ≤ Real.sqrt N := by
      exact_mod_cast (Nat.le_floor_iff (Real.sqrt_nonneg N)).mp
        (Finset.mem_Iic.mp hp'.1)
    have hlogp : Real.log (p : ℝ) ≤ Real.log (Real.sqrt N) :=
      Real.log_le_log (by exact_mod_cast hp'.2.pos) hple
    rw [Real.log_sqrt hNpos.le] at hlogp
    linarith
  have hsets : (Finset.Iic ⌊Real.sqrt N⌋₊).filter Nat.Prime =
      (Finset.Ioc 0 ⌊Real.sqrt N⌋₊).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Iic, Finset.mem_Ioc]
    constructor
    · exact fun h => ⟨⟨h.2.pos, h.1⟩, h.2⟩
    · exact fun h => ⟨h.1.2, h.2⟩
  unfold semiprimeMainResidual primeReciprocalSqrtResidual correctionPrimeSum
  rw [← hsets]
  rw [sub_add_eq_add_sub]
  apply sub_left_inj.mpr
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have hp' := Finset.mem_filter.mp hp
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp'.2.ne_zero
  have hgap := hpbound p hp
  unfold correctionWeight
  field_simp
  ring

/-- The normalized main term for the large-semiprime count tends to the
Meissel--Mertens constant. -/
theorem tendsto_semiprimeMainResidual :
    Tendsto semiprimeMainResidual atTop (nhds Mertens.M) := by
  have h := tendsto_primeReciprocalSqrtResidual.add tendsto_correctionPrimeSum
  have h' : Tendsto
      (fun N => primeReciprocalSqrtResidual N + correctionPrimeSum N)
      atTop (nhds Mertens.M) := by simpa using h
  apply h'.congr'
  filter_upwards [eventually_ge_atTop 16] with N hN
  exact (semiprimeMainResidual_eq N hN).symm

/-- The sum of the PNT errors at all complementary arguments `N / p`, for
primes `p` through `sqrt N`. -/
noncomputable def semiprimePntError (N : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Iic ⌊Real.sqrt N⌋₊).filter Nat.Prime,
    ((Nat.primeCounting ⌊N / p⌋₊ : ℝ) -
      (N / p) / Real.log (N / p))

/-- The reciprocal-prime sum through `sqrt N`, divided by `log N`, tends to
zero in the indexing convention used by `semiprimePntError`. -/
theorem tendsto_sqrtPrimeReciprocal_div_log :
    Tendsto (fun N : ℝ =>
      (∑ p ∈ (Finset.Iic ⌊Real.sqrt N⌋₊).filter Nat.Prime,
          (1 : ℝ) / p) / Real.log N) atTop (nhds 0) := by
  apply tendsto_primeReciprocalSqrt_div_log.congr'
  filter_upwards with N
  congr 2

/-- Uniform PNT errors summed through the square-root cutoff are negligible
at the `N / log N` scale. -/
theorem tendsto_semiprimePntError_div_normalization :
    Tendsto (fun N : ℝ =>
      semiprimePntError N / (N / Real.log N)) atTop (nhds 0) := by
  obtain ⟨C, hC, herr⟩ := (isBigO_iff'.mp primeCounting_sub_main_isBigO)
  obtain ⟨X, hX⟩ := eventually_atTop.mp herr
  let A : ℝ → ℝ := fun N =>
    4 * C * ((∑ p ∈ (Finset.Iic ⌊Real.sqrt N⌋₊).filter Nat.Prime,
      (1 : ℝ) / p) / Real.log N)
  have hA : Tendsto A atTop (nhds 0) := by
    have h := tendsto_sqrtPrimeReciprocal_div_log.const_mul (4 * C)
    simpa [A] using h
  apply squeeze_zero_norm' (a := A)
  · filter_upwards [eventually_ge_atTop
      ((max (16 : ℝ) (max X 2)) ^ 2)] with N hN
    have hY16 : (16 : ℝ) ≤ max 16 (max X 2) := le_max_left _ _
    have hYroot : max X 2 ≤ max (16 : ℝ) (max X 2) := le_max_right _ _
    have hYsq : max (16 : ℝ) (max X 2) ≤
        (max (16 : ℝ) (max X 2)) ^ 2 := by nlinarith
    have hN16 : 16 ≤ N := hY16.trans (hYsq.trans hN)
    have hNpos : 0 < N := by linarith
    have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
    have hroot : max X 2 ≤ Real.sqrt N := by
      apply (Real.le_sqrt (by positivity) hNpos.le).2
      have hbase2 : (2 : ℝ) ≤ max X 2 := le_max_right _ _
      have hsqmono : (max X 2) ^ 2 ≤
          (max (16 : ℝ) (max X 2)) ^ 2 := by nlinarith
      exact hsqmono.trans hN
    have hroot2 : 2 ≤ Real.sqrt N := le_trans (le_max_right X 2) hroot
    have honeach : ∀ p ∈ (Finset.Iic ⌊Real.sqrt N⌋₊).filter Nat.Prime,
        |(Nat.primeCounting ⌊N / p⌋₊ : ℝ) -
            (N / p) / Real.log (N / p)| ≤
          C * (4 * N / ((p : ℝ) * Real.log N ^ 2)) := by
      intro p hp
      have hp' := Finset.mem_filter.mp hp
      have hpRpos : (0 : ℝ) < p := by exact_mod_cast hp'.2.pos
      have hpRle : (p : ℝ) ≤ Real.sqrt N :=
        (Nat.le_floor_iff (Real.sqrt_nonneg N)).mp (Finset.mem_Iic.mp hp'.1)
      have hrootpos : 0 < Real.sqrt N := Real.sqrt_pos.2 hNpos
      have hxroot : Real.sqrt N ≤ N / (p : ℝ) := by
        rw [le_div_iff₀ hpRpos]
        calc
          Real.sqrt N * (p : ℝ) ≤ Real.sqrt N * Real.sqrt N := by gcongr
          _ = N := Real.mul_self_sqrt hNpos.le
      have hxX : X ≤ N / (p : ℝ) := le_trans (le_trans (le_max_left X 2) hroot) hxroot
      have hxpos : 0 < N / (p : ℝ) := div_pos hNpos hpRpos
      have hlogx : Real.log N / 2 ≤ Real.log (N / (p : ℝ)) := by
        rw [← Real.log_sqrt hNpos.le]
        exact Real.log_le_log hrootpos hxroot
      have hlogxpos : 0 < Real.log (N / (p : ℝ)) := by
        linarith
      have hraw := hX (N / (p : ℝ)) hxX
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (div_pos hxpos (sq_pos_of_pos hlogxpos))] at hraw
      calc
        |(Nat.primeCounting ⌊N / ↑p⌋₊ : ℝ) -
            (N / ↑p) / Real.log (N / ↑p)|
          ≤ C * ((N / (p : ℝ)) / Real.log (N / (p : ℝ)) ^ 2) := hraw
        _ ≤ C * ((N / (p : ℝ)) / (Real.log N / 2) ^ 2) := by
          gcongr
        _ = C * (4 * N / ((p : ℝ) * Real.log N ^ 2)) := by
          field_simp
          ring
    have hsum : |semiprimePntError N| ≤
        C * (4 * N / Real.log N ^ 2) *
          (∑ p ∈ (Finset.Iic ⌊Real.sqrt N⌋₊).filter Nat.Prime,
            (1 : ℝ) / p) := by
      unfold semiprimePntError
      calc
        |∑ p ∈ (Finset.Iic ⌊Real.sqrt N⌋₊).filter Nat.Prime,
            ((Nat.primeCounting ⌊N / p⌋₊ : ℝ) -
              (N / p) / Real.log (N / p))|
          ≤ ∑ p ∈ (Finset.Iic ⌊Real.sqrt N⌋₊).filter Nat.Prime,
              |(Nat.primeCounting ⌊N / p⌋₊ : ℝ) -
                (N / p) / Real.log (N / p)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ p ∈ (Finset.Iic ⌊Real.sqrt N⌋₊).filter Nat.Prime,
              C * (4 * N / ((p : ℝ) * Real.log N ^ 2)) := by
            exact Finset.sum_le_sum honeach
        _ = C * (4 * N / Real.log N ^ 2) *
              (∑ p ∈ (Finset.Iic ⌊Real.sqrt N⌋₊).filter Nat.Prime,
                (1 : ℝ) / p) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro p hp
            have hp0 : (p : ℝ) ≠ 0 := by
              exact_mod_cast (Finset.mem_filter.mp hp).2.ne_zero
            field_simp
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (div_pos hNpos hlogN)]
    calc
      |semiprimePntError N| / (N / Real.log N)
        ≤ (C * (4 * N / Real.log N ^ 2) *
            (∑ p ∈ (Finset.Iic ⌊Real.sqrt N⌋₊).filter Nat.Prime,
              (1 : ℝ) / p)) / (N / Real.log N) := by gcongr
      _ = A N := by
        unfold A
        field_simp
  · exact hA

/-- Sum of prime counts at the complementary arguments `N / p`. -/
noncomputable def semiprimePiSum (N : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Iic ⌊Real.sqrt N⌋₊).filter Nat.Prime,
    (Nat.primeCounting ⌊N / p⌋₊ : ℝ)

/-- The complementary-prime sum after normalization and removal of the
leading `log log N`. -/
noncomputable def semiprimePiResidual (N : ℝ) : ℝ :=
  semiprimePiSum N / (N / Real.log N) - Real.log (Real.log N)

/-- Exact decomposition into the explicit main term and the summed uniform
PNT error. -/
theorem semiprimePiResidual_eq (N : ℝ) (hN : 16 ≤ N) :
    semiprimePiResidual N = semiprimeMainResidual N +
      semiprimePntError N / (N / Real.log N) := by
  have hNpos : 0 < N := by linarith
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  let S := (Finset.Iic ⌊Real.sqrt N⌋₊).filter Nat.Prime
  have hsplit : semiprimePiSum N =
      (∑ p ∈ S, (N / (p : ℝ)) / Real.log (N / (p : ℝ))) +
        semiprimePntError N := by
    unfold semiprimePiSum semiprimePntError
    change (∑ p ∈ S, (Nat.primeCounting ⌊N / p⌋₊ : ℝ)) = _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  have hmain :
      (∑ p ∈ S, (N / (p : ℝ)) / Real.log (N / (p : ℝ))) /
          (N / Real.log N) =
        ∑ p ∈ S,
          Real.log N / ((p : ℝ) * (Real.log N - Real.log p)) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hpRpos : (0 : ℝ) < p := by exact_mod_cast hp'.2.pos
    have hpRle : (p : ℝ) ≤ Real.sqrt N :=
      (Nat.le_floor_iff (Real.sqrt_nonneg N)).mp (Finset.mem_Iic.mp hp'.1)
    have hsqrt4 : (4 : ℝ) ≤ Real.sqrt N := by
      calc
        (4 : ℝ) = Real.sqrt 16 := by norm_num
        _ ≤ Real.sqrt N := Real.sqrt_le_sqrt hN
    have hx : 1 < N / (p : ℝ) := by
      have hsqrtpos : 0 < Real.sqrt N := by positivity
      have hxroot : Real.sqrt N ≤ N / (p : ℝ) := by
        rw [le_div_iff₀ hpRpos]
        calc
          Real.sqrt N * (p : ℝ) ≤ Real.sqrt N * Real.sqrt N := by gcongr
          _ = N := Real.mul_self_sqrt hNpos.le
      linarith
    have hp0 : (p : ℝ) ≠ 0 := ne_of_gt hpRpos
    have hlogx : Real.log (N / (p : ℝ)) ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by positivity) (ne_of_gt hx)
    rw [Real.log_div (ne_of_gt hNpos) hp0]
    field_simp
  unfold semiprimePiResidual semiprimeMainResidual
  rw [hsplit, add_div, hmain]
  ring

/-- The normalized complementary-prime sum has second-order limit equal to
Meissel--Mertens' constant. -/
theorem tendsto_semiprimePiResidual :
    Tendsto semiprimePiResidual atTop (nhds Mertens.M) := by
  have h := tendsto_semiprimeMainResidual.add
    tendsto_semiprimePntError_div_normalization
  have h' : Tendsto (fun N => semiprimeMainResidual N +
      semiprimePntError N / (N / Real.log N)) atTop
      (nhds Mertens.M) := by simpa using h
  apply h'.congr'
  filter_upwards [eventually_ge_atTop 16] with N hN
  exact (semiprimePiResidual_eq N hN).symm

/-- The square of the prime count at `sqrt N` is negligible at the
`N / log N` scale. -/
theorem tendsto_primeCounting_sqrt_sq_div_normalization :
    Tendsto (fun N : ℝ =>
      (Nat.primeCounting ⌊Real.sqrt N⌋₊ : ℝ) ^ 2 /
        (N / Real.log N)) atTop (nhds 0) := by
  have hequiv0 := pi_alt'.comp_tendsto Real.tendsto_sqrt_atTop
  have hequiv : (fun N : ℝ =>
      (Nat.primeCounting ⌊Real.sqrt N⌋₊ : ℝ)) ~[atTop]
      (fun N : ℝ => Real.sqrt N / Real.log (Real.sqrt N)) := by
    simpa [Function.comp_def] using hequiv0
  have hden_ne : ∀ᶠ N : ℝ in atTop,
      Real.sqrt N / Real.log (Real.sqrt N) ≠ 0 := by
    filter_upwards [eventually_gt_atTop 1] with N hN
    have hsqrt1 : 1 < Real.sqrt N := by
      rw [Real.lt_sqrt (by norm_num)]
      simpa using hN
    exact div_ne_zero (ne_of_gt (by positivity))
      (Real.log_ne_zero_of_pos_of_ne_one (by positivity) (ne_of_gt hsqrt1))
  rw [isEquivalent_iff_tendsto_one hden_ne] at hequiv
  have hratio : Tendsto (fun N : ℝ =>
      (Nat.primeCounting ⌊Real.sqrt N⌋₊ : ℝ) /
        (Real.sqrt N / Real.log (Real.sqrt N))) atTop (nhds 1) := by
    exact hequiv
  have hinvlog : Tendsto (fun N : ℝ => 4 / Real.log N) atTop (nhds 0) := by
    have h := Real.tendsto_log_atTop.inv_tendsto_atTop.const_mul 4
    simpa [div_eq_mul_inv] using h
  have hprod := (hratio.pow 2).mul hinvlog
  have hprod' : Tendsto (fun N : ℝ =>
      ((Nat.primeCounting ⌊Real.sqrt N⌋₊ : ℝ) /
        (Real.sqrt N / Real.log (Real.sqrt N))) ^ 2 *
          (4 / Real.log N)) atTop (nhds 0) := by simpa using hprod
  apply hprod'.congr'
  filter_upwards [eventually_gt_atTop 1] with N hN
  have hNpos : 0 < N := by linarith
  have hlogN : Real.log N ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by linarith) (ne_of_gt hN)
  have hsqrtpos : 0 < Real.sqrt N := Real.sqrt_pos.2 hNpos
  have hlogsqrt : Real.log (Real.sqrt N) ≠ 0 := by
    rw [Real.log_sqrt hNpos.le]
    exact div_ne_zero hlogN (by norm_num)
  rw [Real.log_sqrt hNpos.le]
  field_simp
  rw [Real.sq_sqrt hNpos.le]
  ring

/-- Nat-indexed complementary-prime sum. -/
def semiprimePiSumNat (n : ℕ) : ℕ :=
  ∑ p ∈ Nat.primesLE n.sqrt, Nat.primeCounting (n / p)

/-- Restriction of the real complementary-prime asymptotic to natural
arguments. -/
theorem tendsto_semiprimePiSumNat_residual :
    Tendsto (fun n : ℕ =>
      (semiprimePiSumNat n : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)) -
        Real.log (Real.log (n : ℝ))) atTop (nhds Mertens.M) := by
  have h := tendsto_semiprimePiResidual.comp tendsto_natCast_atTop_atTop
  apply h.congr'
  filter_upwards with n
  change semiprimePiResidual (n : ℝ) = _
  unfold semiprimePiResidual semiprimePiSum semiprimePiSumNat
  rw [Real.nat_floor_real_sqrt_eq_nat_sqrt]
  have hsets : (Finset.Iic n.sqrt).filter Nat.Prime = Nat.primesLE n.sqrt := by
    ext p
    simp [Nat.mem_primesLE]
  rw [hsets]
  congr 3
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro p hp
  simp [Nat.floor_div_natCast]

/-- Number of large-semiprime pairs, indexed by their smaller prime. -/
def largeSemiprimeCount (n : ℕ) : ℕ :=
  ∑ p ∈ Nat.primesLE n.sqrt,
    (Nat.primeCounting (n / p) - Nat.primeCounting n.sqrt)

/-- Exact real-valued decomposition of the large-semiprime count. -/
theorem largeSemiprimeCount_cast (n : ℕ) :
    (largeSemiprimeCount n : ℝ) =
      (semiprimePiSumNat n : ℝ) - (Nat.primeCounting n.sqrt : ℝ) ^ 2 := by
  have hmono : ∀ p ∈ Nat.primesLE n.sqrt,
      Nat.primeCounting n.sqrt ≤ Nat.primeCounting (n / p) := by
    intro p hp
    have hp' := Nat.mem_primesLE.mp hp
    apply Nat.monotone_primeCounting
    apply (Nat.le_div_iff_mul_le hp'.2.pos).2
    calc
      n.sqrt * p ≤ n.sqrt * n.sqrt := Nat.mul_le_mul_left _ hp'.1
      _ ≤ n := Nat.sqrt_le n
  unfold largeSemiprimeCount semiprimePiSumNat
  rw [Nat.cast_sum]
  calc
    ∑ p ∈ Nat.primesLE n.sqrt,
        ((Nat.primeCounting (n / p) - Nat.primeCounting n.sqrt : ℕ) : ℝ) =
      ∑ p ∈ Nat.primesLE n.sqrt,
        ((Nat.primeCounting (n / p) : ℝ) -
          (Nat.primeCounting n.sqrt : ℝ)) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Nat.cast_sub (hmono p hp)]
    _ = (∑ p ∈ Nat.primesLE n.sqrt,
          (Nat.primeCounting (n / p) : ℝ)) -
        ∑ p ∈ Nat.primesLE n.sqrt,
          (Nat.primeCounting n.sqrt : ℝ) := Finset.sum_sub_distrib _ _
    _ = _ := by
      rw [Nat.cast_sum, Finset.sum_const, nsmul_eq_mul]
      rw [Nat.primesLE_card_eq_primeCounting]
      push_cast
      ring

/-- The large-semiprime count itself has the classical second-order
coefficient `Mertens.M`. -/
theorem tendsto_largeSemiprimeCount_residual :
    Tendsto (fun n : ℕ =>
      (largeSemiprimeCount n : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)) -
        Real.log (Real.log (n : ℝ))) atTop (nhds Mertens.M) := by
  have hmain := tendsto_semiprimePiSumNat_residual
  have herr := tendsto_primeCounting_sqrt_sq_div_normalization.comp
    tendsto_natCast_atTop_atTop
  have hdiff := hmain.sub herr
  have hdiff' : Tendsto (fun n : ℕ =>
      ((semiprimePiSumNat n : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)) -
        Real.log (Real.log (n : ℝ))) -
      (Nat.primeCounting n.sqrt : ℝ) ^ 2 /
          ((n : ℝ) / Real.log (n : ℝ))) atTop (nhds Mertens.M) := by
    simpa [Real.nat_floor_real_sqrt_eq_nat_sqrt] using hdiff
  apply hdiff'.congr'
  filter_upwards with n
  rw [largeSemiprimeCount_cast]
  ring

/-- Removing the prime labels only through `sqrt n` from a fixed reciprocal
dilation does not change its normalized limit. -/
theorem tendsto_primeCounting_sub_sqrt_div_normalization (j : ℕ) (hj : 0 < j) :
    Tendsto (fun n : ℕ =>
      (Nat.primeCounting (n / j) - Nat.primeCounting n.sqrt : ℝ) /
        ((n : ℝ) / Real.log (n : ℝ))) atTop
      (nhds ((1 : ℝ) / j)) := by
  have hmain := (tendsto_primeCounting_div_normalization j hj).sub
    tendsto_primeCounting_sqrt_div_normalization
  have hs : ∀ᶠ n : ℕ in atTop, n.sqrt ≤ n / j := by
    filter_upwards [eventually_ge_atTop (j * j)] with n hn
    have hjs : j ≤ n.sqrt := Nat.le_sqrt.mpr hn
    apply (Nat.le_div_iff_mul_le hj).2
    calc
      n.sqrt * j ≤ n.sqrt * n.sqrt := Nat.mul_le_mul_left _ hjs
      _ ≤ n := Nat.sqrt_le n
  have hmain' : Tendsto (fun n : ℕ =>
      (Nat.primeCounting (n / j) : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)) -
        (Nat.primeCounting n.sqrt : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ))) atTop
      (nhds ((1 : ℝ) / j)) := by simpa using hmain
  apply hmain'.congr'
  filter_upwards [hs] with n hsn
  ring

/-- Contribution from the finitely many primes at most 40. -/
def smallPrimeCorrection40 (n : ℕ) : ℕ :=
  ∑ p ∈ Nat.primesLE 40,
    (Nat.primeCounting (n / p) - Nat.primeCounting n.sqrt)

/-- The fixed small-prime correction has the expected reciprocal-weight
limit. -/
theorem tendsto_smallPrimeCorrection40_div_normalization :
    Tendsto (fun n : ℕ =>
      (smallPrimeCorrection40 n : ℝ) /
        ((n : ℝ) / Real.log (n : ℝ))) atTop
      (nhds (∑ p ∈ Nat.primesLE 40, (1 : ℝ) / p)) := by
  have hp : ∀ p ∈ Nat.primesLE 40, Tendsto (fun n : ℕ =>
      (Nat.primeCounting (n / p) - Nat.primeCounting n.sqrt : ℝ) /
        ((n : ℝ) / Real.log (n : ℝ))) atTop
      (nhds ((1 : ℝ) / p)) := by
    intro p hp
    exact tendsto_primeCounting_sub_sqrt_div_normalization p
      (Nat.prime_of_mem_primesLE hp).pos
  have hsum := tendsto_finsetSum (Nat.primesLE 40) hp
  apply hsum.congr'
  filter_upwards [eventually_ge_atTop (40 * 40)] with n hn
  have h40 : 40 ≤ n.sqrt := Nat.le_sqrt.mpr hn
  unfold smallPrimeCorrection40
  rw [Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p hp
  have hp' := Nat.mem_primesLE.mp hp
  have hle : Nat.primeCounting n.sqrt ≤ Nat.primeCounting (n / p) := by
    apply Nat.monotone_primeCounting
    apply (Nat.le_div_iff_mul_le hp'.2.pos).2
    calc
      n.sqrt * p ≤ n.sqrt * 40 := Nat.mul_le_mul_left _ hp'.1
      _ ≤ n.sqrt * n.sqrt := Nat.mul_le_mul_left _ h40
      _ ≤ n := Nat.sqrt_le n
  rw [Nat.cast_sub hle]

/-- The prime-tail count in the smaller-prime orientation. -/
def profile40PrimeTailSmall (n : ℕ) : ℕ :=
  ∑ p ∈ Nat.primesLE n.sqrt \ Nat.primesLE 40,
    (Nat.primeCounting (n / p) - Nat.primeCounting n.sqrt)

/-- Above the fixed initial range, the full large-semiprime count splits
exactly into the small-prime correction and the profile-40 tail. -/
theorem largeSemiprimeCount_eq_small_add_tail (n : ℕ) (hn : 40 * 40 ≤ n) :
    largeSemiprimeCount n = smallPrimeCorrection40 n +
      profile40PrimeTailSmall n := by
  have h40 : 40 ≤ n.sqrt := Nat.le_sqrt.mpr hn
  have hsub : Nat.primesLE 40 ⊆ Nat.primesLE n.sqrt :=
    Nat.primesLE_mono h40
  have h := Finset.sum_sdiff (f := fun p =>
    Nat.primeCounting (n / p) - Nat.primeCounting n.sqrt) hsub
  unfold largeSemiprimeCount smallPrimeCorrection40 profile40PrimeTailSmall
  omega

/-- The profile-40 prime tail has coefficient `M` minus the reciprocal mass
of the removed small primes. -/
theorem tendsto_profile40PrimeTailSmall_residual :
    Tendsto (fun n : ℕ =>
      (profile40PrimeTailSmall n : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)) -
        Real.log (Real.log (n : ℝ))) atTop
      (nhds (Mertens.M -
        ∑ p ∈ Nat.primesLE 40, (1 : ℝ) / p)) := by
  have h := tendsto_largeSemiprimeCount_residual.sub
    tendsto_smallPrimeCorrection40_div_normalization
  have h' : Tendsto (fun n : ℕ =>
      ((largeSemiprimeCount n : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)) -
        Real.log (Real.log (n : ℝ))) -
      (smallPrimeCorrection40 n : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ))) atTop
      (nhds (Mertens.M -
        ∑ p ∈ Nat.primesLE 40, (1 : ℝ) / p)) := h
  apply h'.congr'
  filter_upwards [eventually_ge_atTop (40 * 40)] with n hn
  rw [largeSemiprimeCount_eq_small_add_tail n hn]
  push_cast
  ring

/-- The prime-tail term occurring literally in the profile cardinality
decomposition. -/
def profile40TailCount (n : ℕ) : ℕ :=
  ∑ q ∈ sqrtPrimeLabels n,
    ((Finset.Icc 41 (n / q)).filter Nat.Prime).card

/-- A common pair finset used to double-count the profile tail. -/
def profile40PrimePairs (n : ℕ) : Finset (ℕ × ℕ) :=
  (((Finset.Icc 41 n.sqrt).filter Nat.Prime).product
    (sqrtPrimeLabels n)).filter fun z => z.1 * z.2 ≤ n

/-- The small-prime indexing set above 40 has the expected interval form. -/
theorem profile40SmallPrimes_eq (n : ℕ) :
    Nat.primesLE n.sqrt \ Nat.primesLE 40 =
      (Finset.Icc 41 n.sqrt).filter Nat.Prime := by
  ext p
  simp only [Finset.mem_sdiff, Nat.mem_primesLE, Finset.mem_filter,
    Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hps, hp⟩, hnot⟩
    have hp41 : 41 ≤ p := by
      by_contra h
      apply hnot
      exact ⟨by omega, hp⟩
    exact ⟨⟨hp41, hps⟩, hp⟩
  · rintro ⟨⟨hp41, hps⟩, hp⟩
    exact ⟨⟨hps, hp⟩, by omega⟩

/-- Counting the common pair finset by its smaller-prime coordinate gives the
small-orientation tail. -/
theorem profile40PrimePairs_card_eq_small (n : ℕ) :
    (profile40PrimePairs n).card = profile40PrimeTailSmall n := by
  unfold profile40PrimePairs profile40PrimeTailSmall
  rw [profile40SmallPrimes_eq]
  rw [Finset.card_filter]
  change (∑ z ∈ ((Finset.Icc 41 n.sqrt).filter Nat.Prime).product
      (sqrtPrimeLabels n), if z.1 * z.2 ≤ n then 1 else 0) = _
  rw [show (∑ z ∈ ((Finset.Icc 41 n.sqrt).filter Nat.Prime).product
      (sqrtPrimeLabels n), if z.1 * z.2 ≤ n then 1 else 0) =
      ∑ p ∈ (Finset.Icc 41 n.sqrt).filter Nat.Prime,
        ∑ q ∈ sqrtPrimeLabels n, if p * q ≤ n then 1 else 0 from
      Finset.sum_product _ _ _]
  apply Finset.sum_congr rfl
  intro p hp
  have hp' := Finset.mem_filter.mp hp
  have hpI := Finset.mem_Icc.mp hp'.1
  have hppos : 0 < p := hp'.2.pos
  have hs : n.sqrt ≤ n / p := by
    apply (Nat.le_div_iff_mul_le hppos).2
    calc
      n.sqrt * p ≤ n.sqrt * n.sqrt := Nat.mul_le_mul_left _ hpI.2
      _ ≤ n := Nat.sqrt_le n
  have hfiber : (sqrtPrimeLabels n).filter (fun q => p * q ≤ n) =
      Nat.primesLE (n / p) \ Nat.primesLE n.sqrt := by
    ext q
    simp only [Finset.mem_filter, sqrtPrimeLabels, Finset.mem_Icc,
      Nat.mem_primesLE, Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨⟨hqlow, hqn⟩, hqprime⟩, hpq⟩
      have hqdiv : q ≤ n / p := (Nat.le_div_iff_mul_le hppos).2 (by
        simpa [Nat.mul_comm] using hpq)
      exact ⟨⟨hqdiv, hqprime⟩, by omega⟩
    · rintro ⟨⟨hqdiv, hqprime⟩, hnot⟩
      have hpq : p * q ≤ n := by
        simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hppos).1 hqdiv
      have hqn : q ≤ n := le_trans hqdiv (Nat.div_le_self n p)
      have hqlow : n.sqrt + 1 ≤ q := by
        simp only [not_and_or, not_le] at hnot
        rcases hnot with h | h
        · omega
        · exact (h hqprime).elim
      exact ⟨⟨⟨hqlow, hqn⟩, hqprime⟩, hpq⟩
  rw [← Finset.card_filter, hfiber]
  rw [Finset.card_sdiff_of_subset (Nat.primesLE_mono hs)]
  simp

/-- Counting the same pair finset by its large-prime label gives the literal
profile tail. -/
theorem profile40PrimePairs_card_eq_tail (n : ℕ) :
    (profile40PrimePairs n).card = profile40TailCount n := by
  unfold profile40PrimePairs profile40TailCount
  rw [Finset.card_filter]
  change (∑ z ∈ ((Finset.Icc 41 n.sqrt).filter Nat.Prime).product
      (sqrtPrimeLabels n), if z.1 * z.2 ≤ n then 1 else 0) = _
  rw [show (∑ z ∈ ((Finset.Icc 41 n.sqrt).filter Nat.Prime).product
      (sqrtPrimeLabels n), if z.1 * z.2 ≤ n then 1 else 0) =
      ∑ p ∈ (Finset.Icc 41 n.sqrt).filter Nat.Prime,
        ∑ q ∈ sqrtPrimeLabels n, if p * q ≤ n then 1 else 0 from
      Finset.sum_product _ _ _]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  have hq' := Finset.mem_filter.mp hq
  have hqpos : 0 < q := hq'.2.pos
  have hcap : n / q ≤ n.sqrt := div_label_le_sqrt hq
  have hfiber : ((Finset.Icc 41 n.sqrt).filter Nat.Prime).filter
      (fun p => p * q ≤ n) =
      (Finset.Icc 41 (n / q)).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨⟨hp41, hps⟩, hpprime⟩, hpq⟩
      exact ⟨⟨hp41, (Nat.le_div_iff_mul_le hqpos).2 hpq⟩, hpprime⟩
    · rintro ⟨⟨hp41, hpdiv⟩, hpprime⟩
      exact ⟨⟨⟨hp41, le_trans hpdiv hcap⟩, hpprime⟩,
        (Nat.le_div_iff_mul_le hqpos).1 hpdiv⟩
  rw [← Finset.card_filter, hfiber]

/-- The literal profile-tail incidence count equals its smaller-prime
orientation. -/
theorem profile40TailCount_eq_small (n : ℕ) :
    profile40TailCount n = profile40PrimeTailSmall n := by
  rw [← profile40PrimePairs_card_eq_tail,
    profile40PrimePairs_card_eq_small]

/-- The literal profile-40 prime tail has the required second-order
asymptotic. -/
theorem tendsto_profile40TailCount_residual :
    Tendsto (fun n : ℕ =>
      (profile40TailCount n : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)) -
        Real.log (Real.log (n : ℝ))) atTop
      (nhds (Mertens.M -
        ∑ p ∈ Nat.primesLE 40, (1 : ℝ) / p)) := by
  simpa only [profile40TailCount_eq_small] using
    tendsto_profile40PrimeTailSmall_residual

/-- Exact real value of the finite profile gain after removing the prime
baseline through 40. -/
theorem profile40Coefficient_eq :
    (∑ i : Fin 40, (fiberDelta40 i : ℝ) / (i.val + 1 : ℕ)) -
      ∑ p ∈ Nat.primesLE 40, (1 : ℝ) / p =
      (1377763 : ℝ) / 928200 := by
  have h :
      (∑ i : Fin 40, (fiberDelta40 i : ℚ) / (i.val + 1 : ℕ)) -
        ∑ p ∈ Nat.primesLE 40, (1 : ℚ) / p =
        (1377763 : ℚ) / 928200 := by native_decide
  have hr := congrArg (fun x : ℚ => (x : ℝ)) h
  norm_num at hr ⊢
  simpa using hr

/-- The exact cardinality split specialized to the certified profile. -/
theorem fiberType40Construction_card_decomposition (n : ℕ) :
    (fiberType40Construction n).card =
      profile40BaseCount n + profile40TailCount n := by
  unfold fiberType40Construction profile40BaseCount profile40TailCount
  exact certifiedProfile40.construction_card_decomposition n

/-- Residual of the explicit certified construction. -/
noncomputable def fiberType40ConstructionResidual (n : ℕ) : ℝ :=
  ((fiberType40Construction n).card : ℝ) /
      ((n : ℝ) / Real.log (n : ℝ)) -
    Real.log (Real.log (n : ℝ))

/-- The certified construction has second-order coefficient
`M + 1377763/928200`. -/
theorem tendsto_fiberType40ConstructionResidual :
    Tendsto fiberType40ConstructionResidual atTop
      (nhds (Mertens.M + (1377763 : ℝ) / 928200)) := by
  have h := tendsto_profile40BaseCount_div_normalization.add
    tendsto_profile40TailCount_residual
  have hcoef := profile40Coefficient_eq
  have h' : Tendsto (fun n : ℕ =>
      (profile40BaseCount n : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)) +
        ((profile40TailCount n : ℝ) /
            ((n : ℝ) / Real.log (n : ℝ)) -
          Real.log (Real.log (n : ℝ)))) atTop
      (nhds (Mertens.M + (1377763 : ℝ) / 928200)) := by
    have hlim :
        (∑ i : Fin 40, (fiberDelta40 i : ℝ) / (i.val + 1 : ℕ)) +
            (Mertens.M - ∑ p ∈ Nat.primesLE 40, (1 : ℝ) / p) =
          Mertens.M + (1377763 : ℝ) / 928200 := by
      linarith [hcoef]
    rw [hlim] at h
    exact h
  apply h'.congr'
  filter_upwards with n
  unfold fiberType40ConstructionResidual
  rw [fiberType40Construction_card_decomposition]
  push_cast
  ring

/-- The explicit construction residual is eventually a lower bound for the
extremal residual. -/
theorem eventually_fiberType40ConstructionResidual_le_normalizedError :
    ∀ᶠ n : ℕ in atTop,
      fiberType40ConstructionResidual n ≤ normalizedError n := by
  filter_upwards [eventually_gt_atTop 1] with n hn
  have hnR : (0 : ℝ) < (n : ℝ) := by positivity
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hden : 0 < (n : ℝ) / Real.log (n : ℝ) := div_pos hnR hlog
  have hcard : ((fiberType40Construction n).card : ℝ) ≤ (g 3 n : ℝ) := by
    exact_mod_cast fiberType40Construction_card_le_g n
  unfold fiberType40ConstructionResidual normalizedError
  calc
    ((fiberType40Construction n).card : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)) -
        Real.log (Real.log (n : ℝ)) =
      (((fiberType40Construction n).card : ℝ) -
          (n : ℝ) * Real.log (Real.log (n : ℝ)) /
            Real.log (n : ℝ)) /
        ((n : ℝ) / Real.log (n : ℝ)) := by
          field_simp
    _ ≤ ((g 3 n : ℝ) -
          (n : ℝ) * Real.log (Real.log (n : ℝ)) /
            Real.log (n : ℝ)) /
        ((n : ℝ) / Real.log (n : ℝ)) := by
          exact div_le_div_of_nonneg_right
            (sub_le_sub_right hcard _) hden.le

/-- Formal asymptotic lower bound for the exact extremal function. -/
theorem eventually_profile40Coefficient_sub_lt_normalizedError
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      Mertens.M + (1377763 : ℝ) / 928200 - ε < normalizedError n := by
  have hnear := tendsto_fiberType40ConstructionResidual.eventually
    (lt_mem_nhds (sub_lt_self _ hε))
  filter_upwards [hnear,
    eventually_fiberType40ConstructionResidual_le_normalizedError]
      with n hn hle
  exact hn.trans_le hle

end Erdos796
