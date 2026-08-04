import Research.LowerBenchmark

/-! # Summable losses for the lower height induction -/

namespace Research

/-- Very conservative bottom value for the high analytic towers. -/
noncomputable def lowerAnalysisBase : ℝ := Real.exp (2 ^ 20 : ℕ)

/-- Height-dependent power-tail loss. -/
noncomputable def lowerEpsilon (k : ℕ) : ℝ :=
  1 / (2 : ℝ) ^ (2 * k + 10)

/-- Exact logarithm of epsilon. -/
theorem log_lowerEpsilon (k : ℕ) :
    Real.log (lowerEpsilon k) =
      -((2 * k + 10 : ℕ) : ℝ) * Real.log 2 := by
  rw [lowerEpsilon, one_div, Real.log_inv, Real.log_pow]
  ring

/-- Its negative logarithm is at most the linear height. -/
theorem neg_log_lowerEpsilon_le_height (k : ℕ) :
    -Real.log (lowerEpsilon k) ≤ (2 * k + 10 : ℕ) := by
  rw [log_lowerEpsilon]
  have hlog : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    linarith
  have hnonneg : (0 : ℝ) ≤ (2 * k + 10 : ℕ) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hlog hnonneg]

/-- Adaptive argument cutoffs.  The fourth-power reserve (after taking one
logarithm) absorbs the power-tail and endpoint shifts. -/
noncomputable def adaptiveLowerCutoff : ℕ → ℝ
  | 0 => lowerAnalysisBase
  | k + 1 => Real.exp
      (4 * adaptiveLowerCutoff k ^ (1 / (1 - lowerEpsilon k)))

/-- Loss incurred at stage `k`. -/
noncomputable def lowerStageLoss (k : ℕ) : ℝ :=
  (2 * k + 3 : ℕ) * lowerEpsilon k

/-- Accumulated multiplicative coefficient. -/
noncomputable def lowerHeightCoefficient : ℕ → ℝ
  | 0 => 1
  | k + 1 => lowerHeightCoefficient k * (1 - lowerEpsilon k) ^ (2 * k + 3)

@[simp] theorem lowerHeightCoefficient_zero : lowerHeightCoefficient 0 = 1 := rfl
@[simp] theorem lowerHeightCoefficient_succ (k : ℕ) :
    lowerHeightCoefficient (k + 1) =
      lowerHeightCoefficient k * (1 - lowerEpsilon k) ^ (2 * k + 3) := rfl

/-- Elementary exponential domination used in the loss sum. -/
theorem two_mul_add_three_le_pow (k : ℕ) : 2 * k + 3 ≤ 2 ^ (k + 2) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [show k + 1 + 2 = (k + 2) + 1 by omega, pow_succ]
      omega

/-- Epsilon is positive and tiny. -/
theorem lowerEpsilon_pos (k : ℕ) : 0 < lowerEpsilon k := by
  rw [lowerEpsilon]
  positivity

theorem lowerEpsilon_le_half (k : ℕ) : lowerEpsilon k ≤ 1 / 2 := by
  rw [lowerEpsilon]
  have hp : (2 : ℝ) ≤ (2 : ℝ) ^ (2 * k + 10) := by
    calc
      (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * k + 10) := pow_le_pow_right₀ (by norm_num) (by omega)
  exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp

/-- Bernoulli's inequality in the precise form needed here. -/
theorem one_sub_mul_le_pow_one_sub {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (n : ℕ) :
    1 - (n : ℝ) * e ≤ (1 - e) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      by_cases hne : (n : ℝ) * e ≤ 1
      · rw [pow_succ]
        have hnonneg : 0 ≤ 1 - e := by linarith
        have hmul := mul_le_mul_of_nonneg_right ih hnonneg
        norm_num only [Nat.cast_add, Nat.cast_one]
        ring_nf at hmul ⊢
        nlinarith [mul_nonneg he0 (sub_nonneg.mpr hne)]
      · have hpow : 0 ≤ (1 - e) ^ (n + 1) :=
          pow_nonneg (by linarith) _
        norm_num only [Nat.cast_add, Nat.cast_one]
        nlinarith

/-- Stage losses are dominated by a geometric sequence. -/
theorem lowerStageLoss_le_geometric (k : ℕ) :
    lowerStageLoss k ≤ 1 / (2 : ℝ) ^ (k + 8) := by
  have hnum : ((2 * k + 3 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (k + 2) := by
    exact_mod_cast two_mul_add_three_le_pow k
  rw [lowerStageLoss, lowerEpsilon]
  have hden : (2 : ℝ) ^ (2 * k + 10) =
      (2 : ℝ) ^ (k + 2) * (2 : ℝ) ^ (k + 8) := by
    rw [← pow_add]
    congr 1
    omega
  rw [one_div, hden]
  have hpos : 0 < (2 : ℝ) ^ (k + 2) := by positivity
  have hpos8 : 0 < (2 : ℝ) ^ (k + 8) := by positivity
  calc
    ((2 * k + 3 : ℕ) : ℝ) *
        ((2 : ℝ) ^ (k + 2) * (2 : ℝ) ^ (k + 8))⁻¹ ≤
      (2 : ℝ) ^ (k + 2) *
        ((2 : ℝ) ^ (k + 2) * (2 : ℝ) ^ (k + 8))⁻¹ :=
      mul_le_mul_of_nonneg_right hnum (by positivity)
    _ = 1 / (2 : ℝ) ^ (k + 8) := by
      rw [one_div]
      field_simp

/-- Every finite accumulated loss is below `1/128`. -/
theorem sum_lowerStageLoss_le (k : ℕ) :
    ∑ j ∈ Finset.range k, lowerStageLoss j ≤ 1 / 128 := by
  calc
    ∑ j ∈ Finset.range k, lowerStageLoss j ≤
        ∑ j ∈ Finset.range k, 1 / (2 : ℝ) ^ (j + 8) := by
      apply Finset.sum_le_sum
      intro j hj
      exact lowerStageLoss_le_geometric j
    _ = (1 / 256 : ℝ) * ∑ j ∈ Finset.range k, (1 / 2 : ℝ) ^ j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [show j + 8 = 8 + j by omega, pow_add]
      norm_num
      field_simp
      rw [← mul_pow]
      norm_num
    _ ≤ (1 / 256 : ℝ) * 2 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      rw [geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1)]
      have hp : 0 ≤ (1 / 2 : ℝ) ^ k := pow_nonneg (by norm_num) _
      apply (div_le_iff_of_neg (by norm_num : (1 / 2 : ℝ) - 1 < 0)).mpr
      nlinarith
    _ = 1 / 128 := by norm_num

/-- Height coefficients are nonnegative. -/
theorem lowerHeightCoefficient_nonneg (k : ℕ) :
    0 ≤ lowerHeightCoefficient k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [lowerHeightCoefficient_succ]
      exact mul_nonneg ih (pow_nonneg (by
        have := lowerEpsilon_le_half k
        linarith) _)

/-- Multiplicative coefficients dominate one minus the accumulated stage
loss. -/
theorem one_sub_sum_loss_le_coefficient (k : ℕ) :
    1 - ∑ j ∈ Finset.range k, lowerStageLoss j ≤ lowerHeightCoefficient k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [lowerHeightCoefficient_succ, Finset.sum_range_succ]
      have he0 := (lowerEpsilon_pos k).le
      have he1 : lowerEpsilon k ≤ 1 :=
        le_trans (lowerEpsilon_le_half k) (by norm_num)
      have hstage0 := one_sub_mul_le_pow_one_sub he0 he1 (2 * k + 3)
      have hstage : 1 - lowerStageLoss k ≤
          (1 - lowerEpsilon k) ^ (2 * k + 3) := by
        simpa [lowerStageLoss] using hstage0
      have hsum0 : 0 ≤ ∑ j ∈ Finset.range k, lowerStageLoss j := by
        apply Finset.sum_nonneg
        intro j hj
        unfold lowerStageLoss lowerEpsilon
        positivity
      have hsum1 : ∑ j ∈ Finset.range k, lowerStageLoss j ≤ 1 :=
        le_trans (sum_lowerStageLoss_le k) (by norm_num)
      have hcoef0 : 0 ≤ lowerHeightCoefficient k :=
        le_trans (by linarith) ih
      have hloss0 : 0 ≤ lowerStageLoss k := by
        unfold lowerStageLoss lowerEpsilon
        positivity
      have hloss1 : lowerStageLoss k ≤ 1 := by
        apply le_trans (lowerStageLoss_le_geometric k)
        apply (div_le_one (by positivity : (0 : ℝ) < (2 : ℝ) ^ (k + 8))).mpr
        exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
      have hmul := mul_le_mul ih hstage (sub_nonneg.mpr hloss1) hcoef0
      calc
        1 - (∑ j ∈ Finset.range k, lowerStageLoss j + lowerStageLoss k) ≤
            (1 - ∑ j ∈ Finset.range k, lowerStageLoss j) *
              (1 - lowerStageLoss k) := by
          nlinarith [mul_nonneg hsum0 hloss0]
        _ ≤ lowerHeightCoefficient k *
            (1 - lowerEpsilon k) ^ (2 * k + 3) := hmul

/-- The analysis base is comfortably above two. -/
theorem two_le_lowerAnalysisBase : 2 ≤ lowerAnalysisBase := by
  rw [lowerAnalysisBase, ← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  apply Real.exp_le_exp.mpr
  have hlog2 : Real.log 2 < 1 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    linarith
  norm_num at ⊢
  linarith

theorem two_lt_lowerAnalysisBase : 2 < lowerAnalysisBase := by
  rw [lowerAnalysisBase, ← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  apply Real.exp_lt_exp.mpr
  have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at h ⊢
  linarith

/-- Every cutoff is at least the base and positive. -/
theorem base_le_adaptiveLowerCutoff (k : ℕ) :
    lowerAnalysisBase ≤ adaptiveLowerCutoff k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [adaptiveLowerCutoff]
      have hR1 : 1 ≤ adaptiveLowerCutoff k :=
        le_trans (by norm_num) (le_trans two_le_lowerAnalysisBase ih)
      have he0 := lowerEpsilon_pos k
      have he1 : lowerEpsilon k < 1 :=
        lt_of_le_of_lt (lowerEpsilon_le_half k) (by norm_num)
      have hq : 1 ≤ 1 / (1 - lowerEpsilon k) := by
        apply (one_le_div (by linarith)).mpr
        linarith
      have hpow : adaptiveLowerCutoff k ≤
          adaptiveLowerCutoff k ^ (1 / (1 - lowerEpsilon k)) := by
        calc
          adaptiveLowerCutoff k = adaptiveLowerCutoff k ^ (1 : ℝ) :=
            (Real.rpow_one _).symm
          _ ≤ adaptiveLowerCutoff k ^ (1 / (1 - lowerEpsilon k)) :=
            Real.rpow_le_rpow_of_exponent_le hR1 hq
      have hexp : lowerAnalysisBase ≤ Real.exp lowerAnalysisBase := by
        have h := Real.add_one_le_exp lowerAnalysisBase
        linarith
      apply le_trans hexp
      apply Real.exp_le_exp.mpr
      have hR0 : 0 ≤ adaptiveLowerCutoff k := by linarith
      have hpow0 : 0 ≤ adaptiveLowerCutoff k ^
          (1 / (1 - lowerEpsilon k)) := le_trans hR0 hpow
      nlinarith

theorem adaptiveLowerCutoff_pos (k : ℕ) : 0 < adaptiveLowerCutoff k :=
  lt_of_lt_of_le (by
    have := two_le_lowerAnalysisBase
    linarith) (base_le_adaptiveLowerCutoff k)

/-- Each cutoff dominates the ordinary tower needed for monotonicity. -/
theorem tower_two_le_adaptiveLowerCutoff (k : ℕ) :
    realTower 2 k ≤ adaptiveLowerCutoff k := by
  induction k with
  | zero => exact two_le_lowerAnalysisBase
  | succ k ih =>
      rw [realTower_succ, adaptiveLowerCutoff]
      apply Real.exp_le_exp.mpr
      have hR1 : 1 ≤ adaptiveLowerCutoff k :=
        le_trans (by norm_num) (le_trans two_le_lowerAnalysisBase
          (base_le_adaptiveLowerCutoff k))
      have he0 := lowerEpsilon_pos k
      have he1 : lowerEpsilon k < 1 :=
        lt_of_le_of_lt (lowerEpsilon_le_half k) (by norm_num)
      have hq : 1 ≤ 1 / (1 - lowerEpsilon k) := by
        apply (one_le_div (by linarith)).mpr
        linarith
      have hpow : adaptiveLowerCutoff k ≤
          adaptiveLowerCutoff k ^ (1 / (1 - lowerEpsilon k)) := by
        calc
          adaptiveLowerCutoff k = adaptiveLowerCutoff k ^ (1 : ℝ) :=
            (Real.rpow_one _).symm
          _ ≤ adaptiveLowerCutoff k ^ (1 / (1 - lowerEpsilon k)) :=
            Real.rpow_le_rpow_of_exponent_le hR1 hq
      nlinarith

/-- Successive cutoffs contain the exponential of the preceding one. -/
theorem exp_cutoff_le_succ (k : ℕ) :
    Real.exp (adaptiveLowerCutoff k) ≤ adaptiveLowerCutoff (k + 1) := by
  rw [adaptiveLowerCutoff]
  apply Real.exp_le_exp.mpr
  have hR1 : 1 ≤ adaptiveLowerCutoff k :=
    le_trans (by norm_num) (le_trans two_le_lowerAnalysisBase
      (base_le_adaptiveLowerCutoff k))
  have he0 := lowerEpsilon_pos k
  have he1 : lowerEpsilon k < 1 :=
    lt_of_le_of_lt (lowerEpsilon_le_half k) (by norm_num)
  have hq : 1 ≤ 1 / (1 - lowerEpsilon k) := by
    apply (one_le_div (by linarith)).mpr
    linarith
  have hpow : adaptiveLowerCutoff k ≤
      adaptiveLowerCutoff k ^ (1 / (1 - lowerEpsilon k)) := by
    calc
      adaptiveLowerCutoff k = adaptiveLowerCutoff k ^ (1 : ℝ) :=
        (Real.rpow_one _).symm
      _ ≤ adaptiveLowerCutoff k ^ (1 / (1 - lowerEpsilon k)) :=
        Real.rpow_le_rpow_of_exponent_le hR1 hq
  nlinarith

/-- Adaptive cutoffs dominate the tower based at the analysis base. -/
theorem analysisBaseTower_le_cutoff (k : ℕ) :
    realTower lowerAnalysisBase k ≤ adaptiveLowerCutoff k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [realTower_succ]
      exact le_trans (Real.exp_le_exp.mpr ih) (exp_cutoff_le_succ k)

/-- The cutoff at height `k` already exceeds the ordinary tower of height
`k+1`. -/
theorem tower_two_succ_le_cutoff (k : ℕ) :
    realTower 2 (k + 1) ≤ adaptiveLowerCutoff k := by
  induction k with
  | zero =>
      rw [realTower_succ, adaptiveLowerCutoff]
      apply Real.exp_le_exp.mpr
      norm_num [realTower]
  | succ k ih =>
      rw [realTower_succ]
      exact le_trans (Real.exp_le_exp.mpr ih) (exp_cutoff_le_succ k)

/-- Exponential growth dominates multiplication by four on our domain. -/
theorem four_mul_le_exp_of_base_le {x : ℝ} (hx : lowerAnalysisBase ≤ x) :
    4 * x ≤ Real.exp x := by
  have hbase12 : (12 : ℝ) ≤ lowerAnalysisBase := by
    rw [lowerAnalysisBase, ← Real.exp_log (by norm_num : (0 : ℝ) < 12)]
    apply Real.exp_le_exp.mpr
    have hlog := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 12)
    norm_num at hlog ⊢
    linarith
  have hx12 : 12 ≤ x := le_trans hbase12 hx
  have he : x / 2 + 1 ≤ Real.exp (x / 2) := Real.add_one_le_exp _
  have he0 : 0 ≤ Real.exp (x / 2) := (Real.exp_pos _).le
  have hlin0 : 0 ≤ x / 2 + 1 := by linarith
  calc
    4 * x ≤ (x / 2 + 1) ^ 2 := by nlinarith [sq_nonneg (x / 2 - 1)]
    _ ≤ Real.exp (x / 2) ^ 2 := by nlinarith
    _ = Real.exp x := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring

/-- The adaptive cutoffs grow by at least a factor four. -/
theorem four_mul_cutoff_le_succ (k : ℕ) :
    4 * adaptiveLowerCutoff k ≤ adaptiveLowerCutoff (k + 1) :=
  le_trans (four_mul_le_exp_of_base_le (base_le_adaptiveLowerCutoff k))
    (exp_cutoff_le_succ k)

/-- A simple geometric lower bound for the cutoff sequence. -/
theorem pow_four_mul_base_le_cutoff (k : ℕ) :
    (4 : ℝ) ^ k * lowerAnalysisBase ≤ adaptiveLowerCutoff k := by
  induction k with
  | zero => simp [adaptiveLowerCutoff]
  | succ k ih =>
      rw [pow_succ]
      calc
        4 ^ k * 4 * lowerAnalysisBase =
            4 * (4 ^ k * lowerAnalysisBase) := by ring
        _ ≤ 4 * adaptiveLowerCutoff k :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
        _ ≤ adaptiveLowerCutoff (k + 1) := four_mul_cutoff_le_succ k

/-- On the same huge domain exponential growth also dominates a factor
sixteen. -/
theorem sixteen_mul_le_exp_of_base_le {x : ℝ}
    (hx : lowerAnalysisBase ≤ x) :
    16 * x ≤ Real.exp x := by
  have hbase64 : (64 : ℝ) ≤ lowerAnalysisBase := by
    rw [lowerAnalysisBase, ← Real.exp_log (by norm_num : (0 : ℝ) < 64)]
    apply Real.exp_le_exp.mpr
    have hlog := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 64)
    norm_num at hlog ⊢
    linarith
  have hx64 : 64 ≤ x := le_trans hbase64 hx
  have he : x / 2 + 1 ≤ Real.exp (x / 2) := Real.add_one_le_exp _
  have hlin0 : 0 ≤ x / 2 + 1 := by linarith
  calc
    16 * x ≤ (x / 2 + 1) ^ 2 := by nlinarith [sq_nonneg (x / 2 - 1)]
    _ ≤ Real.exp (x / 2) ^ 2 := by nlinarith [Real.exp_pos (x / 2)]
    _ = Real.exp x := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring

theorem sixteen_mul_cutoff_le_succ (k : ℕ) :
    16 * adaptiveLowerCutoff k ≤ adaptiveLowerCutoff (k + 1) :=
  le_trans (sixteen_mul_le_exp_of_base_le (base_le_adaptiveLowerCutoff k))
    (exp_cutoff_le_succ k)

theorem pow_sixteen_mul_base_le_cutoff (k : ℕ) :
    (16 : ℝ) ^ k * lowerAnalysisBase ≤ adaptiveLowerCutoff k := by
  induction k with
  | zero => simp [adaptiveLowerCutoff]
  | succ k ih =>
      rw [pow_succ]
      calc
        16 ^ k * 16 * lowerAnalysisBase =
            16 * (16 ^ k * lowerAnalysisBase) := by ring
        _ ≤ 16 * adaptiveLowerCutoff k :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
        _ ≤ adaptiveLowerCutoff (k + 1) := sixteen_mul_cutoff_le_succ k

/-- Epsilon times its current cutoff has a large uniform reserve. -/
theorem two_le_epsilon_mul_cutoff (k : ℕ) :
    2 ≤ lowerEpsilon k * adaptiveLowerCutoff k := by
  have hcut := pow_sixteen_mul_base_le_cutoff k
  have hbase : (2048 : ℝ) ≤ lowerAnalysisBase := by
    rw [lowerAnalysisBase, ← Real.exp_log (by norm_num : (0 : ℝ) < 2048)]
    apply Real.exp_le_exp.mpr
    have hlog := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2048)
    norm_num at hlog ⊢
    linarith
  rw [lowerEpsilon]
  have hpowid : (16 : ℝ) ^ k = (4 : ℝ) ^ k * (4 : ℝ) ^ k := by
    rw [← mul_pow]
    norm_num
  have hden : (2 : ℝ) ^ (2 * k + 10) =
      (4 : ℝ) ^ k * 1024 := by
    rw [show 2 * k + 10 = 2 * k + 10 by rfl, pow_add, pow_mul]
    norm_num
  rw [hpowid] at hcut
  rw [hden]
  have h4 : 0 < (4 : ℝ) ^ k := by positivity
  have hnonneg : 0 ≤ adaptiveLowerCutoff k := (adaptiveLowerCutoff_pos k).le
  field_simp
  have hb0 : 0 ≤ lowerAnalysisBase := by linarith
  have hQ0 : 0 ≤ (4 : ℝ) ^ k := by positivity
  have hQ1 : 1 ≤ (4 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hbaseQ : lowerAnalysisBase ≤ (4 : ℝ) ^ k * lowerAnalysisBase := by
    simpa using mul_le_mul_of_nonneg_right hQ1 hb0
  have hQbase : (4 : ℝ) ^ k * lowerAnalysisBase ≤
      (4 : ℝ) ^ k * ((4 : ℝ) ^ k * lowerAnalysisBase) :=
    mul_le_mul_of_nonneg_left hbaseQ hQ0
  have hneed : 2048 * (4 : ℝ) ^ k ≤
      (4 : ℝ) ^ k * (4 : ℝ) ^ k * lowerAnalysisBase := by
    calc
      2048 * (4 : ℝ) ^ k ≤ lowerAnalysisBase * (4 : ℝ) ^ k :=
        mul_le_mul_of_nonneg_right hbase hQ0
      _ = (4 : ℝ) ^ k * lowerAnalysisBase := by ring
      _ ≤ (4 : ℝ) ^ k * ((4 : ℝ) ^ k * lowerAnalysisBase) := hQbase
      _ = (4 : ℝ) ^ k * (4 : ℝ) ^ k * lowerAnalysisBase := by ring
  nlinarith

/-- Linear height is dominated by a geometric factor. -/
theorem two_mul_add_ten_le_ten_mul_pow_four (k : ℕ) :
    2 * k + 10 ≤ 10 * 4 ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [pow_succ]
      omega

/-- Stronger logarithmic reserve needed by the power-tail ratio. -/
theorem height_le_epsilon_mul_cutoff (k : ℕ) :
    (2 * k + 10 : ℕ) ≤ lowerEpsilon k * adaptiveLowerCutoff k := by
  have hcut := pow_sixteen_mul_base_le_cutoff k
  have hbase : (10240 : ℝ) ≤ lowerAnalysisBase := by
    rw [lowerAnalysisBase, ← Real.exp_log (by norm_num : (0 : ℝ) < 10240)]
    apply Real.exp_le_exp.mpr
    have hlog := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 10240)
    norm_num at hlog ⊢
    linarith
  have hlin : ((2 * k + 10 : ℕ) : ℝ) ≤ 10 * (4 : ℝ) ^ k := by
    exact_mod_cast two_mul_add_ten_le_ten_mul_pow_four k
  rw [lowerEpsilon]
  have hpowid : (16 : ℝ) ^ k = (4 : ℝ) ^ k * (4 : ℝ) ^ k := by
    rw [← mul_pow]
    norm_num
  have hden : (2 : ℝ) ^ (2 * k + 10) =
      (4 : ℝ) ^ k * 1024 := by
    rw [pow_add, pow_mul]
    norm_num
  rw [hpowid] at hcut
  rw [hden]
  have hQ0 : 0 < (4 : ℝ) ^ k := by positivity
  have hbase0 : 0 ≤ lowerAnalysisBase := by
    exact le_trans (by norm_num) hbase
  have hneeded : (10 * (4 : ℝ) ^ k) *
      ((4 : ℝ) ^ k * 1024) ≤ adaptiveLowerCutoff k := by
    apply le_trans ?_ hcut
    calc
      (10 * (4 : ℝ) ^ k) * ((4 : ℝ) ^ k * 1024) =
          (4 : ℝ) ^ k * (4 : ℝ) ^ k * 10240 := by ring
      _ ≤ (4 : ℝ) ^ k * (4 : ℝ) ^ k * lowerAnalysisBase :=
        mul_le_mul_of_nonneg_left hbase (by positivity)
  rw [div_eq_mul_inv]
  have hdiv : 10 * (4 : ℝ) ^ k ≤
      ((4 : ℝ) ^ k * 1024)⁻¹ * adaptiveLowerCutoff k := by
    rw [le_inv_mul_iff₀ (by positivity)]
    nlinarith
  nlinarith

/-- The crucial reserve is also available after taking a logarithm. -/
theorem height_le_epsilon_mul_log_cutoff (k : ℕ) :
    ((2 * k + 10 : ℕ) : ℝ) ≤
      lowerEpsilon k * Real.log (adaptiveLowerCutoff k) := by
  cases k with
  | zero =>
      rw [adaptiveLowerCutoff, lowerAnalysisBase, Real.log_exp, lowerEpsilon]
      norm_num
  | succ n =>
      have hlog : adaptiveLowerCutoff n ≤
          Real.log (adaptiveLowerCutoff (n + 1)) := by
        rw [← Real.log_exp (adaptiveLowerCutoff n)]
        exact Real.log_le_log (Real.exp_pos _)
          (exp_cutoff_le_succ n)
      have hcut := pow_sixteen_mul_base_le_cutoff n
      have hbase : (49152 : ℝ) ≤ lowerAnalysisBase := by
        rw [lowerAnalysisBase, ← Real.exp_log (by norm_num : (0 : ℝ) < 49152)]
        apply Real.exp_le_exp.mpr
        have hlog' := Real.log_lt_sub_one_of_pos
          (by norm_num : (0 : ℝ) < 49152)
        norm_num at hlog' ⊢
        linarith
      have hlin : ((2 * (n + 1) + 10 : ℕ) : ℝ) ≤
          12 * (4 : ℝ) ^ n := by
        have h0 := two_mul_add_ten_le_ten_mul_pow_four n
        have hb : 1 ≤ 4 ^ n := one_le_pow₀ (by omega)
        have hn : 2 * (n + 1) + 10 ≤ 12 * 4 ^ n := by omega
        exact_mod_cast hn
      have hpowid : (16 : ℝ) ^ n = (4 : ℝ) ^ n * (4 : ℝ) ^ n := by
        rw [← mul_pow]
        norm_num
      have hden : (2 : ℝ) ^ (2 * (n + 1) + 10) =
          (4 : ℝ) ^ (n + 1) * 1024 := by
        rw [pow_add, pow_mul]
        norm_num
      have hQ0 : 0 ≤ (4 : ℝ) ^ n := by positivity
      rw [hpowid] at hcut
      have hneed : (12 * (4 : ℝ) ^ n) *
          ((4 : ℝ) ^ (n + 1) * 1024) ≤ adaptiveLowerCutoff n := by
        apply le_trans ?_ hcut
        rw [pow_succ]
        calc
          (12 * 4 ^ n) * (4 ^ n * 4 * 1024) =
              4 ^ n * 4 ^ n * 49152 := by ring
          _ ≤ 4 ^ n * 4 ^ n * lowerAnalysisBase :=
            mul_le_mul_of_nonneg_left hbase (by positivity)
      have heR : ((2 * (n + 1) + 10 : ℕ) : ℝ) ≤
          lowerEpsilon (n + 1) * adaptiveLowerCutoff n := by
        rw [lowerEpsilon, hden, one_div]
        have hpos : 0 < (4 : ℝ) ^ (n + 1) * 1024 := by positivity
        rw [inv_mul_eq_div]
        apply le_trans hlin
        rw [le_div_iff₀ hpos]
        exact hneed
      have he0 := (lowerEpsilon_pos (n + 1)).le
      exact le_trans heR (mul_le_mul_of_nonneg_left hlog he0)

/-- A target above the next cutoff sends the power tail above the current
cutoff, provided the elementary endpoint comparison holds. -/
theorem cutoff_le_rpow_of_next_cutoff {k : ℕ} {z x : ℝ}
    (htarget : adaptiveLowerCutoff (k + 1) ≤ z)
    (hendpoint : (1 - lowerEpsilon k) * Real.log z ≤ x) :
    adaptiveLowerCutoff k ≤ x ^ (1 - lowerEpsilon k) := by
  let R := adaptiveLowerCutoff k
  let e := lowerEpsilon k
  have hRpos : 0 < R := adaptiveLowerCutoff_pos k
  have he0 : 0 < e := lowerEpsilon_pos k
  have he2 : e ≤ 1 / 2 := lowerEpsilon_le_half k
  have hone : 0 < 1 - e := by linarith
  have hqpos : 0 < 1 / (1 - e) := by positivity
  have hnext : adaptiveLowerCutoff (k + 1) =
      Real.exp (4 * R ^ (1 / (1 - e))) := by
    rfl
  have hzpos : 0 < z := lt_of_lt_of_le (by rw [hnext]; positivity) htarget
  have hlogTarget : 4 * R ^ (1 / (1 - e)) ≤ Real.log z := by
    have h := Real.log_le_log (by rw [hnext]; positivity) htarget
    rw [hnext, Real.log_exp] at h
    exact h
  have hpowpos : 0 < R ^ (1 / (1 - e)) :=
    Real.rpow_pos_of_pos hRpos _
  have hpowLeX : R ^ (1 / (1 - e)) ≤ x := by
    dsimp [e] at hlogTarget hendpoint hone ⊢
    nlinarith
  have hxpos : 0 < x := lt_of_lt_of_le hpowpos hpowLeX
  have hrpow := Real.rpow_le_rpow hpowpos.le hpowLeX hone.le
  have hexp : (1 / (1 - e)) * (1 - e) = 1 := by field_simp
  calc
    adaptiveLowerCutoff k = R ^ (1 : ℝ) := by
      dsimp [R]
      rw [Real.rpow_one]
    _ = (R ^ (1 / (1 - e))) ^ (1 - e) := by
      rw [← Real.rpow_mul hRpos.le, hexp]
    _ ≤ x ^ (1 - e) := hrpow

/-- Above the adaptive cutoff, the chosen power-tail point lies below
`epsilon*x`, so its interval has near-full length. -/
theorem rpow_one_sub_le_epsilon_mul {k : ℕ} {x : ℝ}
    (hx : adaptiveLowerCutoff k ≤ x) :
    x ^ (1 - lowerEpsilon k) ≤ lowerEpsilon k * x := by
  have hRpos := adaptiveLowerCutoff_pos k
  have hxpos : 0 < x := lt_of_lt_of_le hRpos hx
  have hepos := lowerEpsilon_pos k
  have hlogMono : Real.log (adaptiveLowerCutoff k) ≤ Real.log x :=
    Real.log_le_log hRpos hx
  have hheight := height_le_epsilon_mul_log_cutoff k
  have hneg := neg_log_lowerEpsilon_le_height k
  have hbudget : -Real.log (lowerEpsilon k) ≤
      lowerEpsilon k * Real.log x := by
    exact le_trans hneg (le_trans hheight
      (mul_le_mul_of_nonneg_left hlogMono hepos.le))
  have hleft : 0 < x ^ (1 - lowerEpsilon k) :=
    Real.rpow_pos_of_pos hxpos _
  have hright : 0 < lowerEpsilon k * x := mul_pos hepos hxpos
  rw [← Real.log_le_log_iff hleft hright]
  rw [Real.log_rpow hxpos, Real.log_mul hepos.ne' hxpos.ne']
  linarith

/-- A fixed tower which majorizes all adaptive cutoffs. -/
noncomputable def lowerUpperTowerBase : ℝ :=
  16 * lowerAnalysisBase ^ 2

theorem lowerUpperTowerBase_le_realTower (k : ℕ) :
    lowerUpperTowerBase ≤ realTower lowerUpperTowerBase k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [realTower_succ]
      have h := Real.add_one_le_exp (realTower lowerUpperTowerBase k)
      linarith

/-- Strong majorization invariant; the factor four is reserve for the next
adaptive step. -/
theorem four_mul_cutoff_le_sqrt_upperTower (k : ℕ) :
    4 * adaptiveLowerCutoff k ≤ Real.sqrt (realTower lowerUpperTowerBase k) := by
  induction k with
  | zero =>
      rw [adaptiveLowerCutoff, realTower, lowerUpperTowerBase]
      have hR : 0 ≤ lowerAnalysisBase :=
        (lt_of_lt_of_le (by norm_num) two_le_lowerAnalysisBase).le
      have heq : 16 * lowerAnalysisBase ^ 2 =
          (4 * lowerAnalysisBase) ^ 2 := by ring
      rw [heq, Real.sqrt_sq (mul_nonneg (by norm_num) hR)]
  | succ k ih =>
      let R := adaptiveLowerCutoff k
      let S := realTower lowerUpperTowerBase k
      let e := lowerEpsilon k
      have hR1 : 1 ≤ R := by
        dsimp [R]
        exact le_trans (by norm_num) (le_trans two_le_lowerAnalysisBase
          (base_le_adaptiveLowerCutoff k))
      have hS0 : 0 ≤ S := by
        cases k with
        | zero =>
            dsimp [S, realTower, lowerUpperTowerBase]
            positivity
        | succ k => dsimp [S, realTower]; positivity
      have hsqrtSq : (Real.sqrt S) ^ 2 = S := by
        exact Real.sq_sqrt hS0
      have hR2 : 16 * R ^ 2 ≤ S := by
        dsimp [R, S] at ih ⊢
        nlinarith [sq_nonneg (Real.sqrt (realTower lowerUpperTowerBase k) -
          4 * adaptiveLowerCutoff k)]
      have he0 := lowerEpsilon_pos k
      have he2 := lowerEpsilon_le_half k
      have hq2 : 1 / (1 - e) ≤ 2 := by
        dsimp [e]
        rw [div_le_iff₀ (by linarith)]
        linarith
      have hrpow : R ^ (1 / (1 - e)) ≤ R ^ (2 : ℕ) := by
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le hR1 hq2
      have hA : 4 * R ^ (1 / (1 - e)) ≤ S / 4 := by
        nlinarith
      have hlog4 : Real.log 4 ≤ S / 4 := by
        have hlog4lt : Real.log 4 < 4 := by
          have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
          norm_num at h
          linarith
        have hSbase : lowerUpperTowerBase ≤ S := by
          dsimp [S]
          exact lowerUpperTowerBase_le_realTower k
        have hbase16 : (16 : ℝ) ≤ lowerUpperTowerBase := by
          rw [lowerUpperTowerBase]
          have hRbase : 1 ≤ lowerAnalysisBase :=
            le_trans (by norm_num) two_le_lowerAnalysisBase
          nlinarith [sq_nonneg (lowerAnalysisBase - 1)]
        nlinarith
      have hExp : 4 * Real.exp (4 * R ^ (1 / (1 - e))) ≤
          Real.exp (S / 2) := by
        calc
          4 * Real.exp (4 * R ^ (1 / (1 - e))) =
              Real.exp (Real.log 4 + 4 * R ^ (1 / (1 - e))) := by
            rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
          _ ≤ Real.exp (S / 2) := Real.exp_le_exp.mpr (by linarith)
      rw [adaptiveLowerCutoff, realTower_succ]
      have hsqrtExp : Real.sqrt (Real.exp S) = Real.exp (S / 2) := by
        have heq : Real.exp S = (Real.exp (S / 2)) ^ 2 := by
          rw [pow_two, ← Real.exp_add]
          congr 1
          ring
        rw [heq, Real.sqrt_sq (Real.exp_pos _).le]
      rw [hsqrtExp]
      exact hExp

/-- In particular each cutoff is bounded by a fixed ordinary tower. -/
theorem cutoff_le_upperTower (k : ℕ) :
    adaptiveLowerCutoff k ≤ realTower lowerUpperTowerBase k := by
  have h := four_mul_cutoff_le_sqrt_upperTower k
  have hSbase := lowerUpperTowerBase_le_realTower k
  have hbase1 : (1 : ℝ) ≤ lowerUpperTowerBase := by
    rw [lowerUpperTowerBase]
    have hR : 1 ≤ lowerAnalysisBase :=
      le_trans (by norm_num) two_le_lowerAnalysisBase
    nlinarith [sq_nonneg (lowerAnalysisBase - 1)]
  have hS1 : (1 : ℝ) ≤ realTower lowerUpperTowerBase k :=
    le_trans hbase1 hSbase
  have hsqrt : Real.sqrt (realTower lowerUpperTowerBase k) ≤
      realTower lowerUpperTowerBase k := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · linarith
    · nlinarith [mul_nonneg (le_trans (by norm_num) hS1)
        (sub_nonneg.mpr hS1)]
  nlinarith

/-- Uniform positive reserve for every height. -/
theorem coefficient_ge_half (k : ℕ) :
    1 / 2 ≤ lowerHeightCoefficient k := by
  have h := one_sub_sum_loss_le_coefficient k
  have hs := sum_lowerStageLoss_le k
  linarith

end Research
