import Research.SmoothExceptional

namespace Erdos796

open Filter Topology

/-- Fourth-root scale used to choose the smoothness threshold. -/
def smoothFourthRoot (n : ℕ) : ℕ := Nat.nthRoot 4 (Nat.log2 n)

/-- Dyadic threshold exponent; the actual threshold is `2^smoothScale`. -/
def smoothScale (n : ℕ) : ℕ := 4 * smoothFourthRoot n

/-- The binary logarithm tends to infinity. -/
theorem tendsto_nat_log2_atTop :
    Tendsto Nat.log2 atTop atTop := by
  rw [tendsto_atTop]
  intro b
  filter_upwards [eventually_ge_atTop (2 ^ b)] with n hn
  have hn0 : n ≠ 0 := by
    have hp : 0 < 2 ^ b := by positivity
    omega
  rw [Nat.le_log2 hn0]
  exact hn

/-- Consequently the chosen fourth-root scale also tends to infinity. -/
theorem tendsto_smoothFourthRoot_atTop :
    Tendsto smoothFourthRoot atTop atTop := by
  rw [tendsto_atTop]
  intro b
  have h := tendsto_nat_log2_atTop.eventually_ge_atTop (b ^ 4)
  filter_upwards [h] with n hn
  unfold smoothFourthRoot
  rw [Nat.le_nthRoot_iff (by norm_num : (4 : ℕ) ≠ 0)]
  exact hn

lemma smoothFourthRoot_pow_le_log2 (n : ℕ) :
    (smoothFourthRoot n) ^ 4 ≤ Nat.log2 n := by
  unfold smoothFourthRoot
  exact Nat.pow_nthRoot_le_iff.mpr (Or.inl (by norm_num))

lemma log2_lt_smoothFourthRoot_succ_pow (n : ℕ) :
    Nat.log2 n < (smoothFourthRoot n + 1) ^ 4 := by
  unfold smoothFourthRoot
  exact Nat.lt_pow_nthRoot_add_one (by norm_num) _

lemma log2_add_one_le_smoothFourthRoot_succ_pow (n : ℕ) :
    Nat.log2 n + 1 ≤ (smoothFourthRoot n + 1) ^ 4 :=
  Nat.succ_le_iff.mpr (log2_lt_smoothFourthRoot_succ_pow n)

/-- The fourth-root scale is eventually tiny compared with the binary
logarithm, in a concrete form used by all exponent comparisons below. -/
theorem eventually_hundred_mul_smoothFourthRoot_le_log2 :
    ∀ᶠ n : ℕ in atTop,
      100 * smoothFourthRoot n ≤ Nat.log2 n := by
  have hr := tendsto_smoothFourthRoot_atTop.eventually_ge_atTop 100
  filter_upwards [hr] with n hn
  let r := smoothFourthRoot n
  have hrpos : 0 < r := by dsimp [r]; omega
  have h100 : 100 * r ≤ r ^ 2 := by
    dsimp [r] at hn ⊢
    nlinarith
  have h24 : r ^ 2 ≤ r ^ 4 := Nat.pow_le_pow_right hrpos (by omega)
  exact h100.trans (h24.trans (smoothFourthRoot_pow_le_log2 n))

lemma two_pow_log2_le {n : ℕ} (hn : n ≠ 0) : 2 ^ Nat.log2 n ≤ n := by
  rw [Nat.log2_eq_log_two]
  exact Nat.pow_log_le_self 2 hn

lemma lt_two_pow_log2_add_one (n : ℕ) : n < 2 ^ (Nat.log2 n + 1) := by
  rw [Nat.log2_eq_log_two]
  exact Nat.lt_pow_succ_log_self Nat.one_lt_two n

/-- Real logarithm compared with binary logarithm. -/
theorem real_log_le_log2_add_one_mul_log_two {n : ℕ} (hn : 0 < n) :
    Real.log (n : ℝ) ≤ (Nat.log2 n + 1 : ℕ) * Real.log 2 := by
  have hnle : n ≤ 2 ^ (Nat.log2 n + 1) :=
    (lt_two_pow_log2_add_one n).le
  have hnR : (0 : ℝ) < n := by positivity
  have hpowR : (0 : ℝ) < ((2 ^ (Nat.log2 n + 1) : ℕ) : ℝ) := by positivity
  have hnleR : (n : ℝ) ≤ ((2 ^ (Nat.log2 n + 1) : ℕ) : ℝ) := by
    exact_mod_cast hnle
  have hlog := Real.log_le_log hnR hnleR
  rw [Nat.cast_pow, Real.log_pow] at hlog
  simpa [Nat.cast_add, Nat.cast_one] using hlog

/-- The fourth root of the dyadic threshold is exact because `smoothScale` is
a multiple of four. -/
theorem sqrt_sqrt_two_pow_smoothScale (n : ℕ) :
    Real.sqrt (Real.sqrt (((2 ^ smoothScale n : ℕ) : ℝ))) =
      ((2 ^ smoothFourthRoot n : ℕ) : ℝ) := by
  let r := smoothFourthRoot n
  have hcast : (((2 ^ smoothScale n : ℕ) : ℝ)) =
      ((((2 ^ r : ℕ) : ℝ) ^ 2) ^ 2) := by
    norm_cast
    unfold smoothScale
    dsimp [r]
    rw [← pow_mul, ← pow_mul]
    congr 1
    omega
  rw [hcast, Real.sqrt_sq_eq_abs, abs_of_nonneg (sq_nonneg _),
    Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]

/-- Cube-free contribution at the chosen threshold. -/
noncomputable def smoothThreeRaw (n : ℕ) : ℝ :=
  (((Nat.log2 n + 1) ^ 3 : ℕ) : ℝ) *
    ((n : ℝ) / (2 ^ smoothScale n : ℕ) +
      2 * (n : ℝ) /
        Real.sqrt (Real.sqrt (((2 ^ smoothScale n : ℕ) : ℝ))))

noncomputable def smoothPeripheralRaw (n : ℕ) : ℝ :=
  (((Nat.log2 n + 1) ^ 2 : ℕ) : ℝ) *
    ((2 ^ (6 * smoothScale n + Nat.log2 n / 4 + Nat.log2 n / 2) : ℕ) : ℝ)

noncomputable def smoothCentralLowRaw (n : ℕ) : ℝ :=
  (((Nat.log2 n + 1) ^ 2 : ℕ) : ℝ) *
    (16 * dyadicPrimeConstant ^ 2 *
      ((2 ^ Nat.log2 n : ℕ) : ℝ) /
        ((((Nat.log2 n : ℕ) : ℝ) ^ 2) *
          ((2 ^ (2 * smoothScale n) : ℕ) : ℝ)))

noncomputable def smoothCentralHighRaw (n : ℕ) : ℝ :=
  (((8 * smoothScale n + 1) ^ 2 : ℕ) : ℝ) *
    (16 * dyadicPrimeConstant ^ 2 * (n : ℝ) /
      ((Nat.log2 n : ℝ) ^ 2))

noncomputable def smoothDegenerateRaw (n : ℕ) : ℝ :=
  2 * (((2 ^ smoothScale n) ^ 6 : ℕ) : ℝ) * (n.sqrt + 2 : ℕ)

/-- The complete explicit majorant for the smooth remainder. -/
noncomputable def smoothRemainderRaw (n : ℕ) : ℝ :=
  smoothThreeRaw n + smoothPeripheralRaw n + smoothCentralLowRaw n +
    smoothCentralHighRaw n + smoothDegenerateRaw n

/-- Normalize the smooth majorant on the second-order scale. -/
noncomputable def smoothRemainderMajorant (n : ℕ) : ℝ :=
  smoothRemainderRaw n / ((n : ℝ) / Real.log (n : ℝ))

/-- A simpler comparison function expressed only through the fourth-root
parameter. -/
noncomputable def smoothComparison (n : ℕ) : ℝ :=
  let r := smoothFourthRoot n
  3 * Real.log 2 * (((r + 1 : ℕ) : ℝ) ^ 16 / (2 ^ r : ℕ)) +
  Real.log 2 * (((r + 1 : ℕ) : ℝ) ^ 12 / (2 ^ r : ℕ)) +
  (16 * dyadicPrimeConstant ^ 2 * Real.log 2) *
      (((r + 1 : ℕ) : ℝ) ^ 12 / (2 ^ r : ℕ)) +
  (32 * 1089 * dyadicPrimeConstant ^ 2 * Real.log 2) * (1 / (r : ℝ)) +
  Real.log 2 * (((r + 1 : ℕ) : ℝ) ^ 4 / (2 ^ r : ℕ))

/-- Polynomial growth loses to the dyadic exponential even after shifting the
natural argument by one. -/
theorem tendsto_succ_pow_div_two_pow (k : ℕ) :
    Tendsto (fun r : ℕ => (((r + 1 : ℕ) : ℝ) ^ k) /
      ((2 ^ r : ℕ) : ℝ)) atTop (nhds 0) := by
  have h := (tendsto_pow_const_div_const_pow_of_one_lt k
    (by norm_num : (1 : ℝ) < 2)).comp (Filter.tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun r : ℕ =>
      2 * ((((r + 1 : ℕ) : ℝ) ^ k) / (2 : ℝ) ^ (r + 1)))
      atTop (nhds 0) := by
    simpa using h.const_mul 2
  apply h2.congr'
  filter_upwards [eventually_ge_atTop 0] with r hr
  norm_num [pow_succ]
  ring

/-- The elementary comparison function tends to zero. -/
theorem tendsto_smoothComparison_zero :
    Tendsto smoothComparison atTop (nhds 0) := by
  have hr := tendsto_smoothFourthRoot_atTop
  have h16 := (tendsto_succ_pow_div_two_pow 16).comp hr
  have h12 := (tendsto_succ_pow_div_two_pow 12).comp hr
  have h4 := (tendsto_succ_pow_div_two_pow 4).comp hr
  have hinv : Tendsto (fun r : ℕ => (1 : ℝ) / (r : ℝ)) atTop (nhds 0) := by
    simpa using tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) 1
  have hinv' := hinv.comp hr
  unfold smoothComparison
  have htotal := ((((h16.const_mul (3 * Real.log 2)).add
    (h12.const_mul (Real.log 2))).add
    (h12.const_mul (16 * dyadicPrimeConstant ^ 2 * Real.log 2))).add
    (hinv'.const_mul
      (32 * 1089 * dyadicPrimeConstant ^ 2 * Real.log 2))).add
    (h4.const_mul (Real.log 2))
  simpa only [Function.comp_apply, mul_zero, add_zero] using htotal

lemma div_secondOrder_eq_mul_log_div {x : ℝ} {n : ℕ} (hn : 1 < n) :
    x / ((n : ℝ) / Real.log (n : ℝ)) =
      x * Real.log (n : ℝ) / (n : ℝ) := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hlog0 : Real.log (n : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast hn))
  field_simp

/-- The cube-free part is controlled by the first term of
`smoothComparison`. -/
theorem smoothThreeRaw_normalized_le {n : ℕ} (hn : 1 < n)
    (hroot : 0 < smoothFourthRoot n) :
    smoothThreeRaw n / ((n : ℝ) / Real.log (n : ℝ)) ≤
      3 * Real.log 2 *
        (((smoothFourthRoot n + 1 : ℕ) : ℝ) ^ 16) /
          ((2 ^ smoothFourthRoot n : ℕ) : ℝ) := by
  let L := Nat.log2 n
  let r := smoothFourthRoot n
  have hn0 : n ≠ 0 := by omega
  have hnR : (0 : ℝ) < n := by positivity
  have hlog := real_log_le_log2_add_one_mul_log_two (by omega : 0 < n)
  have hpolyNat : (L + 1) ^ 4 ≤ (r + 1) ^ 16 := by
    calc
      (L + 1) ^ 4 ≤ ((r + 1) ^ 4) ^ 4 :=
        Nat.pow_le_pow_left
          (log2_add_one_le_smoothFourthRoot_succ_pow n) 4
      _ = (r + 1) ^ 16 := by rw [← pow_mul]
  have hrs : r ≤ smoothScale n := by unfold smoothScale; omega
  have hpow : (2 ^ r : ℕ) ≤ 2 ^ smoothScale n :=
    Nat.pow_le_pow_right (by omega) hrs
  have hrecip : (1 : ℝ) / ((2 ^ smoothScale n : ℕ) : ℝ) ≤
      1 / ((2 ^ r : ℕ) : ℝ) := by
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (by exact_mod_cast hpow)
  rw [div_secondOrder_eq_mul_log_div hn]
  unfold smoothThreeRaw
  rw [sqrt_sqrt_two_pow_smoothScale]
  have heq :
      (((((L + 1) ^ 3 : ℕ) : ℝ) *
          ((n : ℝ) / (2 ^ smoothScale n : ℕ) +
            2 * (n : ℝ) / (2 ^ r : ℕ))) * Real.log (n : ℝ) /
            (n : ℝ)) =
        (((L + 1 : ℕ) : ℝ) ^ 3) * Real.log (n : ℝ) *
          ((1 : ℝ) / (2 ^ smoothScale n : ℕ) +
            2 / (2 ^ r : ℕ)) := by
    push_cast
    field_simp
  change (((((L + 1) ^ 3 : ℕ) : ℝ) *
      ((n : ℝ) / (2 ^ smoothScale n : ℕ) +
        2 * (n : ℝ) / (2 ^ r : ℕ))) * Real.log (n : ℝ) /
        (n : ℝ)) ≤ _
  rw [heq]
  have hbracket : (1 : ℝ) / (2 ^ smoothScale n : ℕ) +
      2 / (2 ^ r : ℕ) ≤ 3 / (2 ^ r : ℕ) := by
    calc
      (1 : ℝ) / (2 ^ smoothScale n : ℕ) + 2 / (2 ^ r : ℕ)
        ≤ 1 / (2 ^ r : ℕ) + 2 / (2 ^ r : ℕ) :=
          add_le_add hrecip le_rfl
      _ = 3 / (2 ^ r : ℕ) := by ring
  have hlog0 : 0 ≤ Real.log (n : ℝ) := (Real.log_pos
    (by exact_mod_cast hn)).le
  have hlog' : Real.log (n : ℝ) ≤
      (((L + 1 : ℕ) : ℝ) * Real.log 2) := by simpa [L] using hlog
  have hp : (((L + 1 : ℕ) : ℝ) ^ 4) ≤
      (((r + 1 : ℕ) : ℝ) ^ 16) := by exact_mod_cast hpolyNat
  calc
    (((L + 1 : ℕ) : ℝ) ^ 3) * Real.log (n : ℝ) *
          ((1 : ℝ) / (2 ^ smoothScale n : ℕ) + 2 / (2 ^ r : ℕ))
      ≤ (((L + 1 : ℕ) : ℝ) ^ 3) *
          (((L + 1 : ℕ) : ℝ) * Real.log 2) *
          ((1 : ℝ) / (2 ^ smoothScale n : ℕ) + 2 / (2 ^ r : ℕ)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlog' (by positivity)) (by positivity)
    _ ≤ (((L + 1 : ℕ) : ℝ) ^ 3) *
          (((L + 1 : ℕ) : ℝ) * Real.log 2) *
          (3 / (2 ^ r : ℕ)) := by
        let C : ℝ := (((L + 1 : ℕ) : ℝ) ^ 3) *
          (((L + 1 : ℕ) : ℝ) * Real.log 2)
        change C * ((1 : ℝ) / (2 ^ smoothScale n : ℕ) +
          2 / (2 ^ r : ℕ)) ≤ C * (3 / (2 ^ r : ℕ))
        have hL1 : (0 : ℝ) ≤ ((L + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.zero_le (L + 1)
        have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        exact mul_le_mul_of_nonneg_left hbracket
          (mul_nonneg (pow_nonneg hL1 3) (mul_nonneg hL1 hlog2))
    _ = 3 * Real.log 2 * (((L + 1 : ℕ) : ℝ) ^ 4) /
          ((2 ^ r : ℕ) : ℝ) := by ring
    _ ≤ 3 * Real.log 2 * (((r + 1 : ℕ) : ℝ) ^ 16) /
          ((2 ^ r : ℕ) : ℝ) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hp (by positivity)) (by positivity)

/-- The peripheral smooth-exception boxes are controlled by the second term
of `smoothComparison`. -/
theorem smoothPeripheralRaw_normalized_le {n : ℕ} (hn : 1 < n)
    (h100 : 100 * smoothFourthRoot n ≤ Nat.log2 n) :
    smoothPeripheralRaw n / ((n : ℝ) / Real.log (n : ℝ)) ≤
      Real.log 2 * (((smoothFourthRoot n + 1 : ℕ) : ℝ) ^ 12) /
        ((2 ^ smoothFourthRoot n : ℕ) : ℝ) := by
  let L := Nat.log2 n
  let r := smoothFourthRoot n
  let E := 6 * smoothScale n + L / 4 + L / 2
  have hn0 : n ≠ 0 := by omega
  have hnR : (0 : ℝ) < n := by positivity
  have hLpos : 0 < L := by
    have hlog : 1 ≤ Nat.log2 n := by
      rw [Nat.le_log2 hn0]
      norm_num
      omega
    exact hlog
  have hr : 0 < r := by
    apply (Nat.le_nthRoot_iff (by norm_num : (4 : ℕ) ≠ 0)).2
    dsimp [r, L]
    norm_num
    omega
  have hEr : E + r ≤ L := by
    dsimp [E, L, r]
    unfold smoothScale
    omega
  have hpowNat : 2 ^ E * 2 ^ r ≤ n := by
    rw [← pow_add]
    exact (Nat.pow_le_pow_right (by omega) hEr).trans (two_pow_log2_le hn0)
  have hratio : (((2 ^ E : ℕ) : ℝ) / (n : ℝ)) ≤
      1 / ((2 ^ r : ℕ) : ℝ) := by
    have hcast : (((2 ^ E : ℕ) : ℝ) * ((2 ^ r : ℕ) : ℝ)) ≤ (n : ℝ) := by
      exact_mod_cast hpowNat
    have hp : (0 : ℝ) < ((2 ^ r : ℕ) : ℝ) := by positivity
    have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
    field_simp
    nlinarith
  have hpolyNat : (L + 1) ^ 3 ≤ (r + 1) ^ 12 := by
    calc
      (L + 1) ^ 3 ≤ ((r + 1) ^ 4) ^ 3 :=
        Nat.pow_le_pow_left
          (log2_add_one_le_smoothFourthRoot_succ_pow n) 3
      _ = (r + 1) ^ 12 := by rw [← pow_mul]
  have hlog := real_log_le_log2_add_one_mul_log_two (by omega : 0 < n)
  have hlog' : Real.log (n : ℝ) ≤
      (((L + 1 : ℕ) : ℝ) * Real.log 2) := by simpa [L] using hlog
  rw [div_secondOrder_eq_mul_log_div hn]
  unfold smoothPeripheralRaw
  change ((((L + 1) ^ 2 : ℕ) : ℝ) * ((2 ^ E : ℕ) : ℝ) *
      Real.log (n : ℝ) / (n : ℝ)) ≤ _
  rw [show ((((L + 1) ^ 2 : ℕ) : ℝ) * ((2 ^ E : ℕ) : ℝ) *
      Real.log (n : ℝ) / (n : ℝ)) =
    (((L + 1 : ℕ) : ℝ) ^ 2) * Real.log (n : ℝ) *
      (((2 ^ E : ℕ) : ℝ) / (n : ℝ)) by push_cast; ring]
  have hp : (((L + 1 : ℕ) : ℝ) ^ 3) ≤
      (((r + 1 : ℕ) : ℝ) ^ 12) := by exact_mod_cast hpolyNat
  calc
    (((L + 1 : ℕ) : ℝ) ^ 2) * Real.log (n : ℝ) *
        (((2 ^ E : ℕ) : ℝ) / (n : ℝ))
      ≤ (((L + 1 : ℕ) : ℝ) ^ 2) *
        (((L + 1 : ℕ) : ℝ) * Real.log 2) *
          (1 / ((2 ^ r : ℕ) : ℝ)) := by
        have h1 := mul_le_mul_of_nonneg_left hlog' (by positivity :
          (0 : ℝ) ≤ (((L + 1 : ℕ) : ℝ) ^ 2))
        have h2 := mul_le_mul_of_nonneg_right h1 (by positivity :
          (0 : ℝ) ≤ (((2 ^ E : ℕ) : ℝ) / (n : ℝ)))
        exact h2.trans (mul_le_mul_of_nonneg_left hratio (by positivity))
    _ = Real.log 2 * (((L + 1 : ℕ) : ℝ) ^ 3) /
          ((2 ^ r : ℕ) : ℝ) := by ring
    _ ≤ Real.log 2 * (((r + 1 : ℕ) : ℝ) ^ 12) /
          ((2 ^ r : ℕ) : ℝ) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hp (Real.log_nonneg (by norm_num)))
          (by positivity)

/-- The below-hyperbola central boxes are controlled by the third term of
`smoothComparison`. -/
theorem smoothCentralLowRaw_normalized_le {n : ℕ} (hn : 1 < n)
    (hroot : 0 < smoothFourthRoot n) :
    smoothCentralLowRaw n / ((n : ℝ) / Real.log (n : ℝ)) ≤
      16 * dyadicPrimeConstant ^ 2 * Real.log 2 *
        (((smoothFourthRoot n + 1 : ℕ) : ℝ) ^ 12) /
          ((2 ^ smoothFourthRoot n : ℕ) : ℝ) := by
  let L := Nat.log2 n
  let r := smoothFourthRoot n
  have hn0 : n ≠ 0 := by omega
  have hnR : (0 : ℝ) < n := by positivity
  have hL1 : 1 ≤ Nat.log2 n := by
    rw [Nat.le_log2 hn0]
    norm_num
    omega
  have hL : 0 < L := by dsimp [L]; omega
  have hlog0 : 0 ≤ Real.log (n : ℝ) :=
    (Real.log_pos (by exact_mod_cast hn)).le
  have hpowN : (((2 ^ L : ℕ) : ℝ) / (n : ℝ)) ≤ 1 := by
    apply (div_le_one hnR).2
    exact_mod_cast two_pow_log2_le hn0
  have hLsq : (1 : ℝ) ≤ (L : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ L := by exact_mod_cast hL
    nlinarith
  have hlogDiv : Real.log (n : ℝ) / (L : ℝ) ^ 2 ≤
      ((L + 1 : ℕ) : ℝ) * Real.log 2 := by
    calc
      Real.log (n : ℝ) / (L : ℝ) ^ 2 ≤ Real.log (n : ℝ) :=
        div_le_self hlog0 hLsq
      _ ≤ ((L + 1 : ℕ) : ℝ) * Real.log 2 := by
        simpa [L] using real_log_le_log2_add_one_mul_log_two (by omega : 0 < n)
  have hrexp : r ≤ 2 * smoothScale n := by unfold smoothScale; omega
  have hpowExp : (2 ^ r : ℕ) ≤ 2 ^ (2 * smoothScale n) :=
    Nat.pow_le_pow_right (by omega) hrexp
  have hrecip : (1 : ℝ) / ((2 ^ (2 * smoothScale n) : ℕ) : ℝ) ≤
      1 / ((2 ^ r : ℕ) : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (by exact_mod_cast hpowExp)
  have hpolyNat : (L + 1) ^ 3 ≤ (r + 1) ^ 12 := by
    calc
      (L + 1) ^ 3 ≤ ((r + 1) ^ 4) ^ 3 :=
        Nat.pow_le_pow_left
          (log2_add_one_le_smoothFourthRoot_succ_pow n) 3
      _ = (r + 1) ^ 12 := by rw [← pow_mul]
  rw [div_secondOrder_eq_mul_log_div hn]
  unfold smoothCentralLowRaw
  have heq :
      (((((L + 1) ^ 2 : ℕ) : ℝ) *
          (16 * dyadicPrimeConstant ^ 2 * ((2 ^ L : ℕ) : ℝ) /
            (((L : ℝ) ^ 2) * ((2 ^ (2 * smoothScale n) : ℕ) : ℝ)))) *
          Real.log (n : ℝ) / (n : ℝ)) =
        16 * dyadicPrimeConstant ^ 2 * (((L + 1 : ℕ) : ℝ) ^ 2) *
          (((2 ^ L : ℕ) : ℝ) / (n : ℝ)) *
          (Real.log (n : ℝ) / (L : ℝ) ^ 2) *
          (1 / ((2 ^ (2 * smoothScale n) : ℕ) : ℝ)) := by
    push_cast
    field_simp
  change (((((L + 1) ^ 2 : ℕ) : ℝ) *
      (16 * dyadicPrimeConstant ^ 2 * ((2 ^ L : ℕ) : ℝ) /
        (((L : ℝ) ^ 2) * ((2 ^ (2 * smoothScale n) : ℕ) : ℝ)))) *
      Real.log (n : ℝ) / (n : ℝ)) ≤ _
  rw [heq]
  have hp : (((L + 1 : ℕ) : ℝ) ^ 3) ≤
      (((r + 1 : ℕ) : ℝ) ^ 12) := by exact_mod_cast hpolyNat
  calc
    16 * dyadicPrimeConstant ^ 2 * (((L + 1 : ℕ) : ℝ) ^ 2) *
          (((2 ^ L : ℕ) : ℝ) / (n : ℝ)) *
          (Real.log (n : ℝ) / (L : ℝ) ^ 2) *
          (1 / ((2 ^ (2 * smoothScale n) : ℕ) : ℝ))
      ≤ 16 * dyadicPrimeConstant ^ 2 * (((L + 1 : ℕ) : ℝ) ^ 2) *
          1 * (((L + 1 : ℕ) : ℝ) * Real.log 2) *
          (1 / ((2 ^ r : ℕ) : ℝ)) := by
        gcongr
    _ = 16 * dyadicPrimeConstant ^ 2 * Real.log 2 *
          (((L + 1 : ℕ) : ℝ) ^ 3) / ((2 ^ r : ℕ) : ℝ) := by ring
    _ ≤ 16 * dyadicPrimeConstant ^ 2 * Real.log 2 *
          (((r + 1 : ℕ) : ℝ) ^ 12) / ((2 ^ r : ℕ) : ℝ) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hp (by positivity)) (by positivity)

/-- The near-hyperbola boxes are controlled by the reciprocal fourth-root
term of `smoothComparison`. -/
theorem smoothCentralHighRaw_normalized_le {n : ℕ} (hn : 1 < n)
    (hroot : 0 < smoothFourthRoot n) :
    smoothCentralHighRaw n / ((n : ℝ) / Real.log (n : ℝ)) ≤
      (32 * 1089 * dyadicPrimeConstant ^ 2 * Real.log 2) *
        (1 / (smoothFourthRoot n : ℝ)) := by
  let L := Nat.log2 n
  let r := smoothFourthRoot n
  let S := 8 * smoothScale n + 1
  have hn0 : n ≠ 0 := by omega
  have hnR : (0 : ℝ) < n := by positivity
  have hr : 0 < r := by exact hroot
  have hL : 0 < L := by
    have hrpow := smoothFourthRoot_pow_le_log2 n
    dsimp [r, L] at hrpow ⊢
    exact (pow_pos hroot 4).trans_le hrpow
  have hS : S ≤ 33 * r := by
    dsimp [S]
    unfold smoothScale
    omega
  have hSsq : S ^ 2 ≤ 1089 * r ^ 2 := by
    calc
      S ^ 2 ≤ (33 * r) ^ 2 := Nat.pow_le_pow_left hS 2
      _ = 1089 * r ^ 2 := by ring
  have hr34 : r ^ 3 ≤ r ^ 4 := Nat.pow_le_pow_right hr (by omega)
  have hprodNat : S ^ 2 * r ≤ 1089 * L := by
    calc
      S ^ 2 * r ≤ (1089 * r ^ 2) * r := by gcongr
      _ = 1089 * r ^ 3 := by ring
      _ ≤ 1089 * r ^ 4 := by gcongr
      _ ≤ 1089 * L := by gcongr; exact smoothFourthRoot_pow_le_log2 n
  have hfrac : ((S : ℝ) ^ 2) / (L : ℝ) ≤ 1089 / (r : ℝ) := by
    have hcast : ((S : ℝ) ^ 2) * (r : ℝ) ≤ 1089 * (L : ℝ) := by
      exact_mod_cast hprodNat
    have hLr : (0 : ℝ) < L := by exact_mod_cast hL
    have hrr : (0 : ℝ) < r := by exact_mod_cast hr
    field_simp
    nlinarith
  have hLratio : (((L + 1 : ℕ) : ℝ) / (L : ℝ)) ≤ 2 := by
    have hLone : (1 : ℝ) ≤ L := by exact_mod_cast hL
    have hLr : (0 : ℝ) < L := by exact_mod_cast hL
    apply (div_le_iff₀ hLr).2
    push_cast
    linarith
  have hlog := real_log_le_log2_add_one_mul_log_two (by omega : 0 < n)
  have hlog' : Real.log (n : ℝ) ≤
      (((L + 1 : ℕ) : ℝ) * Real.log 2) := by simpa [L] using hlog
  rw [div_secondOrder_eq_mul_log_div hn]
  unfold smoothCentralHighRaw
  have heq :
      (((S ^ 2 : ℕ) : ℝ) *
          (16 * dyadicPrimeConstant ^ 2 * (n : ℝ) / (L : ℝ) ^ 2)) *
          Real.log (n : ℝ) / (n : ℝ) =
        16 * dyadicPrimeConstant ^ 2 *
          (Real.log (n : ℝ) / (L : ℝ)) *
          (((S : ℕ) : ℝ) ^ 2 / (L : ℝ)) := by
    push_cast
    field_simp <;> ring
  change (((S ^ 2 : ℕ) : ℝ) *
      (16 * dyadicPrimeConstant ^ 2 * (n : ℝ) / (L : ℝ) ^ 2)) *
      Real.log (n : ℝ) / (n : ℝ) ≤ _
  rw [heq]
  have hlogDiv : Real.log (n : ℝ) / (L : ℝ) ≤ 2 * Real.log 2 := by
    calc
      Real.log (n : ℝ) / (L : ℝ) ≤
          (((L + 1 : ℕ) : ℝ) * Real.log 2) / (L : ℝ) := by
        gcongr
      _ = (((L + 1 : ℕ) : ℝ) / (L : ℝ)) * Real.log 2 := by ring
      _ ≤ 2 * Real.log 2 := by gcongr
  calc
    16 * dyadicPrimeConstant ^ 2 * (Real.log (n : ℝ) / (L : ℝ)) *
          (((S : ℕ) : ℝ) ^ 2 / (L : ℝ))
      ≤ 16 * dyadicPrimeConstant ^ 2 * (2 * Real.log 2) *
          (1089 / (r : ℝ)) := by
        gcongr
    _ = (32 * 1089 * dyadicPrimeConstant ^ 2 * Real.log 2) *
          (1 / (r : ℝ)) := by ring

/-- Degenerate exceptional forms are controlled by the last exponential term
of `smoothComparison`. -/
theorem smoothDegenerateRaw_normalized_le {n : ℕ} (hn : 1 < n)
    (hroot : 0 < smoothFourthRoot n)
    (h100 : 100 * smoothFourthRoot n ≤ Nat.log2 n) :
    smoothDegenerateRaw n / ((n : ℝ) / Real.log (n : ℝ)) ≤
      Real.log 2 * (((smoothFourthRoot n + 1 : ℕ) : ℝ) ^ 4) /
        ((2 ^ smoothFourthRoot n : ℕ) : ℝ) := by
  let L := Nat.log2 n
  let r := smoothFourthRoot n
  let s := smoothScale n
  have hn0 : n ≠ 0 := by omega
  have hnR : (0 : ℝ) < n := by positivity
  have hr : 0 < r := by exact hroot
  have hL : 0 < L := by
    have hrpow := smoothFourthRoot_pow_le_log2 n
    dsimp [r, L] at hrpow ⊢
    exact (pow_pos hroot 4).trans_le hrpow
  let a := 2 ^ (L / 2 + 1)
  have hnltSq : n < a * a := by
    calc
      n < 2 ^ (L + 1) := by dsimp [L]; exact lt_two_pow_log2_add_one n
      _ ≤ 2 ^ (2 * (L / 2 + 1)) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      _ = a * a := by
        dsimp [a]
        rw [show 2 * (L / 2 + 1) = (L / 2 + 1) + (L / 2 + 1) by omega,
          pow_add]
  have hsqrt : n.sqrt < a := Nat.sqrt_lt.mpr hnltSq
  have htwoa : 2 ≤ a := by
    dsimp [a]
    have hpow : (2 : ℕ) ^ 1 ≤ 2 ^ (L / 2 + 1) :=
      Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) (by omega)
    simpa using hpow
  have hsqrtAdd : n.sqrt + 2 ≤ 2 ^ (L / 2 + 2) := by
    calc
      n.sqrt + 2 ≤ a + a := Nat.add_le_add hsqrt.le htwoa
      _ = 2 ^ (L / 2 + 2) := by
        dsimp [a]
        rw [show L / 2 + 2 = (L / 2 + 1) + 1 by omega, pow_succ]
        ring
  have hexp : 1 + 6 * s + (L / 2 + 2) + r ≤ L := by
    dsimp [s, r, L]
    unfold smoothScale
    omega
  have hrawNat :
      2 * (2 ^ s) ^ 6 * (n.sqrt + 2) * 2 ^ r ≤ n := by
    calc
      2 * (2 ^ s) ^ 6 * (n.sqrt + 2) * 2 ^ r
        ≤ 2 * (2 ^ s) ^ 6 * 2 ^ (L / 2 + 2) * 2 ^ r := by gcongr
      _ = 2 ^ 1 * (2 ^ s) ^ 6 * 2 ^ (L / 2 + 2) * 2 ^ r := by norm_num
      _ = 2 ^ (1 + 6 * s + (L / 2 + 2) + r) := by
        rw [← pow_mul, ← pow_add, ← pow_add, ← pow_add]
        congr 1
        omega
      _ ≤ 2 ^ L := Nat.pow_le_pow_right (by omega) hexp
      _ ≤ n := two_pow_log2_le hn0
  have hratio :
      ((2 * (2 ^ s) ^ 6 * (n.sqrt + 2) : ℕ) : ℝ) / (n : ℝ) ≤
        1 / ((2 ^ r : ℕ) : ℝ) := by
    have hcast : ((2 * (2 ^ s) ^ 6 * (n.sqrt + 2) : ℕ) : ℝ) *
        ((2 ^ r : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hrawNat
    have hp : (0 : ℝ) < ((2 ^ r : ℕ) : ℝ) := by positivity
    field_simp
    nlinarith
  have hlog := real_log_le_log2_add_one_mul_log_two (by omega : 0 < n)
  have hlog' : Real.log (n : ℝ) ≤
      (((L + 1 : ℕ) : ℝ) * Real.log 2) := by simpa [L] using hlog
  have hpoly : ((L + 1 : ℕ) : ℝ) ≤
      (((r + 1 : ℕ) : ℝ) ^ 4) := by
    exact_mod_cast log2_add_one_le_smoothFourthRoot_succ_pow n
  rw [div_secondOrder_eq_mul_log_div hn]
  unfold smoothDegenerateRaw
  change ((2 * (((2 ^ s) ^ 6 : ℕ) : ℝ) * (n.sqrt + 2 : ℕ)) *
      Real.log (n : ℝ) / (n : ℝ)) ≤ _
  rw [show ((2 * (((2 ^ s) ^ 6 : ℕ) : ℝ) * (n.sqrt + 2 : ℕ)) *
      Real.log (n : ℝ) / (n : ℝ)) =
    Real.log (n : ℝ) *
      (((2 * (2 ^ s) ^ 6 * (n.sqrt + 2) : ℕ) : ℝ) / (n : ℝ)) by
      push_cast; ring]
  calc
    Real.log (n : ℝ) *
        (((2 * (2 ^ s) ^ 6 * (n.sqrt + 2) : ℕ) : ℝ) / (n : ℝ))
      ≤ (((L + 1 : ℕ) : ℝ) * Real.log 2) *
          (1 / ((2 ^ r : ℕ) : ℝ)) := by
        gcongr
    _ ≤ ((((r + 1 : ℕ) : ℝ) ^ 4) * Real.log 2) *
          (1 / ((2 ^ r : ℕ) : ℝ)) := by
        gcongr
    _ = Real.log 2 * (((r + 1 : ℕ) : ℝ) ^ 4) /
          ((2 ^ r : ℕ) : ℝ) := by ring

/-- The normalized raw majorant is eventually below the elementary
comparison function. -/
theorem smoothRemainderMajorant_le_comparison {n : ℕ} (hn : 1 < n)
    (hroot : 0 < smoothFourthRoot n)
    (h100 : 100 * smoothFourthRoot n ≤ Nat.log2 n) :
    smoothRemainderMajorant n ≤ smoothComparison n := by
  have hthree := smoothThreeRaw_normalized_le hn hroot
  have hper := smoothPeripheralRaw_normalized_le hn h100
  have hlow := smoothCentralLowRaw_normalized_le hn hroot
  have hhigh := smoothCentralHighRaw_normalized_le hn hroot
  have hdeg := smoothDegenerateRaw_normalized_le hn hroot h100
  unfold smoothRemainderMajorant smoothRemainderRaw smoothComparison
  rw [show
    (smoothThreeRaw n + smoothPeripheralRaw n + smoothCentralLowRaw n +
        smoothCentralHighRaw n + smoothDegenerateRaw n) /
        ((n : ℝ) / Real.log (n : ℝ)) =
      smoothThreeRaw n / ((n : ℝ) / Real.log (n : ℝ)) +
      smoothPeripheralRaw n / ((n : ℝ) / Real.log (n : ℝ)) +
      smoothCentralLowRaw n / ((n : ℝ) / Real.log (n : ℝ)) +
      smoothCentralHighRaw n / ((n : ℝ) / Real.log (n : ℝ)) +
      smoothDegenerateRaw n / ((n : ℝ) / Real.log (n : ℝ)) by ring]
  dsimp only
  calc
    smoothThreeRaw n / ((n : ℝ) / Real.log (n : ℝ)) +
        smoothPeripheralRaw n / ((n : ℝ) / Real.log (n : ℝ)) +
        smoothCentralLowRaw n / ((n : ℝ) / Real.log (n : ℝ)) +
        smoothCentralHighRaw n / ((n : ℝ) / Real.log (n : ℝ)) +
        smoothDegenerateRaw n / ((n : ℝ) / Real.log (n : ℝ))
      ≤ (3 * Real.log 2 * (((smoothFourthRoot n + 1 : ℕ) : ℝ) ^ 16) /
          ((2 ^ smoothFourthRoot n : ℕ) : ℝ)) +
        (Real.log 2 * (((smoothFourthRoot n + 1 : ℕ) : ℝ) ^ 12) /
          ((2 ^ smoothFourthRoot n : ℕ) : ℝ)) +
        (16 * dyadicPrimeConstant ^ 2 * Real.log 2 *
          (((smoothFourthRoot n + 1 : ℕ) : ℝ) ^ 12) /
          ((2 ^ smoothFourthRoot n : ℕ) : ℝ)) +
        ((32 * 1089 * dyadicPrimeConstant ^ 2 * Real.log 2) *
          (1 / (smoothFourthRoot n : ℝ))) +
        (Real.log 2 * (((smoothFourthRoot n + 1 : ℕ) : ℝ) ^ 4) /
          ((2 ^ smoothFourthRoot n : ℕ) : ℝ)) := by linarith
    _ = _ := by ring

/-- The normalized smooth-remainder majorant tends to zero. -/
theorem tendsto_smoothRemainderMajorant_zero :
    Tendsto smoothRemainderMajorant atTop (nhds 0) := by
  have hroot := tendsto_smoothFourthRoot_atTop.eventually_ge_atTop 1
  have h100 := eventually_hundred_mul_smoothFourthRoot_le_log2
  have hnonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ smoothRemainderMajorant n := by
    filter_upwards [eventually_gt_atTop 1] with n hn
    unfold smoothRemainderMajorant smoothRemainderRaw smoothThreeRaw
      smoothPeripheralRaw smoothCentralLowRaw smoothCentralHighRaw
      smoothDegenerateRaw
    have hden : 0 < (n : ℝ) / Real.log (n : ℝ) := by
      exact div_pos (by positivity) (Real.log_pos (by exact_mod_cast hn))
    positivity
  have hle : ∀ᶠ n : ℕ in atTop,
      smoothRemainderMajorant n ≤ smoothComparison n := by
    filter_upwards [eventually_gt_atTop 1, hroot, h100] with n hn hr h100n
    exact smoothRemainderMajorant_le_comparison hn (by omega) h100n
  exact squeeze_zero' hnonneg hle tendsto_smoothComparison_zero

/-- The real-valued summand in the relevant exceptional dyadic sum. -/
noncomputable def smoothDyadicTerm (n s : ℕ) (e : ℕ × ℕ) : ℝ :=
  (min ((2 ^ s) ^ 6) (n / 2 ^ (e.1 + e.2)) : ℕ) *
    (dyadicPrimes e.1).card * (dyadicPrimes e.2).card

lemma smoothDyadicTerm_nonneg (n s : ℕ) (e : ℕ × ℕ) :
    0 ≤ smoothDyadicTerm n s e := by
  unfold smoothDyadicTerm
  positivity

lemma dyadicPrimes_card_le_pow (i : ℕ) :
    (dyadicPrimes i).card ≤ 2 ^ i := by
  calc
    (dyadicPrimes i).card ≤ (dyadicInterval i).card := by
      exact Finset.card_le_card (Finset.filter_subset _ _)
    _ = 2 ^ i := dyadicInterval_card i

/-- Without prime-density input, one dyadic exceptional summand is bounded by
the full integer box. -/
theorem smoothDyadicTerm_le_trivial (n s : ℕ) (e : ℕ × ℕ) :
    smoothDyadicTerm n s e ≤ ((2 ^ (6 * s + e.1 + e.2) : ℕ) : ℝ) := by
  unfold smoothDyadicTerm
  have hmin : min ((2 ^ s) ^ 6) (n / 2 ^ (e.1 + e.2)) ≤ (2 ^ s) ^ 6 :=
    min_le_left _ _
  have hpi := dyadicPrimes_card_le_pow e.1
  have hpj := dyadicPrimes_card_le_pow e.2
  have hnat : min ((2 ^ s) ^ 6) (n / 2 ^ (e.1 + e.2)) *
      (dyadicPrimes e.1).card * (dyadicPrimes e.2).card ≤
        2 ^ (6 * s + e.1 + e.2) := by
    calc
      _ ≤ (2 ^ s) ^ 6 * 2 ^ e.1 * 2 ^ e.2 := by gcongr
      _ = 2 ^ (6 * s + e.1 + e.2) := by
        rw [← pow_mul, ← pow_add, ← pow_add]
        congr 2
        omega
  exact_mod_cast hnat

/-- Prime-density version of a single summand. -/
theorem smoothDyadicTerm_le_primeBound
    {n s i j : ℕ}
    (hi : ((dyadicPrimes i).card : ℝ) ≤
      dyadicPrimeConstant * ((2 ^ i : ℕ) : ℝ) / (i + 1))
    (hj : ((dyadicPrimes j).card : ℝ) ≤
      dyadicPrimeConstant * ((2 ^ j : ℕ) : ℝ) / (j + 1)) :
    smoothDyadicTerm n s (i, j) ≤
      (min ((2 ^ s) ^ 6) (n / 2 ^ (i + j)) : ℕ) *
        dyadicPrimeConstant ^ 2 * ((2 ^ (i + j) : ℕ) : ℝ) /
          (((i + 1 : ℕ) : ℝ) * (j + 1 : ℕ)) := by
  unfold smoothDyadicTerm
  have hmin : (0 : ℝ) ≤
      (min ((2 ^ s) ^ 6) (n / 2 ^ (i + j)) : ℕ) := by positivity
  have hC := dyadicPrimeConstant_pos.le
  have hiDen : (0 : ℝ) < (i + 1 : ℕ) := by positivity
  have hjDen : (0 : ℝ) < (j + 1 : ℕ) := by positivity
  calc
    (min ((2 ^ s) ^ 6) (n / 2 ^ (i + j)) : ℕ) *
          (dyadicPrimes i).card * (dyadicPrimes j).card
      ≤ (min ((2 ^ s) ^ 6) (n / 2 ^ (i + j)) : ℕ) *
          (dyadicPrimeConstant * ((2 ^ i : ℕ) : ℝ) / (i + 1)) *
          (dyadicPrimeConstant * ((2 ^ j : ℕ) : ℝ) / (j + 1)) := by
        gcongr
    _ = _ := by
      rw [pow_add]
      push_cast
      field_simp

/-- Indices with at least one factor below the central dyadic range. -/
def smoothPeripheralIndices (n s : ℕ) : Finset (ℕ × ℕ) :=
  (smoothPrimeIndexSquare n s).filter fun e =>
    e.1 < Nat.log2 n / 4 ∨ e.2 < Nat.log2 n / 4

/-- Central indices for which the small-kernel allowance is active. -/
def smoothCentralLowIndices (n s : ℕ) : Finset (ℕ × ℕ) :=
  ((smoothPrimeIndexSquare n s).filter fun e =>
    ¬(e.1 < Nat.log2 n / 4 ∨ e.2 < Nat.log2 n / 4)).filter fun e =>
      e.1 + e.2 + 8 * s ≤ Nat.log2 n

/-- Central indices next to the hyperbola, where the product constraint is
stronger than the small-kernel cutoff. -/
def smoothCentralHighIndices (n s : ℕ) : Finset (ℕ × ℕ) :=
  ((smoothPrimeIndexSquare n s).filter fun e =>
    ¬(e.1 < Nat.log2 n / 4 ∨ e.2 < Nat.log2 n / 4)).filter fun e =>
      ¬(e.1 + e.2 + 8 * s ≤ Nat.log2 n)

lemma smoothIndexSum_partition (n s : ℕ) (f : ℕ × ℕ → ℝ) :
    (∑ e ∈ smoothPrimeIndexSquare n s, f e) =
      (∑ e ∈ smoothPeripheralIndices n s, f e) +
      (∑ e ∈ smoothCentralLowIndices n s, f e) +
      (∑ e ∈ smoothCentralHighIndices n s, f e) := by
  let S := smoothPrimeIndexSquare n s
  let peripheral : ℕ × ℕ → Prop := fun e =>
    e.1 < Nat.log2 n / 4 ∨ e.2 < Nat.log2 n / 4
  let central := S.filter fun e => ¬ peripheral e
  let low : ℕ × ℕ → Prop := fun e => e.1 + e.2 + 8 * s ≤ Nat.log2 n
  have h1 := (Finset.sum_filter_add_sum_filter_not S peripheral f).symm
  have h2 := (Finset.sum_filter_add_sum_filter_not central low f).symm
  change (∑ e ∈ S, f e) =
    (∑ e ∈ S.filter peripheral, f e) +
      (∑ e ∈ central.filter low, f e) +
      (∑ e ∈ central.filter fun e => ¬low e, f e)
  rw [h1, h2]
  ring

lemma smoothPrimeIndexSquare_card_le (n s : ℕ) :
    (smoothPrimeIndexSquare n s).card ≤ (Nat.log2 n + 1) ^ 2 := by
  have hsub : smoothPrimeIndexSquare n s ⊆ dyadicIndexSquare n := by
    intro e he
    have he' := Finset.mem_product.mp he
    have hi := (Finset.mem_Icc.mp he'.1).2
    have hj := (Finset.mem_Icc.mp he'.2).2
    exact Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (lt_of_le_of_lt hi (by omega)),
       Finset.mem_range.mpr (lt_of_le_of_lt hj (by omega))⟩
  calc
    (smoothPrimeIndexSquare n s).card ≤ (dyadicIndexSquare n).card :=
      Finset.card_le_card hsub
    _ = (Nat.log2 n + 1) ^ 2 := dyadicIndexSquare_card n

lemma smoothPeripheralIndices_card_le (n s : ℕ) :
    (smoothPeripheralIndices n s).card ≤ (Nat.log2 n + 1) ^ 2 :=
  (Finset.card_le_card (Finset.filter_subset _ _)).trans
    (smoothPrimeIndexSquare_card_le n s)

lemma smoothCentralLowIndices_card_le (n s : ℕ) :
    (smoothCentralLowIndices n s).card ≤ (Nat.log2 n + 1) ^ 2 :=
  (Finset.card_le_card
    ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _))).trans
      (smoothPrimeIndexSquare_card_le n s)

/-- Near the hyperbola each coordinate lies in one of at most `8s+1`
dyadic intervals. -/
theorem smoothCentralHighIndices_card_le (n s : ℕ) :
    (smoothCentralHighIndices n s).card ≤ (8 * s + 1) ^ 2 := by
  let L := Nat.log2 n
  let J := Finset.Icc (L / 2 - 8 * s) (L / 2)
  have hsub : smoothCentralHighIndices n s ⊆ J.product J := by
    intro e he
    have hehigh := Finset.mem_filter.mp he
    have hecentral := Finset.mem_filter.mp hehigh.1
    have herange := Finset.mem_product.mp hecentral.1
    have hiUpper := (Finset.mem_Icc.mp herange.1).2
    have hjUpper := (Finset.mem_Icc.mp herange.2).2
    have hsum : L < e.1 + e.2 + 8 * s := by
      dsimp [L]
      omega
    apply Finset.mem_product.mpr
    constructor <;> apply Finset.mem_Icc.mpr
    · constructor
      · dsimp [J, L]
        omega
      · exact hiUpper
    · constructor
      · dsimp [J, L]
        omega
      · exact hjUpper
  calc
    (smoothCentralHighIndices n s).card ≤ (J.product J).card :=
      Finset.card_le_card hsub
    _ = (J.card) ^ 2 := by simp [pow_two]
    _ ≤ (8 * s + 1) ^ 2 := by
      gcongr
      dsimp [J, L]
      simp only [Nat.card_Icc]
      omega

/-- Uniform bound for the peripheral part of the dyadic sum. -/
theorem smoothPeripheralSum_le (n s : ℕ) :
    (∑ e ∈ smoothPeripheralIndices n s, smoothDyadicTerm n s e) ≤
      (((Nat.log2 n + 1) ^ 2 : ℕ) : ℝ) *
        ((2 ^ (6 * s + Nat.log2 n / 4 + Nat.log2 n / 2) : ℕ) : ℝ) := by
  have hone : ∀ e ∈ smoothPeripheralIndices n s,
      smoothDyadicTerm n s e ≤
        ((2 ^ (6 * s + Nat.log2 n / 4 + Nat.log2 n / 2) : ℕ) : ℝ) := by
    intro e he
    have he' := Finset.mem_filter.mp he
    have herange := Finset.mem_product.mp he'.1
    have hiUpper := (Finset.mem_Icc.mp herange.1).2
    have hjUpper := (Finset.mem_Icc.mp herange.2).2
    apply (smoothDyadicTerm_le_trivial n s e).trans
    exact_mod_cast Nat.pow_le_pow_right (by omega : 0 < 2) (by omega)
  calc
    (∑ e ∈ smoothPeripheralIndices n s, smoothDyadicTerm n s e)
      ≤ ∑ _e ∈ smoothPeripheralIndices n s,
          (((2 ^ (6 * s + Nat.log2 n / 4 + Nat.log2 n / 2) : ℕ) : ℝ)) :=
        Finset.sum_le_sum hone
    _ = ((smoothPeripheralIndices n s).card : ℝ) *
        ((2 ^ (6 * s + Nat.log2 n / 4 + Nat.log2 n / 2) : ℕ) : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by
      gcongr
      exact_mod_cast smoothPeripheralIndices_card_le n s

/-- Uniform bound for the central boxes below the product hyperbola. -/
theorem smoothCentralLowSum_le (n s : ℕ) (hL : 0 < Nat.log2 n)
    (hprime : ∀ i ∈ smoothPrimeIndexRange n s,
      ((dyadicPrimes i).card : ℝ) ≤
        dyadicPrimeConstant * ((2 ^ i : ℕ) : ℝ) / (i + 1)) :
    (∑ e ∈ smoothCentralLowIndices n s, smoothDyadicTerm n s e) ≤
      (((Nat.log2 n + 1) ^ 2 : ℕ) : ℝ) *
        (16 * dyadicPrimeConstant ^ 2 *
          ((2 ^ Nat.log2 n : ℕ) : ℝ) /
            ((((Nat.log2 n : ℕ) : ℝ) ^ 2) *
              ((2 ^ (2 * s) : ℕ) : ℝ))) := by
  let L := Nat.log2 n
  have hone : ∀ e ∈ smoothCentralLowIndices n s,
      smoothDyadicTerm n s e ≤
        16 * dyadicPrimeConstant ^ 2 * ((2 ^ L : ℕ) : ℝ) /
          ((((L : ℕ) : ℝ) ^ 2) * ((2 ^ (2 * s) : ℕ) : ℝ)) := by
    intro e he
    have helow := Finset.mem_filter.mp he
    have hecentral := Finset.mem_filter.mp helow.1
    have herange := Finset.mem_product.mp hecentral.1
    have hnot := hecentral.2
    have hiQuarter : L / 4 ≤ e.1 := by dsimp [L] at hnot ⊢; omega
    have hjQuarter : L / 4 ≤ e.2 := by dsimp [L] at hnot ⊢; omega
    have hiPrime := hprime e.1 herange.1
    have hjPrime := hprime e.2 herange.2
    apply (smoothDyadicTerm_le_primeBound hiPrime hjPrime).trans
    have hnumNat :
        min ((2 ^ s) ^ 6) (n / 2 ^ (e.1 + e.2)) *
            2 ^ (e.1 + e.2) * 2 ^ (2 * s) ≤ 2 ^ L := by
      calc
        _ ≤ (2 ^ s) ^ 6 * 2 ^ (e.1 + e.2) * 2 ^ (2 * s) := by
          gcongr
          exact min_le_left _ _
        _ = 2 ^ (e.1 + e.2 + 8 * s) := by
          rw [← pow_mul, ← pow_add, ← pow_add]
          congr 1
          omega
        _ ≤ 2 ^ L := Nat.pow_le_pow_right (by omega) (by
          dsimp [L]
          exact helow.2)
    have hpowPos : (0 : ℝ) < ((2 ^ (2 * s) : ℕ) : ℝ) := by positivity
    have hnum :
        (min ((2 ^ s) ^ 6) (n / 2 ^ (e.1 + e.2)) : ℕ) *
            ((2 ^ (e.1 + e.2) : ℕ) : ℝ) ≤
          ((2 ^ L : ℕ) : ℝ) / ((2 ^ (2 * s) : ℕ) : ℝ) := by
      apply (le_div_iff₀ hpowPos).2
      exact_mod_cast hnumNat
    have hiDenNat : L ≤ 4 * (e.1 + 1) := by omega
    have hjDenNat : L ≤ 4 * (e.2 + 1) := by omega
    have hLreal : (0 : ℝ) < L := by exact_mod_cast hL
    have hiDenPos : (0 : ℝ) < (e.1 + 1 : ℕ) := by positivity
    have hjDenPos : (0 : ℝ) < (e.2 + 1 : ℕ) := by positivity
    have hden : ((L : ℝ) ^ 2) ≤
        16 * (((e.1 + 1 : ℕ) : ℝ) * (e.2 + 1 : ℕ)) := by
      have hiDenR : (L : ℝ) ≤ 4 * (e.1 + 1 : ℕ) := by exact_mod_cast hiDenNat
      have hjDenR : (L : ℝ) ≤ 4 * (e.2 + 1 : ℕ) := by exact_mod_cast hjDenNat
      nlinarith
    have hC : 0 ≤ dyadicPrimeConstant ^ 2 := sq_nonneg _
    have hpowL : (0 : ℝ) ≤ ((2 ^ L : ℕ) : ℝ) := by positivity
    calc
      (min ((2 ^ s) ^ 6) (n / 2 ^ (e.1 + e.2)) : ℕ) *
            dyadicPrimeConstant ^ 2 * ((2 ^ (e.1 + e.2) : ℕ) : ℝ) /
              (((e.1 + 1 : ℕ) : ℝ) * (e.2 + 1 : ℕ))
        ≤ (((2 ^ L : ℕ) : ℝ) / ((2 ^ (2 * s) : ℕ) : ℝ)) *
            dyadicPrimeConstant ^ 2 /
              (((e.1 + 1 : ℕ) : ℝ) * (e.2 + 1 : ℕ)) := by
          rw [show
            (min ((2 ^ s) ^ 6) (n / 2 ^ (e.1 + e.2)) : ℕ) *
                dyadicPrimeConstant ^ 2 * ((2 ^ (e.1 + e.2) : ℕ) : ℝ) =
              ((min ((2 ^ s) ^ 6) (n / 2 ^ (e.1 + e.2)) : ℕ) *
                ((2 ^ (e.1 + e.2) : ℕ) : ℝ)) *
                dyadicPrimeConstant ^ 2 by ring]
          gcongr
      _ ≤ 16 * dyadicPrimeConstant ^ 2 * ((2 ^ L : ℕ) : ℝ) /
            (((L : ℝ) ^ 2) * ((2 ^ (2 * s) : ℕ) : ℝ)) := by
          have hdenPos : (0 : ℝ) <
              (((e.1 + 1 : ℕ) : ℝ) * (e.2 + 1 : ℕ)) :=
            mul_pos hiDenPos hjDenPos
          field_simp
          nlinarith
  calc
    (∑ e ∈ smoothCentralLowIndices n s, smoothDyadicTerm n s e)
      ≤ ∑ _e ∈ smoothCentralLowIndices n s,
          (16 * dyadicPrimeConstant ^ 2 * ((2 ^ L : ℕ) : ℝ) /
            ((((L : ℕ) : ℝ) ^ 2) * ((2 ^ (2 * s) : ℕ) : ℝ))) :=
        Finset.sum_le_sum hone
    _ = ((smoothCentralLowIndices n s).card : ℝ) *
        (16 * dyadicPrimeConstant ^ 2 * ((2 ^ L : ℕ) : ℝ) /
          ((((L : ℕ) : ℝ) ^ 2) * ((2 ^ (2 * s) : ℕ) : ℝ))) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by
      dsimp [L]
      gcongr
      exact_mod_cast smoothCentralLowIndices_card_le n s

/-- Uniform bound for the central boxes adjacent to the product hyperbola. -/
theorem smoothCentralHighSum_le (n s : ℕ) (hL : 0 < Nat.log2 n)
    (hprime : ∀ i ∈ smoothPrimeIndexRange n s,
      ((dyadicPrimes i).card : ℝ) ≤
        dyadicPrimeConstant * ((2 ^ i : ℕ) : ℝ) / (i + 1)) :
    (∑ e ∈ smoothCentralHighIndices n s, smoothDyadicTerm n s e) ≤
      (((8 * s + 1) ^ 2 : ℕ) : ℝ) *
        (16 * dyadicPrimeConstant ^ 2 * (n : ℝ) /
          ((Nat.log2 n : ℝ) ^ 2)) := by
  let L := Nat.log2 n
  have hone : ∀ e ∈ smoothCentralHighIndices n s,
      smoothDyadicTerm n s e ≤
        16 * dyadicPrimeConstant ^ 2 * (n : ℝ) / (L : ℝ) ^ 2 := by
    intro e he
    have hehigh := Finset.mem_filter.mp he
    have hecentral := Finset.mem_filter.mp hehigh.1
    have herange := Finset.mem_product.mp hecentral.1
    have hnot := hecentral.2
    have hiQuarter : L / 4 ≤ e.1 := by dsimp [L] at hnot ⊢; omega
    have hjQuarter : L / 4 ≤ e.2 := by dsimp [L] at hnot ⊢; omega
    have hiPrime := hprime e.1 herange.1
    have hjPrime := hprime e.2 herange.2
    apply (smoothDyadicTerm_le_primeBound hiPrime hjPrime).trans
    have hnumNat :
        min ((2 ^ s) ^ 6) (n / 2 ^ (e.1 + e.2)) *
            2 ^ (e.1 + e.2) ≤ n := by
      calc
        _ ≤ (n / 2 ^ (e.1 + e.2)) * 2 ^ (e.1 + e.2) := by
          gcongr
          exact min_le_right _ _
        _ ≤ n := Nat.div_mul_le_self _ _
    have hnum :
        (min ((2 ^ s) ^ 6) (n / 2 ^ (e.1 + e.2)) : ℕ) *
            ((2 ^ (e.1 + e.2) : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hnumNat
    have hiDenNat : L ≤ 4 * (e.1 + 1) := by omega
    have hjDenNat : L ≤ 4 * (e.2 + 1) := by omega
    have hLreal : (0 : ℝ) < L := by exact_mod_cast hL
    have hiDenPos : (0 : ℝ) < (e.1 + 1 : ℕ) := by positivity
    have hjDenPos : (0 : ℝ) < (e.2 + 1 : ℕ) := by positivity
    have hden : ((L : ℝ) ^ 2) ≤
        16 * (((e.1 + 1 : ℕ) : ℝ) * (e.2 + 1 : ℕ)) := by
      have hiDenR : (L : ℝ) ≤ 4 * (e.1 + 1 : ℕ) := by exact_mod_cast hiDenNat
      have hjDenR : (L : ℝ) ≤ 4 * (e.2 + 1 : ℕ) := by exact_mod_cast hjDenNat
      nlinarith
    have hC : 0 ≤ dyadicPrimeConstant ^ 2 := sq_nonneg _
    calc
      (min ((2 ^ s) ^ 6) (n / 2 ^ (e.1 + e.2)) : ℕ) *
            dyadicPrimeConstant ^ 2 * ((2 ^ (e.1 + e.2) : ℕ) : ℝ) /
              (((e.1 + 1 : ℕ) : ℝ) * (e.2 + 1 : ℕ))
        ≤ (n : ℝ) * dyadicPrimeConstant ^ 2 /
              (((e.1 + 1 : ℕ) : ℝ) * (e.2 + 1 : ℕ)) := by
          rw [show
            (min ((2 ^ s) ^ 6) (n / 2 ^ (e.1 + e.2)) : ℕ) *
                dyadicPrimeConstant ^ 2 * ((2 ^ (e.1 + e.2) : ℕ) : ℝ) =
              ((min ((2 ^ s) ^ 6) (n / 2 ^ (e.1 + e.2)) : ℕ) *
                ((2 ^ (e.1 + e.2) : ℕ) : ℝ)) *
                dyadicPrimeConstant ^ 2 by ring]
          gcongr
      _ ≤ 16 * dyadicPrimeConstant ^ 2 * (n : ℝ) / (L : ℝ) ^ 2 := by
          have hdenPos : (0 : ℝ) <
              (((e.1 + 1 : ℕ) : ℝ) * (e.2 + 1 : ℕ)) :=
            mul_pos hiDenPos hjDenPos
          have hscaled := mul_le_mul_of_nonneg_left hden
            (mul_nonneg (by positivity : (0 : ℝ) ≤ n) hC)
          field_simp
          nlinarith [hscaled]
  calc
    (∑ e ∈ smoothCentralHighIndices n s, smoothDyadicTerm n s e)
      ≤ ∑ _e ∈ smoothCentralHighIndices n s,
          (16 * dyadicPrimeConstant ^ 2 * (n : ℝ) / (L : ℝ) ^ 2) :=
        Finset.sum_le_sum hone
    _ = ((smoothCentralHighIndices n s).card : ℝ) *
        (16 * dyadicPrimeConstant ^ 2 * (n : ℝ) / (L : ℝ) ^ 2) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by
      dsimp [L]
      gcongr
      exact_mod_cast smoothCentralHighIndices_card_le n s

/-- All three regions combined into one explicit exceptional prime-pair
majorant. -/
theorem smoothRelevantDyadicSum_le (n s : ℕ) (hL : 0 < Nat.log2 n)
    (hprime : ∀ i ∈ smoothPrimeIndexRange n s,
      ((dyadicPrimes i).card : ℝ) ≤
        dyadicPrimeConstant * ((2 ^ i : ℕ) : ℝ) / (i + 1)) :
    (∑ e ∈ smoothPrimeIndexSquare n s, smoothDyadicTerm n s e) ≤
      (((Nat.log2 n + 1) ^ 2 : ℕ) : ℝ) *
          ((2 ^ (6 * s + Nat.log2 n / 4 + Nat.log2 n / 2) : ℕ) : ℝ) +
      (((Nat.log2 n + 1) ^ 2 : ℕ) : ℝ) *
          (16 * dyadicPrimeConstant ^ 2 *
            ((2 ^ Nat.log2 n : ℕ) : ℝ) /
              ((((Nat.log2 n : ℕ) : ℝ) ^ 2) *
                ((2 ^ (2 * s) : ℕ) : ℝ))) +
      (((8 * s + 1) ^ 2 : ℕ) : ℝ) *
          (16 * dyadicPrimeConstant ^ 2 * (n : ℝ) /
            ((Nat.log2 n : ℝ) ^ 2)) := by
  rw [smoothIndexSum_partition]
  gcongr
  · exact smoothPeripheralSum_le n s
  · exact smoothCentralLowSum_le n s hL hprime
  · exact smoothCentralHighSum_le n s hL hprime

/-- The explicit raw expression bounds every admissible smooth part whenever
the dyadic prime estimate is available on the relevant index interval. -/
theorem smoothPart_card_le_remainderRaw
    {A : Finset ℕ} {n : ℕ}
    (hroot : 0 < smoothFourthRoot n)
    (hAint : A ⊆ Finset.Icc 1 n) (hA : HasRepBound 3 A)
    (hprime : ∀ i ∈ smoothPrimeIndexRange n (smoothScale n),
      ((dyadicPrimes i).card : ℝ) ≤
        dyadicPrimeConstant * ((2 ^ i : ℕ) : ℝ) / (i + 1)) :
    ((smoothPart A n).card : ℝ) ≤ smoothRemainderRaw n := by
  let s := smoothScale n
  have hspos : 0 < s := by unfold s smoothScale; positivity
  have hz : 1 < 2 ^ s := Nat.one_lt_pow hspos.ne' (by omega)
  have hclass := smoothPart_card_le_threeLarge_add_exceptional
    (A := A) (n := n) (z := 2 ^ s) hz hAint
  have hthree := threeLargePart_card_le_dyadic A hA hAint
    (s := s)
  have hexception := smoothExceptionalForms_card_le_relevantSum n s
  have hL : 0 < Nat.log2 n := by
    have hrpow := smoothFourthRoot_pow_le_log2 n
    have hrpowpos : 0 < (smoothFourthRoot n) ^ 4 :=
      pow_pos hroot 4
    omega
  have hsum := smoothRelevantDyadicSum_le n s hL (by
    intro i hi
    exact hprime i hi)
  have hcastException : ((smoothExceptionalForms n (2 ^ s)).card : ℝ) ≤
      (∑ e ∈ smoothPrimeIndexSquare n s, smoothDyadicTerm n s e) +
        2 * (((2 ^ s) ^ 6 : ℕ) : ℝ) * (n.sqrt + 2 : ℕ) := by
    rw [show (∑ e ∈ smoothPrimeIndexSquare n s, smoothDyadicTerm n s e) =
        (((∑ e ∈ smoothPrimeIndexSquare n s,
          min ((2 ^ s) ^ 6) (n / 2 ^ (e.1 + e.2)) *
            (dyadicPrimes e.1).card * (dyadicPrimes e.2).card : ℕ)) : ℝ) by
      simp only [smoothDyadicTerm]
      push_cast
      rfl]
    push_cast
    exact_mod_cast hexception
  have hsmooth : ((smoothPart A n).card : ℝ) ≤
      ((threeLargePart A (2 ^ s)).card : ℝ) +
        ((smoothExceptionalForms n (2 ^ s)).card : ℝ) := by
    exact_mod_cast hclass
  have hthree' : ((threeLargePart A (2 ^ s)).card : ℝ) ≤
      smoothThreeRaw n := by
    simpa [smoothThreeRaw, s] using hthree
  have hsum' : (∑ e ∈ smoothPrimeIndexSquare n s,
      smoothDyadicTerm n s e) ≤
      smoothPeripheralRaw n + smoothCentralLowRaw n +
        smoothCentralHighRaw n := by
    simpa [smoothPeripheralRaw, smoothCentralLowRaw,
      smoothCentralHighRaw, s] using hsum
  have hdeg : 2 * (((2 ^ s) ^ 6 : ℕ) : ℝ) * (n.sqrt + 2 : ℕ) =
      smoothDegenerateRaw n := by
    simp [smoothDegenerateRaw, s]
  calc
    ((smoothPart A n).card : ℝ) ≤
        ((threeLargePart A (2 ^ s)).card : ℝ) +
          ((smoothExceptionalForms n (2 ^ s)).card : ℝ) := hsmooth
    _ ≤ smoothThreeRaw n +
        ((∑ e ∈ smoothPrimeIndexSquare n s, smoothDyadicTerm n s e) +
          smoothDegenerateRaw n) := by
      rw [← hdeg]
      exact add_le_add hthree' hcastException
    _ ≤ smoothThreeRaw n +
        ((smoothPeripheralRaw n + smoothCentralLowRaw n +
          smoothCentralHighRaw n) + smoothDegenerateRaw n) := by
      gcongr
    _ = smoothRemainderRaw n := by
      unfold smoothRemainderRaw
      ring

/-- The eventual dyadic prime estimate holds simultaneously throughout every
relevant index interval. -/
theorem eventually_relevant_dyadicPrime_bound :
    ∀ᶠ n : ℕ in atTop,
      ∀ i ∈ smoothPrimeIndexRange n (smoothScale n),
        ((dyadicPrimes i).card : ℝ) ≤
          dyadicPrimeConstant * ((2 ^ i : ℕ) : ℝ) / (i + 1) := by
  rcases (eventually_atTop.1 eventually_dyadicPrimes_card_le) with ⟨K, hK⟩
  have hr := tendsto_smoothFourthRoot_atTop.eventually_ge_atTop K
  filter_upwards [hr] with n hn i hi
  have his : smoothScale n ≤ i := (Finset.mem_Icc.mp hi).1
  apply hK i
  have hrs : smoothFourthRoot n ≤ smoothScale n := by
    unfold smoothScale
    omega
  exact hn.trans (hrs.trans his)

/-- The first of the two gates in F-034: every admissible square-root-smooth
part is uniformly `o(n/log n)`. -/
theorem smoothRemainderGate_proved : SmoothRemainderGate := by
  intro ε hε
  have hmaj : ∀ᶠ n : ℕ in atTop, smoothRemainderMajorant n < ε :=
    tendsto_smoothRemainderMajorant_zero.eventually (gt_mem_nhds hε)
  have hroot := tendsto_smoothFourthRoot_atTop.eventually_ge_atTop 1
  have hprime := eventually_relevant_dyadicPrime_bound
  filter_upwards [eventually_gt_atTop 1, hroot, hprime, hmaj] with
    n hn hr hp hm A hAint hA
  have hraw := smoothPart_card_le_remainderRaw
    (A := A) (n := n) (by omega) hAint hA hp
  have hden : 0 < (n : ℝ) / Real.log (n : ℝ) :=
    div_pos (by positivity) (Real.log_pos (by exact_mod_cast hn))
  have hdiv : ((smoothPart A n).card : ℝ) /
      ((n : ℝ) / Real.log (n : ℝ)) ≤ smoothRemainderMajorant n := by
    unfold smoothRemainderMajorant
    exact div_le_div_of_nonneg_right hraw hden.le
  exact hdiv.trans_lt hm

end Erdos796
