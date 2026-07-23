import Mathlib

/-!
# Elementary decay of the proposed BCZ cutoff bound
-/

namespace Erdos769

/-- The elementary estimate `2^n * 2^(floor(n/2)) ≤ 3^n`. -/
theorem two_pow_mul_two_pow_half_le_three_pow (n : ℕ) :
    2 ^ n * 2 ^ (n / 2) ≤ 3 ^ n := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num
  | one => norm_num
  | more n hn _ =>
      have hdiv : (n + 2) / 2 = n / 2 + 1 := by omega
      calc
        2 ^ (n + 2) * 2 ^ ((n + 2) / 2) =
            8 * (2 ^ n * 2 ^ (n / 2)) := by
              rw [hdiv, pow_add, pow_succ]
              ring
        _ ≤ 8 * 3 ^ n := Nat.mul_le_mul_left 8 hn
        _ ≤ 9 * 3 ^ n := by omega
        _ = 3 ^ (n + 2) := by rw [pow_add]; ring

/-- For `n≥12`, the base-six term is at most a `2^{-n}` fraction of `n^n`. -/
theorem six_pow_decay_crossmul {n : ℕ} (hn : 12 ≤ n) :
    2 ^ n * 6 ^ n ≤ n ^ n := by
  rw [← mul_pow]
  exact Nat.pow_le_pow_left hn n

/-- The floor appearing in the odd-dimensional truncation is eventually at
most three fifths of the dimension. -/
theorem five_mul_half_add_three_le {n : ℕ} (hn : 15 ≤ n) :
    5 * ((n + 3) / 2) ≤ 3 * n := by
  omega

/-- Cross-multiplied form of the estimate
`2^(n/2) * ((n+3)/2)^n / n^n ≤ (9/10)^n`. -/
theorem middle_term_decay_crossmul {n : ℕ} (hn : 15 ≤ n) :
    10 ^ n * (2 ^ (n / 2) * ((n + 3) / 2) ^ n) ≤
      9 ^ n * n ^ n := by
  have hM := Nat.pow_le_pow_left (five_mul_half_add_three_le hn) n
  rw [mul_pow, mul_pow] at hM
  have h2 := two_pow_mul_two_pow_half_le_three_pow n
  calc
    10 ^ n * (2 ^ (n / 2) * ((n + 3) / 2) ^ n) =
        (2 ^ n * 2 ^ (n / 2)) *
          (5 ^ n * ((n + 3) / 2) ^ n) := by
            rw [show 10 ^ n = 2 ^ n * 5 ^ n by rw [← mul_pow]; norm_num]
            ring
    _ ≤ 3 ^ n * (3 ^ n * n ^ n) := Nat.mul_le_mul h2 hM
    _ = 9 ^ n * n ^ n := by
      rw [show 9 ^ n = 3 ^ n * 3 ^ n by rw [← mul_pow]; norm_num]
      ring

/-- A convenient integral upper threshold arising from the BCZ/gcd-chain
argument. -/
def bczThreshold (n : ℕ) : ℕ :=
  6 ^ n + n * 2 ^ (n / 2) * ((n + 3) / 2) ^ n + 2

lemma six_pow_ratio_le {n : ℕ} (hn : 12 ≤ n) :
    (6 ^ n : ℝ) / (n ^ n : ℕ) ≤ (1 / 2 : ℝ) ^ n := by
  have hnpos : (0 : ℝ) < (n ^ n : ℕ) := by positivity
  rw [div_le_iff₀ hnpos]
  rw [div_pow]
  norm_num
  rw [show (2 ^ n : ℝ)⁻¹ * (n : ℝ) ^ n = (n : ℝ) ^ n / 2 ^ n by
    field_simp]
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ n)]
  exact_mod_cast (by simpa [mul_comm] using six_pow_decay_crossmul hn)

lemma middle_term_ratio_le {n : ℕ} (hn : 15 ≤ n) :
    ((n * 2 ^ (n / 2) * ((n + 3) / 2) ^ n : ℕ) : ℝ) /
        (n ^ n : ℕ) ≤ (n : ℝ) * (9 / 10 : ℝ) ^ n := by
  have hnpos : (0 : ℝ) < (n ^ n : ℕ) := by positivity
  rw [div_le_iff₀ hnpos]
  rw [div_pow]
  norm_num
  rw [show (n : ℝ) * (9 ^ n / 10 ^ n) * (n : ℝ) ^ n =
      ((n : ℝ) * 9 ^ n * (n : ℝ) ^ n) / 10 ^ n by ring]
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 10 ^ n)]
  norm_num only [Nat.cast_mul, Nat.cast_pow]
  exact_mod_cast (by
    have h := Nat.mul_le_mul_left n (middle_term_decay_crossmul hn)
    simpa [mul_assoc, mul_left_comm, mul_comm] using h)

lemma two_ratio_le {n : ℕ} (hn : 2 ≤ n) :
    (2 : ℝ) / (n ^ n : ℕ) ≤ 2 * (1 / 2 : ℝ) ^ n := by
  have hnpos : (0 : ℝ) < (n ^ n : ℕ) := by positivity
  rw [div_le_iff₀ hnpos]
  rw [div_pow]
  norm_num
  rw [show (2 : ℝ) * (2 ^ n : ℝ)⁻¹ * (n : ℝ) ^ n =
      (2 * (n : ℝ) ^ n) / 2 ^ n by field_simp]
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ n)]
  have hpow : 2 ^ n ≤ n ^ n := Nat.pow_le_pow_left hn n
  exact_mod_cast Nat.mul_le_mul_left 2 hpow

/-- The real ratio between the explicit threshold and `n^n`. -/
noncomputable def bczRatio (n : ℕ) : ℝ :=
  (bczThreshold n : ℝ) / (n ^ n : ℕ)

/-- An eventual elementary geometric upper bound for `bczRatio`. -/
theorem bczRatio_le_geometric {n : ℕ} (hn : 15 ≤ n) :
    bczRatio n ≤ 3 * (1 / 2 : ℝ) ^ n + (n : ℝ) * (9 / 10 : ℝ) ^ n := by
  have h1 := six_pow_ratio_le (show 12 ≤ n by omega)
  have h2 := middle_term_ratio_le hn
  have h3 := two_ratio_le (show 2 ≤ n by omega)
  dsimp [bczRatio, bczThreshold]
  push_cast
  rw [add_div, add_div]
  norm_num only [Nat.cast_pow, Nat.cast_mul, Nat.cast_add] at h1 h2 h3 ⊢
  nlinarith

/-- The explicit BCZ/gcd-chain threshold is `o(n^n)`. -/
theorem bczRatio_tendsto_zero :
    Filter.Tendsto bczRatio Filter.atTop (nhds 0) := by
  apply squeeze_zero'
  · filter_upwards with n
    exact div_nonneg (by positivity) (by positivity)
  · filter_upwards [Filter.eventually_ge_atTop 15] with n hn
    exact bczRatio_le_geometric hn
  · have hhalf : Filter.Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n)
        Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hnine : Filter.Tendsto (fun n : ℕ => (n : ℝ) * (9 / 10 : ℝ) ^ n)
        Filter.atTop (nhds 0) :=
      tendsto_self_mul_const_pow_of_lt_one (by norm_num) (by norm_num)
    convert (hhalf.const_mul 3).add hnine using 1 <;> norm_num

/-- Cross-multiplied natural-number form of `bczThreshold(n)/n^n → 0`. -/
theorem eventually_mul_bczThreshold_lt (A B : ℕ) (hA : 0 < A) (hB : 0 < B) :
    ∀ᶠ n : ℕ in Filter.atTop,
      B * bczThreshold n < A * n ^ n := by
  have hratio : ∀ᶠ n : ℕ in Filter.atTop,
      bczRatio n < (A : ℝ) / (B : ℝ) :=
    (tendsto_order.1 bczRatio_tendsto_zero).2 ((A : ℝ) / (B : ℝ)) (by positivity)
  filter_upwards [hratio, Filter.eventually_ge_atTop 1] with n hnratio hn
  have hden : (0 : ℝ) < (n ^ n : ℕ) := by positivity
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hcross := (div_lt_div_iff₀ hden hBR).1 hnratio
  have hreal :
      (B : ℝ) * (bczThreshold n : ℝ) < (A : ℝ) * (n ^ n : ℕ) := by
    simpa [bczRatio, mul_comm] using hcross
  exact_mod_cast hreal

end Erdos769
