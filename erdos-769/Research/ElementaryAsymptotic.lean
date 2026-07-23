import Research.DenseGcdTruncation
import Research.CutoffBridge
import Research.AsymptoticBound

/-!
# Decay of the elementary 49/100 Brauer threshold
-/

namespace Erdos769

/-- The elementary eventual-admissibility threshold. -/
def elementaryThreshold (n : ℕ) : ℕ :=
  n * 2 ^ n * (denseBase n) ^ n + 2

lemma denseBase_cross_bound {n : ℕ} (hn : 201 ≤ n) :
    200 * denseBase n ≤ 99 * n := by
  dsimp [denseBase]
  omega

lemma elementary_main_crossmul {n : ℕ} (hn : 201 ≤ n) :
    100 ^ n * (2 ^ n * (denseBase n) ^ n) ≤ 99 ^ n * n ^ n := by
  have hpow := Nat.pow_le_pow_left (denseBase_cross_bound hn) n
  calc
    100 ^ n * (2 ^ n * (denseBase n) ^ n) =
        (100 ^ n * 2 ^ n) * (denseBase n) ^ n := by ring
    _ = 200 ^ n * (denseBase n) ^ n := by
      rw [show 100 ^ n * 2 ^ n = 200 ^ n by rw [← mul_pow]; norm_num]
    _ = (200 * denseBase n) ^ n := by rw [mul_pow]
    _ ≤ (99 * n) ^ n := hpow
    _ = 99 ^ n * n ^ n := by rw [mul_pow]

lemma elementary_main_ratio_le {n : ℕ} (hn : 201 ≤ n) :
    (((n * 2 ^ n * (denseBase n) ^ n : ℕ) : ℝ) / (n ^ n : ℕ)) ≤
      (n : ℝ) * (99 / 100 : ℝ) ^ n := by
  have hnpos : (0 : ℝ) < (n ^ n : ℕ) := by positivity
  rw [div_le_iff₀ hnpos, div_pow]
  norm_num
  rw [show (n : ℝ) * (99 ^ n / 100 ^ n) * (n : ℝ) ^ n =
      ((n : ℝ) * 99 ^ n * (n : ℝ) ^ n) / 100 ^ n by ring]
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 100 ^ n)]
  have h := Nat.mul_le_mul_left n (elementary_main_crossmul hn)
  exact_mod_cast (by simpa [mul_assoc, mul_left_comm, mul_comm] using h)

noncomputable def elementaryRatio (n : ℕ) : ℝ :=
  (elementaryThreshold n : ℝ) / (n ^ n : ℕ)

lemma elementaryRatio_le_geometric {n : ℕ} (hn : 201 ≤ n) :
    elementaryRatio n ≤
      (n : ℝ) * (99 / 100 : ℝ) ^ n + 2 * (1 / 2 : ℝ) ^ n := by
  have h1 := elementary_main_ratio_le hn
  have h2 := two_ratio_le (show 2 ≤ n by omega)
  dsimp [elementaryRatio, elementaryThreshold]
  push_cast
  rw [add_div]
  norm_num only [Nat.cast_pow, Nat.cast_mul, Nat.cast_add] at h1 h2 ⊢
  nlinarith

/-- The elementary threshold is `o(n^n)`. -/
theorem elementaryRatio_tendsto_zero :
    Filter.Tendsto elementaryRatio Filter.atTop (nhds 0) := by
  apply squeeze_zero'
  · filter_upwards with n
    exact div_nonneg (by positivity) (by positivity)
  · filter_upwards [Filter.eventually_ge_atTop 201] with n hn
    exact elementaryRatio_le_geometric hn
  · have h99 : Filter.Tendsto
        (fun n : ℕ => (n : ℝ) * (99 / 100 : ℝ) ^ n)
        Filter.atTop (nhds 0) :=
      tendsto_self_mul_const_pow_of_lt_one (by norm_num) (by norm_num)
    have hhalf : Filter.Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n)
        Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    convert h99.add (hhalf.const_mul 2) using 1 <;> norm_num

 theorem eventually_mul_elementaryThreshold_lt
    (A B : ℕ) (hA : 0 < A) (hB : 0 < B) :
    ∀ᶠ n : ℕ in Filter.atTop,
      B * elementaryThreshold n < A * n ^ n := by
  have hratio : ∀ᶠ n : ℕ in Filter.atTop,
      elementaryRatio n < (A : ℝ) / (B : ℝ) :=
    (tendsto_order.1 elementaryRatio_tendsto_zero).2
      ((A : ℝ) / (B : ℝ)) (by positivity)
  filter_upwards [hratio, Filter.eventually_ge_atTop 1] with n hnratio hn
  have hden : (0 : ℝ) < (n ^ n : ℕ) := by positivity
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hcross := (div_lt_div_iff₀ hden hBR).1 hnratio
  have hreal :
      (B : ℝ) * (elementaryThreshold n : ℝ) < (A : ℝ) * (n ^ n : ℕ) := by
    simpa [elementaryRatio, mul_comm] using hcross
  exact_mod_cast hreal

/-- Eventual admissibility at the elementary threshold in odd dimensions
formally disproves the canonical lower bound. -/
theorem erdos769LowerBound_false_of_eventually_odd_elementaryThreshold
    (hadm : ∃ N₀ : ℕ, ∀ n, N₀ ≤ n → Odd n →
      ∀ k, elementaryThreshold n ≤ k → Admissible n k) :
    ¬ Erdos769LowerBound := by
  apply erdos769LowerBound_false_of_thresholds elementaryThreshold
  intro A B N hA hB
  obtain ⟨N₀, hadm⟩ := hadm
  obtain ⟨N₁, hsmall⟩ :=
    Filter.eventually_atTop.1 (eventually_mul_elementaryThreshold_lt A B hA hB)
  let L := max N (max N₀ N₁)
  let n := 2 * L + 1
  have hnL : L ≤ n := by dsimp [n]; omega
  have hnN : N ≤ n := le_trans (le_max_left N (max N₀ N₁)) hnL
  have hnN₀ : N₀ ≤ n :=
    le_trans (le_trans (le_max_left N₀ N₁) (le_max_right N (max N₀ N₁))) hnL
  have hnN₁ : N₁ ≤ n :=
    le_trans (le_trans (le_max_right N₀ N₁) (le_max_right N (max N₀ N₁))) hnL
  have hnodd : Odd n := by dsimp [n]; exact odd_two_mul_add_one L
  exact ⟨n, hnN, hsmall n hnN₁, hadm n hnN₀ hnodd⟩

end Erdos769
