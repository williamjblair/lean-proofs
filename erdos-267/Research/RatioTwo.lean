import Mathlib

/-!
# The elementary denominator method at the endpoint ratio two
-/

namespace Research

open Filter Topology
open Real goldenRatio
open scoped BigOperators

/-- A sharp upper bound for Fibonacci numbers, in a division-free form. -/
theorem goldenRatio_mul_fib_le_pow (n : ℕ) :
    φ * (Nat.fib n : ℝ) ≤ φ ^ n := by
  cases n with
  | zero => simp
  | succ k =>
      have h := Real.goldenRatio_mul_fib_succ_add_fib k
      have hf : (0 : ℝ) ≤ Nat.fib k := by positivity
      nlinarith

/-- A sharp lower bound for positive-index Fibonacci numbers, also written
without division. -/
theorem goldenRatio_pow_le_sq_mul_fib (n : ℕ) (hn : 0 < n) :
    φ ^ n ≤ φ ^ 2 * (Nat.fib n : ℝ) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have h := Real.goldenRatio_mul_fib_succ_add_fib k
  have hmono : (Nat.fib k : ℝ) ≤ Nat.fib (k + 1) := by
    exact_mod_cast Nat.fib_le_fib_succ
  calc
    φ ^ (k + 1) = φ * (Nat.fib (k + 1) : ℝ) + Nat.fib k := h.symm
    _ ≤ φ * (Nat.fib (k + 1) : ℝ) + Nat.fib (k + 1) := by gcongr
    _ = φ ^ 2 * (Nat.fib (k + 1) : ℝ) := by rw [Real.goldenRatio_sq]; ring

/-- Under doubling gaps, all indices before `n N`, together with one extra copy
of the first index, fit below `n N`. -/
theorem sum_range_add_first_le_of_doubling
    (n : ℕ → ℕ) (hdouble : ∀ k : ℕ, 2 * n k ≤ n (k + 1)) :
    ∀ N : ℕ, (∑ k ∈ Finset.range N, n k) + n 0 ≤ n N := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ]
      have hd := hdouble N
      omega

/-- Strict monotonicity gives the additive lower bound needed for every shifted
tail. -/
theorem add_index_le_of_strictMono (n : ℕ → ℕ) (hmono : StrictMono n)
    (N j : ℕ) : n N + j ≤ n (N + j) := by
  simpa [add_comm] using hmono.add_le_nat j N

/-- A reciprocal Fibonacci term is bounded by a geometric term in the inverse
golden ratio. -/
theorem inv_fib_le_golden_geometric (m : ℕ) (hm : 0 < m) :
    (Nat.fib m : ℝ)⁻¹ ≤ φ ^ 2 * (φ⁻¹) ^ m := by
  have hf : (0 : ℝ) < Nat.fib m := by exact_mod_cast Nat.fib_pos.mpr hm
  have hp : 0 < φ ^ m := pow_pos Real.goldenRatio_pos _
  have h := goldenRatio_pow_le_sq_mul_fib m hm
  rw [inv_pow]
  have hdiv : (1 : ℝ) / Nat.fib m ≤ φ ^ 2 / φ ^ m :=
    (div_le_div_iff₀ hf hp).2 (by simpa [mul_comm] using h)
  simpa [one_div, div_eq_mul_inv, mul_assoc] using hdiv

/-- Every shifted reciprocal-Fibonacci tail is summable and admits a uniform
geometric upper bound. -/
theorem summable_and_tsum_shift_le
    (n : ℕ → ℕ) (hpos : ∀ k : ℕ, 0 < n k) (hmono : StrictMono n) (N : ℕ) :
    Summable (fun j : ℕ => (Nat.fib (n (N + j)) : ℝ)⁻¹) ∧
      (∑' j : ℕ, (Nat.fib (n (N + j)) : ℝ)⁻¹) ≤
        (φ ^ 2 * (φ⁻¹) ^ (n N)) * φ ^ 2 := by
  let r : ℝ := φ⁻¹
  let C : ℝ := φ ^ 2 * r ^ (n N)
  have hr0 : 0 ≤ r := by dsimp [r]; exact (inv_pos.mpr Real.goldenRatio_pos).le
  have hr1 : r < 1 := by dsimp [r]; exact inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have habs : |r| < 1 := by simpa [abs_of_nonneg hr0] using hr1
  have hg : Summable (fun j : ℕ => C * r ^ j) := by
    have h := (summable_geometric_of_abs_lt_one habs).const_smul C
    simpa only [smul_eq_mul] using h
  have hle (j : ℕ) :
      (Nat.fib (n (N + j)) : ℝ)⁻¹ ≤ C * r ^ j := by
    have hidx : n N + j ≤ n (N + j) := add_index_le_of_strictMono n hmono N j
    have hfirst := inv_fib_le_golden_geometric (n (N + j)) (hpos (N + j))
    have hpow : r ^ (n (N + j)) ≤ r ^ (n N + j) :=
      (pow_right_anti₀ hr0 hr1.le) hidx
    calc
      (Nat.fib (n (N + j)) : ℝ)⁻¹ ≤ φ ^ 2 * r ^ (n (N + j)) := by
        simpa [r] using hfirst
      _ ≤ φ ^ 2 * r ^ (n N + j) := by gcongr
      _ = C * r ^ j := by simp [C, pow_add]; ring
  have hf : Summable (fun j : ℕ => (Nat.fib (n (N + j)) : ℝ)⁻¹) :=
    hg.of_nonneg_of_le (fun _ => inv_nonneg.mpr (by positivity)) hle
  refine ⟨hf, ?_⟩
  have hsumle := Summable.tsum_le_tsum hle hf hg
  have hgeom : (1 - r)⁻¹ = φ ^ 2 := by
    apply inv_eq_of_mul_eq_one_right
    dsimp [r]
    field_simp [Real.goldenRatio_ne_zero]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
  have hsumg : (∑' j : ℕ, C * r ^ j) = C * (1 - r)⁻¹ := by
    have h := (hasSum_geometric_of_abs_lt_one habs).const_smul C
    simpa only [smul_eq_mul] using h.tsum_eq
  rw [hsumg, hgeom] at hsumle
  simpa [C, r] using hsumle

/-- Product form of the upper golden-ratio bound for a finite collection of
Fibonacci numbers. -/
theorem prod_fib_le_golden_geometric (n : ℕ → ℕ) (N : ℕ) :
    (∏ k ∈ Finset.range N, (Nat.fib (n k) : ℝ)) ≤
      (φ⁻¹) ^ N * φ ^ (∑ k ∈ Finset.range N, n k) := by
  have hterm (k : ℕ) :
      (Nat.fib (n k) : ℝ) ≤ φ⁻¹ * φ ^ (n k) := by
    have h := goldenRatio_mul_fib_le_pow (n k)
    have hp := Real.goldenRatio_pos
    rw [← div_eq_inv_mul]
    exact (le_div_iff₀ hp).2 (by simpa [mul_comm] using h)
  calc
    (∏ k ∈ Finset.range N, (Nat.fib (n k) : ℝ)) ≤
        ∏ k ∈ Finset.range N, (φ⁻¹ * φ ^ (n k)) := by
          apply Finset.prod_le_prod
          · intro k hk
            positivity
          · intro k hk
            exact hterm k
    _ = (φ⁻¹) ^ N * φ ^ (∑ k ∈ Finset.range N, n k) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
        Finset.prod_pow_eq_pow_sum]

/-- Cancellation inequality between powers of the golden ratio and its
inverse. -/
theorem golden_pow_mul_inv_pow_le (a b c : ℕ) (h : a + c ≤ b) :
    φ ^ a * (φ⁻¹) ^ b ≤ (φ⁻¹) ^ c := by
  have hr0 : 0 ≤ φ⁻¹ := (inv_pos.mpr Real.goldenRatio_pos).le
  have hr1 : φ⁻¹ ≤ 1 := (inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio).le
  calc
    φ ^ a * (φ⁻¹) ^ b ≤ φ ^ a * (φ⁻¹) ^ (a + c) := by
      exact mul_le_mul_of_nonneg_left ((pow_right_anti₀ hr0 hr1) h) (by positivity)
    _ = (φ⁻¹) ^ c := by
      rw [pow_add]
      calc
        φ ^ a * ((φ⁻¹) ^ a * (φ⁻¹) ^ c) =
            (φ * φ⁻¹) ^ a * (φ⁻¹) ^ c := by rw [mul_pow]; ring
        _ = (φ⁻¹) ^ c := by
          have hmul : φ * φ⁻¹ = (1 : ℝ) := mul_inv_cancel₀ Real.goldenRatio_ne_zero
          rw [hmul, one_pow, one_mul]

/-- At ratio at least two, the common product denominator times every shifted
tail tends to zero.  This includes the endpoint omitted by the cruder exponent
count. -/
theorem tendsto_prod_fib_mul_tail_zero_of_doubling
    (n : ℕ → ℕ) (hpos : ∀ k : ℕ, 0 < n k)
    (hmono : StrictMono n) (hdouble : ∀ k : ℕ, 2 * n k ≤ n (k + 1)) :
    Tendsto
      (fun N : ℕ =>
        (∏ k ∈ Finset.range N, (Nat.fib (n k) : ℝ)) *
          (∑' j : ℕ, (Nat.fib (n (N + j)) : ℝ)⁻¹))
      atTop (𝓝 0) := by
  let r : ℝ := φ⁻¹
  have hr0 : 0 ≤ r := by dsimp [r]; exact (inv_pos.mpr Real.goldenRatio_pos).le
  have hr1 : r < 1 := by dsimp [r]; exact inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have hbound (N : ℕ) :
      (∏ k ∈ Finset.range N, (Nat.fib (n k) : ℝ)) *
          (∑' j : ℕ, (Nat.fib (n (N + j)) : ℝ)⁻¹) ≤
        φ ^ 4 * r ^ (N + n 0) := by
    have hprod := prod_fib_le_golden_geometric n N
    have htail := (summable_and_tsum_shift_le n hpos hmono N).2
    have hsumidx := sum_range_add_first_le_of_doubling n hdouble N
    have hcancel := golden_pow_mul_inv_pow_le
      (∑ k ∈ Finset.range N, n k) (n N) (n 0) hsumidx
    calc
      (∏ k ∈ Finset.range N, (Nat.fib (n k) : ℝ)) *
          (∑' j : ℕ, (Nat.fib (n (N + j)) : ℝ)⁻¹) ≤
          (r ^ N * φ ^ (∑ k ∈ Finset.range N, n k)) *
            ((φ ^ 2 * r ^ (n N)) * φ ^ 2) := by gcongr
      _ = φ ^ 4 * r ^ N *
          (φ ^ (∑ k ∈ Finset.range N, n k) * r ^ (n N)) := by
            dsimp [r] at hcancel ⊢
            ring
      _ ≤ φ ^ 4 * r ^ N * r ^ (n 0) := by
            exact mul_le_mul_of_nonneg_left (by simpa [r] using hcancel) (by positivity)
      _ = φ ^ 4 * r ^ (N + n 0) := by rw [pow_add]; ring
  have hnonneg (N : ℕ) :
      0 ≤ (∏ k ∈ Finset.range N, (Nat.fib (n k) : ℝ)) *
          (∑' j : ℕ, (Nat.fib (n (N + j)) : ℝ)⁻¹) := by
    positivity
  have hmajor : Tendsto (fun N : ℕ => φ ^ 4 * r ^ (N + n 0)) atTop (𝓝 0) := by
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
    simpa [pow_add, mul_assoc] using
      (tendsto_const_nhds.mul (hp.mul_const (r ^ (n 0))))
  exact squeeze_zero hnonneg hbound hmajor

end Research
