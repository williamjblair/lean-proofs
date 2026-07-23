import Research.Mahler

/-!
# Divisibility-chain subclasses
-/

namespace Research

open Filter Topology
open Real goldenRatio
open scoped BigOperators

/-- Mahler's criterion with an arbitrary integer scaling denominator for each
partial sum. -/
theorem irrational_tsum_unitFractions_of_scaled_tail_zero
    (d D A : ℕ → ℕ) (hpos : ∀ k : ℕ, 0 < d k)
    (hDpos : ∀ N : ℕ, 0 < D N)
    (hsum : Summable (fun k : ℕ => (d k : ℝ)⁻¹))
    (hscaled : ∀ N : ℕ,
      (D N : ℝ) * (∑ k ∈ Finset.range N, (d k : ℝ)⁻¹) = (A N : ℝ))
    (hlim : Tendsto
      (fun N : ℕ => (D N : ℝ) * (∑' j : ℕ, (d (N + j) : ℝ)⁻¹))
      atTop (𝓝 0)) :
    Irrational (∑' k : ℕ, (d k : ℝ)⁻¹) := by
  rw [irrational_iff_ne_rational]
  intro a b hb hrat
  let S : ℝ := ∑' k : ℕ, (d k : ℝ)⁻¹
  let P : ℕ → ℝ := fun N => ∑ k ∈ Finset.range N, (d k : ℝ)⁻¹
  let T : ℕ → ℝ := fun N => ∑' j : ℕ, (d (N + j) : ℝ)⁻¹
  have hsplit (N : ℕ) : P N + T N = S := by
    have h := hsum.sum_add_tsum_nat_add N
    simpa [P, T, S, add_comm] using h
  have hTpos (N : ℕ) : 0 < T N := by
    have ht : Summable (fun j : ℕ => (d (N + j) : ℝ)⁻¹) := by
      have := (summable_nat_add_iff N).2 hsum
      simpa [add_comm] using this
    exact ht.tsum_pos (fun _ => inv_nonneg.mpr (by positivity)) 0
      (inv_pos.mpr (by exact_mod_cast hpos N))
  have hDP (N : ℕ) : (D N : ℝ) * P N = (A N : ℝ) := by
    simpa [P] using hscaled N
  have hlower (N : ℕ) : (1 : ℝ) ≤ |(b : ℝ)| * ((D N : ℝ) * T N) := by
    let z : ℤ := a * (D N : ℤ) - b * (A N : ℤ)
    have hinter : (b : ℝ) * (D N : ℝ) * T N = (z : ℝ) := by
      have hT : T N = S - P N := by linarith [hsplit N]
      rw [hT]
      change (b : ℝ) * (D N : ℝ) * (S - P N) = (z : ℝ)
      have hrat' : S = (a : ℝ) / (b : ℝ) := by simpa [S] using hrat
      rw [hrat']
      calc
        (b : ℝ) * (D N : ℝ) * ((a : ℝ) / (b : ℝ) - P N) =
            (a : ℝ) * (D N : ℝ) - (b : ℝ) * ((D N : ℝ) * P N) := by
              field_simp [Int.cast_ne_zero.mpr hb]
        _ = (a : ℝ) * (D N : ℝ) - (b : ℝ) * (A N : ℝ) := by rw [hDP]
        _ = (z : ℝ) := by dsimp [z]; push_cast; ring
    have hz : z ≠ 0 := by
      intro hz0
      have hleft : (b : ℝ) * (D N : ℝ) * T N ≠ 0 := by
        exact mul_ne_zero (mul_ne_zero (Int.cast_ne_zero.mpr hb)
          (by exact_mod_cast (Nat.ne_of_gt (hDpos N)))) (ne_of_gt (hTpos N))
      apply hleft
      rw [hinter, hz0]
      norm_num
    have hzlower : (1 : ℝ) ≤ |(z : ℝ)| := by
      exact_mod_cast Int.one_le_abs hz
    have habs : |(z : ℝ)| = |(b : ℝ)| * ((D N : ℝ) * T N) := by
      have hDabs : |(D N : ℝ)| = (D N : ℝ) :=
        abs_of_pos (by exact_mod_cast hDpos N)
      have hTabs : |T N| = T N := abs_of_pos (hTpos N)
      rw [← hinter, abs_mul, abs_mul, hDabs, hTabs]
      ring
    rwa [habs] at hzlower
  have hlim' : Tendsto (fun N : ℕ => |(b : ℝ)| * ((D N : ℝ) * T N))
      atTop (𝓝 0) := by
    have hc : Tendsto (fun _ : ℕ => |(b : ℝ)|) atTop (𝓝 |(b : ℝ)|) :=
      tendsto_const_nhds
    have h := hc.mul hlim
    simpa [T, mul_assoc] using h
  have hfalse : (1 : ℝ) ≤ 0 := ge_of_tendsto' hlim' hlower
  norm_num at hfalse

/-- A simple endpoint denominator for a nested divisibility chain. -/
def nestedDenom (d : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | N + 1 => d N

/-- Corresponding scaled numerator. -/
def nestedNumerator (d : ℕ → ℕ) (N : ℕ) : ℕ :=
  ∑ k ∈ Finset.range N, nestedDenom d N / d k

/-- Divisibility propagates along a chain. -/
theorem dvd_of_dvd_succ_chain (d : ℕ → ℕ) (hchain : ∀ k, d k ∣ d (k + 1))
    {i j : ℕ} (hij : i ≤ j) : d i ∣ d j := by
  induction j, hij using Nat.le_induction with
  | base => exact dvd_refl _
  | succ j hij ih => exact ih.trans (hchain j)

/-- Every denominator occurring before `N` divides the nested endpoint
denominator. -/
theorem dvd_nestedDenom (d : ℕ → ℕ) (hchain : ∀ k, d k ∣ d (k + 1))
    {k N : ℕ} (hk : k ∈ Finset.range N) : d k ∣ nestedDenom d N := by
  have hklt : k < N := Finset.mem_range.mp hk
  cases N with
  | zero => simp at hklt
  | succ M =>
      dsimp [nestedDenom]
      exact dvd_of_dvd_succ_chain d hchain (Nat.le_of_lt_succ hklt)

/-- The nested endpoint clears every finite reciprocal sum. -/
theorem nestedDenom_mul_partialSum_eq
    (d : ℕ → ℕ) (hpos : ∀ k, 0 < d k) (hchain : ∀ k, d k ∣ d (k + 1))
    (N : ℕ) :
    (nestedDenom d N : ℝ) * (∑ k ∈ Finset.range N, (d k : ℝ)⁻¹) =
      (nestedNumerator d N : ℝ) := by
  rw [Finset.mul_sum]
  simp only [nestedNumerator, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hdvd := dvd_nestedDenom d hchain hk
  have hcast : (d k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hpos k))
  rw [Nat.cast_div hdvd hcast]
  simp [div_eq_mul_inv]

/-- If successive index gaps dominate the step number, the single nested
endpoint denominator times the tail tends to zero. -/
theorem tendsto_nested_fib_denom_mul_tail_zero
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (hgap : ∀ k, n k + k ≤ n (k + 1)) :
    Tendsto
      (fun N : ℕ =>
        (nestedDenom (fun k => Nat.fib (n k)) N : ℝ) *
          (∑' j : ℕ, (Nat.fib (n (N + j)) : ℝ)⁻¹))
      atTop (𝓝 0) := by
  let r : ℝ := φ⁻¹
  have hr0 : 0 ≤ r := by dsimp [r]; exact (inv_pos.mpr Real.goldenRatio_pos).le
  have hr1 : r < 1 := by dsimp [r]; exact inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have hrpow (m : ℕ) : r ^ m ≤ 1 := by
    simpa using (pow_le_one₀ hr0 hr1.le)
  have hbound (N : ℕ) :
      (nestedDenom (fun k => Nat.fib (n k)) N : ℝ) *
          (∑' j : ℕ, (Nat.fib (n (N + j)) : ℝ)⁻¹) ≤ φ ^ 4 * r ^ N := by
    have htail := (summable_and_tsum_shift_le n hpos hmono N).2
    cases N with
    | zero =>
        rw [nestedDenom]
        norm_num only [Nat.cast_one]
        calc
          (1 : ℝ) * (∑' j : ℕ, (Nat.fib (n (0 + j)) : ℝ)⁻¹) ≤
              (φ ^ 2 * r ^ (n 0)) * φ ^ 2 := by simpa [r] using htail
          _ = φ ^ 4 * r ^ (n 0) := by ring
          _ ≤ φ ^ 4 * 1 := mul_le_mul_of_nonneg_left (hrpow (n 0)) (by positivity)
          _ = φ ^ 4 * r ^ 0 := by simp
    | succ M =>
        have hfib : (Nat.fib (n M) : ℝ) ≤ r * φ ^ (n M) := by
          have h := goldenRatio_mul_fib_le_pow (n M)
          dsimp [r]
          rw [← div_eq_inv_mul]
          exact (le_div_iff₀ Real.goldenRatio_pos).2 (by simpa [mul_comm] using h)
        have hcancel := golden_pow_mul_inv_pow_le (n M) (n (M + 1)) M (hgap M)
        dsimp [nestedDenom]
        calc
          (Nat.fib (n M) : ℝ) *
              (∑' j : ℕ, (Nat.fib (n (M + 1 + j)) : ℝ)⁻¹) ≤
              (r * φ ^ (n M)) * ((φ ^ 2 * r ^ (n (M + 1))) * φ ^ 2) := by
                gcongr
          _ = φ ^ 4 * r * (φ ^ (n M) * r ^ (n (M + 1))) := by ring
          _ ≤ φ ^ 4 * r * r ^ M := by
                exact mul_le_mul_of_nonneg_left (by simpa [r] using hcancel) (by positivity)
          _ = φ ^ 4 * r ^ (M + 1) := by rw [pow_succ]; ring
  have hnonneg (N : ℕ) :
      0 ≤ (nestedDenom (fun k => Nat.fib (n k)) N : ℝ) *
          (∑' j : ℕ, (Nat.fib (n (N + j)) : ℝ)⁻¹) := by positivity
  have hmajor : Tendsto (fun N : ℕ => φ ^ 4 * r ^ N) atTop (𝓝 0) := by
    have hc : Tendsto (fun _ : ℕ => φ ^ 4) atTop (𝓝 (φ ^ 4)) := tendsto_const_nhds
    simpa using hc.mul (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1)
  exact squeeze_zero hnonneg hbound hmajor

/-- A uniform real ratio gap gives the expected geometric lower bound on the
indices. -/
theorem index_geometric_lower_of_ratio
    (n : ℕ → ℕ) (c : ℝ) (hc : 1 < c)
    (hratio : ∀ k, c * (n k : ℝ) ≤ n (k + 1)) :
    ∀ k, (n 0 : ℝ) * c ^ k ≤ n k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        (n 0 : ℝ) * c ^ (k + 1) = c * ((n 0 : ℝ) * c ^ k) := by rw [pow_succ]; ring
        _ ≤ c * (n k : ℝ) := mul_le_mul_of_nonneg_left ih (le_of_lt (lt_trans zero_lt_one hc))
        _ ≤ n (k + 1) := hratio k

/-- After deleting finitely many terms, a uniform ratio gap forces the additive
gap to dominate the new term number. -/
theorem exists_shift_index_gap_of_ratio
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (c : ℝ) (hc : 1 < c)
    (hratio : ∀ k, c * (n k : ℝ) ≤ n (k + 1)) :
    ∃ K : ℕ, ∀ k : ℕ, n (K + k) + k ≤ n (K + k + 1) := by
  have hdecay := tendsto_pow_const_div_const_pow_of_one_lt 1 hc
  have heps : 0 < c - 1 := sub_pos.mpr hc
  have hev : ∀ᶠ q : ℕ in atTop, (q : ℝ) ^ 1 / c ^ q < c - 1 :=
    (tendsto_order.1 hdecay).2 _ heps
  rcases (eventually_atTop.1 hev) with ⟨K, hK⟩
  refine ⟨K, fun k => ?_⟩
  let q := K + k
  have hqK : K ≤ q := by dsimp [q]; omega
  have hsmall := hK q hqK
  simp only [pow_one] at hsmall
  have hcq : 0 < c ^ q := pow_pos (lt_trans zero_lt_one hc) _
  have hqexp : (q : ℝ) < (c - 1) * c ^ q := by
    exact (div_lt_iff₀ hcq).mp hsmall
  have hgeom := index_geometric_lower_of_ratio n c hc hratio q
  have hn0 : (1 : ℝ) ≤ n 0 := by exact_mod_cast hpos 0
  have hcqn : c ^ q ≤ (n q : ℝ) := by
    calc
      c ^ q ≤ (n 0 : ℝ) * c ^ q := by nlinarith [pow_nonneg (le_of_lt (lt_trans zero_lt_one hc)) q]
      _ ≤ n q := hgeom
  have hq_n : (q : ℝ) < (c - 1) * (n q : ℝ) :=
    lt_of_lt_of_le hqexp (mul_le_mul_of_nonneg_left hcqn heps.le)
  have hstep := hratio q
  have hqstep : (n q : ℝ) + q < n (q + 1) := by
    nlinarith
  have hnat : n q + q ≤ n (q + 1) := by exact_mod_cast (le_of_lt hqstep)
  dsimp [q] at hnat ⊢
  omega

/-- Every positive Fibonacci reciprocal series whose indices form a divisibility
chain and whose additive gaps eventually dominate the term number is
irrational. -/
theorem irrational_reciprocal_fib_of_nested_indices
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (hdiv : ∀ k, n k ∣ n (k + 1))
    (hgap : ∀ k, n k + k ≤ n (k + 1)) :
    Irrational (∑' k : ℕ, (Nat.fib (n k) : ℝ)⁻¹) := by
  let d : ℕ → ℕ := fun k => Nat.fib (n k)
  have hdpos : ∀ k, 0 < d k := fun k => Nat.fib_pos.mpr (hpos k)
  have hdchain : ∀ k, d k ∣ d (k + 1) := fun k => Nat.fib_dvd _ _ (hdiv k)
  apply irrational_tsum_unitFractions_of_scaled_tail_zero d
    (nestedDenom d) (nestedNumerator d) hdpos
  · intro N
    cases N <;> simp [nestedDenom, hdpos]
  · have h := (summable_and_tsum_shift_le n hpos hmono 0).1
    simpa [d] using h
  · exact nestedDenom_mul_partialSum_eq d hdpos hdchain
  · simpa [d] using tendsto_nested_fib_denom_mul_tail_zero n hpos hmono hgap

/-- The full nested-divisibility subclass of Erdős Problem 267: every uniform
ratio constant strictly above one suffices. -/
theorem irrational_reciprocal_fib_of_nested_ratio
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (hdiv : ∀ k, n k ∣ n (k + 1))
    (c : ℝ) (hc : 1 < c) (hratio : ∀ k, c * (n k : ℝ) ≤ n (k + 1)) :
    Irrational (∑' k : ℕ, (Nat.fib (n k) : ℝ)⁻¹) := by
  obtain ⟨K, hK⟩ := exists_shift_index_gap_of_ratio n hpos c hc hratio
  let m : ℕ → ℕ := fun k => n (K + k)
  have hmpos : ∀ k, 0 < m k := fun k => hpos (K + k)
  have hmmono : StrictMono m := hmono.comp add_right_strictMono
  have hmdiv : ∀ k, m k ∣ m (k + 1) := by
    intro k
    dsimp [m]
    simpa [add_assoc] using hdiv (K + k)
  have hmgap : ∀ k, m k + k ≤ m (k + 1) := by
    intro k
    dsimp [m]
    simpa [add_assoc] using hK k
  have htail := irrational_reciprocal_fib_of_nested_indices m hmpos hmmono hmdiv hmgap
  let q : ℚ := ∑ k ∈ Finset.range K, (Nat.fib (n k) : ℚ)⁻¹
  have hqcast :
      (q : ℝ) = ∑ k ∈ Finset.range K, (Nat.fib (n k) : ℝ)⁻¹ := by
    simp [q]
  have hsum := (summable_and_tsum_shift_le n hpos hmono 0).1
  have hsplit := hsum.sum_add_tsum_nat_add K
  have heq :
      (∑' k : ℕ, (Nat.fib (n k) : ℝ)⁻¹) =
        (q : ℝ) + ∑' k : ℕ, (Nat.fib (m k) : ℝ)⁻¹ := by
    rw [hqcast]
    symm
    simpa [m, add_comm] using hsplit
  rw [heq]
  exact htail.ratCast_add q

end Research
