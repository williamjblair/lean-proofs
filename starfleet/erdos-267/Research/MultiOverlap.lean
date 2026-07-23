import Research.LcmState

/-!
# Simultaneous reuse of several coprime Fibonacci overlap factors
-/

namespace Research

open Filter Topology
open Real goldenRatio
open scoped BigOperators

/-- Product of the Fibonacci factors indexed by a finite overlap set. -/
def multiOverlapFactor (E : ℕ → Finset ℕ) (k : ℕ) : ℕ :=
  ∏ e ∈ E k, Nat.fib e

/-- General exact lcm bound when each new denominator reuses an arbitrary
common factor already present in the preceding lcm. -/
theorem reciprocalLcm_dvd_commonFactor_product
    (d g : ℕ → ℕ) (hgpos : ∀ k, 0 < g k)
    (hgd : ∀ k, g k ∣ d k)
    (hgprev : ∀ k, g k ∣ reciprocalLcm d k) :
    ∀ N, reciprocalLcm d N ∣ ∏ k ∈ Finset.range N, d k / g k := by
  intro N
  induction N with
  | zero => simp [reciprocalLcm]
  | succ N ih =>
      rw [show N + 1 = Nat.succ N by rfl, Finset.prod_range_succ,
        reciprocalLcm_succ]
      have hgB : g N ∣ ∏ k ∈ Finset.range N, d k / g k :=
        (hgprev N).trans ih
      have h := lcm_dvd_mul_div_of_common_dvd
        (reciprocalLcm d N) (d N)
        (∏ k ∈ Finset.range N, d k / g k) (g N)
        (hgpos N) ih hgB (hgd N)
      simpa [Nat.lcm_comm] using h

/-- A pairwise-coprime product of Fibonacci factors divides the selected
Fibonacci denominator. -/
theorem multiOverlapFactor_dvd_fib
    (n : ℕ → ℕ) (E : ℕ → Finset ℕ)
    (hpair : ∀ k,
      (↑(E k) : Set ℕ).Pairwise
        (Function.onFun IsCoprime fun e => Nat.fib e))
    (hediv : ∀ k e, e ∈ E k → e ∣ n k) (k : ℕ) :
    multiOverlapFactor E k ∣ Nat.fib (n k) := by
  apply Finset.prod_dvd_of_coprime (hpair k)
  intro e he
  exact Nat.fib_dvd _ _ (hediv k e he)

/-- If every overlap factor at a positive position divides some earlier
selected index, their coprime product is already in the preceding lcm. -/
theorem multiOverlapFactor_dvd_previous_lcm
    (n : ℕ → ℕ) (E : ℕ → Finset ℕ) (hE0 : E 0 = ∅)
    (hpair : ∀ k,
      (↑(E k) : Set ℕ).Pairwise
        (Function.onFun IsCoprime fun e => Nat.fib e))
    (heprev : ∀ k e, e ∈ E k → 0 < k → ∃ i < k, e ∣ n i) (k : ℕ) :
    multiOverlapFactor E k ∣ reciprocalLcm (fun i => Nat.fib (n i)) k := by
  by_cases hk : k = 0
  · subst k
    simp [multiOverlapFactor, hE0]
  · apply Finset.prod_dvd_of_coprime (hpair k)
    intro e he
    obtain ⟨i, hi, hd⟩ := heprev k e he (Nat.pos_of_ne_zero hk)
    exact (Nat.fib_dvd _ _ hd).trans (Finset.dvd_lcm (Finset.mem_range.mpr hi))

/-- Exact lcm bound obtained by simultaneously reusing all factors in each
coprime overlap set. -/
theorem reciprocalLcm_fib_dvd_multiOverlap_product
    (n : ℕ → ℕ) (E : ℕ → Finset ℕ)
    (hepos : ∀ k e, e ∈ E k → 0 < e) (hE0 : E 0 = ∅)
    (hpair : ∀ k,
      (↑(E k) : Set ℕ).Pairwise
        (Function.onFun IsCoprime fun e => Nat.fib e))
    (hediv : ∀ k e, e ∈ E k → e ∣ n k)
    (heprev : ∀ k e, e ∈ E k → 0 < k → ∃ i < k, e ∣ n i) :
    ∀ N, reciprocalLcm (fun k => Nat.fib (n k)) N ∣
      ∏ k ∈ Finset.range N, Nat.fib (n k) / multiOverlapFactor E k := by
  apply reciprocalLcm_dvd_commonFactor_product
  · intro k
    exact Finset.prod_pos fun e he => Nat.fib_pos.mpr (hepos k e he)
  · exact multiOverlapFactor_dvd_fib n E hpair hediv
  · exact multiOverlapFactor_dvd_previous_lcm n E hE0 hpair heprev

/-- Golden-ratio bound for the quotient after simultaneously reusing a finite
coprime family of Fibonacci factors. -/
theorem fib_div_multiOverlap_le_geometric
    (n : ℕ → ℕ) (E : ℕ → Finset ℕ)
    (_hpos : ∀ k, 0 < n k)
    (hepos : ∀ k e, e ∈ E k → 0 < e)
    (hpair : ∀ k,
      (↑(E k) : Set ℕ).Pairwise
        (Function.onFun IsCoprime fun e => Nat.fib e))
    (hediv : ∀ k e, e ∈ E k → e ∣ n k) (k : ℕ) :
    ((Nat.fib (n k) / multiOverlapFactor E k : ℕ) : ℝ) ≤
      φ⁻¹ * φ ^ (n k) *
        (φ ^ (2 * (E k).card) * (φ⁻¹) ^ (∑ e ∈ E k, e)) := by
  have hgd := multiOverlapFactor_dvd_fib n E hpair hediv k
  have hgpos : 0 < multiOverlapFactor E k :=
    Finset.prod_pos fun e he => Nat.fib_pos.mpr (hepos k e he)
  have hg0 : (multiOverlapFactor E k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hgpos)
  rw [Nat.cast_div hgd hg0, div_eq_mul_inv]
  have hfn : (Nat.fib (n k) : ℝ) ≤ φ⁻¹ * φ ^ (n k) := by
    have h := goldenRatio_mul_fib_le_pow (n k)
    rw [← div_eq_inv_mul]
    exact (le_div_iff₀ Real.goldenRatio_pos).2 (by simpa [mul_comm] using h)
  have hinv : (multiOverlapFactor E k : ℝ)⁻¹ ≤
      φ ^ (2 * (E k).card) * (φ⁻¹) ^ (∑ e ∈ E k, e) := by
    calc
      (multiOverlapFactor E k : ℝ)⁻¹ =
          ∏ e ∈ E k, (Nat.fib e : ℝ)⁻¹ := by
            rw [multiOverlapFactor]
            push_cast
            exact (Finset.prod_inv_distrib _).symm
      _ ≤ ∏ e ∈ E k, (φ ^ 2 * (φ⁻¹) ^ e) := by
            apply Finset.prod_le_prod
            · intro e he
              positivity
            · intro e he
              exact inv_fib_le_golden_geometric e (hepos k e he)
      _ = φ ^ (2 * (E k).card) * (φ⁻¹) ^ (∑ e ∈ E k, e) := by
            rw [Finset.prod_mul_distrib, Finset.prod_const,
              Finset.prod_pow_eq_pow_sum]
            congr 1
            rw [← pow_mul]
  gcongr

/-- A cumulative budget using several coprime reusable factors at each step
forces exact-lcm tail decay. -/
theorem tendsto_fib_lcm_tail_zero_of_multiOverlap_budget
    (n : ℕ → ℕ) (E : ℕ → Finset ℕ)
    (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (hepos : ∀ k e, e ∈ E k → 0 < e) (hE0 : E 0 = ∅)
    (hpair : ∀ k,
      (↑(E k) : Set ℕ).Pairwise
        (Function.onFun IsCoprime fun e => Nat.fib e))
    (hediv : ∀ k e, e ∈ E k → e ∣ n k)
    (heprev : ∀ k e, e ∈ E k → 0 < k → ∃ i < k, e ∣ n i)
    (hbudget : ∀ N,
      (∑ k ∈ Finset.range N, n k) +
          (∑ k ∈ Finset.range N, 2 * (E k).card) ≤
        n N + ∑ k ∈ Finset.range N, (∑ e ∈ E k, e)) :
    Tendsto
      (fun N : ℕ =>
        (reciprocalLcm (fun k => Nat.fib (n k)) N : ℝ) *
          (∑' j : ℕ, (Nat.fib (n (N + j)) : ℝ)⁻¹))
      atTop (𝓝 0) := by
  let r : ℝ := φ⁻¹
  have hr0 : 0 ≤ r := by dsimp [r]; exact (inv_pos.mpr Real.goldenRatio_pos).le
  have hr1 : r < 1 := by dsimp [r]; exact inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have hlcm_bound (N : ℕ) :
      (reciprocalLcm (fun k => Nat.fib (n k)) N : ℝ) ≤
        r ^ N * φ ^ (∑ k ∈ Finset.range N, n k) *
          (φ ^ (∑ k ∈ Finset.range N, 2 * (E k).card) *
            r ^ (∑ k ∈ Finset.range N, (∑ e ∈ E k, e))) := by
    have hdvd := reciprocalLcm_fib_dvd_multiOverlap_product n E hepos hE0
      hpair hediv heprev N
    have hquotpos (k : ℕ) :
        0 < Nat.fib (n k) / multiOverlapFactor E k := by
      apply Nat.div_pos
      · exact Nat.le_of_dvd (Nat.fib_pos.mpr (hpos k))
          (multiOverlapFactor_dvd_fib n E hpair hediv k)
      · exact Finset.prod_pos fun e he => Nat.fib_pos.mpr (hepos k e he)
    have hnat : reciprocalLcm (fun k => Nat.fib (n k)) N ≤
        ∏ k ∈ Finset.range N, Nat.fib (n k) / multiOverlapFactor E k :=
      Nat.le_of_dvd (Finset.prod_pos fun k hk => hquotpos k) hdvd
    calc
      (reciprocalLcm (fun k => Nat.fib (n k)) N : ℝ) ≤
          (∏ k ∈ Finset.range N,
            Nat.fib (n k) / multiOverlapFactor E k : ℕ) := by exact_mod_cast hnat
      _ = ∏ k ∈ Finset.range N,
          ((Nat.fib (n k) / multiOverlapFactor E k : ℕ) : ℝ) := by push_cast; rfl
      _ ≤ ∏ k ∈ Finset.range N,
          (r * φ ^ (n k) *
            (φ ^ (2 * (E k).card) * r ^ (∑ e ∈ E k, e))) := by
              apply Finset.prod_le_prod
              · intro k hk
                positivity
              · intro k hk
                simpa [r] using fib_div_multiOverlap_le_geometric
                  n E hpos hepos hpair hediv k
      _ = r ^ N * φ ^ (∑ k ∈ Finset.range N, n k) *
          (φ ^ (∑ k ∈ Finset.range N, 2 * (E k).card) *
            r ^ (∑ k ∈ Finset.range N, (∑ e ∈ E k, e))) := by
              repeat' rw [Finset.prod_mul_distrib]
              rw [Finset.prod_const, Finset.card_range,
                Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum,
                Finset.prod_pow_eq_pow_sum]
  have hbound (N : ℕ) :
      (reciprocalLcm (fun k => Nat.fib (n k)) N : ℝ) *
          (∑' j : ℕ, (Nat.fib (n (N + j)) : ℝ)⁻¹) ≤
        φ ^ 4 * r ^ N := by
    have htail := (summable_and_tsum_shift_le n hpos hmono N).2
    have hcancel := golden_pow_mul_inv_pow_le
      ((∑ k ∈ Finset.range N, n k) +
        ∑ k ∈ Finset.range N, 2 * (E k).card)
      (n N + ∑ k ∈ Finset.range N, (∑ e ∈ E k, e)) 0 (by
        simpa using hbudget N)
    calc
      (reciprocalLcm (fun k => Nat.fib (n k)) N : ℝ) *
          (∑' j : ℕ, (Nat.fib (n (N + j)) : ℝ)⁻¹) ≤
          (r ^ N * φ ^ (∑ k ∈ Finset.range N, n k) *
            (φ ^ (∑ k ∈ Finset.range N, 2 * (E k).card) *
              r ^ (∑ k ∈ Finset.range N, (∑ e ∈ E k, e)))) *
            ((φ ^ 2 * r ^ (n N)) * φ ^ 2) := by
              gcongr
              exact hlcm_bound N
      _ = φ ^ 4 * r ^ N *
          (φ ^ ((∑ k ∈ Finset.range N, n k) +
            ∑ k ∈ Finset.range N, 2 * (E k).card) *
            r ^ (n N + ∑ k ∈ Finset.range N, (∑ e ∈ E k, e))) := by
              rw [pow_add, pow_add]
              ring
      _ ≤ φ ^ 4 * r ^ N * r ^ 0 := by
              exact mul_le_mul_of_nonneg_left
                (by simpa [r] using hcancel) (by positivity)
      _ = φ ^ 4 * r ^ N := by simp
  have hnonneg (N : ℕ) :
      0 ≤ (reciprocalLcm (fun k => Nat.fib (n k)) N : ℝ) *
          (∑' j : ℕ, (Nat.fib (n (N + j)) : ℝ)⁻¹) := by positivity
  have hmajor : Tendsto (fun N : ℕ => φ ^ 4 * r ^ N) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1)
  exact squeeze_zero hnonneg hbound hmajor

/-- Multi-factor overlap budget implies irrationality. -/
theorem irrational_reciprocal_fib_of_multiOverlap_budget
    (n : ℕ → ℕ) (E : ℕ → Finset ℕ)
    (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (hepos : ∀ k e, e ∈ E k → 0 < e) (hE0 : E 0 = ∅)
    (hpair : ∀ k,
      (↑(E k) : Set ℕ).Pairwise
        (Function.onFun IsCoprime fun e => Nat.fib e))
    (hediv : ∀ k e, e ∈ E k → e ∣ n k)
    (heprev : ∀ k e, e ∈ E k → 0 < k → ∃ i < k, e ∣ n i)
    (hbudget : ∀ N,
      (∑ k ∈ Finset.range N, n k) +
          (∑ k ∈ Finset.range N, 2 * (E k).card) ≤
        n N + ∑ k ∈ Finset.range N, (∑ e ∈ E k, e)) :
    Irrational (∑' k : ℕ, (Nat.fib (n k) : ℝ)⁻¹) := by
  apply irrational_tsum_reciprocals_of_lcm_tail_zero
    (d := fun k => Nat.fib (n k))
  · exact fun k => Nat.fib_pos.mpr (hpos k)
  · simpa using (summable_and_tsum_shift_le n hpos hmono 0).1
  · exact tendsto_fib_lcm_tail_zero_of_multiOverlap_budget n E hpos hmono
      hepos hE0 hpair hediv heprev hbudget

end Research
