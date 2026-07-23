import Research.Nested

/-!
# Least-common-multiple denominator criterion
-/

namespace Research

open Filter Topology
open Real goldenRatio
open scoped BigOperators

/-- Least common multiple of the first `N` denominators. -/
def reciprocalLcm (d : ℕ → ℕ) (N : ℕ) : ℕ :=
  (Finset.range N).lcm d

/-- Numerator after scaling a partial reciprocal sum by its lcm. -/
def reciprocalLcmNumerator (d : ℕ → ℕ) (N : ℕ) : ℕ :=
  ∑ k ∈ Finset.range N, reciprocalLcm d N / d k

/-- A finite reciprocal sum is cleared by the lcm of its denominators. -/
theorem reciprocalLcm_mul_partialSum_eq
    (d : ℕ → ℕ) (hpos : ∀ k, 0 < d k) (N : ℕ) :
    (reciprocalLcm d N : ℝ) * (∑ k ∈ Finset.range N, (d k : ℝ)⁻¹) =
      (reciprocalLcmNumerator d N : ℝ) := by
  rw [Finset.mul_sum]
  simp only [reciprocalLcmNumerator, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hdvd : d k ∣ reciprocalLcm d N := Finset.dvd_lcm hk
  have hcast : (d k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hpos k))
  rw [Nat.cast_div hdvd hcast]
  simp [div_eq_mul_inv]

/-- Positivity of the finite lcm when all entries are positive. -/
theorem reciprocalLcm_pos (d : ℕ → ℕ) (hpos : ∀ k, 0 < d k) (N : ℕ) :
    0 < reciprocalLcm d N := by
  apply Nat.pos_of_ne_zero
  rw [ne_eq, reciprocalLcm, Finset.lcm_eq_zero_iff]
  push Not
  intro k hk
  exact Nat.ne_of_gt (hpos k)

/-- If `g` divides both a new denominator `b` and an existing common
multiple `B` of `a`, then adjoining `b` costs at most the quotient `b/g`. -/
theorem lcm_dvd_mul_div_of_common_dvd
    (a b B g : ℕ) (hg : 0 < g) (haB : a ∣ B) (hgB : g ∣ B) (hgb : g ∣ b) :
    Nat.lcm a b ∣ B * (b / g) := by
  apply Nat.lcm_dvd
  · exact haB.trans (dvd_mul_right B (b / g))
  · obtain ⟨x, rfl⟩ := hgB
    obtain ⟨y, rfl⟩ := hgb
    have hdiv : g * y / g = y := Nat.mul_div_cancel_left y hg
    rw [hdiv]
    exact ⟨x, by ring⟩

/-- The finite lcm is obtained recursively by adjoining the last entry. -/
theorem reciprocalLcm_succ (d : ℕ → ℕ) (N : ℕ) :
    reciprocalLcm d (N + 1) = Nat.lcm (d N) (reciprocalLcm d N) := by
  simp [reciprocalLcm, Finset.range_add_one, Finset.lcm_insert, lcm_eq_nat_lcm]

/-- Exact gcd-overlap bound for selected Fibonacci denominators.  Each `e k`
is an index divisor of `n k`; except at the first term, it must also divide one
earlier selected index. -/
theorem reciprocalLcm_fib_dvd_overlap_product
    (n e : ℕ → ℕ) (hepos : ∀ k, 0 < e k) (he0 : e 0 = 1)
    (hediv : ∀ k, e k ∣ n k)
    (heprev : ∀ k, 0 < k → ∃ i < k, e k ∣ n i) :
    ∀ N,
      reciprocalLcm (fun k => Nat.fib (n k)) N ∣
        ∏ k ∈ Finset.range N, Nat.fib (n k) / Nat.fib (e k) := by
  intro N
  induction N with
  | zero => simp [reciprocalLcm]
  | succ N ih =>
      rw [show N + 1 = Nat.succ N by rfl, Finset.prod_range_succ,
        reciprocalLcm_succ]
      have hgd : Nat.fib (e N) ∣ Nat.fib (n N) := Nat.fib_dvd _ _ (hediv N)
      have hgpos : 0 < Nat.fib (e N) := Nat.fib_pos.mpr (hepos N)
      have hgB : Nat.fib (e N) ∣
          ∏ k ∈ Finset.range N, Nat.fib (n k) / Nat.fib (e k) := by
        by_cases hN : N = 0
        · subst N
          simp [he0]
        · obtain ⟨i, hi, hei⟩ := heprev N (Nat.pos_of_ne_zero hN)
          have himem : i ∈ Finset.range N := Finset.mem_range.mpr hi
          have hgfib : Nat.fib (e N) ∣ Nat.fib (n i) := Nat.fib_dvd _ _ hei
          have hflcm : Nat.fib (n i) ∣ reciprocalLcm (fun k => Nat.fib (n k)) N :=
            Finset.dvd_lcm himem
          exact (hgfib.trans hflcm).trans ih
      have h := lcm_dvd_mul_div_of_common_dvd
        (reciprocalLcm (fun k => Nat.fib (n k)) N) (Nat.fib (n N))
        (∏ k ∈ Finset.range N, Nat.fib (n k) / Nat.fib (e k))
        (Nat.fib (e N)) hgpos ih hgB hgd
      simpa [Nat.lcm_comm] using h

/-- The cost of adjoining `F_n` after reusing the common factor `F_e` has a
sharp enough golden-ratio upper bound. -/
theorem fib_div_fib_le_overlap_geometric
    (n e : ℕ) (_hn : 0 < n) (he : 0 < e) (hed : e ∣ n) :
    ((Nat.fib n / Nat.fib e : ℕ) : ℝ) ≤
      φ * φ ^ n * (φ⁻¹) ^ e := by
  have hfed : Nat.fib e ∣ Nat.fib n := Nat.fib_dvd _ _ hed
  have hfe0 : (Nat.fib e : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.fib_pos.mpr he))
  rw [Nat.cast_div hfed hfe0, div_eq_mul_inv]
  have hfn : (Nat.fib n : ℝ) ≤ φ⁻¹ * φ ^ n := by
    have h := goldenRatio_mul_fib_le_pow n
    rw [← div_eq_inv_mul]
    exact (le_div_iff₀ Real.goldenRatio_pos).2 (by simpa [mul_comm] using h)
  have hfe := inv_fib_le_golden_geometric e he
  calc
    (Nat.fib n : ℝ) * (Nat.fib e : ℝ)⁻¹ ≤
        (φ⁻¹ * φ ^ n) * (φ ^ 2 * (φ⁻¹) ^ e) := by gcongr
    _ = φ * φ ^ n * (φ⁻¹) ^ e := by
      field_simp [Real.goldenRatio_ne_zero]

/-- A cumulative gcd-overlap budget which beats the next index forces the lcm
denominator times the tail to zero. -/
theorem tendsto_fib_lcm_tail_zero_of_overlap_budget
    (n e : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (hepos : ∀ k, 0 < e k) (he0 : e 0 = 1)
    (hediv : ∀ k, e k ∣ n k)
    (heprev : ∀ k, 0 < k → ∃ i < k, e k ∣ n i)
    (hbudget : ∀ N,
      (∑ k ∈ Finset.range N, n k) + 2 * N ≤
        n N + ∑ k ∈ Finset.range N, e k) :
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
        φ ^ N * φ ^ (∑ k ∈ Finset.range N, n k) *
          r ^ (∑ k ∈ Finset.range N, e k) := by
    have hdvd := reciprocalLcm_fib_dvd_overlap_product n e hepos he0 hediv heprev N
    have hquotpos (k : ℕ) : 0 < Nat.fib (n k) / Nat.fib (e k) := by
      apply Nat.div_pos
      · exact Nat.le_of_dvd (Nat.fib_pos.mpr (hpos k))
          (Nat.fib_dvd _ _ (hediv k))
      · exact Nat.fib_pos.mpr (hepos k)
    have hnat : reciprocalLcm (fun k => Nat.fib (n k)) N ≤
        ∏ k ∈ Finset.range N, Nat.fib (n k) / Nat.fib (e k) :=
      Nat.le_of_dvd (Finset.prod_pos fun k hk => hquotpos k) hdvd
    calc
      (reciprocalLcm (fun k => Nat.fib (n k)) N : ℝ) ≤
          (∏ k ∈ Finset.range N, Nat.fib (n k) / Nat.fib (e k) : ℕ) := by
            exact_mod_cast hnat
      _ = ∏ k ∈ Finset.range N,
          ((Nat.fib (n k) / Nat.fib (e k) : ℕ) : ℝ) := by push_cast; rfl
      _ ≤ ∏ k ∈ Finset.range N,
          (φ * φ ^ (n k) * r ^ (e k)) := by
            apply Finset.prod_le_prod
            · intro k hk
              positivity
            · intro k hk
              simpa [r] using fib_div_fib_le_overlap_geometric
                (n k) (e k) (hpos k) (hepos k) (hediv k)
      _ = φ ^ N * φ ^ (∑ k ∈ Finset.range N, n k) *
          r ^ (∑ k ∈ Finset.range N, e k) := by
            repeat' rw [Finset.prod_mul_distrib]
            rw [Finset.prod_const, Finset.card_range,
              Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum]
  have hbound (N : ℕ) :
      (reciprocalLcm (fun k => Nat.fib (n k)) N : ℝ) *
          (∑' j : ℕ, (Nat.fib (n (N + j)) : ℝ)⁻¹) ≤
        φ ^ 4 * r ^ N := by
    have htail := (summable_and_tsum_shift_le n hpos hmono N).2
    have hcancel := golden_pow_mul_inv_pow_le
      ((∑ k ∈ Finset.range N, n k) + N)
      (n N + ∑ k ∈ Finset.range N, e k) N (by
        have hb := hbudget N
        omega)
    calc
      (reciprocalLcm (fun k => Nat.fib (n k)) N : ℝ) *
          (∑' j : ℕ, (Nat.fib (n (N + j)) : ℝ)⁻¹) ≤
          (φ ^ N * φ ^ (∑ k ∈ Finset.range N, n k) *
            r ^ (∑ k ∈ Finset.range N, e k)) *
              ((φ ^ 2 * r ^ (n N)) * φ ^ 2) := by
                gcongr
                exact hlcm_bound N
      _ = φ ^ 4 *
          (φ ^ ((∑ k ∈ Finset.range N, n k) + N) *
            r ^ (n N + ∑ k ∈ Finset.range N, e k)) := by
              rw [pow_add, pow_add]
              ring
      _ ≤ φ ^ 4 * r ^ N := by
              exact mul_le_mul_of_nonneg_left (by simpa [r] using hcancel) (by positivity)
  have hnonneg (N : ℕ) :
      0 ≤ (reciprocalLcm (fun k => Nat.fib (n k)) N : ℝ) *
          (∑' j : ℕ, (Nat.fib (n (N + j)) : ℝ)⁻¹) := by positivity
  have hmajor : Tendsto (fun N : ℕ => φ ^ 4 * r ^ N) atTop (𝓝 0) := by
    have hc : Tendsto (fun _ : ℕ => φ ^ 4) atTop (𝓝 (φ ^ 4)) := tendsto_const_nhds
    simpa using hc.mul (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1)
  exact squeeze_zero hnonneg hbound hmajor

/-- The overlap-budget condition is therefore a concrete sufficient condition
for irrationality below ratio two. -/
theorem irrational_reciprocal_fib_of_overlap_budget
    (n e : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (hepos : ∀ k, 0 < e k) (he0 : e 0 = 1)
    (hediv : ∀ k, e k ∣ n k)
    (heprev : ∀ k, 0 < k → ∃ i < k, e k ∣ n i)
    (hbudget : ∀ N,
      (∑ k ∈ Finset.range N, n k) + 2 * N ≤
        n N + ∑ k ∈ Finset.range N, e k) :
    Irrational (∑' k : ℕ, (Nat.fib (n k) : ℝ)⁻¹) := by
  exact irrational_tsum_unitFractions_of_scaled_tail_zero
    (fun k => Nat.fib (n k))
    (reciprocalLcm (fun k => Nat.fib (n k)))
    (reciprocalLcmNumerator (fun k => Nat.fib (n k)))
    (fun k => Nat.fib_pos.mpr (hpos k))
    (reciprocalLcm_pos _ (fun k => Nat.fib_pos.mpr (hpos k)))
    (by
      have h := (summable_and_tsum_shift_le n hpos hmono 0).1
      simpa using h)
    (reciprocalLcm_mul_partialSum_eq _
      (fun k => Nat.fib_pos.mpr (hpos k)))
    (tendsto_fib_lcm_tail_zero_of_overlap_budget n e hpos hmono
      hepos he0 hediv heprev hbudget)

/-- Exact lcm form of Mahler's criterion.  This isolates the remaining
arithmetic task in Erdős 267: control the lcm of the selected Fibonacci
numbers. -/
theorem irrational_tsum_reciprocals_of_lcm_tail_zero
    (d : ℕ → ℕ) (hpos : ∀ k, 0 < d k)
    (hsum : Summable (fun k : ℕ => (d k : ℝ)⁻¹))
    (hlim : Tendsto
      (fun N : ℕ =>
        (reciprocalLcm d N : ℝ) * (∑' j : ℕ, (d (N + j) : ℝ)⁻¹))
      atTop (𝓝 0)) :
    Irrational (∑' k : ℕ, (d k : ℝ)⁻¹) := by
  exact irrational_tsum_unitFractions_of_scaled_tail_zero d
    (reciprocalLcm d) (reciprocalLcmNumerator d) hpos
    (reciprocalLcm_pos d hpos) hsum
    (reciprocalLcm_mul_partialSum_eq d hpos) hlim

end Research
