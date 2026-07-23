import Research.Overlap

/-!
# Mahler's denominator argument along unbounded subsequences of cut points
-/

namespace Research

open Filter Topology
open Real goldenRatio
open scoped BigOperators

/-- Mahler's integer-denominator argument only needs small scaled tails along
an arbitrary sequence of cut points. -/
theorem irrational_tsum_unitFractions_of_scaled_tail_zero_at_cuts
    (d D A q : ℕ → ℕ) (hpos : ∀ k, 0 < d k)
    (hDpos : ∀ N, 0 < D N)
    (hsum : Summable (fun k : ℕ => (d k : ℝ)⁻¹))
    (hscaled : ∀ N,
      (D N : ℝ) * (∑ k ∈ Finset.range (q N), (d k : ℝ)⁻¹) = (A N : ℝ))
    (hlim : Tendsto
      (fun N : ℕ => (D N : ℝ) * (∑' j : ℕ, (d (q N + j) : ℝ)⁻¹))
      atTop (𝓝 0)) :
    Irrational (∑' k : ℕ, (d k : ℝ)⁻¹) := by
  rw [irrational_iff_ne_rational]
  intro a b hb hrat
  let S : ℝ := ∑' k : ℕ, (d k : ℝ)⁻¹
  let P : ℕ → ℝ := fun N => ∑ k ∈ Finset.range (q N), (d k : ℝ)⁻¹
  let T : ℕ → ℝ := fun N => ∑' j : ℕ, (d (q N + j) : ℝ)⁻¹
  have hsplit (N : ℕ) : P N + T N = S := by
    have h := hsum.sum_add_tsum_nat_add (q N)
    simpa [P, T, S, add_comm] using h
  have hTpos (N : ℕ) : 0 < T N := by
    have ht : Summable (fun j : ℕ => (d (q N + j) : ℝ)⁻¹) := by
      have := (summable_nat_add_iff (q N)).2 hsum
      simpa [add_comm] using this
    exact ht.tsum_pos (fun _ => inv_nonneg.mpr (by positivity)) 0
      (inv_pos.mpr (by exact_mod_cast hpos (q N)))
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

/-- Lcm form of the preceding arbitrary-cut criterion. -/
theorem irrational_tsum_reciprocals_of_lcm_tail_zero_at_cuts
    (d q : ℕ → ℕ) (hpos : ∀ k, 0 < d k)
    (hsum : Summable (fun k : ℕ => (d k : ℝ)⁻¹))
    (hlim : Tendsto
      (fun N : ℕ =>
        (reciprocalLcm d (q N) : ℝ) *
          (∑' j : ℕ, (d (q N + j) : ℝ)⁻¹))
      atTop (𝓝 0)) :
    Irrational (∑' k : ℕ, (d k : ℝ)⁻¹) := by
  exact irrational_tsum_unitFractions_of_scaled_tail_zero_at_cuts d
    (fun N => reciprocalLcm d (q N))
    (fun N => reciprocalLcmNumerator d (q N)) q hpos
    (fun N => reciprocalLcm_pos d hpos (q N)) hsum
    (fun N => reciprocalLcm_mul_partialSum_eq d hpos (q N)) hlim

/-- Pointwise version of the overlap estimate.  Unlike F-008's limit theorem,
this requires its cumulative budget at just one cut point. -/
theorem fib_lcm_mul_tail_le_of_overlap_budget_at
    (n e : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (hepos : ∀ k, 0 < e k) (he0 : e 0 = 1)
    (hediv : ∀ k, e k ∣ n k)
    (heprev : ∀ k, 0 < k → ∃ i < k, e k ∣ n i)
    (N : ℕ)
    (hbudget : (∑ k ∈ Finset.range N, n k) + 2 * N ≤
      n N + ∑ k ∈ Finset.range N, e k) :
    (reciprocalLcm (fun k => Nat.fib (n k)) N : ℝ) *
        (∑' j : ℕ, (Nat.fib (n (N + j)) : ℝ)⁻¹) ≤
      φ ^ 4 * (φ⁻¹) ^ N := by
  let r : ℝ := φ⁻¹
  have hlcm_bound :
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
  have htail := (summable_and_tsum_shift_le n hpos hmono N).2
  have hcancel := golden_pow_mul_inv_pow_le
    ((∑ k ∈ Finset.range N, n k) + N)
    (n N + ∑ k ∈ Finset.range N, e k) N (by omega)
  calc
    (reciprocalLcm (fun k => Nat.fib (n k)) N : ℝ) *
        (∑' j : ℕ, (Nat.fib (n (N + j)) : ℝ)⁻¹) ≤
        (φ ^ N * φ ^ (∑ k ∈ Finset.range N, n k) *
          r ^ (∑ k ∈ Finset.range N, e k)) *
            ((φ ^ 2 * r ^ (n N)) * φ ^ 2) := by
              gcongr
    _ = φ ^ 4 *
        (φ ^ ((∑ k ∈ Finset.range N, n k) + N) *
          r ^ (n N + ∑ k ∈ Finset.range N, e k)) := by
            rw [pow_add, pow_add]
            ring
    _ ≤ φ ^ 4 * r ^ N := by
            exact mul_le_mul_of_nonneg_left (by simpa [r] using hcancel) (by positivity)
    _ = φ ^ 4 * (φ⁻¹) ^ N := by rfl

/-- It is enough for the cumulative overlap budget to hold at any unbounded
sequence of cut points, rather than at every cut point. -/
theorem irrational_reciprocal_fib_of_overlap_budget_subsequence
    (n e s : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (hepos : ∀ k, 0 < e k) (he0 : e 0 = 1)
    (hediv : ∀ k, e k ∣ n k)
    (heprev : ∀ k, 0 < k → ∃ i < k, e k ∣ n i)
    (hs : Tendsto s atTop atTop)
    (hbudget : ∀ t,
      (∑ k ∈ Finset.range (s t), n k) + 2 * s t ≤
        n (s t) + ∑ k ∈ Finset.range (s t), e k) :
    Irrational (∑' k : ℕ, (Nat.fib (n k) : ℝ)⁻¹) := by
  have hsum := (summable_and_tsum_shift_le n hpos hmono 0).1
  have hnonneg (t : ℕ) :
      0 ≤ (reciprocalLcm (fun k => Nat.fib (n k)) (s t) : ℝ) *
        (∑' j : ℕ, (Nat.fib (n (s t + j)) : ℝ)⁻¹) := by positivity
  have hbound (t : ℕ) :
      (reciprocalLcm (fun k => Nat.fib (n k)) (s t) : ℝ) *
          (∑' j : ℕ, (Nat.fib (n (s t + j)) : ℝ)⁻¹) ≤
        φ ^ 4 * (φ⁻¹) ^ (s t) :=
    fib_lcm_mul_tail_le_of_overlap_budget_at n e hpos hmono hepos he0
      hediv heprev (s t) (hbudget t)
  have hr0 : 0 ≤ φ⁻¹ := (inv_pos.mpr Real.goldenRatio_pos).le
  have hr1 : φ⁻¹ < 1 := inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have hpow : Tendsto (fun N : ℕ => (φ⁻¹) ^ N) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
  have hmajor : Tendsto (fun t : ℕ => φ ^ 4 * (φ⁻¹) ^ (s t))
      atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul (hpow.comp hs)
  have hlim : Tendsto
      (fun t : ℕ =>
        (reciprocalLcm (fun k => Nat.fib (n k)) (s t) : ℝ) *
          (∑' j : ℕ, (Nat.fib (n (s t + j)) : ℝ)⁻¹))
      atTop (𝓝 0) := squeeze_zero hnonneg hbound hmajor
  exact irrational_tsum_reciprocals_of_lcm_tail_zero_at_cuts
    (fun k => Nat.fib (n k)) s (fun k => Nat.fib_pos.mpr (hpos k))
    (by simpa using hsum) hlim

end Research
