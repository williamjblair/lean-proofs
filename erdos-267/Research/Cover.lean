import Research.Subsequence

/-!
# Finite index-divisibility covers for Fibonacci lcm bounds
-/

namespace Research

open Filter Topology
open Real goldenRatio
open scoped BigOperators

/-- If every selected index before a cut divides one of the indices in `J`,
then the corresponding Fibonacci lcm divides the product over `J`.  The cover
indices need not occur earlier than the indices they cover. -/
theorem reciprocalLcm_fib_dvd_cover_product
    (n : ℕ → ℕ) (N : ℕ) (J : Finset ℕ)
    (hcover : ∀ k < N, ∃ j ∈ J, n k ∣ n j) :
    reciprocalLcm (fun k => Nat.fib (n k)) N ∣
      ∏ j ∈ J, Nat.fib (n j) := by
  rw [reciprocalLcm]
  apply Finset.lcm_dvd
  intro k hk
  obtain ⟨j, hj, hd⟩ := hcover k (Finset.mem_range.mp hk)
  exact (Nat.fib_dvd _ _ hd).trans
    (Finset.dvd_prod_of_mem (fun j => Nat.fib (n j)) hj)

/-- Golden-ratio upper bound for a Fibonacci product over an arbitrary finite
set of selected positions. -/
theorem prod_fib_finset_le_golden_geometric
    (n : ℕ → ℕ) (J : Finset ℕ) :
    (∏ j ∈ J, (Nat.fib (n j) : ℝ)) ≤
      (φ⁻¹) ^ J.card * φ ^ (∑ j ∈ J, n j) := by
  have hterm (j : ℕ) :
      (Nat.fib (n j) : ℝ) ≤ φ⁻¹ * φ ^ (n j) := by
    have h := goldenRatio_mul_fib_le_pow (n j)
    rw [← div_eq_inv_mul]
    exact (le_div_iff₀ Real.goldenRatio_pos).2 (by simpa [mul_comm] using h)
  calc
    (∏ j ∈ J, (Nat.fib (n j) : ℝ)) ≤
        ∏ j ∈ J, (φ⁻¹ * φ ^ (n j)) := by
          apply Finset.prod_le_prod
          · intro j hj
            positivity
          · intro j hj
            exact hterm j
    _ = (φ⁻¹) ^ J.card * φ ^ (∑ j ∈ J, n j) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const,
            Finset.prod_pow_eq_pow_sum]

/-- A divisibility cover whose total index weight lies sufficiently below the
next index forces irrationality.  This nonlocal criterion permits an early
index to be covered by a later index in the same finite prefix. -/
theorem irrational_reciprocal_fib_of_divisibility_covers
    (n s : ℕ → ℕ) (J : ℕ → Finset ℕ)
    (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (hs : Tendsto s atTop atTop)
    (hcover : ∀ t k, k < s t → ∃ j ∈ J t, n k ∣ n j)
    (hbudget : ∀ t,
      (∑ j ∈ J t, n j) + s t ≤ n (s t) + (J t).card) :
    Irrational (∑' k : ℕ, (Nat.fib (n k) : ℝ)⁻¹) := by
  let r : ℝ := φ⁻¹
  have hr0 : 0 ≤ r := by dsimp [r]; exact (inv_pos.mpr Real.goldenRatio_pos).le
  have hr1 : r < 1 := by dsimp [r]; exact inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have hpoint (t : ℕ) :
      (reciprocalLcm (fun k => Nat.fib (n k)) (s t) : ℝ) *
          (∑' j : ℕ, (Nat.fib (n (s t + j)) : ℝ)⁻¹) ≤
        φ ^ 4 * r ^ (s t) := by
    have hdvd := reciprocalLcm_fib_dvd_cover_product n (s t) (J t) (hcover t)
    have hprodpos : 0 < ∏ j ∈ J t, Nat.fib (n j) :=
      Finset.prod_pos fun j hj => Nat.fib_pos.mpr (hpos j)
    have hnat : reciprocalLcm (fun k => Nat.fib (n k)) (s t) ≤
        ∏ j ∈ J t, Nat.fib (n j) := Nat.le_of_dvd hprodpos hdvd
    have hlcm :
        (reciprocalLcm (fun k => Nat.fib (n k)) (s t) : ℝ) ≤
          r ^ (J t).card * φ ^ (∑ j ∈ J t, n j) := by
      calc
        (reciprocalLcm (fun k => Nat.fib (n k)) (s t) : ℝ) ≤
            (∏ j ∈ J t, Nat.fib (n j) : ℕ) := by exact_mod_cast hnat
        _ = ∏ j ∈ J t, (Nat.fib (n j) : ℝ) := by push_cast; rfl
        _ ≤ r ^ (J t).card * φ ^ (∑ j ∈ J t, n j) := by
          simpa [r] using prod_fib_finset_le_golden_geometric n (J t)
    have htail := (summable_and_tsum_shift_le n hpos hmono (s t)).2
    have hcancel := golden_pow_mul_inv_pow_le
      (∑ j ∈ J t, n j) (n (s t) + (J t).card) (s t) (hbudget t)
    calc
      (reciprocalLcm (fun k => Nat.fib (n k)) (s t) : ℝ) *
          (∑' j : ℕ, (Nat.fib (n (s t + j)) : ℝ)⁻¹) ≤
          (r ^ (J t).card * φ ^ (∑ j ∈ J t, n j)) *
            ((φ ^ 2 * r ^ (n (s t))) * φ ^ 2) := by gcongr
      _ = φ ^ 4 *
          (φ ^ (∑ j ∈ J t, n j) *
            r ^ (n (s t) + (J t).card)) := by
              rw [pow_add]
              ring
      _ ≤ φ ^ 4 * r ^ (s t) := by
              exact mul_le_mul_of_nonneg_left
                (by simpa [r] using hcancel) (by positivity)
  have hnonneg (t : ℕ) :
      0 ≤ (reciprocalLcm (fun k => Nat.fib (n k)) (s t) : ℝ) *
          (∑' j : ℕ, (Nat.fib (n (s t + j)) : ℝ)⁻¹) := by positivity
  have hmajor : Tendsto (fun t : ℕ => φ ^ 4 * r ^ (s t)) atTop (𝓝 0) := by
    have hp : Tendsto (fun N : ℕ => r ^ N) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
    simpa using tendsto_const_nhds.mul (hp.comp hs)
  have hlim : Tendsto
      (fun t : ℕ =>
        (reciprocalLcm (fun k => Nat.fib (n k)) (s t) : ℝ) *
          (∑' j : ℕ, (Nat.fib (n (s t + j)) : ℝ)⁻¹))
      atTop (𝓝 0) := squeeze_zero hnonneg hpoint hmajor
  exact irrational_tsum_reciprocals_of_lcm_tail_zero_at_cuts
    (fun k => Nat.fib (n k)) s (fun k => Nat.fib_pos.mpr (hpos k))
    (by simpa using (summable_and_tsum_shift_le n hpos hmono 0).1) hlim

end Research
