import Research.MultiOverlap

/-!
# Reusing the lcm of two overlapping Fibonacci factors
-/

namespace Research

open Filter Topology
open Real goldenRatio
open scoped BigOperators

/-- Common factor obtained from two reusable index divisors. -/
def twoOverlapFactor (e f : ℕ → ℕ) (k : ℕ) : ℕ :=
  Nat.lcm (Nat.fib (e k)) (Nat.fib (f k))

/-- The two-factor overlap divides the new Fibonacci denominator. -/
theorem twoOverlapFactor_dvd_fib
    (n e f : ℕ → ℕ) (hediv : ∀ k, e k ∣ n k)
    (hfdiv : ∀ k, f k ∣ n k) (k : ℕ) :
    twoOverlapFactor e f k ∣ Nat.fib (n k) := by
  apply Nat.lcm_dvd
  · exact Nat.fib_dvd _ _ (hediv k)
  · exact Nat.fib_dvd _ _ (hfdiv k)

/-- Except at the initial position, both factors being represented earlier
puts their lcm in the preceding selected-Fibonacci lcm. -/
theorem twoOverlapFactor_dvd_previous_lcm
    (n e f : ℕ → ℕ) (he0 : e 0 = 1) (hf0 : f 0 = 1)
    (heprev : ∀ k, 0 < k → ∃ i < k, e k ∣ n i)
    (hfprev : ∀ k, 0 < k → ∃ i < k, f k ∣ n i) (k : ℕ) :
    twoOverlapFactor e f k ∣ reciprocalLcm (fun i => Nat.fib (n i)) k := by
  by_cases hk : k = 0
  · subst k
    simp [twoOverlapFactor, he0, hf0, reciprocalLcm]
  · apply Nat.lcm_dvd
    · obtain ⟨i, hi, hd⟩ := heprev k (Nat.pos_of_ne_zero hk)
      exact (Nat.fib_dvd _ _ hd).trans (Finset.dvd_lcm (Finset.mem_range.mpr hi))
    · obtain ⟨i, hi, hd⟩ := hfprev k (Nat.pos_of_ne_zero hk)
      exact (Nat.fib_dvd _ _ hd).trans (Finset.dvd_lcm (Finset.mem_range.mpr hi))

/-- Exact finite lcm bound using both reusable factors simultaneously. -/
theorem reciprocalLcm_fib_dvd_twoOverlap_product
    (n e f : ℕ → ℕ) (hepos : ∀ k, 0 < e k) (hfpos : ∀ k, 0 < f k)
    (he0 : e 0 = 1) (hf0 : f 0 = 1)
    (hediv : ∀ k, e k ∣ n k) (hfdiv : ∀ k, f k ∣ n k)
    (heprev : ∀ k, 0 < k → ∃ i < k, e k ∣ n i)
    (hfprev : ∀ k, 0 < k → ∃ i < k, f k ∣ n i) :
    ∀ N, reciprocalLcm (fun k => Nat.fib (n k)) N ∣
      ∏ k ∈ Finset.range N, Nat.fib (n k) / twoOverlapFactor e f k := by
  apply reciprocalLcm_dvd_commonFactor_product
  · intro k
    exact Nat.lcm_pos (Nat.fib_pos.mpr (hepos k)) (Nat.fib_pos.mpr (hfpos k))
  · exact twoOverlapFactor_dvd_fib n e f hediv hfdiv
  · exact twoOverlapFactor_dvd_previous_lcm n e f he0 hf0 heprev hfprev

/-- The inverse two-factor lcm has exponent cost governed by
`e+f-gcd(e,f)`. -/
theorem inv_twoOverlapFactor_le_geometric
    (e f : ℕ) (he : 0 < e) (hf : 0 < f) :
    (twoOverlapFactor (fun _ => e) (fun _ => f) 0 : ℝ)⁻¹ ≤
      φ ^ 3 * (φ⁻¹) ^ (e + f - Nat.gcd e f) := by
  let H := Nat.lcm (Nat.fib e) (Nat.fib f)
  have heF : (0 : ℝ) < Nat.fib e := by exact_mod_cast Nat.fib_pos.mpr he
  have hfF : (0 : ℝ) < Nat.fib f := by exact_mod_cast Nat.fib_pos.mpr hf
  have hgpos : 0 < Nat.gcd e f := Nat.gcd_pos_of_pos_left _ he
  have hgF : (0 : ℝ) < Nat.fib (Nat.gcd e f) := by
    exact_mod_cast Nat.fib_pos.mpr hgpos
  have hprodNat : Nat.fib (Nat.gcd e f) * H = Nat.fib e * Nat.fib f := by
    dsimp [H]
    rw [Nat.fib_gcd]
    exact Nat.gcd_mul_lcm _ _
  have hprod : (Nat.fib (Nat.gcd e f) : ℝ) * H =
      (Nat.fib e : ℝ) * Nat.fib f := by exact_mod_cast hprodNat
  have hH : (0 : ℝ) < H := by
    exact_mod_cast Nat.lcm_pos (Nat.fib_pos.mpr he) (Nat.fib_pos.mpr hf)
  have hident : (H : ℝ)⁻¹ =
      (Nat.fib (Nat.gcd e f) : ℝ) *
        (Nat.fib e : ℝ)⁻¹ * (Nat.fib f : ℝ)⁻¹ := by
    field_simp [ne_of_gt hH, ne_of_gt heF, ne_of_gt hfF]
    nlinarith [hprod]
  have hgUpper : (Nat.fib (Nat.gcd e f) : ℝ) ≤
      φ⁻¹ * φ ^ (Nat.gcd e f) := by
    have h := goldenRatio_mul_fib_le_pow (Nat.gcd e f)
    rw [← div_eq_inv_mul]
    exact (le_div_iff₀ Real.goldenRatio_pos).2 (by simpa [mul_comm] using h)
  have heInv := inv_fib_le_golden_geometric e he
  have hfInv := inv_fib_le_golden_geometric f hf
  rw [show twoOverlapFactor (fun _ => e) (fun _ => f) 0 = H by rfl, hident]
  calc
    (Nat.fib (Nat.gcd e f) : ℝ) * (Nat.fib e : ℝ)⁻¹ *
        (Nat.fib f : ℝ)⁻¹ ≤
      (φ⁻¹ * φ ^ (Nat.gcd e f)) *
        (φ ^ 2 * (φ⁻¹) ^ e) * (φ ^ 2 * (φ⁻¹) ^ f) := by gcongr
    _ = φ ^ 3 * (φ⁻¹) ^ (e + f - Nat.gcd e f) := by
      have hge : Nat.gcd e f ≤ e := Nat.gcd_le_left f he
      have hgf : Nat.gcd e f ≤ f := Nat.gcd_le_right e hf
      have hsum : e + f = Nat.gcd e f + (e + f - Nat.gcd e f) := by omega
      have hpow : φ ^ (Nat.gcd e f) * (φ⁻¹) ^ e * (φ⁻¹) ^ f =
          (φ⁻¹) ^ (e + f - Nat.gcd e f) := by
        calc
          φ ^ (Nat.gcd e f) * (φ⁻¹) ^ e * (φ⁻¹) ^ f =
              φ ^ (Nat.gcd e f) * (φ⁻¹) ^ (e + f) := by
                rw [mul_assoc, ← pow_add]
          _ = φ ^ (Nat.gcd e f) *
              (φ⁻¹) ^ (Nat.gcd e f + (e + f - Nat.gcd e f)) := by
                congr 2
          _ = (φ * φ⁻¹) ^ (Nat.gcd e f) *
              (φ⁻¹) ^ (e + f - Nat.gcd e f) := by
                rw [pow_add, mul_pow]
                ring
          _ = (φ⁻¹) ^ (e + f - Nat.gcd e f) := by
                rw [mul_inv_cancel₀ Real.goldenRatio_ne_zero, one_pow, one_mul]
      calc
        (φ⁻¹ * φ ^ (Nat.gcd e f)) *
            (φ ^ 2 * (φ⁻¹) ^ e) * (φ ^ 2 * (φ⁻¹) ^ f) =
            φ ^ 3 *
              (φ ^ (Nat.gcd e f) * (φ⁻¹) ^ e * (φ⁻¹) ^ f) := by
                field_simp [Real.goldenRatio_ne_zero]
        _ = φ ^ 3 * (φ⁻¹) ^ (e + f - Nat.gcd e f) := by rw [hpow]

/-- Quotient estimate after reusing the two-factor lcm. -/
theorem fib_div_twoOverlap_le_geometric
    (n e f : ℕ) (_hn : 0 < n) (he : 0 < e) (hf : 0 < f)
    (hed : e ∣ n) (hfd : f ∣ n) :
    ((Nat.fib n / Nat.lcm (Nat.fib e) (Nat.fib f) : ℕ) : ℝ) ≤
      φ ^ 2 * φ ^ n * (φ⁻¹) ^ (e + f - Nat.gcd e f) := by
  have hdiv : Nat.lcm (Nat.fib e) (Nat.fib f) ∣ Nat.fib n :=
    Nat.lcm_dvd (Nat.fib_dvd _ _ hed) (Nat.fib_dvd _ _ hfd)
  have hHpos := Nat.lcm_pos (Nat.fib_pos.mpr he) (Nat.fib_pos.mpr hf)
  have hH0 : (Nat.lcm (Nat.fib e) (Nat.fib f) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hHpos)
  rw [Nat.cast_div hdiv hH0, div_eq_mul_inv]
  have hfn : (Nat.fib n : ℝ) ≤ φ⁻¹ * φ ^ n := by
    have h := goldenRatio_mul_fib_le_pow n
    rw [← div_eq_inv_mul]
    exact (le_div_iff₀ Real.goldenRatio_pos).2 (by simpa [mul_comm] using h)
  have hinv : (Nat.lcm (Nat.fib e) (Nat.fib f) : ℝ)⁻¹ ≤
      φ ^ 3 * (φ⁻¹) ^ (e + f - Nat.gcd e f) := by
    simpa [twoOverlapFactor] using inv_twoOverlapFactor_le_geometric e f he hf
  calc
    (Nat.fib n : ℝ) * (Nat.lcm (Nat.fib e) (Nat.fib f) : ℝ)⁻¹ ≤
        (φ⁻¹ * φ ^ n) *
          (φ ^ 3 * (φ⁻¹) ^ (e + f - Nat.gcd e f)) := by gcongr
    _ = φ ^ 2 * φ ^ n * (φ⁻¹) ^ (e + f - Nat.gcd e f) := by
      field_simp [Real.goldenRatio_ne_zero]

/-- Two-overlap cumulative budget implies irrationality. -/
theorem irrational_reciprocal_fib_of_twoOverlap_budget
    (n e f : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (hepos : ∀ k, 0 < e k) (hfpos : ∀ k, 0 < f k)
    (he0 : e 0 = 1) (hf0 : f 0 = 1)
    (hediv : ∀ k, e k ∣ n k) (hfdiv : ∀ k, f k ∣ n k)
    (heprev : ∀ k, 0 < k → ∃ i < k, e k ∣ n i)
    (hfprev : ∀ k, 0 < k → ∃ i < k, f k ∣ n i)
    (hbudget : ∀ N,
      (∑ k ∈ Finset.range N, n k) + 3 * N ≤
        n N + ∑ k ∈ Finset.range N,
          (e k + f k - Nat.gcd (e k) (f k))) :
    Irrational (∑' k : ℕ, (Nat.fib (n k) : ℝ)⁻¹) := by
  let r : ℝ := φ⁻¹
  have hr0 : 0 ≤ r := by dsimp [r]; exact (inv_pos.mpr Real.goldenRatio_pos).le
  have hr1 : r < 1 := by dsimp [r]; exact inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have hlcm (N : ℕ) :
      (reciprocalLcm (fun k => Nat.fib (n k)) N : ℝ) ≤
        φ ^ (2 * N) * φ ^ (∑ k ∈ Finset.range N, n k) *
          r ^ (∑ k ∈ Finset.range N,
            (e k + f k - Nat.gcd (e k) (f k))) := by
    have hdvd := reciprocalLcm_fib_dvd_twoOverlap_product n e f hepos hfpos
      he0 hf0 hediv hfdiv heprev hfprev N
    have hqpos (k : ℕ) :
        0 < Nat.fib (n k) / twoOverlapFactor e f k := by
      apply Nat.div_pos
      · exact Nat.le_of_dvd (Nat.fib_pos.mpr (hpos k))
          (twoOverlapFactor_dvd_fib n e f hediv hfdiv k)
      · exact Nat.lcm_pos (Nat.fib_pos.mpr (hepos k)) (Nat.fib_pos.mpr (hfpos k))
    have hnat : reciprocalLcm (fun k => Nat.fib (n k)) N ≤
        ∏ k ∈ Finset.range N, Nat.fib (n k) / twoOverlapFactor e f k :=
      Nat.le_of_dvd (Finset.prod_pos fun k hk => hqpos k) hdvd
    calc
      (reciprocalLcm (fun k => Nat.fib (n k)) N : ℝ) ≤
          (∏ k ∈ Finset.range N,
            Nat.fib (n k) / twoOverlapFactor e f k : ℕ) := by exact_mod_cast hnat
      _ = ∏ k ∈ Finset.range N,
          ((Nat.fib (n k) / twoOverlapFactor e f k : ℕ) : ℝ) := by push_cast; rfl
      _ ≤ ∏ k ∈ Finset.range N,
          (φ ^ 2 * φ ^ (n k) *
            r ^ (e k + f k - Nat.gcd (e k) (f k))) := by
              apply Finset.prod_le_prod
              · intro k hk
                positivity
              · intro k hk
                simpa [twoOverlapFactor, r] using fib_div_twoOverlap_le_geometric
                  (n k) (e k) (f k) (hpos k) (hepos k) (hfpos k)
                    (hediv k) (hfdiv k)
      _ = φ ^ (2 * N) * φ ^ (∑ k ∈ Finset.range N, n k) *
          r ^ (∑ k ∈ Finset.range N,
            (e k + f k - Nat.gcd (e k) (f k))) := by
              repeat' rw [Finset.prod_mul_distrib]
              rw [Finset.prod_const, Finset.card_range,
                Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum]
              rw [← pow_mul]
  have hlim : Tendsto
      (fun N : ℕ =>
        (reciprocalLcm (fun k => Nat.fib (n k)) N : ℝ) *
          (∑' j : ℕ, (Nat.fib (n (N + j)) : ℝ)⁻¹))
      atTop (𝓝 0) := by
    have hbound (N : ℕ) :
        (reciprocalLcm (fun k => Nat.fib (n k)) N : ℝ) *
            (∑' j : ℕ, (Nat.fib (n (N + j)) : ℝ)⁻¹) ≤
          φ ^ 4 * r ^ N := by
      have htail := (summable_and_tsum_shift_le n hpos hmono N).2
      have hcancel := golden_pow_mul_inv_pow_le
        ((∑ k ∈ Finset.range N, n k) + 2 * N)
        (n N + ∑ k ∈ Finset.range N,
          (e k + f k - Nat.gcd (e k) (f k))) N (by
            have hb := hbudget N
            omega)
      calc
        (reciprocalLcm (fun k => Nat.fib (n k)) N : ℝ) *
            (∑' j : ℕ, (Nat.fib (n (N + j)) : ℝ)⁻¹) ≤
            (φ ^ (2 * N) * φ ^ (∑ k ∈ Finset.range N, n k) *
              r ^ (∑ k ∈ Finset.range N,
                (e k + f k - Nat.gcd (e k) (f k)))) *
              ((φ ^ 2 * r ^ (n N)) * φ ^ 2) := by
                gcongr
                exact hlcm N
        _ = φ ^ 4 *
            (φ ^ ((∑ k ∈ Finset.range N, n k) + 2 * N) *
              r ^ (n N + ∑ k ∈ Finset.range N,
                (e k + f k - Nat.gcd (e k) (f k)))) := by
                rw [pow_add, pow_add]
                ring
        _ ≤ φ ^ 4 * r ^ N := by
                exact mul_le_mul_of_nonneg_left
                  (by simpa [r] using hcancel) (by positivity)
    have hnonneg (N : ℕ) :
        0 ≤ (reciprocalLcm (fun k => Nat.fib (n k)) N : ℝ) *
          (∑' j : ℕ, (Nat.fib (n (N + j)) : ℝ)⁻¹) := by positivity
    have hmajor : Tendsto (fun N : ℕ => φ ^ 4 * r ^ N) atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.mul
        (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1)
    exact squeeze_zero hnonneg hbound hmajor
  exact irrational_tsum_reciprocals_of_lcm_tail_zero
    (fun k => Nat.fib (n k)) (fun k => Nat.fib_pos.mpr (hpos k))
    (by simpa using (summable_and_tsum_shift_le n hpos hmono 0).1) hlim

end Research
