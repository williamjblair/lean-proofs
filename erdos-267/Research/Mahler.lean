import Research.RatioTwo

/-!
# A product-denominator irrationality criterion
-/

namespace Research

open Filter Topology
open scoped BigOperators

/-- Product common denominator for the first `N` reciprocal terms. -/
def reciprocalDenomProd (d : ℕ → ℕ) (N : ℕ) : ℕ :=
  ∏ k ∈ Finset.range N, d k

/-- Integer numerator obtained after scaling the first `N` reciprocal terms by
the product common denominator. -/
def reciprocalScaledNumerator (d : ℕ → ℕ) (N : ℕ) : ℕ :=
  ∑ k ∈ Finset.range N, reciprocalDenomProd d N / d k

/-- Multiplying a finite reciprocal sum by the product denominator gives the
explicit integer numerator. -/
theorem denomProd_mul_partialSum_eq_scaledNumerator
    (d : ℕ → ℕ) (hpos : ∀ k : ℕ, 0 < d k) (N : ℕ) :
    (reciprocalDenomProd d N : ℝ) *
        (∑ k ∈ Finset.range N, (d k : ℝ)⁻¹) =
      (reciprocalScaledNumerator d N : ℝ) := by
  rw [Finset.mul_sum]
  simp only [reciprocalScaledNumerator, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hdvd : d k ∣ reciprocalDenomProd d N := by
    exact Finset.dvd_prod_of_mem d hk
  have hcast : (d k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hpos k))
  rw [Nat.cast_div hdvd hcast]
  simp [div_eq_mul_inv]

/-- Mahler's elementary criterion specialized to unit fractions: if the product
common denominator times the positive shifted tail tends to zero, then the
series sum is irrational. -/
theorem irrational_tsum_reciprocals_of_prod_tail_zero
    (d : ℕ → ℕ) (hpos : ∀ k : ℕ, 0 < d k)
    (hsum : Summable (fun k : ℕ => (d k : ℝ)⁻¹))
    (hlim : Tendsto
      (fun N : ℕ =>
        (reciprocalDenomProd d N : ℝ) *
          (∑' j : ℕ, (d (N + j) : ℝ)⁻¹))
      atTop (𝓝 0)) :
    Irrational (∑' k : ℕ, (d k : ℝ)⁻¹) := by
  rw [irrational_iff_ne_rational]
  intro a b hb hrat
  let S : ℝ := ∑' k : ℕ, (d k : ℝ)⁻¹
  let D : ℕ → ℕ := fun N => reciprocalDenomProd d N
  let A : ℕ → ℕ := fun N => reciprocalScaledNumerator d N
  let P : ℕ → ℝ := fun N => ∑ k ∈ Finset.range N, (d k : ℝ)⁻¹
  let T : ℕ → ℝ := fun N => ∑' j : ℕ, (d (N + j) : ℝ)⁻¹
  have hDpos (N : ℕ) : 0 < D N := by
    dsimp [D, reciprocalDenomProd]
    exact Finset.prod_pos fun k hk => hpos k
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
    simpa [D, A, P] using denomProd_mul_partialSum_eq_scaledNumerator d hpos N
  have hlower (N : ℕ) :
      (1 : ℝ) ≤ |(b : ℝ)| * ((D N : ℝ) * T N) := by
    let z : ℤ := a * (D N : ℤ) - b * (A N : ℤ)
    have hinter :
        (b : ℝ) * (D N : ℝ) * T N = (z : ℝ) := by
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
    simpa [D, T, mul_assoc] using h
  have hfalse : (1 : ℝ) ≤ 0 := ge_of_tendsto' hlim' hlower
  norm_num at hfalse

/-- Erdős Problem 267 has an affirmative answer at the full endpoint
`n_{k+1}/n_k ≥ 2` (not merely for a strict bound above two). -/
theorem irrational_reciprocal_fib_of_doubling
    (n : ℕ → ℕ) (hpos : ∀ k : ℕ, 0 < n k)
    (hmono : StrictMono n) (hdouble : ∀ k : ℕ, 2 * n k ≤ n (k + 1)) :
    Irrational (∑' k : ℕ, (Nat.fib (n k) : ℝ)⁻¹) := by
  apply irrational_tsum_reciprocals_of_prod_tail_zero
    (d := fun k => Nat.fib (n k))
  · intro k
    exact Nat.fib_pos.mpr (hpos k)
  · have h := (summable_and_tsum_shift_le n hpos hmono 0).1
    simpa using h
  · simpa [reciprocalDenomProd] using
      tendsto_prod_fib_mul_tail_zero_of_doubling n hpos hmono hdouble

end Research
