import Research.CoefficientSeries

/-!
# The globally collected Lambert coefficient series
-/

namespace Research

open Real goldenRatio
open scoped BigOperators

set_option maxHeartbeats 800000

private theorem summable_double_fibLambertCoeff
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n) :
    Summable (Function.uncurry fun k m : ℕ =>
      (fibLambertCoeff (n k) m : ℝ) * (φ⁻¹) ^ m) := by
  let r : ℝ := φ⁻¹
  have hr0 : 0 ≤ r := by
    dsimp [r]
    exact (inv_pos.mpr Real.goldenRatio_pos).le
  have hr1 : r < 1 := by
    dsimp [r]
    exact inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  let g : ℕ × ℕ → ℝ := fun p => if p.2 < p.1 then r ^ p.1 else 0
  have hg : Summable g := by
    have hg0 : ∀ p, 0 ≤ g p := by
      intro p
      dsimp [g]
      split_ifs <;> positivity
    rw [summable_prod_of_nonneg hg0]
    constructor
    · intro m
      apply summable_of_ne_finset_zero (s := Finset.range m)
      intro k hk
      simp only [Finset.mem_range, not_lt] at hk
      simp [g, hk]
    · have hrow : (fun m : ℕ => ∑' k : ℕ, g (m, k)) =
          (fun m : ℕ => (m : ℝ) * r ^ m) := by
        funext m
        rw [tsum_eq_sum (s := Finset.range m)]
        · calc
            (∑ k ∈ Finset.range m, g (m, k)) =
                ∑ _k ∈ Finset.range m, r ^ m := by
                  apply Finset.sum_congr rfl
                  intro k hk
                  simp [g, Finset.mem_range.mp hk]
            _ = (m : ℝ) * r ^ m := by simp
        · intro k hk
          simp only [Finset.mem_range, not_lt] at hk
          simp [g, hk]
      rw [hrow]
      simpa only [pow_one] using
        (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
          (by simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1))
  have hswap : Summable (fun p : ℕ × ℕ =>
      (fibLambertCoeff (n p.2) p.1 : ℝ) * r ^ p.1) := by
    apply Summable.of_norm_bounded hg
    intro p
    by_cases hkm : p.2 < p.1
    · have hc : |(fibLambertCoeff (n p.2) p.1 : ℝ)| ≤ 1 := by
        exact_mod_cast abs_fibLambertCoeff_le_one (n p.2) p.1
      rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hr0]
      simp only [g, if_pos hkm]
      simpa using mul_le_mul_of_nonneg_right hc (pow_nonneg hr0 p.1)
    · have hmk : p.1 ≤ p.2 := by omega
      have hz := fibLambertCoeff_eq_zero_of_exponent_le_position
        n hpos hmono hmk
      simp [hz, g, hkm]
  have horig : Summable (fun p : ℕ × ℕ =>
      (fibLambertCoeff (n p.1) p.2 : ℝ) * r ^ p.2) := by
    exact ((Equiv.prodComm ℕ ℕ).summable_iff).mp (by
      simpa [Function.comp_def] using hswap)
  change Summable (fun p : ℕ × ℕ =>
    (fibLambertCoeff (n p.1) p.2 : ℝ) * (φ⁻¹) ^ p.2)
  simpa [r] using horig

private theorem tsum_over_positions_eq_selected
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (m : ℕ) :
    (∑' k : ℕ,
      (fibLambertCoeff (n k) m : ℝ) * (φ⁻¹) ^ m) =
      (selectedFibLambertCoeff n m : ℝ) * (φ⁻¹) ^ m := by
  rw [tsum_eq_sum (s := Finset.range m)]
  · rw [selectedFibLambertCoeff]
    push_cast
    rw [Finset.sum_mul]
  · intro k hk
    have hmk : m ≤ k := by
      simpa only [Finset.mem_range, not_lt] using hk
    rw [fibLambertCoeff_eq_zero_of_exponent_le_position n hpos hmono hmk]
    simp

/-- Exact global collection identity.  The sum of the full integer
coefficients at powers of `φ⁻¹` is `1/√5` times the original reciprocal
Fibonacci series. -/
theorem hasSum_selectedFibLambertCoeff
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n) :
    HasSum (fun m : ℕ =>
      (selectedFibLambertCoeff n m : ℝ) * (φ⁻¹) ^ m)
      ((√5)⁻¹ * ∑' k : ℕ, (Nat.fib (n k) : ℝ)⁻¹) := by
  have hd := summable_double_fibLambertCoeff n hpos hmono
  have hcomm := hd.tsum_comm
  have hleft :
      (∑' m : ℕ, ∑' k : ℕ,
        (fibLambertCoeff (n k) m : ℝ) * (φ⁻¹) ^ m) =
      ∑' m : ℕ,
        (selectedFibLambertCoeff n m : ℝ) * (φ⁻¹) ^ m := by
    apply tsum_congr
    exact tsum_over_positions_eq_selected n hpos hmono
  have hright :
      (∑' k : ℕ, ∑' m : ℕ,
        (fibLambertCoeff (n k) m : ℝ) * (φ⁻¹) ^ m) =
      (√5)⁻¹ * ∑' k : ℕ, (Nat.fib (n k) : ℝ)⁻¹ := by
    calc
      (∑' k : ℕ, ∑' m : ℕ,
        (fibLambertCoeff (n k) m : ℝ) * (φ⁻¹) ^ m) =
          ∑' k : ℕ, (√5)⁻¹ * (Nat.fib (n k) : ℝ)⁻¹ := by
            apply tsum_congr
            intro k
            exact (hasSum_fibLambertCoeff_eq_inv_sqrtFive_mul_inv_fib
              (n k) (hpos k)).tsum_eq
      _ = (√5)⁻¹ * ∑' k : ℕ, (Nat.fib (n k) : ℝ)⁻¹ := tsum_mul_left
  have hsum :
      (∑' m : ℕ,
        (selectedFibLambertCoeff n m : ℝ) * (φ⁻¹) ^ m) =
      (√5)⁻¹ * ∑' k : ℕ, (Nat.fib (n k) : ℝ)⁻¹ := by
    rw [← hleft, hcomm, hright]
  have hsummable : Summable (fun m : ℕ =>
      (selectedFibLambertCoeff n m : ℝ) * (φ⁻¹) ^ m) := by
    have hdswap : Summable (fun p : ℕ × ℕ =>
        (fibLambertCoeff (n p.2) p.1 : ℝ) * (φ⁻¹) ^ p.1) := by
      change Summable ((Function.uncurry fun k m : ℕ =>
        (fibLambertCoeff (n k) m : ℝ) * (φ⁻¹) ^ m) ∘
          (Equiv.prodComm ℕ ℕ))
      exact ((Equiv.prodComm ℕ ℕ).summable_iff).mpr hd
    have hp : Summable (fun m : ℕ => ∑' k : ℕ,
        (fibLambertCoeff (n k) m : ℝ) * (φ⁻¹) ^ m) := hdswap.prod
    convert hp using 1
    funext m
    exact (tsum_over_positions_eq_selected n hpos hmono m).symm
  rw [← hsum]
  exact hsummable.hasSum

end Research
