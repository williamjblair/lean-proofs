import Research.TailLattice

/-!
# Analytic normalized coefficient tails
-/

namespace Research

open Real goldenRatio
open scoped BigOperators

/-- The normalized coefficient tail beginning at exponent `N`. -/
noncomputable def coefficientTail (C : ℕ → ℤ) (N : ℕ) : ℝ :=
  ∑' t : ℕ, (C (N + t) : ℝ) * (φ⁻¹) ^ t

private theorem goldenRatio_pow_mul_inv_pow_add (N t : ℕ) :
    φ ^ N * (φ⁻¹) ^ (t + N) = (φ⁻¹) ^ t := by
  rw [pow_add]
  have hu : φ ^ N * (φ⁻¹) ^ N = 1 := by
    rw [inv_pow, mul_inv_cancel₀ (pow_ne_zero _ Real.goldenRatio_ne_zero)]
  rw [show φ ^ N * ((φ⁻¹) ^ t * (φ⁻¹) ^ N) =
    (φ⁻¹) ^ t * (φ ^ N * (φ⁻¹) ^ N) by ring, hu, mul_one]

private theorem goldenRatio_pow_mul_inv_pow_of_le
    {N m : ℕ} (hmN : m ≤ N) :
    φ ^ N * (φ⁻¹) ^ m = φ ^ (N - m) := by
  rw [inv_pow, pow_sub₀ φ Real.goldenRatio_ne_zero hmN]

/-- Summability of the original coefficient series implies summability of every
normalized tail. -/
theorem summable_coefficientTail
    (C : ℕ → ℤ)
    (hsum : Summable (fun m : ℕ => (C m : ℝ) * (φ⁻¹) ^ m))
    (N : ℕ) :
    Summable (fun t : ℕ => (C (N + t) : ℝ) * (φ⁻¹) ^ t) := by
  have hshift : Summable (fun t : ℕ =>
      (C (t + N) : ℝ) * (φ⁻¹) ^ (t + N)) :=
    (summable_nat_add_iff N).mpr hsum
  have hmul := hshift.mul_left (φ ^ N)
  apply hmul.congr
  intro t
  rw [Nat.add_comm t N]
  rw [show φ ^ N * ((C (N + t) : ℝ) * (φ⁻¹) ^ (N + t)) =
    (C (N + t) : ℝ) * (φ ^ N * (φ⁻¹) ^ (t + N)) by
      rw [Nat.add_comm N t]
      ring,
    goldenRatio_pow_mul_inv_pow_add]

/-- The algebraic prefix residual of F-024 equals the analytic normalized
infinite tail whenever the coefficient series has sum `T`. -/
theorem normalizedCoefficientResidual_eq_coefficientTail
    (C : ℕ → ℤ) (T : ℝ)
    (hsum : HasSum (fun m : ℕ => (C m : ℝ) * (φ⁻¹) ^ m) T)
    (N : ℕ) :
    normalizedCoefficientResidual C T N = coefficientTail C N := by
  have hs := hsum.summable
  have hdecomp := hs.sum_add_tsum_nat_add N
  rw [hsum.tsum_eq] at hdecomp
  have hprefix :
      φ ^ N * (∑ m ∈ Finset.range N,
        (C m : ℝ) * (φ⁻¹) ^ m) =
      ∑ m ∈ Finset.range N, (C m : ℝ) * φ ^ (N - m) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    have hmN : m ≤ N := (Finset.mem_range.mp hm).le
    rw [show φ ^ N * ((C m : ℝ) * (φ⁻¹) ^ m) =
      (C m : ℝ) * (φ ^ N * (φ⁻¹) ^ m) by ring,
      goldenRatio_pow_mul_inv_pow_of_le hmN]
  have htail :
      φ ^ N * (∑' t : ℕ,
        (C (t + N) : ℝ) * (φ⁻¹) ^ (t + N)) =
      coefficientTail C N := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro t
    rw [Nat.add_comm t N]
    rw [show φ ^ N * ((C (N + t) : ℝ) * (φ⁻¹) ^ (N + t)) =
      (C (N + t) : ℝ) * (φ ^ N * (φ⁻¹) ^ (t + N)) by
        rw [Nat.add_comm N t]
        ring,
      goldenRatio_pow_mul_inv_pow_add]
  unfold normalizedCoefficientResidual
  rw [← hprefix, ← htail]
  have hmuldecomp := congrArg (fun x : ℝ => φ ^ N * x) hdecomp
  rw [mul_add] at hmuldecomp
  linarith

/-- A normalized tail splits into a finite length-`L` block and a rescaled
later tail. -/
theorem coefficientTail_eq_block_add
    (C : ℕ → ℤ)
    (hsum : Summable (fun m : ℕ => (C m : ℝ) * (φ⁻¹) ^ m))
    (N L : ℕ) :
    coefficientTail C N =
      (∑ t ∈ Finset.range L, (C (N + t) : ℝ) * (φ⁻¹) ^ t) +
        (φ⁻¹) ^ L * coefficientTail C (N + L) := by
  have htailSum := summable_coefficientTail C hsum N
  have hdecomp := htailSum.sum_add_tsum_nat_add L
  unfold coefficientTail
  rw [← hdecomp]
  congr 1
  rw [← tsum_mul_left]
  apply tsum_congr
  intro t
  rw [show N + (t + L) = N + L + t by omega, pow_add]
  ring

/-- A linear coefficient bound gives an explicit linear bound for every
normalized tail. -/
theorem abs_coefficientTail_le
    (C : ℕ → ℤ) (hC : ∀ m, |C m| ≤ (m : ℤ)) (N : ℕ) :
    |coefficientTail C N| ≤
      (N : ℝ) * (1 - φ⁻¹)⁻¹ + φ⁻¹ / (1 - φ⁻¹) ^ 2 := by
  let r : ℝ := φ⁻¹
  have hr0 : 0 ≤ r := by
    dsimp [r]
    exact (inv_pos.mpr Real.goldenRatio_pos).le
  have hr1 : r < 1 := by
    dsimp [r]
    exact inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have hrabs : |r| < 1 := by simpa [abs_of_nonneg hr0] using hr1
  let g : ℕ → ℝ := fun t => (N + t : ℕ) * r ^ t
  have hgeom : Summable (fun t : ℕ => r ^ t) :=
    summable_geometric_of_abs_lt_one hrabs
  have hlin : Summable (fun t : ℕ => (t : ℝ) * r ^ t) := by
    simpa only [pow_one] using
      (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
        (by simpa [Real.norm_eq_abs] using hrabs))
  have hconst : Summable (fun t : ℕ => (N : ℝ) * r ^ t) :=
    hgeom.mul_left (N : ℝ)
  have hg : Summable g := by
    apply (hconst.add hlin).congr
    intro t
    dsimp [g]
    push_cast
    ring
  have hterm : ∀ t : ℕ,
      ‖(C (N + t) : ℝ) * r ^ t‖ ≤ g t := by
    intro t
    have hc : |(C (N + t) : ℝ)| ≤ (N + t : ℕ) := by
      exact_mod_cast hC (N + t)
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hr0]
    exact mul_le_mul_of_nonneg_right hc (pow_nonneg hr0 t)
  have hf : Summable (fun t : ℕ => (C (N + t) : ℝ) * r ^ t) :=
    Summable.of_norm_bounded hg hterm
  have hnorm := norm_tsum_le_tsum_norm hf.norm
  have hle := hf.norm.tsum_le_tsum hterm hg
  have hgvalue :
      (∑' t : ℕ, g t) =
        (N : ℝ) * (1 - r)⁻¹ + r / (1 - r) ^ 2 := by
    calc
      (∑' t : ℕ, g t) =
          ∑' t : ℕ, ((N : ℝ) * r ^ t + (t : ℝ) * r ^ t) := by
            apply tsum_congr
            intro t
            dsimp [g]
            push_cast
            ring
      _ = (∑' t : ℕ, (N : ℝ) * r ^ t) +
          ∑' t : ℕ, (t : ℝ) * r ^ t := hconst.tsum_add hlin
      _ = (N : ℝ) * (1 - r)⁻¹ + r / (1 - r) ^ 2 := by
        rw [tsum_mul_left, tsum_geometric_of_abs_lt_one hrabs,
          tsum_coe_mul_geometric_of_norm_lt_one
            (by simpa [Real.norm_eq_abs] using hrabs)]
  have hfinal := hnorm.trans hle
  rw [hgvalue] at hfinal
  change |∑' t : ℕ, (C (N + t) : ℝ) * r ^ t| ≤
    (N : ℝ) * (1 - r)⁻¹ + r / (1 - r) ^ 2
  rw [← Real.norm_eq_abs]
  exact hfinal

/-- Two identical length-`L` coefficient blocks force their normalized-tail
difference to acquire the factor `φ⁻ᴸ`. -/
theorem coefficientTail_sub_eq_pow_mul_of_block_eq
    (C : ℕ → ℤ)
    (hsum : Summable (fun m : ℕ => (C m : ℝ) * (φ⁻¹) ^ m))
    (N M L : ℕ)
    (hblock : ∀ t < L, C (N + t) = C (M + t)) :
    coefficientTail C N - coefficientTail C M =
      (φ⁻¹) ^ L *
        (coefficientTail C (N + L) - coefficientTail C (M + L)) := by
  rw [coefficientTail_eq_block_add C hsum N L,
    coefficientTail_eq_block_add C hsum M L]
  have hfinite :
      (∑ t ∈ Finset.range L, (C (N + t) : ℝ) * (φ⁻¹) ^ t) =
      ∑ t ∈ Finset.range L, (C (M + t) : ℝ) * (φ⁻¹) ^ t := by
    apply Finset.sum_congr rfl
    intro t ht
    rw [hblock t (Finset.mem_range.mp ht)]
  rw [hfinite]
  ring

end Research
