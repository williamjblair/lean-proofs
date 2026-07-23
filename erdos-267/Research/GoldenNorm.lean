import Research.FullCoefficient

/-!
# Elementary quadratic norm gate in `ℤ[φ]`
-/

namespace Research

open Real goldenRatio

/-- A nontrivial integral linear form in the golden ratio is nonzero. -/
theorem int_add_mul_goldenRatio_ne_zero (A B : ℤ)
    (hAB : A ≠ 0 ∨ B ≠ 0) :
    (A : ℝ) + (B : ℝ) * φ ≠ 0 := by
  by_cases hB : B = 0
  · subst B
    simp only [Int.cast_zero, zero_mul, add_zero]
    exact_mod_cast hAB.resolve_right (by simp)
  · intro h
    have hrat := (irrational_iff_ne_rational φ).mp Real.goldenRatio_irrational
      (-A) B hB
    have hB0 : (B : ℝ) ≠ 0 := by exact_mod_cast hB
    apply hrat
    apply (eq_div_iff hB0).2
    push_cast
    linarith

/-- The same nonvanishing statement at the conjugate embedding. -/
theorem int_add_mul_goldenConj_ne_zero (A B : ℤ)
    (hAB : A ≠ 0 ∨ B ≠ 0) :
    (A : ℝ) + (B : ℝ) * ψ ≠ 0 := by
  by_cases hB : B = 0
  · subst B
    simp only [Int.cast_zero, zero_mul, add_zero]
    exact_mod_cast hAB.resolve_right (by simp)
  · intro h
    have hrat := (irrational_iff_ne_rational ψ).mp Real.goldenConj_irrational
      (-A) B hB
    have hB0 : (B : ℝ) ≠ 0 := by exact_mod_cast hB
    apply hrat
    apply (eq_div_iff hB0).2
    push_cast
    linarith

/-- Explicit norm formula in the quadratic order `ℤ[φ]`. -/
theorem golden_integer_norm_eq (A B : ℤ) :
    ((A : ℝ) + (B : ℝ) * φ) * ((A : ℝ) + (B : ℝ) * ψ) =
      ((A * A + A * B - B * B : ℤ) : ℝ) := by
  calc
    ((A : ℝ) + (B : ℝ) * φ) * ((A : ℝ) + (B : ℝ) * ψ) =
        (A : ℝ) ^ 2 + (A : ℝ) * B * (φ + ψ) +
          (B : ℝ) ^ 2 * (φ * ψ) := by ring
    _ = ((A * A + A * B - B * B : ℤ) : ℝ) := by
      rw [Real.goldenRatio_add_goldenConj,
        Real.goldenRatio_mul_goldenConj]
      push_cast
      ring

/-- A nonzero element of `ℤ[φ]` has archimedean product at least one.  This is
the elementary degree-two algebraic-norm lower bound used by the planned block
argument. -/
theorem one_le_abs_golden_mul_abs_conj (A B : ℤ)
    (hAB : A ≠ 0 ∨ B ≠ 0) :
    (1 : ℝ) ≤
      |(A : ℝ) + (B : ℝ) * φ| * |(A : ℝ) + (B : ℝ) * ψ| := by
  have hφ := int_add_mul_goldenRatio_ne_zero A B hAB
  have hψ := int_add_mul_goldenConj_ne_zero A B hAB
  have hnorm : A * A + A * B - B * B ≠ 0 := by
    intro h
    have hprod := golden_integer_norm_eq A B
    rw [h, Int.cast_zero] at hprod
    exact mul_ne_zero hφ hψ hprod
  have hone : (1 : ℝ) ≤ |((A * A + A * B - B * B : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs hnorm
  rw [← golden_integer_norm_eq, abs_mul] at hone
  exact hone

/-- Scaled form: if `q>0`, a nonzero element of `(1/q)ℤ[φ]` has the product of
its two real embeddings at least `q⁻²`. -/
theorem inv_sq_le_abs_scaled_golden_mul_abs_conj
    (A B : ℤ) (q : ℕ) (hq : 0 < q) (hAB : A ≠ 0 ∨ B ≠ 0) :
    ((q : ℝ)⁻¹) ^ 2 ≤
      |((A : ℝ) + (B : ℝ) * φ) / q| *
        |((A : ℝ) + (B : ℝ) * ψ) / q| := by
  have hbase := one_le_abs_golden_mul_abs_conj A B hAB
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  rw [abs_div, abs_div, abs_of_pos hqR]
  have hq0 : (q : ℝ) ≠ 0 := ne_of_gt hqR
  calc
    ((q : ℝ)⁻¹) ^ 2 ≤
        (|(A : ℝ) + (B : ℝ) * φ| * |(A : ℝ) + (B : ℝ) * ψ|) *
          ((q : ℝ)⁻¹) ^ 2 := by
            simpa only [one_mul] using
              mul_le_mul_of_nonneg_right hbase (sq_nonneg ((q : ℝ)⁻¹))
    _ = |(A : ℝ) + (B : ℝ) * φ| / q *
        (|(A : ℝ) + (B : ℝ) * ψ| / q) := by
          field_simp

end Research
