import Research.ConjugateTail

/-!
# Fully explicit matched-block norm contradiction gate
-/

namespace Research

open Real goldenRatio
open scoped BigOperators

noncomputable def tailLinearBound (N : ℕ) : ℝ :=
  (N : ℝ) * (1 - φ⁻¹)⁻¹ + φ⁻¹ / (1 - φ⁻¹) ^ 2

noncomputable def conjugateQuadraticBound (Tconj : ℝ) (N : ℕ) : ℝ :=
  |Tconj| + (N : ℝ) ^ 2

/-- A coarse quadratic bound for the explicit conjugate residual. -/
theorem abs_conjugateCoefficientResidual_le
    (C : ℕ → ℤ) (hC : ∀ m, |C m| ≤ (m : ℤ))
    (Tconj : ℝ) (N : ℕ) :
    |conjugateCoefficientResidual C Tconj N| ≤
      conjugateQuadraticBound Tconj N := by
  have hψabs0 : 0 ≤ |ψ| := abs_nonneg _
  have hψabs1 : |ψ| ≤ 1 := by
    rw [abs_of_neg Real.goldenConj_neg]
    linarith [Real.neg_one_lt_goldenConj]
  have hpow : ∀ p : ℕ, |ψ| ^ p ≤ 1 := fun p =>
    pow_le_one₀ hψabs0 hψabs1
  have hfirst : |ψ ^ N * Tconj| ≤ |Tconj| := by
    rw [abs_mul, abs_pow]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (hpow N) (abs_nonneg Tconj)
  have hterm : ∀ m ∈ Finset.range N,
      |(C m : ℝ) * ψ ^ (N - m)| ≤ (N : ℝ) := by
    intro m hm
    have hmN : m ≤ N := (Finset.mem_range.mp hm).le
    have hc : |(C m : ℝ)| ≤ (m : ℝ) := by
      exact_mod_cast hC m
    rw [abs_mul, abs_pow]
    calc
      |(C m : ℝ)| * |ψ| ^ (N - m) ≤ (m : ℝ) * 1 :=
        mul_le_mul hc (hpow (N - m)) (pow_nonneg hψabs0 _) (by positivity)
      _ ≤ (N : ℝ) := by
        simpa using (show (m : ℝ) ≤ (N : ℝ) by exact_mod_cast hmN)
  have hprefix :
      |∑ m ∈ Finset.range N, (C m : ℝ) * ψ ^ (N - m)| ≤
        (N : ℝ) ^ 2 := by
    calc
      |∑ m ∈ Finset.range N, (C m : ℝ) * ψ ^ (N - m)| ≤
          ∑ m ∈ Finset.range N, |(C m : ℝ) * ψ ^ (N - m)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _m ∈ Finset.range N, (N : ℝ) := by
        apply Finset.sum_le_sum
        exact hterm
      _ = (N : ℝ) ^ 2 := by
        simp
        ring
  unfold conjugateCoefficientResidual conjugateQuadraticBound
  exact (abs_sub _ _).trans (add_le_add hfirst hprefix)

/-- Equal coefficient blocks make the principal tail difference exponentially
small, with a completely explicit endpoint bound. -/
theorem abs_coefficientTail_sub_le_of_block_eq
    (C : ℕ → ℤ) (hC : ∀ m, |C m| ≤ (m : ℤ))
    (hsum : Summable (fun m : ℕ => (C m : ℝ) * (φ⁻¹) ^ m))
    (N M L : ℕ) (hblock : ∀ t < L, C (N + t) = C (M + t)) :
    |coefficientTail C N - coefficientTail C M| ≤
      (φ⁻¹) ^ L *
        (tailLinearBound (N + L) + tailLinearBound (M + L)) := by
  rw [coefficientTail_sub_eq_pow_mul_of_block_eq C hsum N M L hblock,
    abs_mul, abs_pow, abs_of_nonneg (inv_nonneg.mpr Real.goldenRatio_pos.le)]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (inv_nonneg.mpr Real.goldenRatio_pos.le) _)
  exact (abs_sub _ _).trans <| add_le_add
    (abs_coefficientTail_le C hC (N + L))
    (abs_coefficientTail_le C hC (M + L))

/-- The two conjugate residuals have a quadratic difference bound. -/
theorem abs_conjugateResidual_sub_le
    (C : ℕ → ℤ) (hC : ∀ m, |C m| ≤ (m : ℤ))
    (Tconj : ℝ) (N M : ℕ) :
    |conjugateCoefficientResidual C Tconj N -
      conjugateCoefficientResidual C Tconj M| ≤
      conjugateQuadraticBound Tconj N +
        conjugateQuadraticBound Tconj M := by
  exact (abs_sub _ _).trans <| add_le_add
    (abs_conjugateCoefficientResidual_le C hC Tconj N)
    (abs_conjugateCoefficientResidual_le C hC Tconj M)

/-- **Matched-block contradiction gate.**  Under the rationality identity for
the coefficient sum, a nonzero repeated block cannot be long enough to make
the displayed explicit product smaller than the fixed norm lower bound. -/
theorem matched_block_norm_obstruction
    (C : ℕ → ℤ) (hC : ∀ m, |C m| ≤ (m : ℤ))
    (a : ℤ) (b : ℕ) (hb : 0 < b)
    (hsum : HasSum (fun m : ℕ => (C m : ℝ) * (φ⁻¹) ^ m)
      ((√5)⁻¹ * ((a : ℝ) / (b : ℝ))))
    (N M L : ℕ)
    (hblock : ∀ t < L, C (N + t) = C (M + t))
    (hne : coefficientTail C N ≠ coefficientTail C M)
    (hsmall :
      (φ⁻¹) ^ L *
          (tailLinearBound (N + L) + tailLinearBound (M + L)) *
        (conjugateQuadraticBound
            (-((√5)⁻¹ * ((a : ℝ) / (b : ℝ)))) N +
          conjugateQuadraticBound
            (-((√5)⁻¹ * ((a : ℝ) / (b : ℝ)))) M) <
      (((5 * b : ℕ) : ℝ)⁻¹) ^ 2) :
    False := by
  let T : ℝ := (√5)⁻¹ * ((a : ℝ) / (b : ℝ))
  let Tc : ℝ := -T
  let x : ℝ := coefficientTail C N - coefficientTail C M
  let y : ℝ := conjugateCoefficientResidual C Tc N -
    conjugateCoefficientResidual C Tc M
  have hpairN := normalized_and_conjugate_residual_mem_pair C a b N hb
  have hpairM := normalized_and_conjugate_residual_mem_pair C a b M hb
  have hresN := normalizedCoefficientResidual_eq_coefficientTail C T hsum N
  have hresM := normalizedCoefficientResidual_eq_coefficientTail C T hsum M
  have hpair : InScaledGoldenPair (5 * b) x y := by
    dsimp [x, y, Tc]
    rw [← hresN, ← hresM]
    exact hpairN.sub (by omega) hpairM
  have hx : x ≠ 0 := sub_ne_zero.mpr hne
  have hlower := hpair.norm_lower (by omega) hx
  have hxupper : |x| ≤
      (φ⁻¹) ^ L *
        (tailLinearBound (N + L) + tailLinearBound (M + L)) := by
    exact abs_coefficientTail_sub_le_of_block_eq C hC hsum.summable
      N M L hblock
  have hyupper : |y| ≤
      conjugateQuadraticBound Tc N + conjugateQuadraticBound Tc M := by
    exact abs_conjugateResidual_sub_le C hC Tc N M
  have hpnonneg : 0 ≤
      (φ⁻¹) ^ L *
        (tailLinearBound (N + L) + tailLinearBound (M + L)) :=
    (abs_nonneg x).trans hxupper
  have hproduct : |x| * |y| ≤
      ((φ⁻¹) ^ L *
        (tailLinearBound (N + L) + tailLinearBound (M + L))) *
      (conjugateQuadraticBound Tc N + conjugateQuadraticBound Tc M) := by
    exact mul_le_mul hxupper hyupper (abs_nonneg _) hpnonneg
  dsimp [Tc, T] at hproduct
  exact (not_lt_of_ge (hlower.trans hproduct)) hsmall

end Research
