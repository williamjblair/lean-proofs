import Research.FourthModularCubicStage
import Research.FourthOriginalNoWrapDecay
import Mathlib.Tactic

open scoped BigOperators

namespace Erdos521

/-- At index `N+2`, the largest cubic Pascal coefficient is at most `2N³`. -/
lemma fourthCoefficientA_terminal_le (N : ℕ) (hN : 20 ≤ N) :
    fourthCoefficientA (N + 2) ≤ 2 * (N : ℝ) ^ 3 := by
  rw [fourthCoefficientA_formula]
  push_cast
  have h3 : (N + 3 : ℝ) ≤ 2 * N := by exact_mod_cast (show N + 3 ≤ 2 * N by omega)
  have h4 : (N + 4 : ℝ) ≤ 2 * N := by exact_mod_cast (show N + 4 ≤ 2 * N by omega)
  have h5 : (N + 5 : ℝ) ≤ 2 * N := by exact_mod_cast (show N + 5 ≤ 2 * N by omega)
  calc
    _ = (N + 3 : ℝ) * (N + 4 : ℝ) * (N + 5 : ℝ) / 6 := by ring
    _ ≤
        (2 * N : ℝ) * (2 * N : ℝ) * (2 * N : ℝ) / 6 := by gcongr
    _ ≤ 2 * (N : ℝ) ^ 3 := by
      have hN3 : 0 ≤ (N : ℝ) ^ 3 := by positivity
      nlinarith

/-- At index `N+2`, the largest quadratic Pascal coefficient is at most `2N²`. -/
lemma fourthCoefficientB_terminal_le (N : ℕ) (hN : 20 ≤ N) :
    fourthCoefficientB (N + 2) ≤ 2 * (N : ℝ) ^ 2 := by
  rw [fourthCoefficientB_formula]
  push_cast
  have h4 : (N + 4 : ℝ) ≤ 2 * N := by exact_mod_cast (show N + 4 ≤ 2 * N by omega)
  have h5 : (N + 5 : ℝ) ≤ 2 * N := by exact_mod_cast (show N + 5 ≤ 2 * N by omega)
  calc
    _ = (N + 4 : ℝ) * (N + 5 : ℝ) / 2 := by ring
    _ ≤
        (2 * N : ℝ) * (2 * N : ℝ) / 2 := by gcongr
    _ = 2 * (N : ℝ) ^ 2 := by ring

lemma fourthVarianceA_scaled_upper (N : ℕ) (hN : 20 ≤ N) :
    fourthVarianceA (N + 2) ≤ 8 * (N : ℝ) ^ 7 := by
  have hterm := fourthCoefficientA_terminal_le N hN
  have hcount : (N + 3 : ℝ) ≤ 2 * N := by
    exact_mod_cast (show N + 3 ≤ 2 * N by omega)
  have hterm0 : 0 ≤ fourthCoefficientA (N + 2) := by
    unfold fourthCoefficientA
    positivity
  have htermSq : fourthCoefficientA (N + 2) ^ 2 ≤
      (2 * (N : ℝ) ^ 3) ^ 2 := (sq_le_sq₀ hterm0 (by positivity)).2 hterm
  unfold fourthVarianceA
  calc
    (∑ l ∈ Finset.range (N + 2 + 1), (Nat.choose (l + 3) 3 : ℝ) ^ 2) ≤
        ∑ _l ∈ Finset.range (N + 2 + 1),
          (fourthCoefficientA (N + 2)) ^ 2 := by
      apply Finset.sum_le_sum
      intro l hl
      have hlN : l ≤ N + 2 := by have := Finset.mem_range.mp hl; omega
      have hm := fourthCoefficientA_mono hlN
      have hl0 : 0 ≤ fourthCoefficientA l := by unfold fourthCoefficientA; positivity
      have ht0 : 0 ≤ fourthCoefficientA (N + 2) := by
        unfold fourthCoefficientA
        positivity
      exact (sq_le_sq₀ hl0 ht0).2 hm
    _ = (N + 3 : ℝ) * (fourthCoefficientA (N + 2)) ^ 2 := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      ring
    _ ≤ (2 * N : ℝ) * (fourthCoefficientA (N + 2)) ^ 2 :=
      mul_le_mul_of_nonneg_right hcount (sq_nonneg _)
    _ ≤ (2 * N : ℝ) * (2 * (N : ℝ) ^ 3) ^ 2 :=
      mul_le_mul_of_nonneg_left htermSq (by positivity)
    _ = 8 * (N : ℝ) ^ 7 := by ring

lemma fourthIncrementVarianceB_scaled_upper (N : ℕ) (hN : 20 ≤ N) :
    fourthIncrementVarianceB (N + 2) ≤ 9 * (N : ℝ) ^ 5 := by
  have hterm := fourthCoefficientB_terminal_le N hN
  have hcount : (N + 3 : ℝ) ≤ 2 * N := by
    exact_mod_cast (show N + 3 ≤ 2 * N by omega)
  have hterm0 : 0 ≤ fourthCoefficientB (N + 2) := by
    unfold fourthCoefficientB
    positivity
  have htermSq : fourthCoefficientB (N + 2) ^ 2 ≤
      (2 * (N : ℝ) ^ 2) ^ 2 := (sq_le_sq₀ hterm0 (by positivity)).2 hterm
  have hsum : (∑ l ∈ Finset.range (N + 2 + 1),
      (Nat.choose (l + 3) 2 : ℝ) ^ 2) ≤ 8 * (N : ℝ) ^ 5 := by
    calc
      _ ≤ ∑ _l ∈ Finset.range (N + 2 + 1),
          (fourthCoefficientB (N + 2)) ^ 2 := by
        apply Finset.sum_le_sum
        intro l hl
        have hlN : l ≤ N + 2 := by have := Finset.mem_range.mp hl; omega
        have hm := fourthCoefficientB_mono hlN
        have hl0 : 0 ≤ fourthCoefficientB l := by unfold fourthCoefficientB; positivity
        have ht0 : 0 ≤ fourthCoefficientB (N + 2) := by
          unfold fourthCoefficientB
          positivity
        exact (sq_le_sq₀ hl0 ht0).2 hm
      _ = (N + 3 : ℝ) * (fourthCoefficientB (N + 2)) ^ 2 := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
      _ ≤ (2 * N : ℝ) * (fourthCoefficientB (N + 2)) ^ 2 :=
        mul_le_mul_of_nonneg_right hcount (sq_nonneg _)
      _ ≤ (2 * N : ℝ) * (2 * (N : ℝ) ^ 2) ^ 2 :=
        mul_le_mul_of_nonneg_left htermSq (by positivity)
      _ = 8 * (N : ℝ) ^ 5 := by ring
  unfold fourthIncrementVarianceB
  have hNpow : (1 : ℝ) ≤ (N : ℝ) ^ 5 := by
    have hNR : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hNR 5]
  nlinarith

/-- The full phase covariance quadratic form is bounded above by the natural anisotropic scales. -/
lemma fourthOriginalPhase_sq_sum_scaled_upper (N : ℕ) (hN : 20 ≤ N) (s t : ℝ) :
    (∑ i : Option (Fin (N + 2 + 1)), fourthOriginalPhase (N + 2) s t i ^ 2) ≤
      16 * (N : ℝ) ^ 7 * s ^ 2 + 18 * (N : ℝ) ^ 5 * t ^ 2 := by
  have hA := fourthVarianceA_scaled_upper N hN
  have hB := fourthIncrementVarianceB_scaled_upper N hN
  rw [fourthOriginalPhase_sq_sum]
  have hquad : fourthVarianceA (N + 2) * s ^ 2 +
      2 * fourthIncrementCovarianceC (N + 2) * s * t +
      fourthIncrementVarianceB (N + 2) * t ^ 2 ≤
      2 * fourthVarianceA (N + 2) * s ^ 2 +
        2 * fourthIncrementVarianceB (N + 2) * t ^ 2 := by
    unfold fourthVarianceA fourthIncrementVarianceB fourthIncrementCovarianceC
    have hpoint (q : ℕ) :
        (s * fourthCoefficientA q + t * fourthCoefficientB q) ^ 2 ≤
          2 * ((s * fourthCoefficientA q) ^ 2 +
            (t * fourthCoefficientB q) ^ 2) := by
      nlinarith [first_difference_sq_le (-s * fourthCoefficientA q)
        (t * fourthCoefficientB q)]
    have hsum : (∑ q ∈ Finset.range (N + 2 + 1),
        (s * fourthCoefficientA q + t * fourthCoefficientB q) ^ 2) ≤
        ∑ q ∈ Finset.range (N + 2 + 1),
          2 * ((s * fourthCoefficientA q) ^ 2 +
            (t * fourthCoefficientB q) ^ 2) :=
      Finset.sum_le_sum fun q hq ↦ hpoint q
    have hleft : (∑ q ∈ Finset.range (N + 2 + 1),
        (s * fourthCoefficientA q + t * fourthCoefficientB q) ^ 2) =
        s ^ 2 * (∑ q ∈ Finset.range (N + 2 + 1), fourthCoefficientA q ^ 2) +
          2 * s * t * (∑ q ∈ Finset.range (N + 2 + 1),
            fourthCoefficientA q * fourthCoefficientB q) +
          t ^ 2 * (∑ q ∈ Finset.range (N + 2 + 1), fourthCoefficientB q ^ 2) := by
      simp_rw [show ∀ q : ℕ,
        (s * fourthCoefficientA q + t * fourthCoefficientB q) ^ 2 =
          s ^ 2 * fourthCoefficientA q ^ 2 +
            2 * s * t * (fourthCoefficientA q * fourthCoefficientB q) +
            t ^ 2 * fourthCoefficientB q ^ 2 by intro q; ring]
      simp only [Finset.sum_add_distrib]
      simp_rw [← Finset.mul_sum]
    have hright : (∑ q ∈ Finset.range (N + 2 + 1),
        2 * ((s * fourthCoefficientA q) ^ 2 +
          (t * fourthCoefficientB q) ^ 2)) =
        2 * s ^ 2 * (∑ q ∈ Finset.range (N + 2 + 1), fourthCoefficientA q ^ 2) +
          2 * t ^ 2 * (∑ q ∈ Finset.range (N + 2 + 1),
            fourthCoefficientB q ^ 2) := by
      simp_rw [show ∀ q : ℕ,
        2 * ((s * fourthCoefficientA q) ^ 2 +
          (t * fourthCoefficientB q) ^ 2) =
          2 * s ^ 2 * fourthCoefficientA q ^ 2 +
            2 * t ^ 2 * fourthCoefficientB q ^ 2 by intro q; ring]
      rw [Finset.sum_add_distrib]
      simp_rw [← Finset.mul_sum]
    rw [hleft, hright] at hsum
    simp only [fourthCoefficientA, fourthCoefficientB] at hsum
    nlinarith [sq_nonneg t]
  calc
    _ ≤ 2 * fourthVarianceA (N + 2) * s ^ 2 +
        2 * fourthIncrementVarianceB (N + 2) * t ^ 2 := hquad
    _ ≤ 2 * (8 * (N : ℝ) ^ 7) * s ^ 2 +
        2 * (9 * (N : ℝ) ^ 5) * t ^ 2 := by gcongr
    _ = _ := by ring

/-- Either the modular energy is a fixed linear fraction of the length, or it controls the full
covariance quadratic form. -/
lemma fourth_old_modular_energy_dichotomy (N : ℕ) (s t : ℝ) (m : ℕ → ℤ)
    (hN : 20 ≤ N) (hs : |s| ≤ Real.pi / 2) (ht : |t| ≤ Real.pi / 2) :
    let E := ∑ q ∈ Finset.range (N + 3),
      (fourthOldPolynomialPhase q s t - (m q : ℝ) * Real.pi) ^ 2
    (N : ℝ) / 100000000000000000000 ≤ E ∨
      (∑ i : Option (Fin (N + 2 + 1)),
        fourthOriginalPhase (N + 2) s t i ^ 2) ≤ 3000000000 * E := by
  dsimp only
  let E : ℝ := ∑ q ∈ Finset.range (N + 3),
    (fourthOldPolynomialPhase q s t - (m q : ℝ) * Real.pi) ^ 2
  by_cases hlarge : (N : ℝ) ≤ 100000000000000000000 * E
  · left
    nlinarith
  · right
    have hsmall : 100000000000000000000 *
        (∑ q ∈ Finset.range (N + 3),
          (fourthOldPolynomialPhase q s t - (m q : ℝ) * Real.pi) ^ 2) < N := by
      dsimp [E] at hlarge
      exact lt_of_not_ge hlarge
    have hcubic := fourth_modular_cubic_stage N s t m hN hs ht hsmall
    have hscale := fourthOriginalPhase_sq_sum_scaled_upper N hN s t
    have hE0 : 0 ≤ ∑ q ∈ Finset.range (N + 3),
        (fourthOldPolynomialPhase q s t - (m q : ℝ) * Real.pi) ^ 2 :=
      Finset.sum_nonneg fun q hq ↦ sq_nonneg _
    calc
      _ ≤ 16 * (N : ℝ) ^ 7 * s ^ 2 + 18 * (N : ℝ) ^ 5 * t ^ 2 := hscale
      _ ≤ 16 * (30000000 * ∑ q ∈ Finset.range (N + 3),
            (fourthOldPolynomialPhase q s t - (m q : ℝ) * Real.pi) ^ 2) +
          18 * (100000000 * ∑ q ∈ Finset.range (N + 3),
            (fourthOldPolynomialPhase q s t - (m q : ℝ) * Real.pi) ^ 2) := by
        have hx := mul_le_mul_of_nonneg_left hcubic.1 (by norm_num : (0 : ℝ) ≤ 16)
        have hy := mul_le_mul_of_nonneg_left hcubic.2 (by norm_num : (0 : ℝ) ≤ 18)
        nlinarith
      _ ≤ 3000000000 * ∑ q ∈ Finset.range (N + 3),
          (fourthOldPolynomialPhase q s t - (m q : ℝ) * Real.pi) ^ 2 := by
        nlinarith

end Erdos521
