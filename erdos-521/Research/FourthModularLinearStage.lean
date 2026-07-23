import Research.LinearModularCoercivity
import Mathlib.Tactic

open scoped BigOperators

namespace Erdos521

/-- Integer representatives induced on the second finite differences. -/
def fourthSecondDifferenceIndex (m : ℕ → ℤ) (q : ℕ) : ℤ :=
  m (q + 2) - 2 * m (q + 1) + m q

/-- The second-difference residual energy, written as a linear modular phase. -/
noncomputable def fourthSecondDifferenceEnergy (N : ℕ) (s t : ℝ) (m : ℕ → ℤ) : ℝ :=
  ∑ q ∈ Finset.range N,
    ((3 * s + t) + s * (q : ℝ) -
      (fourthSecondDifferenceIndex m q : ℝ) * Real.pi) ^ 2

lemma fourthSecondDifferenceEnergy_eq (N : ℕ) (s t : ℝ) (m : ℕ → ℤ) :
    fourthSecondDifferenceEnergy N s t m =
      ∑ q ∈ Finset.range N,
        (s * (q + 3 : ℝ) + t -
          ((m (q + 2) : ℝ) - 2 * (m (q + 1) : ℝ) + (m q : ℝ)) * Real.pi) ^ 2 := by
  unfold fourthSecondDifferenceEnergy fourthSecondDifferenceIndex
  apply Finset.sum_congr rfl
  intro q hq
  push_cast
  congr 1
  ring

lemma fourthSecondDifferenceEnergy_le (N : ℕ) (s t : ℝ) (m : ℕ → ℤ) :
    fourthSecondDifferenceEnergy N s t m ≤
      18 * ∑ q ∈ Finset.range (N + 2),
        (fourthOldPolynomialPhase q s t - (m q : ℝ) * Real.pi) ^ 2 := by
  rw [fourthSecondDifferenceEnergy_eq]
  exact fourthPhase_second_difference_energy_sum N s t m

/-- A sufficiently small normalized old-phase energy de-aliases the linear second-difference
sequence and controls both naturally rescaled original dual coordinates. -/
lemma fourth_modular_linear_stage (N : ℕ) (s t : ℝ) (m : ℕ → ℤ)
    (hN : 2 ≤ N) (hs : |s| ≤ Real.pi / 2) (ht : |t| ≤ Real.pi / 2)
    (hsmall : 100000 * (∑ q ∈ Finset.range (N + 3),
      (fourthOldPolynomialPhase q s t - (m q : ℝ) * Real.pi) ^ 2) < N) :
    (N : ℝ) * |s| < 1 ∧
    (N : ℝ) ^ 3 * s ^ 2 ≤
      5184 * ∑ q ∈ Finset.range (N + 3),
        (fourthOldPolynomialPhase q s t - (m q : ℝ) * Real.pi) ^ 2 ∧
    (N : ℝ) * t ^ 2 ≤
      50000 * ∑ q ∈ Finset.range (N + 3),
        (fourthOldPolynomialPhase q s t - (m q : ℝ) * Real.pi) ^ 2 := by
  let E : ℝ := ∑ q ∈ Finset.range (N + 3),
    (fourthOldPolynomialPhase q s t - (m q : ℝ) * Real.pi) ^ 2
  let E2 : ℝ := fourthSecondDifferenceEnergy N s t m
  have hE0 : 0 ≤ E := Finset.sum_nonneg fun q hq ↦ sq_nonneg _
  have hE2 : E2 ≤ 18 * E := by
    dsimp [E, E2]
    have h := fourthSecondDifferenceEnergy_le N s t m
    exact h.trans (mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono (by omega : N + 2 ≤ N + 3))
        (fun q hq hnot ↦ sq_nonneg _)) (by norm_num))
  have hthird : (N : ℝ) * s ^ 2 ≤ 80 * E := by
    dsimp [E]
    exact fourthPhase_energy_controls_cubic_coordinate N s t m hs
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hsquarter : |s| ≤ 1 / 4 := by
    have hs2 : s ^ 2 < (1 / 4 : ℝ) ^ 2 := by
      nlinarith
    have habs2 : |s| ^ 2 < (1 / 4 : ℝ) ^ 2 := by simpa [sq_abs] using hs2
    exact (sq_lt_sq₀ (abs_nonneg s) (by norm_num)).mp habs2 |>.le
  have hE2small : 128 * E2 < N := by nlinarith
  have hsLocal : (N : ℝ) * |s| < 1 := by
    by_cases hs0 : s = 0
    · simp [hs0]
    · apply linearPhase_small_energy_forces_local N s (3 * s + t)
        (fourthSecondDifferenceIndex m) (by omega) (abs_pos.mpr hs0) hsquarter
      simpa [E2, fourthSecondDifferenceEnergy] using hE2small
  have hsScaled : (N : ℝ) ^ 3 * s ^ 2 ≤ 5184 * E := by
    have hlin := linearPhase_local_slope_energy N s (3 * s + t)
      (fourthSecondDifferenceIndex m) hN hsLocal
    have hlin' : (N : ℝ) ^ 3 * s ^ 2 ≤ 288 * E2 := by
      simpa [E2, fourthSecondDifferenceEnergy] using hlin
    nlinarith
  have htpoint (q : ℕ) (hq : q ∈ Finset.range N) :
      t ^ 2 ≤ 2 * (((3 * s + t) + s * (q : ℝ) -
        (fourthSecondDifferenceIndex m q : ℝ) * Real.pi) ^ 2 +
        (s * (q + 3 : ℝ)) ^ 2) := by
    have hnear := sq_le_sq_sub_int_mul_pi ht (fourthSecondDifferenceIndex m q)
    have hid : t - (fourthSecondDifferenceIndex m q : ℝ) * Real.pi =
        ((3 * s + t) + s * (q : ℝ) -
          (fourthSecondDifferenceIndex m q : ℝ) * Real.pi) -
        s * (q + 3 : ℝ) := by ring
    rw [hid] at hnear
    have hc := first_difference_sq_le
      (s * (q + 3 : ℝ))
      ((3 * s + t) + s * (q : ℝ) -
        (fourthSecondDifferenceIndex m q : ℝ) * Real.pi)
    have hc' : (((3 * s + t) + s * (q : ℝ) -
        (fourthSecondDifferenceIndex m q : ℝ) * Real.pi) -
        s * (q + 3 : ℝ)) ^ 2 ≤
        2 * (((3 * s + t) + s * (q : ℝ) -
          (fourthSecondDifferenceIndex m q : ℝ) * Real.pi) ^ 2 +
          (s * (q + 3 : ℝ)) ^ 2) := by
      nlinarith
    exact hnear.trans hc'
  have hqsum : (∑ q ∈ Finset.range N, (s * (q + 3 : ℝ)) ^ 2) ≤
      4 * (N : ℝ) ^ 3 * s ^ 2 := by
    calc
      _ ≤ ∑ _q ∈ Finset.range N, (s * (N + 2 : ℝ)) ^ 2 := by
        apply Finset.sum_le_sum
        intro q hq
        have hqN : (q + 3 : ℝ) ≤ N + 2 := by
          have := Finset.mem_range.mp hq
          exact_mod_cast (by omega : q + 3 ≤ N + 2)
        have hq0 : (0 : ℝ) ≤ q + 3 := by positivity
        have hN0 : (0 : ℝ) ≤ N + 2 := by positivity
        nlinarith [sq_nonneg s, (sq_le_sq₀ hq0 hN0).2 hqN]
      _ = (N : ℝ) * (s * (N + 2 : ℝ)) ^ 2 := by simp
      _ ≤ 4 * (N : ℝ) ^ 3 * s ^ 2 := by
        have hNp : (N + 2 : ℝ) ≤ 2 * N := by nlinarith
        have hNp0 : (0 : ℝ) ≤ N + 2 := by positivity
        have h2N0 : (0 : ℝ) ≤ 2 * N := by positivity
        have hsq := (sq_le_sq₀ hNp0 h2N0).2 hNp
        calc
          (N : ℝ) * (s * (N + 2 : ℝ)) ^ 2 =
              ((N : ℝ) * s ^ 2) * (N + 2 : ℝ) ^ 2 := by ring
          _ ≤ ((N : ℝ) * s ^ 2) * (2 * N : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_left hsq (by positivity)
          _ = 4 * (N : ℝ) ^ 3 * s ^ 2 := by ring
  have htScaled : (N : ℝ) * t ^ 2 ≤ 50000 * E := by
    have hsumPoint : (∑ _q ∈ Finset.range N, t ^ 2) ≤
        ∑ q ∈ Finset.range N, 2 *
          (((3 * s + t) + s * (q : ℝ) -
            (fourthSecondDifferenceIndex m q : ℝ) * Real.pi) ^ 2 +
            (s * (q + 3 : ℝ)) ^ 2) :=
      Finset.sum_le_sum fun q hq ↦ htpoint q hq
    have hsumEq : (∑ _q ∈ Finset.range N, t ^ 2) = (N : ℝ) * t ^ 2 := by simp
    have hright : (∑ q ∈ Finset.range N, 2 *
          (((3 * s + t) + s * (q : ℝ) -
            (fourthSecondDifferenceIndex m q : ℝ) * Real.pi) ^ 2 +
            (s * (q + 3 : ℝ)) ^ 2)) =
        2 * (E2 + ∑ q ∈ Finset.range N, (s * (q + 3 : ℝ)) ^ 2) := by
      dsimp [E2, fourthSecondDifferenceEnergy]
      simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hsumEq, hright] at hsumPoint
    nlinarith
  exact ⟨hsLocal, hsScaled, htScaled⟩

end Erdos521
