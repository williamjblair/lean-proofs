import Research.ModularDifferenceTransforms
import Mathlib.Tactic

open scoped BigOperators

namespace Erdos521

noncomputable def fourthFirstDifferencePhase (s t : ℝ) (q : ℕ) : ℝ :=
  s * fourthCoefficientB q + t * (q + 3 : ℝ)

def fourthFirstDifferenceIndex (m : ℕ → ℤ) (q : ℕ) : ℤ := m (q + 1) - m q

noncomputable def fourthFirstDifferenceEnergy (N : ℕ) (s t : ℝ) (m : ℕ → ℤ) : ℝ :=
  ∑ q ∈ Finset.range N,
    (fourthFirstDifferencePhase s t q -
      (fourthFirstDifferenceIndex m q : ℝ) * Real.pi) ^ 2

lemma fourthFirstDifferenceEnergy_le (N : ℕ) (s t : ℝ) (m : ℕ → ℤ) :
    fourthFirstDifferenceEnergy N s t m ≤
      4 * ∑ q ∈ Finset.range (N + 1),
        (fourthOldPolynomialPhase q s t - (m q : ℝ) * Real.pi) ^ 2 := by
  unfold fourthFirstDifferenceEnergy fourthFirstDifferencePhase fourthFirstDifferenceIndex
  convert fourthPhase_first_difference_energy_sum N s t m using 1 <;> push_cast <;> ring

lemma fourthFirstDifferencePhase_lag (s t : ℝ) (q L : ℕ) :
    fourthFirstDifferencePhase s t (q + L) - fourthFirstDifferencePhase s t q =
      (s * (L : ℝ)) * (q : ℝ) +
        (s * (L : ℝ) * (L + 5 : ℝ) / 2 + t * (L : ℝ)) := by
  unfold fourthFirstDifferencePhase
  rw [fourthCoefficientB_formula, fourthCoefficientB_formula]
  push_cast
  ring

lemma fourthFirstDifferencePhase_reflect (s t : ℝ) {q K : ℕ} (hq : q ≤ K) :
    fourthFirstDifferencePhase s t (K - q) - fourthFirstDifferencePhase s t q =
      (-(s * (K + 5 : ℝ) + 2 * t)) * (q : ℝ) +
        (s * (K : ℝ) * (K + 5 : ℝ) / 2 + t * (K : ℝ)) := by
  unfold fourthFirstDifferencePhase
  rw [fourthCoefficientB_formula, fourthCoefficientB_formula]
  push_cast
  rw [Nat.cast_sub hq]
  ring

set_option maxHeartbeats 5000000 in
/-- The quadratic first-difference phase de-aliases at a half-length lag and under reflection. -/
lemma fourth_modular_quadratic_stage (N : ℕ) (s t : ℝ) (m : ℕ → ℤ)
    (hN : 12 ≤ N) (hs : |s| ≤ Real.pi / 2) (ht : |t| ≤ Real.pi / 2)
    (hsmall : 1000000000000 * (∑ q ∈ Finset.range (N + 3),
      (fourthOldPolynomialPhase q s t - (m q : ℝ) * Real.pi) ^ 2) < N) :
    (N : ℝ) ^ 5 * s ^ 2 ≤
      400000 * ∑ q ∈ Finset.range (N + 3),
        (fourthOldPolynomialPhase q s t - (m q : ℝ) * Real.pi) ^ 2 ∧
    (N : ℝ) ^ 3 * t ^ 2 ≤
      1000000 * ∑ q ∈ Finset.range (N + 3),
        (fourthOldPolynomialPhase q s t - (m q : ℝ) * Real.pi) ^ 2 := by
  let E : ℝ := ∑ q ∈ Finset.range (N + 3),
    (fourthOldPolynomialPhase q s t - (m q : ℝ) * Real.pi) ^ 2
  let E1 : ℝ := fourthFirstDifferenceEnergy (N + 1) s t m
  have hE0 : 0 ≤ E := Finset.sum_nonneg fun q hq ↦ sq_nonneg _
  have hE1 : E1 ≤ 4 * E := by
    dsimp [E1]
    have h := fourthFirstDifferenceEnergy_le (N + 1) s t m
    have hsub : (∑ q ∈ Finset.range (N + 1 + 1),
        (fourthOldPolynomialPhase q s t - (m q : ℝ) * Real.pi) ^ 2) ≤ E := by
      dsimp [E]
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono (by omega : N + 1 + 1 ≤ N + 3))
        (fun q hq hnot ↦ sq_nonneg _)
    nlinarith
  have hlinearSmall : 100000 * (∑ q ∈ Finset.range (N + 3),
      (fourthOldPolynomialPhase q s t - (m q : ℝ) * Real.pi) ^ 2) < N := by
    nlinarith
  have hlinear := fourth_modular_linear_stage N s t m (by omega) hs ht hlinearSmall
  have hs3 : (N : ℝ) ^ 3 * s ^ 2 ≤ 5184 * E := hlinear.2.1
  have ht1 : (N : ℝ) * t ^ 2 ≤ 50000 * E := hlinear.2.2
  let L : ℕ := N / 2
  let R : ℕ := N + 1 - L
  let mLag : ℕ → ℤ := fun q ↦
    fourthFirstDifferenceIndex m (q + L) - fourthFirstDifferenceIndex m q
  let bLag : ℝ := s * (L : ℝ) * (L + 5 : ℝ) / 2 + t * (L : ℝ)
  have hL : L ≤ N + 1 := by dsimp [L]; omega
  have hR : R = N + 1 - L := rfl
  have hLagEnergy : (∑ q ∈ Finset.range R,
      (bLag + (s * (L : ℝ)) * (q : ℝ) - (mLag q : ℝ) * Real.pi) ^ 2) ≤
      4 * E1 := by
    have h := modular_lag_difference_energy
      (fourthFirstDifferencePhase s t) (fourthFirstDifferenceIndex m) (N + 1) L hL
    dsimp [R, bLag, mLag]
    rw [show N + 1 - L = N + 1 - L by rfl]
    convert h using 1
    · apply Finset.sum_congr rfl
      intro q hq
      rw [fourthFirstDifferencePhase_lag]
      push_cast
      congr 1
      ring
    · rfl
  have hRlower : (N : ℝ) / 2 ≤ (R : ℝ) := by
    have hc : N ≤ 2 * R := by dsimp [R, L]; omega
    have hcR : (N : ℝ) ≤ 2 * (R : ℝ) := by exact_mod_cast hc
    linarith
  have hLlower : (N : ℝ) / 3 ≤ (L : ℝ) := by
    have hc : N ≤ 3 * L := by dsimp [L]; omega
    have hcR : (N : ℝ) ≤ 3 * (L : ℝ) := by exact_mod_cast hc
    linarith
  have hLagSlopeQuarter : |s * (L : ℝ)| ≤ 1 / 4 := by
    have hLcast : (L : ℝ) ≤ N := by exact_mod_cast (show L ≤ N by dsimp [L]; omega)
    have hsq : (s * (L : ℝ)) ^ 2 ≤ 5184 * E / N := by
      have hmul : (s * (L : ℝ)) ^ 2 * (N : ℝ) ≤ (N : ℝ) ^ 3 * s ^ 2 := by
        have hLsq : (L : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 :=
          (sq_le_sq₀ (by positivity) (by positivity)).2 hLcast
        calc
          (s * (L : ℝ)) ^ 2 * (N : ℝ) = ((N : ℝ) * s ^ 2) * (L : ℝ) ^ 2 := by ring
          _ ≤ ((N : ℝ) * s ^ 2) * (N : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_left hLsq (by positivity)
          _ = (N : ℝ) ^ 3 * s ^ 2 := by ring
      have hNR : (0 : ℝ) < N := by positivity
      apply (le_div_iff₀ hNR).2
      nlinarith
    have hsmallR : E / (N : ℝ) < 1 / 1000000000000 := by
      have hNR : (0 : ℝ) < N := by positivity
      apply (div_lt_iff₀ hNR).2
      nlinarith
    have hsquareSmall : (s * (L : ℝ)) ^ 2 < (1 / 4 : ℝ) ^ 2 := by
      calc
        _ ≤ 5184 * E / N := hsq
        _ < 5184 * (1 / 1000000000000 : ℝ) := by
          have hm := mul_lt_mul_of_pos_left hsmallR (by norm_num : (0 : ℝ) < 5184)
          simpa [div_eq_mul_inv, mul_assoc] using hm
        _ < (1 / 4 : ℝ) ^ 2 := by norm_num
    have habs2 : |s * (L : ℝ)| ^ 2 < (1 / 4 : ℝ) ^ 2 := by
      rw [sq_abs]
      exact hsquareSmall
    exact (sq_lt_sq₀ (abs_nonneg _) (by norm_num)).mp habs2 |>.le
  have hLagSmall : 128 * (4 * E1) < R := by
    nlinarith
  have hLagLocal : (R : ℝ) * |s * (L : ℝ)| < 1 := by
    by_cases hz : s * (L : ℝ) = 0
    · simp [hz]
    · apply linearPhase_small_energy_forces_local R (s * (L : ℝ)) bLag mLag
        (by dsimp [R, L]; omega) (abs_pos.mpr hz) hLagSlopeQuarter
      calc
        128 * (∑ q ∈ Finset.range R,
          (bLag + (s * (L : ℝ)) * (q : ℝ) - (mLag q : ℝ) * Real.pi) ^ 2) ≤
            128 * (4 * E1) := by gcongr
        _ < R := hLagSmall
  have hLagScaled : (R : ℝ) ^ 3 * (s * (L : ℝ)) ^ 2 ≤ 4608 * E := by
    have h := linearPhase_local_slope_energy R (s * (L : ℝ)) bLag mLag
      (by dsimp [R, L]; omega) hLagLocal
    calc
      _ ≤ 288 * (4 * E1) := by
        exact h.trans (mul_le_mul_of_nonneg_left hLagEnergy (by norm_num))
      _ ≤ 4608 * E := by nlinarith
  have hs5 : (N : ℝ) ^ 5 * s ^ 2 ≤ 400000 * E := by
    have hR3 : ((N : ℝ) / 2) ^ 3 ≤ (R : ℝ) ^ 3 :=
      pow_le_pow_left₀ (by positivity) hRlower 3
    have hL2 : ((N : ℝ) / 3) ^ 2 ≤ (L : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hLlower 2
    have hbase : ((N : ℝ) / 2) ^ 3 * ((N : ℝ) / 3) ^ 2 * s ^ 2 ≤
        (R : ℝ) ^ 3 * (s * (L : ℝ)) ^ 2 := by
      have hs0 : 0 ≤ s ^ 2 := sq_nonneg _
      calc
        _ ≤ (R : ℝ) ^ 3 * ((N : ℝ) / 3) ^ 2 * s ^ 2 := by gcongr
        _ ≤ (R : ℝ) ^ 3 * (L : ℝ) ^ 2 * s ^ 2 := by gcongr
        _ = _ := by ring
    nlinarith
  let aRef : ℝ := -(s * (N + 5 : ℝ) + 2 * t)
  let bRef : ℝ := s * (N : ℝ) * (N + 5 : ℝ) / 2 + t * (N : ℝ)
  let mRef : ℕ → ℤ := fun q ↦
    fourthFirstDifferenceIndex m (N - q) - fourthFirstDifferenceIndex m q
  have hRefEnergy : (∑ q ∈ Finset.range (N + 1),
      (bRef + aRef * (q : ℝ) - (mRef q : ℝ) * Real.pi) ^ 2) ≤ 4 * E1 := by
    have h := modular_reflection_difference_energy
      (fourthFirstDifferencePhase s t) (fourthFirstDifferenceIndex m)
      N (N + 1) le_rfl
    dsimp [aRef, bRef, mRef]
    convert h using 1
    · apply Finset.sum_congr rfl
      intro q hq
      have hqN : q ≤ N := by have := Finset.mem_range.mp hq; omega
      rw [fourthFirstDifferencePhase_reflect s t hqN]
      push_cast
      congr 1
      ring
    · rfl
  have hRefQuarter : |aRef| ≤ 1 / 4 := by
    have hNR12 : (12 : ℝ) ≤ N := by exact_mod_cast hN
    have hNp : (N + 5 : ℝ) ≤ 2 * N := by nlinarith
    have hsTerm : (s * (N + 5 : ℝ)) ^ 2 ≤ 20736 * E / N := by
      have hcoefSq : (N + 5 : ℝ) ^ 2 ≤ (2 * N : ℝ) ^ 2 :=
        (sq_le_sq₀ (by positivity) (by positivity)).2 hNp
      have hNR : (0 : ℝ) < N := by positivity
      apply (le_div_iff₀ hNR).2
      have hm := mul_le_mul_of_nonneg_left hcoefSq (sq_nonneg s)
      nlinarith
    have htSq : (2 * t) ^ 2 ≤ 200000 * E / N := by
      have hNR : (0 : ℝ) < N := by positivity
      apply (le_div_iff₀ hNR).2
      nlinarith
    have haSq : aRef ^ 2 ≤ 441472 * E / N := by
      have hc := first_difference_sq_le (s * (N + 5 : ℝ)) (-2 * t)
      have hc' : aRef ^ 2 ≤
          2 * ((s * (N + 5 : ℝ)) ^ 2 + (2 * t) ^ 2) := by
        dsimp [aRef]
        nlinarith
      calc
        _ ≤ 2 * ((s * (N + 5 : ℝ)) ^ 2 + (2 * t) ^ 2) := hc'
        _ ≤ 2 * (20736 * E / N + 200000 * E / N) := by gcongr
        _ = 441472 * E / N := by ring
    have hsmallR : E / (N : ℝ) < 1 / 1000000000000 := by
      have hNR : (0 : ℝ) < N := by positivity
      apply (div_lt_iff₀ hNR).2
      nlinarith
    have haSmall : aRef ^ 2 < (1 / 4 : ℝ) ^ 2 := by
      calc
        _ ≤ 441472 * E / N := haSq
        _ < 441472 * (1 / 1000000000000 : ℝ) := by
          have hm := mul_lt_mul_of_pos_left hsmallR (by norm_num : (0 : ℝ) < 441472)
          simpa [div_eq_mul_inv, mul_assoc] using hm
        _ < (1 / 4 : ℝ) ^ 2 := by norm_num
    have habs2 : |aRef| ^ 2 < (1 / 4 : ℝ) ^ 2 := by
      rw [sq_abs]
      exact haSmall
    exact (sq_lt_sq₀ (abs_nonneg _) (by norm_num)).mp habs2 |>.le
  have hRefSmall : 128 * (4 * E1) < (N + 1 : ℕ) := by
    push_cast
    nlinarith
  have hRefLocal : ((N + 1 : ℕ) : ℝ) * |aRef| < 1 := by
    by_cases hz : aRef = 0
    · simp [hz]
    · apply linearPhase_small_energy_forces_local (N + 1) aRef bRef mRef
        (by omega) (abs_pos.mpr hz) hRefQuarter
      calc
        128 * (∑ q ∈ Finset.range (N + 1),
          (bRef + aRef * (q : ℝ) - (mRef q : ℝ) * Real.pi) ^ 2) ≤
            128 * (4 * E1) := by gcongr
        _ < (N + 1 : ℕ) := hRefSmall
  have hRefScaled : (N : ℝ) ^ 3 * aRef ^ 2 ≤ 4608 * E := by
    have h := linearPhase_local_slope_energy (N + 1) aRef bRef mRef
      (by omega) hRefLocal
    have hNpow : (N : ℝ) ^ 3 ≤ ((N + 1 : ℕ) : ℝ) ^ 3 := by
      gcongr
      push_cast
      omega
    calc
      _ ≤ ((N + 1 : ℕ) : ℝ) ^ 3 * aRef ^ 2 :=
        mul_le_mul_of_nonneg_right hNpow (sq_nonneg _)
      _ ≤ 288 * (∑ q ∈ Finset.range (N + 1),
          (bRef + aRef * (q : ℝ) - (mRef q : ℝ) * Real.pi) ^ 2) := h
      _ ≤ 288 * (4 * E1) := by gcongr
      _ ≤ 4608 * E := by nlinarith
  have ht3 : (N : ℝ) ^ 3 * t ^ 2 ≤ 1000000 * E := by
    have hid : 2 * t = -aRef - s * (N + 5 : ℝ) := by dsimp [aRef]; ring
    have hNR12 : (12 : ℝ) ≤ N := by exact_mod_cast hN
    have hNp : (N + 5 : ℝ) ≤ 2 * N := by nlinarith
    have hcoefSq : (N + 5 : ℝ) ^ 2 ≤ (2 * N : ℝ) ^ 2 :=
      (sq_le_sq₀ (by positivity) (by positivity)).2 hNp
    have hsterm : (N : ℝ) ^ 3 * (s * (N + 5 : ℝ)) ^ 2 ≤
        4 * ((N : ℝ) ^ 5 * s ^ 2) := by
      have hm := mul_le_mul_of_nonneg_left hcoefSq
        (mul_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ 3) (sq_nonneg s))
      nlinarith
    have htwo : (2 * t) ^ 2 ≤
        2 * ((-aRef) ^ 2 + (s * (N + 5 : ℝ)) ^ 2) := by
      rw [hid]
      convert first_difference_sq_le (s * (N + 5 : ℝ)) (-aRef) using 1 <;> ring
    have hscaledTwo : (N : ℝ) ^ 3 * (2 * t) ^ 2 ≤
        2 * ((N : ℝ) ^ 3 * aRef ^ 2 +
          (N : ℝ) ^ 3 * (s * (N + 5 : ℝ)) ^ 2) := by
      calc
        _ ≤ (N : ℝ) ^ 3 *
            (2 * ((-aRef) ^ 2 + (s * (N + 5 : ℝ)) ^ 2)) :=
          mul_le_mul_of_nonneg_left htwo (by positivity)
        _ = _ := by ring
    nlinarith [hscaledTwo, hs5]
  exact ⟨hs5, ht3⟩

end Erdos521
