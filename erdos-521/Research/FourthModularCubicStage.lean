import Research.FourthModularQuadraticStage
import Mathlib.Tactic

open scoped BigOperators

namespace Erdos521

/-- A fixed lag of the old cubic fourth phase. -/
noncomputable def fourthOldLagPhase (s t : ℝ) (L q : ℕ) : ℝ :=
  fourthOldPolynomialPhase (q + L) s t - fourthOldPolynomialPhase q s t

/-- Integer representatives induced by a fixed lag. -/
def fourthOldLagIndex (m : ℕ → ℤ) (L q : ℕ) : ℤ := m (q + L) - m q

/-- Two fixed lags turn the old cubic phase into an explicit linear phase. -/
lemma fourthOldLagPhase_nested_lag (s t : ℝ) (q L M : ℕ) :
    fourthOldLagPhase s t L (q + M) - fourthOldLagPhase s t L q =
      (s * (L : ℝ) * (M : ℝ)) * (q : ℝ) +
        (s * (L : ℝ) * (M : ℝ) * (L + M + 4 : ℝ) / 2 +
          t * (L : ℝ) * (M : ℝ)) := by
  unfold fourthOldLagPhase fourthOldPolynomialPhase
  simp_rw [fourthCoefficientA_formula, fourthCoefficientB_formula]
  push_cast
  ring

/-- Reflecting a lagged cubic phase gives a line whose slope detects
`L * (s(K+L+4)+2t)`. -/
lemma fourthOldLagPhase_reflect (s t : ℝ) (L : ℕ) {q K : ℕ} (hq : q ≤ K) :
    fourthOldLagPhase s t L (K - q) - fourthOldLagPhase s t L q =
      (-(L : ℝ) * (s * (K + L + 4 : ℝ) + 2 * t)) * (q : ℝ) +
        ((L : ℝ) * (K : ℝ) * (s * (K + L + 4 : ℝ) + 2 * t) / 2) := by
  unfold fourthOldLagPhase fourthOldPolynomialPhase
  simp_rw [fourthCoefficientA_formula, fourthCoefficientB_formula]
  push_cast
  rw [Nat.cast_sub hq]
  ring

set_option maxHeartbeats 8000000 in
/-- Tiny old-phase modular energy forces both cubic coefficients to their natural covariance
scales. This is the final de-aliasing stage. -/
lemma fourth_modular_cubic_stage (N : ℕ) (s t : ℝ) (m : ℕ → ℤ)
    (hN : 20 ≤ N) (hs : |s| ≤ Real.pi / 2) (ht : |t| ≤ Real.pi / 2)
    (hsmall : 100000000000000000000 * (∑ q ∈ Finset.range (N + 3),
      (fourthOldPolynomialPhase q s t - (m q : ℝ) * Real.pi) ^ 2) < N) :
    (N : ℝ) ^ 7 * s ^ 2 ≤
      30000000 * ∑ q ∈ Finset.range (N + 3),
        (fourthOldPolynomialPhase q s t - (m q : ℝ) * Real.pi) ^ 2 ∧
    (N : ℝ) ^ 5 * t ^ 2 ≤
      100000000 * ∑ q ∈ Finset.range (N + 3),
        (fourthOldPolynomialPhase q s t - (m q : ℝ) * Real.pi) ^ 2 := by
  let E : ℝ := ∑ q ∈ Finset.range (N + 3),
    (fourthOldPolynomialPhase q s t - (m q : ℝ) * Real.pi) ^ 2
  have hE0 : 0 ≤ E := Finset.sum_nonneg fun q hq ↦ sq_nonneg _
  have hsmallR : E / (N : ℝ) < 1 / 100000000000000000000 := by
    have hNR : (0 : ℝ) < N := by positivity
    apply (div_lt_iff₀ hNR).2
    nlinarith
  have hquadSmall : 1000000000000 * (∑ q ∈ Finset.range (N + 3),
      (fourthOldPolynomialPhase q s t - (m q : ℝ) * Real.pi) ^ 2) < N := by
    nlinarith
  have hquad := fourth_modular_quadratic_stage N s t m (by omega) hs ht hquadSmall
  have hs5 : (N : ℝ) ^ 5 * s ^ 2 ≤ 400000 * E := hquad.1
  have ht3 : (N : ℝ) ^ 3 * t ^ 2 ≤ 1000000 * E := hquad.2

  let L : ℕ := N / 4
  let D : ℕ := N + 3 - L
  let R : ℕ := D - L
  let K : ℕ := N + 2 - L
  let mLag : ℕ → ℤ := fun q ↦ fourthOldLagIndex m L q
  let mNested : ℕ → ℤ := fun q ↦ mLag (q + L) - mLag q
  have hLN : L ≤ N := by dsimp [L]; omega
  have hLT : L ≤ N + 3 := by omega
  have hLD : L ≤ D := by dsimp [D, L]; omega
  have hKD : K + 1 = D := by dsimp [K, D, L]; omega
  have hLlower : (N : ℝ) / 5 ≤ (L : ℝ) := by
    have hc : N ≤ 5 * L := by dsimp [L]; omega
    have hcR : (N : ℝ) ≤ 5 * (L : ℝ) := by exact_mod_cast hc
    linarith
  have hLupper : (L : ℝ) ≤ N := by exact_mod_cast hLN
  have hDlower : (N : ℝ) / 2 ≤ (D : ℝ) := by
    have hc : N ≤ 2 * D := by dsimp [D, L]; omega
    have hcR : (N : ℝ) ≤ 2 * (D : ℝ) := by exact_mod_cast hc
    linarith
  have hRlower : (N : ℝ) / 2 ≤ (R : ℝ) := by
    have hc : N ≤ 2 * R := by dsimp [R, D, L]; omega
    have hcR : (N : ℝ) ≤ 2 * (R : ℝ) := by exact_mod_cast hc
    linarith
  have hDtwo : 2 ≤ D := by dsimp [D, L]; omega
  have hRtwo : 2 ≤ R := by dsimp [R, D, L]; omega

  have hLagEnergy : (∑ q ∈ Finset.range D,
      (fourthOldLagPhase s t L q - (mLag q : ℝ) * Real.pi) ^ 2) ≤ 4 * E := by
    have h := modular_lag_difference_energy
      (fun q ↦ fourthOldPolynomialPhase q s t) m (N + 3) L hLT
    dsimp [D, mLag, fourthOldLagIndex, fourthOldLagPhase]
    convert h using 1
    apply Finset.sum_congr rfl
    intro q hq
    push_cast
    rfl

  let aNested : ℝ := s * (L : ℝ) * (L : ℝ)
  let bNested : ℝ :=
    s * (L : ℝ) * (L : ℝ) * (L + L + 4 : ℝ) / 2 +
      t * (L : ℝ) * (L : ℝ)
  have hNestedEnergy : (∑ q ∈ Finset.range R,
      (bNested + aNested * (q : ℝ) - (mNested q : ℝ) * Real.pi) ^ 2) ≤
      16 * E := by
    have h := modular_lag_difference_energy
      (fourthOldLagPhase s t L) mLag D L hLD
    have hform : (∑ q ∈ Finset.range R,
        (bNested + aNested * (q : ℝ) - (mNested q : ℝ) * Real.pi) ^ 2) ≤
        4 * ∑ q ∈ Finset.range D,
          (fourthOldLagPhase s t L q - (mLag q : ℝ) * Real.pi) ^ 2 := by
      dsimp [R, aNested, bNested, mNested]
      convert h using 1
      apply Finset.sum_congr rfl
      intro q hq
      rw [fourthOldLagPhase_nested_lag]
      push_cast
      congr 1
      ring
    exact hform.trans (by nlinarith)

  have hNestedQuarter : |aNested| ≤ 1 / 4 := by
    have hL4 : (L : ℝ) ^ 4 ≤ (N : ℝ) ^ 4 :=
      pow_le_pow_left₀ (by positivity) hLupper 4
    have haMul : aNested ^ 2 * (N : ℝ) ≤ (N : ℝ) ^ 5 * s ^ 2 := by
      calc
        aNested ^ 2 * (N : ℝ) = ((N : ℝ) * s ^ 2) * (L : ℝ) ^ 4 := by
          dsimp [aNested]
          ring
        _ ≤ ((N : ℝ) * s ^ 2) * (N : ℝ) ^ 4 :=
          mul_le_mul_of_nonneg_left hL4 (by positivity)
        _ = (N : ℝ) ^ 5 * s ^ 2 := by ring
    have hNR : (0 : ℝ) < N := by positivity
    have haSq : aNested ^ 2 ≤ 400000 * E / N := by
      apply (le_div_iff₀ hNR).2
      nlinarith
    have haSmall : aNested ^ 2 < (1 / 4 : ℝ) ^ 2 := by
      calc
        _ ≤ 400000 * E / N := haSq
        _ < 400000 * (1 / 100000000000000000000 : ℝ) := by
          have hm := mul_lt_mul_of_pos_left hsmallR
            (by norm_num : (0 : ℝ) < 400000)
          simpa [div_eq_mul_inv, mul_assoc] using hm
        _ < (1 / 4 : ℝ) ^ 2 := by norm_num
    have habs : |aNested| ^ 2 < (1 / 4 : ℝ) ^ 2 := by
      rw [sq_abs]
      exact haSmall
    exact (sq_lt_sq₀ (abs_nonneg _) (by norm_num)).mp habs |>.le
  have hNestedSmall : 128 * (∑ q ∈ Finset.range R,
      (bNested + aNested * (q : ℝ) - (mNested q : ℝ) * Real.pi) ^ 2) < R := by
    have hNR : (0 : ℝ) < N := by positivity
    have hC : (2048 : ℝ) < 100000000000000000000 := by norm_num
    have hEN : 2048 * E < (N : ℝ) := by nlinarith
    nlinarith
  have hNestedLocal : (R : ℝ) * |aNested| < 1 := by
    by_cases hz : aNested = 0
    · simp [hz]
    · apply linearPhase_small_energy_forces_local R aNested bNested mNested
        (by omega) (abs_pos.mpr hz) hNestedQuarter hNestedSmall
  have hNestedScaled : (R : ℝ) ^ 3 * aNested ^ 2 ≤ 4608 * E := by
    have h := linearPhase_local_slope_energy R aNested bNested mNested hRtwo hNestedLocal
    exact h.trans (by nlinarith [hNestedEnergy])
  have hs7 : (N : ℝ) ^ 7 * s ^ 2 ≤ 30000000 * E := by
    have hR3 : ((N : ℝ) / 2) ^ 3 ≤ (R : ℝ) ^ 3 :=
      pow_le_pow_left₀ (by positivity) hRlower 3
    have hL4 : ((N : ℝ) / 5) ^ 4 ≤ (L : ℝ) ^ 4 :=
      pow_le_pow_left₀ (by positivity) hLlower 4
    have hbase : ((N : ℝ) / 2) ^ 3 * ((N : ℝ) / 5) ^ 4 * s ^ 2 ≤
        (R : ℝ) ^ 3 * aNested ^ 2 := by
      calc
        _ ≤ (R : ℝ) ^ 3 * ((N : ℝ) / 5) ^ 4 * s ^ 2 := by gcongr
        _ ≤ (R : ℝ) ^ 3 * (L : ℝ) ^ 4 * s ^ 2 := by gcongr
        _ = _ := by dsimp [aNested]; ring
    have hbase' : (N : ℝ) ^ 7 * s ^ 2 / 5000 ≤
        (R : ℝ) ^ 3 * aNested ^ 2 := by
      convert hbase using 1 <;> ring
    nlinarith

  let combo : ℝ := s * (N + 6 : ℝ) + 2 * t
  let aRef : ℝ := -(L : ℝ) * combo
  let bRef : ℝ := (L : ℝ) * (K : ℝ) * combo / 2
  let mRef : ℕ → ℤ := fun q ↦ mLag (K - q) - mLag q
  have hRefEnergy : (∑ q ∈ Finset.range D,
      (bRef + aRef * (q : ℝ) - (mRef q : ℝ) * Real.pi) ^ 2) ≤ 16 * E := by
    have h := modular_reflection_difference_energy
      (fourthOldLagPhase s t L) mLag K D (by omega)
    have hform : (∑ q ∈ Finset.range D,
        (bRef + aRef * (q : ℝ) - (mRef q : ℝ) * Real.pi) ^ 2) ≤
        4 * ∑ q ∈ Finset.range (K + 1),
          (fourthOldLagPhase s t L q - (mLag q : ℝ) * Real.pi) ^ 2 := by
      dsimp [aRef, bRef, combo, mRef]
      convert h using 1
      · apply Finset.sum_congr rfl
        intro q hq
        have hqK : q ≤ K := by
          have hqD := Finset.mem_range.mp hq
          omega
        rw [fourthOldLagPhase_reflect s t L hqK]
        push_cast
        congr 1
        have hsum : K + L + 4 = N + 6 := by dsimp [K, L]; omega
        have hsumR : (K : ℝ) + (L : ℝ) + 4 = (N : ℝ) + 6 := by
          exact_mod_cast hsum
        rw [hsumR]
        ring
    exact hform.trans (by rw [hKD]; nlinarith [hLagEnergy])

  have hNp : (N + 6 : ℝ) ≤ 2 * N := by
    have hNR20 : (20 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  have hRefQuarter : |aRef| ≤ 1 / 4 := by
    have hNpSq : (N + 6 : ℝ) ^ 2 ≤ (2 * N : ℝ) ^ 2 :=
      (sq_le_sq₀ (by positivity) (by positivity)).2 hNp
    have hsTermMul : ((L : ℝ) * s * (N + 6 : ℝ)) ^ 2 * (N : ℝ) ≤
        4 * ((N : ℝ) ^ 5 * s ^ 2) := by
      have hL2 : (L : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hLupper 2
      calc
        _ = ((N : ℝ) * s ^ 2) * (L : ℝ) ^ 2 * (N + 6 : ℝ) ^ 2 := by ring
        _ ≤ ((N : ℝ) * s ^ 2) * (N : ℝ) ^ 2 * (N + 6 : ℝ) ^ 2 := by
          gcongr
        _ ≤ ((N : ℝ) * s ^ 2) * (N : ℝ) ^ 2 * (2 * N : ℝ) ^ 2 := by
          gcongr
        _ = 4 * ((N : ℝ) ^ 5 * s ^ 2) := by ring
    have htTermMul : ((L : ℝ) * (2 * t)) ^ 2 * (N : ℝ) ≤
        4 * ((N : ℝ) ^ 3 * t ^ 2) := by
      have hL2 : (L : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hLupper 2
      calc
        _ = 4 * ((N : ℝ) * t ^ 2) * (L : ℝ) ^ 2 := by ring
        _ ≤ 4 * ((N : ℝ) * t ^ 2) * (N : ℝ) ^ 2 := by gcongr
        _ = 4 * ((N : ℝ) ^ 3 * t ^ 2) := by ring
    have hNR : (0 : ℝ) < N := by positivity
    have hsTermSq : ((L : ℝ) * s * (N + 6 : ℝ)) ^ 2 ≤ 1600000 * E / N := by
      apply (le_div_iff₀ hNR).2
      nlinarith
    have htTermSq : ((L : ℝ) * (2 * t)) ^ 2 ≤ 4000000 * E / N := by
      apply (le_div_iff₀ hNR).2
      nlinarith
    have haSq : aRef ^ 2 ≤ 11200000 * E / N := by
      have hc := first_difference_sq_le
        ((L : ℝ) * s * (N + 6 : ℝ)) (-((L : ℝ) * (2 * t)))
      have hc' : aRef ^ 2 ≤ 2 *
          (((L : ℝ) * s * (N + 6 : ℝ)) ^ 2 +
            ((L : ℝ) * (2 * t)) ^ 2) := by
        dsimp [aRef, combo]
        nlinarith
      calc
        _ ≤ 2 * (((L : ℝ) * s * (N + 6 : ℝ)) ^ 2 +
            ((L : ℝ) * (2 * t)) ^ 2) := hc'
        _ ≤ 2 * (1600000 * E / N + 4000000 * E / N) := by gcongr
        _ = 11200000 * E / N := by ring
    have haSmall : aRef ^ 2 < (1 / 4 : ℝ) ^ 2 := by
      calc
        _ ≤ 11200000 * E / N := haSq
        _ < 11200000 * (1 / 100000000000000000000 : ℝ) := by
          have hm := mul_lt_mul_of_pos_left hsmallR
            (by norm_num : (0 : ℝ) < 11200000)
          simpa [div_eq_mul_inv, mul_assoc] using hm
        _ < (1 / 4 : ℝ) ^ 2 := by norm_num
    have habs : |aRef| ^ 2 < (1 / 4 : ℝ) ^ 2 := by
      rw [sq_abs]
      exact haSmall
    exact (sq_lt_sq₀ (abs_nonneg _) (by norm_num)).mp habs |>.le
  have hRefSmall : 128 * (∑ q ∈ Finset.range D,
      (bRef + aRef * (q : ℝ) - (mRef q : ℝ) * Real.pi) ^ 2) < D := by
    have hEN : 2048 * E < (N : ℝ) := by nlinarith
    nlinarith
  have hRefLocal : (D : ℝ) * |aRef| < 1 := by
    by_cases hz : aRef = 0
    · simp [hz]
    · apply linearPhase_small_energy_forces_local D aRef bRef mRef
        (by omega) (abs_pos.mpr hz) hRefQuarter hRefSmall
  have hRefScaled : (D : ℝ) ^ 3 * aRef ^ 2 ≤ 4608 * E := by
    have h := linearPhase_local_slope_energy D aRef bRef mRef hDtwo hRefLocal
    exact h.trans (by nlinarith [hRefEnergy])
  have hcombo5 : (N : ℝ) ^ 5 * combo ^ 2 ≤ 1000000 * E := by
    have hD3 : ((N : ℝ) / 2) ^ 3 ≤ (D : ℝ) ^ 3 :=
      pow_le_pow_left₀ (by positivity) hDlower 3
    have hL2 : ((N : ℝ) / 5) ^ 2 ≤ (L : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hLlower 2
    have hbase : ((N : ℝ) / 2) ^ 3 * ((N : ℝ) / 5) ^ 2 * combo ^ 2 ≤
        (D : ℝ) ^ 3 * aRef ^ 2 := by
      calc
        _ ≤ (D : ℝ) ^ 3 * ((N : ℝ) / 5) ^ 2 * combo ^ 2 := by gcongr
        _ ≤ (D : ℝ) ^ 3 * (L : ℝ) ^ 2 * combo ^ 2 := by gcongr
        _ = _ := by dsimp [aRef]; ring
    have hbase' : (N : ℝ) ^ 5 * combo ^ 2 / 200 ≤
        (D : ℝ) ^ 3 * aRef ^ 2 := by
      convert hbase using 1 <;> ring
    nlinarith
  have ht5 : (N : ℝ) ^ 5 * t ^ 2 ≤ 100000000 * E := by
    have hNpSq : (N + 6 : ℝ) ^ 2 ≤ (2 * N : ℝ) ^ 2 :=
      (sq_le_sq₀ (by positivity) (by positivity)).2 hNp
    have hsTerm : (N : ℝ) ^ 5 * (s * (N + 6 : ℝ)) ^ 2 ≤
        4 * ((N : ℝ) ^ 7 * s ^ 2) := by
      have hm := mul_le_mul_of_nonneg_left hNpSq
        (mul_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ 5) (sq_nonneg s))
      nlinarith
    have htwo : (2 * t) ^ 2 ≤ 2 * (combo ^ 2 + (s * (N + 6 : ℝ)) ^ 2) := by
      have hc := first_difference_sq_le (s * (N + 6 : ℝ)) combo
      have hid : 2 * t = combo - s * (N + 6 : ℝ) := by dsimp [combo]; ring
      rw [hid]
      simpa [add_comm] using hc
    have hscaledTwo : (N : ℝ) ^ 5 * (2 * t) ^ 2 ≤
        2 * ((N : ℝ) ^ 5 * combo ^ 2 +
          (N : ℝ) ^ 5 * (s * (N + 6 : ℝ)) ^ 2) := by
      calc
        _ ≤ (N : ℝ) ^ 5 *
            (2 * (combo ^ 2 + (s * (N + 6 : ℝ)) ^ 2)) :=
          mul_le_mul_of_nonneg_left htwo (by positivity)
        _ = _ := by ring
    nlinarith
  exact ⟨hs7, ht5⟩

end Erdos521
