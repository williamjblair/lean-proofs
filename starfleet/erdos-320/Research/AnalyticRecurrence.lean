import Research.SmoothLcm

/-!
# Logarithmic form of the exact upper recurrence
-/

namespace Research

/-- There is always at least the empty reciprocal subset sum. -/
theorem S_pos (N : ℕ) : 0 < S N := by
  rw [S]
  apply Finset.card_pos.mpr
  refine ⟨0, ?_⟩
  rw [reciprocalSubsetSums, Finset.mem_image]
  refine ⟨∅, by simp, ?_⟩
  simp [reciprocalSubsetSum]

/-- The logarithm of the common-denominator factor has the required
`O(log N + Q + sqrt N)` bound. -/
theorem log_commonFactor_le (N Q : ℕ) (hN : 1 ≤ N) :
    Real.log (N * smoothCommonDenominator N Q + 1 : ℕ) ≤
      Real.log 2 + Real.log N +
        (Real.log 4 + 4) * Q + 2 * (Real.log 4 + 4) * N.sqrt := by
  let L := smoothCommonDenominator N Q
  change Real.log ((N * L + 1 : ℕ) : ℝ) ≤ _
  have hL : 0 < L := by
    exact Nat.mul_pos (Nat.lcmUpto_pos Q) (pow_pos (Nat.lcmUpto_pos N.sqrt) 2)
  have hNL : 1 ≤ N * L := Nat.mul_pos hN hL
  have hnat : N * L + 1 ≤ 2 * (N * L) := by omega
  have hpos : (0 : ℝ) < (N * L + 1 : ℕ) := by positivity
  have hcast : ((N * L + 1 : ℕ) : ℝ) ≤ ((2 * (N * L) : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hlog := Real.log_le_log hpos hcast
  have hNq : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hN))
  have hLq : (L : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hL)
  norm_num only [Nat.cast_mul] at hlog
  rw [Real.log_mul (by norm_num) (mul_ne_zero hNq hLq),
    Real.log_mul hNq hLq] at hlog
  have hLlog := log_smoothCommonDenominator_le N Q
  dsimp [L] at hlog
  linarith

/-- Taking exact real logarithms in F-006 gives an additive recurrence. -/
theorem logS_le_logCommonFactor_add_primeSum (N Q : ℕ)
    (hNQ : N ≤ Q * Q) :
    logS N ≤ Real.log (N * smoothCommonDenominator N Q + 1 : ℕ) +
      ∑ p ∈ largePrimes N Q, logS (N / p) := by
  let A := N * smoothCommonDenominator N Q + 1
  let P := ∏ p ∈ largePrimes N Q, S (N / p)
  have hnat : S N ≤ A * P :=
    S_le_commonFactor_mul_primeProduct N Q hNQ
  have hSpos : (0 : ℝ) < S N := by exact_mod_cast S_pos N
  have hApos : (0 : ℝ) < A := by
    exact_mod_cast (by dsimp [A]; omega : 0 < A)
  have hPpos : (0 : ℝ) < P := by
    exact_mod_cast (Finset.prod_pos (fun p hp => S_pos (N / p)))
  have hcast : (S N : ℝ) ≤ (A : ℝ) * (P : ℝ) := by
    exact_mod_cast hnat
  have hlog := Real.log_le_log hSpos hcast
  rw [Real.log_mul hApos.ne' hPpos.ne'] at hlog
  have hprodCast :
      (P : ℝ) = ∏ p ∈ largePrimes N Q, (S (N / p) : ℝ) := by
    simp [P]
  rw [hprodCast, Real.log_prod] at hlog
  · simpa [logS, A] using hlog
  · intro p hp
    exact_mod_cast (Nat.ne_of_gt (S_pos (N / p)))

/-- Explicit logarithmic large-prime recurrence, ready for the prime-bin and
renewal estimates. -/
theorem logS_le_error_add_primeSum (N Q : ℕ)
    (hN : 1 ≤ N) (hNQ : N ≤ Q * Q) :
    logS N ≤ Real.log 2 + Real.log N +
      (Real.log 4 + 4) * Q + 2 * (Real.log 4 + 4) * N.sqrt +
        ∑ p ∈ largePrimes N Q, logS (N / p) := by
  calc
    logS N ≤ Real.log (N * smoothCommonDenominator N Q + 1 : ℕ) +
        ∑ p ∈ largePrimes N Q, logS (N / p) :=
      logS_le_logCommonFactor_add_primeSum N Q hNQ
    _ ≤ (Real.log 2 + Real.log N +
          (Real.log 4 + 4) * Q + 2 * (Real.log 4 + 4) * N.sqrt) +
        ∑ p ∈ largePrimes N Q, logS (N / p) :=
      add_le_add (log_commonFactor_le N Q hN) (le_refl _)
    _ = _ := by ring

end Research
