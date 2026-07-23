import Research.SparseExponentBound

/-!
# Elementary polynomial-polylog upper bound for the sparse cutoff
-/

namespace Research

/-- A direct linear-times-log upper bound for the common prime scale. -/
theorem binaryPrimeScale_le_linear_log {n : ℕ} (hn : 0 < n) :
    binaryPrimeScale n ≤ 256 * n * (Nat.log 2 n + 1) := by
  let r := Nat.log 2 n + 1
  have hp0 := Nat.pow_log_le_self 2 (Nat.ne_of_gt hn)
  have hp : 2 ^ r ≤ 2 * n := by
    dsimp [r]
    rw [pow_succ]
    simpa [Nat.mul_comm] using Nat.mul_le_mul_right 2 hp0
  unfold binaryPrimeScale
  calc
    128 * r * 2 ^ r ≤ 128 * r * (2 * n) := Nat.mul_le_mul_left (128 * r) hp
    _ = 256 * n * r := by ring

/-- The exact sparse cutoff is at most a fixed constant times
`(m+1)^2 * sparseLog(m)^4`. -/
theorem sparsePrimeCutoff_le_polynomial_log (m : ℕ) :
    sparsePrimeCutoff m ≤
      (sparseSeedProduct * (256 ^ 3 * 2048 * 2049)) *
        (m + 1) ^ 2 * (sparseLog m) ^ 4 := by
  let r := sparseLog m
  let h := sparseHeight m
  let S := binaryPrimeScale (m + 1)
  let T := binaryPrimeScale h
  have hr : 1 ≤ r := by simp [r, sparseLog]
  have hh : h = 2048 * r := by rfl
  have hS : S ≤ 256 * (m + 1) * r := by
    simpa [S, r, sparseLog] using
      (binaryPrimeScale_le_linear_log (n := m + 1) (by omega))
  have hlogh : Nat.log 2 h + 1 ≤ 2049 * r := by
    have hlog := Nat.log_le_self 2 h
    rw [hh] at hlog ⊢
    nlinarith
  have hT0 := binaryPrimeScale_le_linear_log (n := h) (sparseHeight_pos m)
  have hT : T ≤ 256 * (2048 * r) * (2049 * r) := by
    calc
      T ≤ 256 * h * (Nat.log 2 h + 1) := hT0
      _ ≤ 256 * h * (2049 * r) := Nat.mul_le_mul_left (256 * h) hlogh
      _ = 256 * (2048 * r) * (2049 * r) := by rw [hh]
  unfold sparsePrimeCutoff sparseLateScale
  have hmul := Nat.mul_le_mul (Nat.mul_le_mul hS hS) hT
  calc
    sparseSeedProduct * (S ^ 2 * T) ≤
        sparseSeedProduct *
          ((256 * (m + 1) * r) ^ 2 *
            (256 * (2048 * r) * (2049 * r))) := by
      apply Nat.mul_le_mul_left
      simpa [pow_two] using hmul
    _ = sparseSeedProduct * (256 ^ 3 * 2048 * 2049) *
          (m + 1) ^ 2 * r ^ 4 := by ring

end Research
