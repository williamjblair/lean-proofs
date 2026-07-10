/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686ConstantQuotient

/-!
# Erdős Problem 686: exact ratio-window pinning

The two `N = 4` ratio-window inequalities pin `n + 1` to a band of
exact width `k` at every gap `d`: if `A` satisfies the lower-window
shape `4A^k ≤ (A+d)^k` and `B` satisfies the upper-window shape
`(B+d+k-1)^k ≤ 4(B+k-1)^k`, then `A ≤ B + (k-1)`.  In particular any
two window-compatible values of `n+1` at the same `d` differ by at
most `k - 1`.  Purely elementary: one cross-multiplication and power
monotonicity, no real numbers.

This is the uniform version of the `k = 5` tight-window discovery
(`compute/theory/k5_third_row_note.md`, Lemma B): the earlier banded
certificates used per-`k` rational brackets one continued-fraction
convergent short of this exact width.
-/

namespace Erdos686

namespace Erdos686Variant

/-- **Window pinning.**  Lower-window shape at `A` and upper-window
shape at `B` (with exponent `m + 1` and shift `m = k - 1`) force
`A ≤ B + m`. -/
theorem ratio_window_pin {m d A B : ℕ}
    (h1 : 4 * A ^ (m + 1) ≤ (A + d) ^ (m + 1))
    (h2 : (B + d + m) ^ (m + 1) ≤ 4 * (B + m) ^ (m + 1)) :
    A ≤ B + m := by
  by_contra hnot
  have hBA : B + m + 1 ≤ A := by omega
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · subst hd0
    simp only [Nat.add_zero] at h1
    have hA5 : A ^ (m + 1) = 0 := by omega
    have hA0 : A = 0 := pow_eq_zero_iff (Nat.succ_ne_zero m) |>.mp hA5
    omega
  · have hcross : (A + d) * (B + m) < (B + m + d) * A := by
      nlinarith
    have hpow : ((A + d) * (B + m)) ^ (m + 1)
        < ((B + m + d) * A) ^ (m + 1) :=
      Nat.pow_lt_pow_left hcross (Nat.succ_ne_zero m)
    have hchain : 4 * A ^ (m + 1) * (B + m) ^ (m + 1)
        ≤ (A + d) ^ (m + 1) * (B + m) ^ (m + 1) :=
      Nat.mul_le_mul_right _ h1
    have hfinal : 4 * (B + m) ^ (m + 1) * A ^ (m + 1)
        < (B + m + d) ^ (m + 1) * A ^ (m + 1) := by
      calc 4 * (B + m) ^ (m + 1) * A ^ (m + 1)
          = 4 * A ^ (m + 1) * (B + m) ^ (m + 1) := by ring
        _ ≤ (A + d) ^ (m + 1) * (B + m) ^ (m + 1) := hchain
        _ = ((A + d) * (B + m)) ^ (m + 1) := by rw [mul_pow]
        _ < ((B + m + d) * A) ^ (m + 1) := hpow
        _ = (B + m + d) ^ (m + 1) * A ^ (m + 1) := by rw [mul_pow]
    have hApos : 0 < A ^ (m + 1) := by
      have : 0 < A := by omega
      positivity
    have hlt : 4 * (B + m) ^ (m + 1) < (B + m + d) ^ (m + 1) :=
      Nat.lt_of_mul_lt_mul_right hfinal
    have heq : B + m + d = B + d + m := by ring
    rw [heq] at hlt
    omega

/-- Any two window-compatible values of `n + 1` at the same gap `d`
lie within `k - 1` of each other: the exact band width is `k`. -/
theorem window_band_width {k d n₁ n₂ : ℕ} (hk : 1 ≤ k)
    (hup₁ : (n₁ + d + k) ^ k ≤ 4 * (n₁ + k) ^ k)
    (hlo₂ : 4 * (n₂ + 1) ^ k ≤ (n₂ + d + 1) ^ k) :
    n₂ + 1 ≤ n₁ + k := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have h1 : 4 * (n₂ + 1) ^ (m + 1) ≤ ((n₂ + 1) + d) ^ (m + 1) := by
    have : n₂ + d + 1 = (n₂ + 1) + d := by ring
    rwa [this] at hlo₂
  have h2 : ((n₁ + 1) + d + m) ^ (m + 1) ≤ 4 * ((n₁ + 1) + m) ^ (m + 1) := by
    have e1 : (n₁ + 1) + d + m = n₁ + d + (m + 1) := by ring
    have e2 : (n₁ + 1) + m = n₁ + (m + 1) := by ring
    rw [e1, e2]
    exact hup₁
  have := ratio_window_pin h1 h2
  omega

end Erdos686Variant

end Erdos686
