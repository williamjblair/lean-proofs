import Mathlib

/-!
Demonstration that the k=5 tight-window pinning lemma (Lemma B of
compute/theory/k5_third_row_note.md) is Lean-provable with elementary tactics.

`4A⁵ ≤ (A+d)⁵` says `A ≤ c·d` and `(B+d+4)⁵ ≤ 4(B+4)⁵` says `c·d ≤ B+4`
for `c = 1/(4^{1/5}-1)`; together they must force `A ≤ B+4`, with no real
numbers appearing anywhere.
-/

theorem k_five_window_pin {d A B : ℕ}
    (h1 : 4 * A ^ 5 ≤ (A + d) ^ 5)
    (h2 : (B + d + 4) ^ 5 ≤ 4 * (B + 4) ^ 5) :
    A ≤ B + 4 := by
  by_contra hnot
  have hBA : B + 5 ≤ A := by omega
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · -- d = 0: h1 gives 4A⁵ ≤ A⁵, so A = 0, contradicting B + 5 ≤ A.
    subst hd0
    simp only [Nat.add_zero] at h1
    have hA5 : A ^ 5 = 0 := by omega
    have hA0 : A = 0 := by
      exact pow_eq_zero_iff (by norm_num) |>.mp hA5
    omega
  · -- cross-multiplication: (A+d)(B+4) < (B+4+d)A since d(A-B-4) > 0
    have hcross : (A + d) * (B + 4) < (B + 4 + d) * A := by nlinarith
    have hpow : ((A + d) * (B + 4)) ^ 5 < ((B + 4 + d) * A) ^ 5 :=
      Nat.pow_lt_pow_left hcross (by norm_num)
    have hchain : 4 * A ^ 5 * (B + 4) ^ 5 ≤ (A + d) ^ 5 * (B + 4) ^ 5 :=
      Nat.mul_le_mul_right _ h1
    have hfinal : 4 * (B + 4) ^ 5 * A ^ 5 < (B + 4 + d) ^ 5 * A ^ 5 := by
      calc 4 * (B + 4) ^ 5 * A ^ 5 = 4 * A ^ 5 * (B + 4) ^ 5 := by ring
        _ ≤ (A + d) ^ 5 * (B + 4) ^ 5 := hchain
        _ = ((A + d) * (B + 4)) ^ 5 := by ring
        _ < ((B + 4 + d) * A) ^ 5 := hpow
        _ = (B + 4 + d) ^ 5 * A ^ 5 := by ring
    have hlt : 4 * (B + 4) ^ 5 < (B + 4 + d) ^ 5 :=
      Nat.lt_of_mul_lt_mul_right hfinal
    have h2' : (B + d + 4) ^ 5 = (B + 4 + d) ^ 5 := by ring
    rw [h2'] at h2
    exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt h2 hlt)

/-- At most 5 consecutive candidates: two window integers differ by ≤ 4. -/
theorem k_five_window_width {d A B : ℕ}
    (h1A : 4 * A ^ 5 ≤ (A + d) ^ 5) (h2A : (A + d + 4) ^ 5 ≤ 4 * (A + 4) ^ 5)
    (h1B : 4 * B ^ 5 ≤ (B + d) ^ 5) (h2B : (B + d + 4) ^ 5 ≤ 4 * (B + 4) ^ 5) :
    A ≤ B + 4 ∧ B ≤ A + 4 :=
  ⟨k_five_window_pin h1A h2B, k_five_window_pin h1B h2A⟩
