import Research.LatticeLens

namespace Erdos959

/-- Integer radius used for a target odd squared distance `s`. -/
def blockRadius (s : ℕ) : ℕ := (s / 2).sqrt

lemma blockRadius_ge_thirtyTwo (s : ℕ) (hs : 2049 ≤ s) :
    32 ≤ blockRadius s := by
  apply Nat.le_sqrt'.mpr
  apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2
  norm_num [blockRadius]
  omega

lemma blockRadius_sq_bounds
    (s : ℕ) (hs : 2049 ≤ s) (hodd : s % 2 = 1) :
    2 * blockRadius s ^ 2 < s ∧
      4 * s ≤ 9 * blockRadius s ^ 2 := by
  let m := s / 2
  let R := blockRadius s
  have hR : 32 ≤ R := blockRadius_ge_thirtyTwo s hs
  have hlow : R ^ 2 ≤ m := by
    exact Nat.sqrt_le' m
  have hupp : m < (R + 1) ^ 2 := by
    simpa [R, blockRadius, m] using Nat.lt_succ_sqrt' m
  have hdecomp : 2 * m + 1 = s := by
    have hd := Nat.div_add_mod s 2
    rw [hodd] at hd
    simpa [m] using hd
  constructor
  · change 2 * R ^ 2 < s
    omega
  · change 4 * s ≤ 9 * R ^ 2
    have hRR : 32 * R ≤ R ^ 2 := by
      simpa [pow_two] using Nat.mul_le_mul_right R hR
    nlinarith

lemma blockRadius_real_target_window
    (s : ℕ) (hs : 2049 ≤ s) (hodd : s % 2 = 1) :
    2 * (blockRadius s : ℝ) ^ 2 < s ∧
      (s : ℝ) ≤ (3 * (blockRadius s : ℝ) / 2) ^ 2 := by
  have h := blockRadius_sq_bounds s hs hodd
  constructor
  · exact_mod_cast h.1
  · have hcast : (4 * s : ℕ) ≤ 9 * blockRadius s ^ 2 := h.2
    have hcastR : (4 * s : ℝ) ≤ 9 * (blockRadius s : ℝ) ^ 2 := by
      exact_mod_cast hcast
    nlinarith

lemma latticeDisk_size_comparable_to_target
    (s : ℕ) (hs : 2049 ≤ s) (hodd : s % 2 = 1) :
    s ≤ 576 * (latticeDisk (blockRadius s)).card ∧
      (latticeDisk (blockRadius s)).card ≤ 5 * s := by
  let R := blockRadius s
  have hR : 32 ≤ R := blockRadius_ge_thirtyTwo s hs
  have hsR : 4 * s ≤ 9 * R ^ 2 := (blockRadius_sq_bounds s hs hodd).2
  have hRdisk : R ^ 2 ≤ 256 * (latticeDisk R).card :=
    latticeDisk_card_lower R hR
  have hdiskUpper := latticeDisk_card_upper R
  have hRlt : 2 * R ^ 2 < s := (blockRadius_sq_bounds s hs hodd).1
  constructor
  · nlinarith
  · have hside : 2 * R + 1 ≤ 3 * R := by omega
    have hsq := Nat.pow_le_pow_left hside 2
    calc
      (latticeDisk R).card ≤ (2 * R + 1) ^ 2 := hdiskUpper
      _ ≤ (3 * R) ^ 2 := hsq
      _ = 9 * R ^ 2 := by ring
      _ ≤ 5 * s := by nlinarith

lemma floor_ratio_balance {Q s : ℕ} (hs : 1 ≤ s) (hQs : s ≤ Q) :
    Q ≤ 2 * (Q / s * s) ∧ Q / s * s ≤ Q := by
  have hc : 1 ≤ Q / s := (Nat.le_div_iff_mul_le (by omega : 0 < s)).2 (by simpa using hQs)
  have hmod : Q % s < s := Nat.mod_lt Q (by omega)
  have hdecomp : s * (Q / s) + Q % s = Q := Nat.div_add_mod Q s
  constructor
  · nlinarith
  · exact Nat.div_mul_le_self Q s

end Erdos959
