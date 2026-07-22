import ErdosProblems.Erdos686.Core.CenteredRatioWindow

/-!
# Erdős 686: a sharper centered ratio band

This module tightens the centered equation window with an exact rational
root bracket.  It also records an exact `k=16` counterboundary showing that
the endpoint and centered power windows alone cannot yield `7*k*d<10*n`.
-/

namespace Erdos686
namespace Erdos686Variant

/-- The exact root bracket used for the `23/35` centered ratio.  The proof
keeps the first seven binomial terms and bounds each normalized falling
factor below by its value at `k=16`. -/
lemma four_mul_twenty_five_hundred_k_pow_lt_add_three_six_two_one_pow
    {k : ℕ} (hk : 16 ≤ k) :
    4 * (2500 * k) ^ k < (2500 * k + 3621) ^ k := by
  let x : ℚ := 3621 / (2500 * k)
  have hkq : (16 : ℚ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℚ) < k := by linarith
  have hx0 : (0 : ℚ) ≤ x := by dsimp [x]; positivity
  have h1 : (15 / 16 : ℚ) ≤ ((k : ℚ) - 1) / k := by
    rw [div_le_div_iff₀ (by norm_num : (0 : ℚ) < 16) hkpos]
    linarith
  have h2 : (14 / 16 : ℚ) ≤ ((k : ℚ) - 2) / k := by
    rw [div_le_div_iff₀ (by norm_num : (0 : ℚ) < 16) hkpos]
    linarith
  have h3 : (13 / 16 : ℚ) ≤ ((k : ℚ) - 3) / k := by
    rw [div_le_div_iff₀ (by norm_num : (0 : ℚ) < 16) hkpos]
    linarith
  have h4 : (12 / 16 : ℚ) ≤ ((k : ℚ) - 4) / k := by
    rw [div_le_div_iff₀ (by norm_num : (0 : ℚ) < 16) hkpos]
    linarith
  have h5 : (11 / 16 : ℚ) ≤ ((k : ℚ) - 5) / k := by
    rw [div_le_div_iff₀ (by norm_num : (0 : ℚ) < 16) hkpos]
    linarith
  have hchoose2 : (k.choose 2 : ℚ) = k * (k - 1) / 2 := by
    simpa using (Nat.cast_choose_two ℚ k)
  have hchoose3 : (k.choose 3 : ℚ) = k * (k - 1) * (k - 2) / 6 := by
    have h := Nat.choose_succ_right_eq k 2
    have hcast := congrArg (fun z : ℕ ↦ (z : ℚ)) h
    norm_num [hchoose2, Nat.cast_sub (by omega : 2 ≤ k)] at hcast ⊢
    linarith
  have hchoose4 : (k.choose 4 : ℚ) =
      k * (k - 1) * (k - 2) * (k - 3) / 24 := by
    have h := Nat.choose_succ_right_eq k 3
    have hcast := congrArg (fun z : ℕ ↦ (z : ℚ)) h
    norm_num [hchoose3, Nat.cast_sub (by omega : 3 ≤ k)] at hcast ⊢
    linarith
  have hchoose5 : (k.choose 5 : ℚ) =
      k * (k - 1) * (k - 2) * (k - 3) * (k - 4) / 120 := by
    have h := Nat.choose_succ_right_eq k 4
    have hcast := congrArg (fun z : ℕ ↦ (z : ℚ)) h
    norm_num [hchoose4, Nat.cast_sub (by omega : 4 ≤ k)] at hcast ⊢
    linarith
  have hchoose6 : (k.choose 6 : ℚ) =
      k * (k - 1) * (k - 2) * (k - 3) * (k - 4) * (k - 5) / 720 := by
    have h := Nat.choose_succ_right_eq k 5
    have hcast := congrArg (fun z : ℕ ↦ (z : ℚ)) h
    norm_num [hchoose5, Nat.cast_sub (by omega : 5 ≤ k)] at hcast ⊢
    linarith
  have ht0 : (Nat.choose 16 0 : ℚ) * (3621 / 40000 : ℚ) ^ 0 ≤
      (k.choose 0 : ℚ) * x ^ 0 := by norm_num [Nat.choose]
  have ht1 : (Nat.choose 16 1 : ℚ) * (3621 / 40000 : ℚ) ^ 1 ≤
      (k.choose 1 : ℚ) * x ^ 1 := by
    simp only [Nat.choose_one_right, pow_one]
    dsimp [x]
    field_simp
    norm_num
  have ht2 : (Nat.choose 16 2 : ℚ) * (3621 / 40000 : ℚ) ^ 2 ≤
      (k.choose 2 : ℚ) * x ^ 2 := by
    rw [hchoose2]
    dsimp [x]
    have hy : (0 : ℚ) ≤ (3621 / 2500) ^ 2 / 2 := by positivity
    calc
      (Nat.choose 16 2 : ℚ) * (3621 / 40000 : ℚ) ^ 2 =
          ((3621 / 2500 : ℚ) ^ 2 / 2) * (15 / 16) := by
        norm_num [Nat.choose]
      _ ≤ ((3621 / 2500 : ℚ) ^ 2 / 2) * (((k : ℚ) - 1) / k) :=
        mul_le_mul_of_nonneg_left h1 hy
      _ = (k * (k - 1) / 2) * (3621 / (2500 * k)) ^ 2 := by
        field_simp
  have ht3 : (Nat.choose 16 3 : ℚ) * (3621 / 40000 : ℚ) ^ 3 ≤
      (k.choose 3 : ℚ) * x ^ 3 := by
    rw [hchoose3]
    dsimp [x]
    have hp : (15 / 16 : ℚ) * (14 / 16) ≤
        (((k : ℚ) - 1) / k) * (((k : ℚ) - 2) / k) := by
      gcongr
    have hy : (0 : ℚ) ≤ (3621 / 2500) ^ 3 / 6 := by positivity
    calc
      (Nat.choose 16 3 : ℚ) * (3621 / 40000 : ℚ) ^ 3 =
          ((3621 / 2500 : ℚ) ^ 3 / 6) * ((15 / 16) * (14 / 16)) := by
        norm_num [Nat.choose]
      _ ≤ ((3621 / 2500 : ℚ) ^ 3 / 6) *
          ((((k : ℚ) - 1) / k) * (((k : ℚ) - 2) / k)) :=
        mul_le_mul_of_nonneg_left hp hy
      _ = (k * (k - 1) * (k - 2) / 6) * (3621 / (2500 * k)) ^ 3 := by
        field_simp
  have ht4 : (Nat.choose 16 4 : ℚ) * (3621 / 40000 : ℚ) ^ 4 ≤
      (k.choose 4 : ℚ) * x ^ 4 := by
    rw [hchoose4]
    dsimp [x]
    have hp : (15 / 16 : ℚ) * (14 / 16) * (13 / 16) ≤
        (((k : ℚ) - 1) / k) * (((k : ℚ) - 2) / k) *
          (((k : ℚ) - 3) / k) := by
      gcongr
    have hy : (0 : ℚ) ≤ (3621 / 2500) ^ 4 / 24 := by positivity
    calc
      (Nat.choose 16 4 : ℚ) * (3621 / 40000 : ℚ) ^ 4 =
          ((3621 / 2500 : ℚ) ^ 4 / 24) *
            ((15 / 16) * (14 / 16) * (13 / 16)) := by
        norm_num [Nat.choose]
      _ ≤ ((3621 / 2500 : ℚ) ^ 4 / 24) *
          ((((k : ℚ) - 1) / k) * (((k : ℚ) - 2) / k) *
            (((k : ℚ) - 3) / k)) :=
        mul_le_mul_of_nonneg_left hp hy
      _ = (k * (k - 1) * (k - 2) * (k - 3) / 24) *
          (3621 / (2500 * k)) ^ 4 := by
        field_simp
  have ht5 : (Nat.choose 16 5 : ℚ) * (3621 / 40000 : ℚ) ^ 5 ≤
      (k.choose 5 : ℚ) * x ^ 5 := by
    rw [hchoose5]
    dsimp [x]
    have hp : (15 / 16 : ℚ) * (14 / 16) * (13 / 16) * (12 / 16) ≤
        (((k : ℚ) - 1) / k) * (((k : ℚ) - 2) / k) *
          (((k : ℚ) - 3) / k) * (((k : ℚ) - 4) / k) := by
      gcongr
    have hy : (0 : ℚ) ≤ (3621 / 2500) ^ 5 / 120 := by positivity
    calc
      (Nat.choose 16 5 : ℚ) * (3621 / 40000 : ℚ) ^ 5 =
          ((3621 / 2500 : ℚ) ^ 5 / 120) *
            ((15 / 16) * (14 / 16) * (13 / 16) * (12 / 16)) := by
        norm_num [Nat.choose]
      _ ≤ ((3621 / 2500 : ℚ) ^ 5 / 120) *
          ((((k : ℚ) - 1) / k) * (((k : ℚ) - 2) / k) *
            (((k : ℚ) - 3) / k) * (((k : ℚ) - 4) / k)) :=
        mul_le_mul_of_nonneg_left hp hy
      _ = (k * (k - 1) * (k - 2) * (k - 3) * (k - 4) / 120) *
          (3621 / (2500 * k)) ^ 5 := by
        field_simp
  have ht6 : (Nat.choose 16 6 : ℚ) * (3621 / 40000 : ℚ) ^ 6 ≤
      (k.choose 6 : ℚ) * x ^ 6 := by
    rw [hchoose6]
    dsimp [x]
    have hp : (15 / 16 : ℚ) * (14 / 16) * (13 / 16) * (12 / 16) * (11 / 16) ≤
        (((k : ℚ) - 1) / k) * (((k : ℚ) - 2) / k) *
          (((k : ℚ) - 3) / k) * (((k : ℚ) - 4) / k) *
            (((k : ℚ) - 5) / k) := by
      gcongr
    have hy : (0 : ℚ) ≤ (3621 / 2500) ^ 6 / 720 := by positivity
    calc
      (Nat.choose 16 6 : ℚ) * (3621 / 40000 : ℚ) ^ 6 =
          ((3621 / 2500 : ℚ) ^ 6 / 720) *
            ((15 / 16) * (14 / 16) * (13 / 16) * (12 / 16) * (11 / 16)) := by
        norm_num [Nat.choose]
      _ ≤ ((3621 / 2500 : ℚ) ^ 6 / 720) *
          ((((k : ℚ) - 1) / k) * (((k : ℚ) - 2) / k) *
            (((k : ℚ) - 3) / k) * (((k : ℚ) - 4) / k) *
              (((k : ℚ) - 5) / k)) :=
        mul_le_mul_of_nonneg_left hp hy
      _ = (k * (k - 1) * (k - 2) * (k - 3) * (k - 4) * (k - 5) / 720) *
          (3621 / (2500 * k)) ^ 6 := by
        field_simp
  have hterm : ∀ i ∈ Finset.range 7,
      (Nat.choose 16 i : ℚ) * (3621 / 40000 : ℚ) ^ i ≤
        (k.choose i : ℚ) * x ^ i := by
    intro i hi
    simp only [Finset.mem_range] at hi
    interval_cases i <;> assumption
  have hconst : (4 : ℚ) < ∑ i ∈ Finset.range 7,
      (Nat.choose 16 i : ℚ) * (3621 / 40000 : ℚ) ^ i := by
    norm_num [Finset.sum_range_succ, Nat.choose]
  have hsum : ∑ i ∈ Finset.range 7,
      (k.choose i : ℚ) * x ^ i ≤ (1 + x) ^ k := by
    rw [show (1 + x) ^ k = (x + 1) ^ k by ring, add_pow]
    simp only [one_pow, one_mul, mul_comm]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro i hi
      simp only [Finset.mem_range] at hi ⊢
      omega
    · intro i hi _
      positivity
  have hratio : (4 : ℚ) < (1 + x) ^ k := by
    calc
      (4 : ℚ) < ∑ i ∈ Finset.range 7,
          (Nat.choose 16 i : ℚ) * (3621 / 40000 : ℚ) ^ i := hconst
      _ ≤ ∑ i ∈ Finset.range 7, (k.choose i : ℚ) * x ^ i :=
        Finset.sum_le_sum hterm
      _ ≤ (1 + x) ^ k := hsum
  have hone : (1 : ℚ) + x =
      (2500 * k + 3621 : ℚ) / (2500 * k : ℚ) := by
    dsimp [x]
    field_simp
  rw [hone, div_pow] at hratio
  have hden : (0 : ℚ) < (2500 * k : ℚ) ^ k := by positivity
  have hcross : (4 : ℚ) * (2500 * k : ℚ) ^ k <
      (2500 * k + 3621 : ℚ) ^ k := (lt_div_iff₀ hden).mp hratio
  exact_mod_cast hcross

/-- Sharper equation-facing centered ratio. -/
theorem twenty_three_k_mul_gap_lt_thirty_five_mul_n_of_four_solution
    {k n d : ℕ} (hk : 16 ≤ k) (hd : k ≤ d)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    23 * k * d < 35 * n := by
  by_contra hnot
  have hnle : 35 * n ≤ 23 * k * d := Nat.le_of_not_gt hnot
  have hquad : 126735 * (k + 1) < 8434 * k * k := by
    nlinarith [sq_nonneg ((k : ℤ) - 16)]
  have hquad' : 126735 * (k + 1) < 8434 * k * d := by
    exact lt_of_lt_of_le hquad (by nlinarith)
  have hscaled : 253470 * n ≤ 166566 * k * d := by
    nlinarith
  let T := 2 * n + k + 1
  let W := T + 2 * d
  have hlinear : (2500 * k + 3621) * T < (2500 * k) * W := by
    dsimp [T, W]
    nlinarith
  have hpow := Nat.pow_lt_pow_left hlinear (by omega : k ≠ 0)
  have hpow' :
      (2500 * k + 3621) ^ k * T ^ k < (2500 * k) ^ k * W ^ k := by
    simpa [Nat.mul_pow, mul_assoc, mul_comm, mul_left_comm] using hpow
  have hwin : W ^ k < 4 * T ^ k := by
    simpa [W, T, add_assoc] using centered_ratio_window_of_four_solution hk hd heq
  have hcomb :
      (2500 * k + 3621) ^ k * T ^ k <
        (4 * (2500 * k) ^ k) * T ^ k := by
    have hcoefpos : 0 < (2500 * k) ^ k := by positivity
    calc
      _ < (2500 * k) ^ k * W ^ k := hpow'
      _ < (2500 * k) ^ k * (4 * T ^ k) :=
        Nat.mul_lt_mul_of_pos_left hwin hcoefpos
      _ = (4 * (2500 * k) ^ k) * T ^ k := by ring
  have hTpos : 0 < T ^ k := by
    apply Nat.pow_pos
    dsimp [T]
    omega
  have hcancel : (2500 * k + 3621) ^ k < 4 * (2500 * k) ^ k :=
    (Nat.mul_lt_mul_right hTpos).mp hcomb
  exact (Nat.not_lt_of_ge (Nat.le_of_lt hcancel))
    (four_mul_twenty_five_hundred_k_pow_lt_add_three_six_two_one_pow hk)

/-- The strongest coefficient supported by this module's fixed
`3621/2500` root bracket and the worst centered boundary `k=d=16`.
The linear comparison is allowed to be non-strict; strictness then comes
from the centered equation window. -/
theorem maximal_sharp_bracket_ratio_of_four_solution
    {k n d : ℕ} (hk : 16 ≤ k) (hd : k ≤ d)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    1218443 * k * d < 1853952 * n := by
  by_contra hnot
  have hnle : 1853952 * n ≤ 1218443 * k * d := Nat.le_of_not_gt hnot
  have hquad : 256 * (k + 1) ≤ 17 * k * k := by
    nlinarith [sq_nonneg ((k : ℤ) - 16)]
  have hquad' : 256 * (k + 1) ≤ 17 * k * d := by
    exact le_trans hquad (by nlinarith)
  have hscaled : 7242 * (1853952 * n) ≤
      7242 * (1218443 * k * d) := Nat.mul_le_mul_left 7242 hnle
  let T := 2 * n + k + 1
  let W := T + 2 * d
  have hlinear : (2500 * k + 3621) * T ≤ (2500 * k) * W := by
    dsimp [T, W]
    nlinarith
  have hpow := Nat.pow_le_pow_left hlinear k
  have hpow' :
      (2500 * k + 3621) ^ k * T ^ k ≤ (2500 * k) ^ k * W ^ k := by
    simpa [Nat.mul_pow, mul_assoc, mul_comm, mul_left_comm] using hpow
  have hwin : W ^ k < 4 * T ^ k := by
    simpa [W, T, add_assoc] using centered_ratio_window_of_four_solution hk hd heq
  have hcomb :
      (2500 * k + 3621) ^ k * T ^ k <
        (4 * (2500 * k) ^ k) * T ^ k := by
    have hcoefpos : 0 < (2500 * k) ^ k := by positivity
    calc
      _ ≤ (2500 * k) ^ k * W ^ k := hpow'
      _ < (2500 * k) ^ k * (4 * T ^ k) :=
        Nat.mul_lt_mul_of_pos_left hwin hcoefpos
      _ = (4 * (2500 * k) ^ k) * T ^ k := by ring
  have hTpos : 0 < T ^ k := by
    apply Nat.pow_pos
    dsimp [T]
    omega
  have hcancel : (2500 * k + 3621) ^ k < 4 * (2500 * k) ^ k :=
    (Nat.mul_lt_mul_right hTpos).mp hcomb
  exact (Nat.not_lt_of_ge (Nat.le_of_lt hcancel))
    (four_mul_twenty_five_hundred_k_pow_lt_add_three_six_two_one_pow hk)

/-- The sharper centered ratio expands the any-position large-prime owner
band to `70*a ≤ 23*k`. -/
theorem no_four_solution_lower_term_cofactor_prime_power_base_gt_length_of_sharp_band
    {p k n d i A a : ℕ}
    (hp : p.Prime) (hk : 16 ≤ k) (hd : k ≤ d) (hpk : k < p)
    (hi : i ∈ Finset.Icc 1 k) (hA : 1 ≤ A)
    (hband : 70 * a ≤ 23 * k)
    (howner : n + i = a * p ^ A) :
    blockProduct k (n + d) ≠ 4 * blockProduct k n := by
  intro heq
  have hratio : 23 * k * d < 35 * n :=
    twenty_three_k_mul_gap_lt_thirty_five_mul_n_of_four_solution hk hd heq
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hsize : a * (d + k - 1) < n + i := by
    by_cases ha : a = 0
    · subst a
      simp
      omega
    · have ha0 : 0 < a := Nat.pos_of_ne_zero ha
      have hspan : d + k - 1 < 2 * d := by omega
      have hamul : a * (d + k - 1) < a * (2 * d) :=
        Nat.mul_lt_mul_of_pos_left hspan ha0
      have hbandd : 70 * a * d ≤ 23 * k * d :=
        Nat.mul_le_mul_right d hband
      have hltN : a * (d + k - 1) < n := by
        nlinarith
      omega
  exact no_four_solution_lower_term_cofactor_prime_power_base_gt_length_of_size
    hp hd hpk hi hA howner hsize heq

/-- Maximal cofactor band obtained from the fixed `3621/2500` bracket. -/
theorem no_four_solution_lower_term_cofactor_prime_power_base_gt_length_of_maximal_sharp_band
    {p k n d i A a : ℕ}
    (hp : p.Prime) (hk : 16 ≤ k) (hd : k ≤ d) (hpk : k < p)
    (hi : i ∈ Finset.Icc 1 k) (hA : 1 ≤ A)
    (hband : 3707904 * a ≤ 1218443 * k)
    (howner : n + i = a * p ^ A) :
    blockProduct k (n + d) ≠ 4 * blockProduct k n := by
  intro heq
  have hratio : 1218443 * k * d < 1853952 * n :=
    maximal_sharp_bracket_ratio_of_four_solution hk hd heq
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hsize : a * (d + k - 1) < n + i := by
    by_cases ha : a = 0
    · subst a
      simp
      omega
    · have ha0 : 0 < a := Nat.pos_of_ne_zero ha
      have hspan : d + k - 1 < 2 * d := by omega
      have hamul : a * (d + k - 1) < a * (2 * d) :=
        Nat.mul_lt_mul_of_pos_left hspan ha0
      have hbandd : 3707904 * a * d ≤ 1218443 * k * d :=
        Nat.mul_le_mul_right d hband
      have hltN : a * (d + k - 1) < n := by
        nlinarith
      omega
  exact no_four_solution_lower_term_cofactor_prime_power_base_gt_length_of_size
    hp hd hpk hi hA howner hsize heq

/-- Exact counterboundary to deriving `7*k*d<10*n` from the centered and
endpoint power windows alone.  It is not asserted to be a block equation. -/
theorem seven_tenths_not_forced_by_exact_power_windows :
    10 * 175 ≤ 7 * 16 * 16 ∧
      399 ^ 16 < 4 * 367 ^ 16 ∧
      4 * 176 ^ 16 ≤ 192 ^ 16 ∧
      207 ^ 16 ≤ 4 * 191 ^ 16 := by
  norm_num

#print axioms four_mul_twenty_five_hundred_k_pow_lt_add_three_six_two_one_pow
#print axioms twenty_three_k_mul_gap_lt_thirty_five_mul_n_of_four_solution
#print axioms maximal_sharp_bracket_ratio_of_four_solution
#print axioms no_four_solution_lower_term_cofactor_prime_power_base_gt_length_of_sharp_band
#print axioms no_four_solution_lower_term_cofactor_prime_power_base_gt_length_of_maximal_sharp_band
#print axioms seven_tenths_not_forced_by_exact_power_windows

end Erdos686Variant
end Erdos686
