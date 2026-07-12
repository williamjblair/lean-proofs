import ErdosProblems.Erdos686SmallPrimeBand

/-!
# Erdős 686: centered quotient-four ratio window

The exact quotient-four equation admits a centered pairing of opposite block
positions.  Multiplying those pair inequalities gives a sharper root window
than the endpoint estimate, uniformly through the boundary case `k = 16`.
-/

namespace Erdos686
namespace Erdos686Variant

lemma four_mul_twenty_k_pow_lt_twenty_k_add_twenty_nine_pow
    {k : ℕ} (hk : 16 ≤ k) :
    (4 : ℕ) * (20 * k) ^ k < (20 * k + 29) ^ k := by
  let x : ℚ := 29 / (20 * k)
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
  have hchoose2 : (k.choose 2 : ℚ) = k * (k - 1) / 2 := by
    simpa using (Nat.cast_choose_two ℚ k)
  have hchoose3 : (k.choose 3 : ℚ) = k * (k - 1) * (k - 2) / 6 := by
    have h := Nat.choose_succ_right_eq k 2
    have hcast := congrArg (fun z : ℕ ↦ (z : ℚ)) h
    norm_num [hchoose2, Nat.cast_sub (by omega : 2 ≤ k)] at hcast ⊢
    linarith
  have hchoose4 : (k.choose 4 : ℚ) = k * (k - 1) * (k - 2) * (k - 3) / 24 := by
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
  have ht0 : (Nat.choose 16 0 : ℚ) * (29 / 320 : ℚ) ^ 0 ≤
      (k.choose 0 : ℚ) * x ^ 0 := by norm_num [Nat.choose]
  have ht1 : (Nat.choose 16 1 : ℚ) * (29 / 320 : ℚ) ^ 1 ≤
      (k.choose 1 : ℚ) * x ^ 1 := by
    simp only [Nat.choose_one_right, pow_one]
    dsimp [x]
    field_simp
    norm_num
  have ht2 : (Nat.choose 16 2 : ℚ) * (29 / 320 : ℚ) ^ 2 ≤
      (k.choose 2 : ℚ) * x ^ 2 := by
    rw [hchoose2]
    dsimp [x]
    have hfac : (15 / 16 : ℚ) ≤ ((k : ℚ) - 1) / k := h1
    have hy : (0 : ℚ) ≤ (29 / 20) ^ 2 / 2 := by positivity
    calc
      (Nat.choose 16 2 : ℚ) * (29 / 320 : ℚ) ^ 2 =
          ((29 / 20 : ℚ) ^ 2 / 2) * (15 / 16) := by norm_num [Nat.choose]
      _ ≤ ((29 / 20 : ℚ) ^ 2 / 2) * (((k : ℚ) - 1) / k) :=
        mul_le_mul_of_nonneg_left hfac hy
      _ = (k * (k - 1) / 2) * (29 / (20 * k)) ^ 2 := by
        field_simp
  have ht3 : (Nat.choose 16 3 : ℚ) * (29 / 320 : ℚ) ^ 3 ≤
      (k.choose 3 : ℚ) * x ^ 3 := by
    rw [hchoose3]
    dsimp [x]
    have hp : (15 / 16 : ℚ) * (14 / 16) ≤
        (((k : ℚ) - 1) / k) * (((k : ℚ) - 2) / k) := by
      gcongr
    have hy : (0 : ℚ) ≤ (29 / 20) ^ 3 / 6 := by positivity
    calc
      (Nat.choose 16 3 : ℚ) * (29 / 320 : ℚ) ^ 3 =
          ((29 / 20 : ℚ) ^ 3 / 6) * ((15 / 16) * (14 / 16)) := by
        norm_num [Nat.choose]
      _ ≤ ((29 / 20 : ℚ) ^ 3 / 6) *
          ((((k : ℚ) - 1) / k) * (((k : ℚ) - 2) / k)) :=
        mul_le_mul_of_nonneg_left hp hy
      _ = (k * (k - 1) * (k - 2) / 6) * (29 / (20 * k)) ^ 3 := by
        field_simp
  have ht4 : (Nat.choose 16 4 : ℚ) * (29 / 320 : ℚ) ^ 4 ≤
      (k.choose 4 : ℚ) * x ^ 4 := by
    rw [hchoose4]
    dsimp [x]
    have hp : (15 / 16 : ℚ) * (14 / 16) * (13 / 16) ≤
        (((k : ℚ) - 1) / k) * (((k : ℚ) - 2) / k) *
          (((k : ℚ) - 3) / k) := by
      gcongr
    have hy : (0 : ℚ) ≤ (29 / 20) ^ 4 / 24 := by positivity
    calc
      (Nat.choose 16 4 : ℚ) * (29 / 320 : ℚ) ^ 4 =
          ((29 / 20 : ℚ) ^ 4 / 24) *
            ((15 / 16) * (14 / 16) * (13 / 16)) := by norm_num [Nat.choose]
      _ ≤ ((29 / 20 : ℚ) ^ 4 / 24) *
          ((((k : ℚ) - 1) / k) * (((k : ℚ) - 2) / k) *
            (((k : ℚ) - 3) / k)) :=
        mul_le_mul_of_nonneg_left hp hy
      _ = (k * (k - 1) * (k - 2) * (k - 3) / 24) *
          (29 / (20 * k)) ^ 4 := by
        field_simp
  have ht5 : (Nat.choose 16 5 : ℚ) * (29 / 320 : ℚ) ^ 5 ≤
      (k.choose 5 : ℚ) * x ^ 5 := by
    rw [hchoose5]
    dsimp [x]
    have hp : (15 / 16 : ℚ) * (14 / 16) * (13 / 16) * (12 / 16) ≤
        (((k : ℚ) - 1) / k) * (((k : ℚ) - 2) / k) *
          (((k : ℚ) - 3) / k) * (((k : ℚ) - 4) / k) := by
      gcongr
    have hy : (0 : ℚ) ≤ (29 / 20) ^ 5 / 120 := by positivity
    calc
      (Nat.choose 16 5 : ℚ) * (29 / 320 : ℚ) ^ 5 =
          ((29 / 20 : ℚ) ^ 5 / 120) *
            ((15 / 16) * (14 / 16) * (13 / 16) * (12 / 16)) := by
        norm_num [Nat.choose]
      _ ≤ ((29 / 20 : ℚ) ^ 5 / 120) *
          ((((k : ℚ) - 1) / k) * (((k : ℚ) - 2) / k) *
            (((k : ℚ) - 3) / k) * (((k : ℚ) - 4) / k)) :=
        mul_le_mul_of_nonneg_left hp hy
      _ = (k * (k - 1) * (k - 2) * (k - 3) * (k - 4) / 120) *
          (29 / (20 * k)) ^ 5 := by
        field_simp
  have hterm : ∀ i ∈ Finset.range 6,
      (Nat.choose 16 i : ℚ) * (29 / 320 : ℚ) ^ i ≤
        (k.choose i : ℚ) * x ^ i := by
    intro i hi
    simp only [Finset.mem_range] at hi
    interval_cases i <;> assumption
  have hconst : (4 : ℚ) < ∑ i ∈ Finset.range 6,
      (Nat.choose 16 i : ℚ) * (29 / 320 : ℚ) ^ i := by
    norm_num [Finset.sum_range_succ, Nat.choose]
  have hsum : ∑ i ∈ Finset.range 6,
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
      (4 : ℚ) < ∑ i ∈ Finset.range 6,
          (Nat.choose 16 i : ℚ) * (29 / 320 : ℚ) ^ i := hconst
      _ ≤ ∑ i ∈ Finset.range 6, (k.choose i : ℚ) * x ^ i :=
        Finset.sum_le_sum hterm
      _ ≤ (1 + x) ^ k := hsum
  have hone : (1 : ℚ) + x = (20 * k + 29 : ℚ) / (20 * k : ℚ) := by
    dsimp [x]
    field_simp
  rw [hone, div_pow] at hratio
  have hden : (0 : ℚ) < (20 * k : ℚ) ^ k := by positivity
  have hcross : (4 : ℚ) * (20 * k : ℚ) ^ k <
      (20 * k + 29 : ℚ) ^ k := (lt_div_iff₀ hden).mp hratio
  exact_mod_cast hcross

private lemma centered_pair_identity (x y d : ℕ) :
    (((x + y) ^ 2 * (x + d) * (y + d) : ℕ) : ℤ) =
      (((x + y + 2 * d) ^ 2 * x * y : ℕ) : ℤ) +
        (d : ℤ) * (x + y + d) * ((x : ℤ) - y) ^ 2 := by
  push_cast
  ring

private lemma centered_pair_le (x y d : ℕ) :
    (x + y + 2 * d) ^ 2 * x * y ≤ (x + y) ^ 2 * (x + d) * (y + d) := by
  have hid := centered_pair_identity x y d
  have hnon : (0 : ℤ) ≤
      (d : ℤ) * (x + y + d) * ((x : ℤ) - y) ^ 2 := by positivity
  have hz : ((((x + y + 2 * d) ^ 2 * x * y : ℕ) : ℤ) ≤
      (((x + y) ^ 2 * (x + d) * (y + d) : ℕ) : ℤ)) := by linarith
  exact_mod_cast hz

private lemma centered_pair_lt {x y d : ℕ} (hd : 0 < d) (hxy : x ≠ y) :
    (x + y + 2 * d) ^ 2 * x * y < (x + y) ^ 2 * (x + d) * (y + d) := by
  have hid := centered_pair_identity x y d
  have hdiff : (0 : ℤ) < ((x : ℤ) - y) ^ 2 := by
    apply sq_pos_of_ne_zero
    intro hzero
    apply hxy
    have heq : (x : ℤ) = (y : ℤ) := by linarith
    exact_mod_cast heq
  have hpos : (0 : ℤ) <
      (d : ℤ) * (x + y + d) * ((x : ℤ) - y) ^ 2 := by
    have : (0 : ℤ) < (d : ℤ) := by exact_mod_cast hd
    have : (0 : ℤ) < (x + y + d : ℕ) := by omega
    positivity
  have hz : ((((x + y + 2 * d) ^ 2 * x * y : ℕ) : ℤ) <
      (((x + y) ^ 2 * (x + d) * (y + d) : ℕ) : ℤ)) := by linarith
  exact_mod_cast hz

private lemma prod_reflect_Icc (k : ℕ) (f : ℕ → ℕ) :
    ∏ i ∈ Finset.Icc 1 k, f (k + 1 - i) = ∏ i ∈ Finset.Icc 1 k, f i := by
  refine Finset.prod_bij'
    (fun i _hi ↦ k + 1 - i) (fun i _hi ↦ k + 1 - i) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_Icc] at hi ⊢
    omega
  · intro i hi
    simp only [Finset.mem_Icc] at hi ⊢
    omega
  · intro i hi
    simp only [Finset.mem_Icc] at hi
    change k + 1 - (k + 1 - i) = i
    omega
  · intro i hi
    simp only [Finset.mem_Icc] at hi
    change k + 1 - (k + 1 - i) = i
    omega
  · intro i hi
    rfl

lemma centered_ratio_window_of_four_solution
    {k n d : ℕ} (hk : 16 ≤ k) (hd : k ≤ d)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    (2 * n + k + 1 + 2 * d) ^ k < 4 * (2 * n + k + 1) ^ k := by
  let S := Finset.Icc 1 k
  let T := 2 * n + k + 1
  let W := T + 2 * d
  have hcard : S.card = k := by
    dsimp [S]
    simp
  have hpair : ∀ i ∈ S,
      W ^ 2 * (n + i) * (n + (k + 1 - i)) ≤
        T ^ 2 * (n + d + i) * (n + d + (k + 1 - i)) := by
    intro i hi
    have hi' := Finset.mem_Icc.mp hi
    have hsum : (n + i) + (n + (k + 1 - i)) = T := by
      dsimp [T]
      omega
    have hxd : n + i + d = n + d + i := by omega
    have hyd : n + (k + 1 - i) + d = n + d + (k + 1 - i) := by omega
    have h := centered_pair_le (n + i) (n + (k + 1 - i)) d
    rw [hsum, hxd, hyd] at h
    simpa [W] using h
  have hstrict :
      W ^ 2 * (n + 1) * (n + (k + 1 - 1)) <
        T ^ 2 * (n + d + 1) * (n + d + (k + 1 - 1)) := by
    have hd0 : 0 < d := by omega
    have hne : n + 1 ≠ n + (k + 1 - 1) := by omega
    have h := centered_pair_lt hd0 hne
    have hsum : (n + 1) + (n + (k + 1 - 1)) = T := by
      dsimp [T]
      omega
    have hxd : n + 1 + d = n + d + 1 := by omega
    have hyd : n + (k + 1 - 1) + d = n + d + (k + 1 - 1) := by omega
    rw [hsum, hxd, hyd] at h
    simpa [W] using h
  have hprod :
      ∏ i ∈ S, (W ^ 2 * (n + i) * (n + (k + 1 - i))) <
        ∏ i ∈ S, (T ^ 2 * (n + d + i) * (n + d + (k + 1 - i))) := by
    apply Finset.prod_lt_prod
    · intro i hi
      have hi' := Finset.mem_Icc.mp hi
      dsimp [W, T]
      have hni : 0 < n + i := by omega
      have hnj : 0 < n + (k + 1 - i) := by omega
      positivity
    · exact hpair
    · refine ⟨1, ?_, hstrict⟩
      dsimp [S]
      simp
      omega
  have hrefL : ∏ i ∈ S, (n + (k + 1 - i)) = blockProduct k n := by
    dsimp [S]
    exact prod_reflect_Icc k (fun i ↦ n + i)
  have hrefU : ∏ i ∈ S, (n + d + (k + 1 - i)) = blockProduct k (n + d) := by
    dsimp [S]
    exact prod_reflect_Icc k (fun i ↦ n + d + i)
  have hagg :
      (W ^ k) ^ 2 * (blockProduct k n) ^ 2 <
        (T ^ k) ^ 2 * (blockProduct k (n + d)) ^ 2 := by
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.prod_const, hcard, hrefL, hrefU] at hprod
    unfold blockProduct at hprod
    change (W ^ 2) ^ k * (∏ i ∈ S, (n + i)) * blockProduct k n <
      (T ^ 2) ^ k * (∏ i ∈ S, (n + d + i)) * blockProduct k (n + d) at hprod
    rw [show (∏ i ∈ S, (n + i)) = blockProduct k n by rfl,
      show (∏ i ∈ S, (n + d + i)) = blockProduct k (n + d) by rfl] at hprod
    have hWp : (W ^ 2) ^ k = (W ^ k) ^ 2 := by
      rw [← pow_mul, ← pow_mul]
      congr 1
      omega
    have hTp : (T ^ 2) ^ k = (T ^ k) ^ 2 := by
      rw [← pow_mul, ← pow_mul]
      congr 1
      omega
    rw [hWp, hTp] at hprod
    simpa [pow_two, mul_assoc] using hprod
  rw [heq] at hagg
  have hLpos : 0 < (blockProduct k n) ^ 2 := by
    exact pow_pos (blockProduct_pos k n) _
  have hsq : (W ^ k) ^ 2 < (4 * T ^ k) ^ 2 := by
    have hc : (W ^ k) ^ 2 * (blockProduct k n) ^ 2 <
        (4 * T ^ k) ^ 2 * (blockProduct k n) ^ 2 := by
      simpa [mul_pow, mul_comm, mul_left_comm, mul_assoc] using hagg
    exact (Nat.mul_lt_mul_right hLpos).mp hc
  have hbase : W ^ k < 4 * T ^ k := by
    by_contra hnot
    have hle : 4 * T ^ k ≤ W ^ k := Nat.le_of_not_gt hnot
    exact (Nat.not_lt_of_ge (Nat.pow_le_pow_left hle 2)) hsq
  simpa [W, T, add_assoc] using hbase

theorem thirteen_k_mul_gap_lt_twenty_mul_n_of_four_solution
    {k n d : ℕ} (hk : 16 ≤ k) (hd : k ≤ d)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    13 * k * d < 20 * n := by
  by_contra hnot
  have hnle : 20 * n ≤ 13 * k * d := Nat.le_of_not_gt hnot
  have hquad : 290 * (k + 1) < 23 * k * k := by
    nlinarith [sq_nonneg ((k : ℤ) - 16)]
  have hquad' : 290 * (k + 1) < 23 * k * d := by
    exact lt_of_lt_of_le hquad (by nlinarith)
  have hscaled : 580 * n ≤ 377 * k * d := by
    nlinarith
  let T := 2 * n + k + 1
  let W := T + 2 * d
  have hlinear : (20 * k + 29) * T < (20 * k) * W := by
    dsimp [T, W]
    nlinarith
  have hpow := Nat.pow_lt_pow_left hlinear (by omega : k ≠ 0)
  have hpow' :
      (20 * k + 29) ^ k * T ^ k < (20 * k) ^ k * W ^ k := by
    simpa [Nat.mul_pow, mul_assoc, mul_comm, mul_left_comm] using hpow
  have hwin : W ^ k < 4 * T ^ k := by
    simpa [W, T, add_assoc] using centered_ratio_window_of_four_solution hk hd heq
  have hcomb :
      (20 * k + 29) ^ k * T ^ k <
        (4 * (20 * k) ^ k) * T ^ k := by
    have hcoefpos : 0 < (20 * k) ^ k := by positivity
    calc
      _ < (20 * k) ^ k * W ^ k := hpow'
      _ < (20 * k) ^ k * (4 * T ^ k) :=
        Nat.mul_lt_mul_of_pos_left hwin hcoefpos
      _ = (4 * (20 * k) ^ k) * T ^ k := by ring
  have hTpos : 0 < T ^ k := by
    apply Nat.pow_pos
    dsimp [T]
    omega
  have hcancel : (20 * k + 29) ^ k < 4 * (20 * k) ^ k :=
    (Nat.mul_lt_mul_right hTpos).mp hcomb
  exact (Nat.not_lt_of_ge (Nat.le_of_lt hcancel))
    (four_mul_twenty_k_pow_lt_twenty_k_add_twenty_nine_pow hk)

/-- The centered ratio window expands the any-position large-prime owner
obstruction from constant cofactors to the linear band `40*a ≤ 13*k`. -/
theorem no_four_solution_lower_term_cofactor_prime_power_base_gt_length_of_band
    {p k n d i A a : ℕ}
    (hp : p.Prime) (hk : 16 ≤ k) (hd : k ≤ d) (hpk : k < p)
    (hi : i ∈ Finset.Icc 1 k) (hA : 1 ≤ A)
    (hband : 40 * a ≤ 13 * k)
    (howner : n + i = a * p ^ A) :
    blockProduct k (n + d) ≠ 4 * blockProduct k n := by
  intro heq
  have hratio : 13 * k * d < 20 * n :=
    thirteen_k_mul_gap_lt_twenty_mul_n_of_four_solution hk hd heq
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
      have hbandd : 40 * a * d ≤ 13 * k * d := by
        exact Nat.mul_le_mul_right d hband
      have hltN : a * (d + k - 1) < n := by
        nlinarith
      omega
  exact no_four_solution_lower_term_cofactor_prime_power_base_gt_length_of_size
    hp hd hpk hi hA howner hsize heq

#print axioms four_mul_twenty_k_pow_lt_twenty_k_add_twenty_nine_pow
#print axioms centered_ratio_window_of_four_solution
#print axioms thirteen_k_mul_gap_lt_twenty_mul_n_of_four_solution
#print axioms no_four_solution_lower_term_cofactor_prime_power_base_gt_length_of_band

end Erdos686Variant
end Erdos686
