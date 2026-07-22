/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.Core.MatchingCompression

/-!
# Erdős 686: a `0.6*k*d` lower ratio window

The previous large-row interface retained only `n>9d` and `k*d<5n`.
This module uses the exact endpoint power window to prove the substantially
sharper uniform inequality

```text
3*k*d < 5*n
```

for every `k>=16`, `d>=k` quotient-four solution.
-/

namespace Erdos686
namespace Erdos686Variant

private lemma four_mul_three_k_add_five_pow_lt_small
    {k : ℕ} (hk : 16 ≤ k) (hk' : k < 90) :
    4 * (3 * k + 5) ^ k < (3 * k + 10) ^ k := by
  interval_cases k <;> norm_num

/-- Uniform tail of the exact power comparison.  Put `m=floor(k/9)`.
Bernoulli gives `(1+a)^m >= 1+ma`; for `k>=90`, the latter exceeds `7/6`.
Nine such groups work because `7^9>4*6^9`. -/
private lemma four_mul_three_k_add_five_pow_lt_large
    {k : ℕ} (hk : 90 ≤ k) :
    4 * (3 * k + 5) ^ k < (3 * k + 10) ^ k := by
  let m : ℕ := k / 9
  let D : ℚ := 3 * k + 5
  let a : ℚ := 5 / D
  have hm10 : 10 ≤ m := by
    dsimp [m]
    omega
  have hmod : k % 9 < 9 := Nat.mod_lt k (by norm_num)
  have hdecomp : k % 9 + 9 * m = k := by
    dsimp [m]
    exact Nat.mod_add_div k 9
  have h9m : 9 * m ≤ k := by omega
  have hDpos : (0 : ℚ) < D := by
    dsimp [D]
    positivity
  have ha0 : (0 : ℚ) ≤ a := by
    dsimp [a]
    positivity
  have hbern : (1 : ℚ) + m * a ≤ (1 + a) ^ m :=
    one_add_mul_le_pow (by linarith : (-2 : ℚ) ≤ a) m
  have hDlt : (D : ℚ) < 30 * m := by
    dsimp [D, m]
    norm_num at hdecomp hmod ⊢
    exact_mod_cast (show 3 * k + 5 < 30 * (k / 9) by omega)
  have hseven : (7 / 6 : ℚ) < 1 + m * a := by
    dsimp [a]
    rw [show (1 : ℚ) + (m : ℚ) * (5 / D) = (D + 5 * m) / D by field_simp]
    rw [div_lt_div_iff₀ (by norm_num : (0 : ℚ) < 6) hDpos]
    linarith
  have hbase : (7 / 6 : ℚ) < (1 + a) ^ m :=
    lt_of_lt_of_le hseven hbern
  have hpow9 : (7 / 6 : ℚ) ^ 9 < ((1 + a) ^ m) ^ 9 :=
    pow_lt_pow_left₀ hbase (by norm_num) (by norm_num)
  have hone : (1 : ℚ) ≤ 1 + a := by linarith
  have hexp : (1 + a) ^ (9 * m) ≤ (1 + a) ^ k :=
    pow_le_pow_right₀ hone h9m
  have hfourseven : (4 : ℚ) < (7 / 6 : ℚ) ^ 9 := by norm_num
  have hratioA : (4 : ℚ) < (1 + a) ^ k := by
    calc
      (4 : ℚ) < (7 / 6 : ℚ) ^ 9 := hfourseven
      _ < ((1 + a) ^ m) ^ 9 := hpow9
      _ = (1 + a) ^ (m * 9) := by rw [← pow_mul]
      _ = (1 + a) ^ (9 * m) := by rw [mul_comm]
      _ ≤ (1 + a) ^ k := hexp
  have honeEq : (1 : ℚ) + a =
      (3 * k + 10 : ℚ) / (3 * k + 5 : ℚ) := by
    dsimp [a, D]
    field_simp
    ring
  rw [honeEq] at hratioA
  have hdenPow : (0 : ℚ) < ((3 * k + 5 : ℚ) ^ k) := by positivity
  rw [div_pow] at hratioA
  have hcross : (4 : ℚ) * ((3 * k + 5 : ℚ) ^ k) <
      ((3 * k + 10 : ℚ) ^ k) :=
    (lt_div_iff₀ hdenPow).mp hratioA
  exact_mod_cast hcross

lemma four_mul_three_k_add_five_pow_lt
    {k : ℕ} (hk : 16 ≤ k) :
    4 * (3 * k + 5) ^ k < (3 * k + 10) ^ k := by
  by_cases h : k < 90
  · exact four_mul_three_k_add_five_pow_lt_small hk h
  · exact four_mul_three_k_add_five_pow_lt_large (by omega)

/-- Exact endpoint-window form of the sharper lower ratio bound. -/
theorem three_k_mul_gap_lt_five_mul_n_of_ratio_window
    {k n d : ℕ} (hk : 16 ≤ k) (hd : k ≤ d)
    (hwin : (n + d + k) ^ k ≤ 4 * (n + k) ^ k) :
    3 * k * d < 5 * n := by
  by_contra hnot
  have hnle : 5 * n ≤ 3 * k * d := Nat.le_of_not_gt hnot
  have hlinear : (3 * k + 10) * (n + k) ≤
      (3 * k + 5) * (n + d + k) := by
    nlinarith
  have hpow := Nat.pow_le_pow_left hlinear k
  have hpow' :
      (3 * k + 10) ^ k * (n + k) ^ k ≤
        (3 * k + 5) ^ k * (n + d + k) ^ k := by
    simpa [Nat.mul_pow, mul_assoc, mul_comm, mul_left_comm] using hpow
  have hcomb :
      (3 * k + 10) ^ k * (n + k) ^ k ≤
        (4 * (3 * k + 5) ^ k) * (n + k) ^ k := by
    calc
      _ ≤ (3 * k + 5) ^ k * (n + d + k) ^ k := hpow'
      _ ≤ (3 * k + 5) ^ k * (4 * (n + k) ^ k) :=
        Nat.mul_le_mul_left ((3 * k + 5) ^ k) hwin
      _ = (4 * (3 * k + 5) ^ k) * (n + k) ^ k := by ring
  have hbase : 0 < (n + k) ^ k := Nat.pow_pos (by omega)
  have hcancel : (3 * k + 10) ^ k ≤ 4 * (3 * k + 5) ^ k :=
    Nat.le_of_mul_le_mul_right hcomb hbase
  exact (Nat.not_lt_of_ge hcancel)
    (four_mul_three_k_add_five_pow_lt hk)

/-- Equation-facing wrapper. -/
theorem three_k_mul_gap_lt_five_mul_n_of_four_solution
    {k n d : ℕ} (hk : 16 ≤ k) (hd : k ≤ d)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    3 * k * d < 5 * n := by
  exact three_k_mul_gap_lt_five_mul_n_of_ratio_window hk hd
    (ratio_window_four_nat heq).1

#print axioms four_mul_three_k_add_five_pow_lt
#print axioms three_k_mul_gap_lt_five_mul_n_of_ratio_window
#print axioms three_k_mul_gap_lt_five_mul_n_of_four_solution

end Erdos686Variant
end Erdos686
