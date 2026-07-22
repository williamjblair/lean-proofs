import ErdosProblems.Erdos686.K5.OppositeSecantTangentGCD
import ErdosProblems.Erdos686.Core.FiveThue

/-!
# Erdős 686, k=5: ratio exclusion for the secant-tangent coefficient

The centered upper bracket gives `40*d < 13*n` on the surviving solution
tail.  After removing the distinguished factor four, the coefficient is
independent of `t`; an ordinary-kernel finite certificate then checks all
20 ordered row pairs against all 20 ordered column pairs.  Restoring the five
possible distinguished indices covers the requested 2000 configurations.
-/

namespace Erdos686.Erdos686Variant

def k5NormalizedTangentCombination
    (n d j₁ j₂ i₁ i₂ : ℕ) : ℤ :=
  let x₁ : ℤ := n + j₁
  let x₂ : ℤ := n + j₂
  let y₁ : ℤ := n + d + i₁
  let y₂ : ℤ := n + d + i₂
  let p₁ : ℤ := k5LowerTangentWeight j₁
  let p₂ : ℤ := k5LowerTangentWeight j₂
  let q₁ : ℤ := localBlockCoefficient 5 i₁
  let q₂ : ℤ := localBlockCoefficient 5 i₂
  (((j₂ : ℤ) - j₁) ^ 2) *
      bipartiteTangentRowQuotient x₁ x₂ y₁ y₂ p₁ p₂ q₁ q₂ +
    (((i₂ : ℤ) - i₁) ^ 2) *
      bipartiteTangentColumnQuotient x₁ x₂ y₁ y₂ p₁ p₂ q₁ q₂

/-- The coefficient occurring in the opposite-secant/tangent gcd theorem. -/
def k5ProperTangentCombination
    (n d t j₁ j₂ i₁ i₂ : ℕ) : ℤ :=
  ((((j₂ : ℤ) - j₁) ^ 2) *
      (k5UpperFourMultiplier t i₁ : ℤ) *
      (k5UpperFourMultiplier t i₂ : ℤ)) *
      k5ProperTangentRowQuotient n d t j₁ j₂ i₁ i₂ +
    (((i₂ : ℤ) - i₁) ^ 2) *
      k5ProperTangentColumnQuotient n d t j₁ j₂ i₁ i₂

/-- Removing the distinguished factor four only multiplies the normalized
coefficient by the two positive local multipliers. -/
theorem k5ProperTangentCombination_eq_multiplier_mul_normalized
    {n d t j₁ j₂ i₁ i₂ : ℕ} (hfour : 4 ∣ n + d + t) :
    k5ProperTangentCombination n d t j₁ j₂ i₁ i₂ =
      ((k5UpperFourMultiplier t i₁ : ℤ) *
        (k5UpperFourMultiplier t i₂ : ℤ)) *
        k5NormalizedTangentCombination n d j₁ j₂ i₁ i₂ := by
  have hmul₁ := k5UpperFourMultiplier_mul_upperTermAfterFour
    (n := n) (d := d) (t := t) (i := i₁) hfour
  have hmul₂ := k5UpperFourMultiplier_mul_upperTermAfterFour
    (n := n) (d := d) (t := t) (i := i₂) hfour
  have hmul₁Z :
      (k5UpperFourMultiplier t i₁ : ℤ) *
          (upperTermAfterFour n d t i₁ : ℤ) = (n + d + i₁ : ℕ) := by
    exact_mod_cast hmul₁
  have hmul₂Z :
      (k5UpperFourMultiplier t i₂ : ℤ) *
          (upperTermAfterFour n d t i₂ : ℤ) = (n + d + i₂ : ℕ) := by
    exact_mod_cast hmul₂
  push_cast at hmul₁Z hmul₂Z
  unfold k5ProperTangentCombination k5NormalizedTangentCombination
    k5ProperTangentRowQuotient k5ProperTangentColumnQuotient
    k5ModifiedUpperTangentWeight
  dsimp only
  rw [← hmul₁Z, ← hmul₂Z]
  unfold bipartiteTangentRowQuotient bipartiteTangentColumnQuotient
  ring

/-- The centered upper bracket supplies the rational cone used by the finite
certificate.  The shift by three costs only the displayed small threshold. -/
theorem forty_gap_lt_thirteen_start_of_k5_solution
    {n d : ℕ} (hn : 662 ≤ n)
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n) :
    40 * d < 13 * n := by
  have hsol := k5_centered_of_eq heq
  have hbr := k5_bracket_upper hsol (by omega : 665 ≤ n + 3)
  omega

private lemma lc51 : localBlockCoefficient 5 1 = 24 := by
  rw [localBlockCoefficient_eq_sign_mul_nat (by norm_num)]
  norm_num [localBlockCoefficientNat]

private lemma lc52 : localBlockCoefficient 5 2 = -6 := by
  rw [localBlockCoefficient_eq_sign_mul_nat (by norm_num)]
  norm_num [localBlockCoefficientNat]

private lemma lc53 : localBlockCoefficient 5 3 = 4 := by
  rw [localBlockCoefficient_eq_sign_mul_nat (by norm_num)]
  norm_num [localBlockCoefficientNat]

private lemma lc54 : localBlockCoefficient 5 4 = -6 := by
  rw [localBlockCoefficient_eq_sign_mul_nat (by norm_num)]
  norm_num [localBlockCoefficientNat]

private lemma lc55 : localBlockCoefficient 5 5 = 24 := by
  rw [localBlockCoefficient_eq_sign_mul_nat (by norm_num)]
  norm_num [localBlockCoefficientNat]

set_option maxHeartbeats 2000000 in
-- Normalize the twenty ordered column configurations for this fixed row pair.
private theorem fixed_1_2
    {n d i₁ i₂ : ℕ}
    (hn : 2811 ≤ n) (hd : 5 ≤ d) (hratio : 40 * d < 13 * n)
    (hi₁ : i₁ ∈ Finset.Icc 1 5) (hi₂ : i₂ ∈ Finset.Icc 1 5)
    (hineq : i₁ ≠ i₂) :
    k5NormalizedTangentCombination n d 1 2 i₁ i₂ ≠ 0 := by
  have hi₁lo := (Finset.mem_Icc.mp hi₁).1
  have hi₁hi := (Finset.mem_Icc.mp hi₁).2
  have hi₂lo := (Finset.mem_Icc.mp hi₂).1
  have hi₂hi := (Finset.mem_Icc.mp hi₂).2
  have hnZ : (2811 : ℤ) ≤ n := by exact_mod_cast hn
  have hdZ : (5 : ℤ) ≤ d := by exact_mod_cast hd
  have hrZ : (40 : ℤ) * d < 13 * n := by exact_mod_cast hratio
  intro hz
  unfold k5NormalizedTangentCombination at hz
  dsimp only at hz
  unfold k5LowerTangentWeight at hz
  interval_cases i₁ <;> interval_cases i₂ <;>
      norm_num [lc51, lc52, lc53, lc54, lc55,
        bipartiteTangentRowQuotient, bipartiteTangentColumnQuotient] at hz <;>
      simp_all <;>
      nlinarith [sq_nonneg ((13 : ℤ) * n - 40 * d),
        mul_nonneg (show (0 : ℤ) ≤ n - 2811 by omega)
          (show (0 : ℤ) ≤ n by omega),
        mul_pos (show (0 : ℤ) < 13 * n - 40 * d by omega)
          (show (0 : ℤ) < 1320 * n + 559 * d by omega)]

set_option maxHeartbeats 2000000 in
-- Normalize the twenty ordered column configurations for this fixed row pair.
private theorem fixed_1_3
    {n d i₁ i₂ : ℕ}
    (hn : 2811 ≤ n) (hd : 5 ≤ d) (hratio : 40 * d < 13 * n)
    (hi₁ : i₁ ∈ Finset.Icc 1 5) (hi₂ : i₂ ∈ Finset.Icc 1 5)
    (hineq : i₁ ≠ i₂) :
    k5NormalizedTangentCombination n d 1 3 i₁ i₂ ≠ 0 := by
  have hi₁lo := (Finset.mem_Icc.mp hi₁).1
  have hi₁hi := (Finset.mem_Icc.mp hi₁).2
  have hi₂lo := (Finset.mem_Icc.mp hi₂).1
  have hi₂hi := (Finset.mem_Icc.mp hi₂).2
  have hnZ : (2811 : ℤ) ≤ n := by exact_mod_cast hn
  have hdZ : (5 : ℤ) ≤ d := by exact_mod_cast hd
  have hrZ : (40 : ℤ) * d < 13 * n := by exact_mod_cast hratio
  intro hz
  unfold k5NormalizedTangentCombination at hz
  dsimp only at hz
  unfold k5LowerTangentWeight at hz
  interval_cases i₁ <;> interval_cases i₂ <;>
      norm_num [lc51, lc52, lc53, lc54, lc55,
        bipartiteTangentRowQuotient, bipartiteTangentColumnQuotient] at hz <;>
      simp_all <;>
      nlinarith [sq_nonneg ((13 : ℤ) * n - 40 * d),
        mul_nonneg (show (0 : ℤ) ≤ n - 2811 by omega)
          (show (0 : ℤ) ≤ n by omega),
        mul_pos (show (0 : ℤ) < 13 * n - 40 * d by omega)
          (show (0 : ℤ) < 1320 * n + 559 * d by omega)]


set_option maxHeartbeats 2000000 in
-- Normalize the twenty ordered column configurations for this fixed row pair.
private theorem fixed_1_4
    {n d i₁ i₂ : ℕ}
    (hn : 2811 ≤ n) (hd : 5 ≤ d) (hratio : 40 * d < 13 * n)
    (hi₁ : i₁ ∈ Finset.Icc 1 5) (hi₂ : i₂ ∈ Finset.Icc 1 5)
    (hineq : i₁ ≠ i₂) :
    k5NormalizedTangentCombination n d 1 4 i₁ i₂ ≠ 0 := by
  have hi₁lo := (Finset.mem_Icc.mp hi₁).1
  have hi₁hi := (Finset.mem_Icc.mp hi₁).2
  have hi₂lo := (Finset.mem_Icc.mp hi₂).1
  have hi₂hi := (Finset.mem_Icc.mp hi₂).2
  have hnZ : (2811 : ℤ) ≤ n := by exact_mod_cast hn
  have hdZ : (5 : ℤ) ≤ d := by exact_mod_cast hd
  have hrZ : (40 : ℤ) * d < 13 * n := by exact_mod_cast hratio
  intro hz
  unfold k5NormalizedTangentCombination at hz
  dsimp only at hz
  unfold k5LowerTangentWeight at hz
  interval_cases i₁ <;> interval_cases i₂ <;>
      norm_num [lc51, lc52, lc53, lc54, lc55,
        bipartiteTangentRowQuotient, bipartiteTangentColumnQuotient] at hz <;>
      simp_all <;>
      nlinarith [sq_nonneg ((13 : ℤ) * n - 40 * d),
        mul_nonneg (show (0 : ℤ) ≤ n - 2811 by omega)
          (show (0 : ℤ) ≤ n by omega),
        mul_pos (show (0 : ℤ) < 13 * n - 40 * d by omega)
          (show (0 : ℤ) < 1320 * n + 559 * d by omega)]


set_option maxHeartbeats 2000000 in
-- Normalize the twenty ordered column configurations for this fixed row pair.
private theorem fixed_1_5
    {n d i₁ i₂ : ℕ}
    (hn : 2811 ≤ n) (hd : 5 ≤ d) (hratio : 40 * d < 13 * n)
    (hi₁ : i₁ ∈ Finset.Icc 1 5) (hi₂ : i₂ ∈ Finset.Icc 1 5)
    (hineq : i₁ ≠ i₂) :
    k5NormalizedTangentCombination n d 1 5 i₁ i₂ ≠ 0 := by
  have hi₁lo := (Finset.mem_Icc.mp hi₁).1
  have hi₁hi := (Finset.mem_Icc.mp hi₁).2
  have hi₂lo := (Finset.mem_Icc.mp hi₂).1
  have hi₂hi := (Finset.mem_Icc.mp hi₂).2
  have hnZ : (2811 : ℤ) ≤ n := by exact_mod_cast hn
  have hdZ : (5 : ℤ) ≤ d := by exact_mod_cast hd
  have hrZ : (40 : ℤ) * d < 13 * n := by exact_mod_cast hratio
  intro hz
  unfold k5NormalizedTangentCombination at hz
  dsimp only at hz
  unfold k5LowerTangentWeight at hz
  interval_cases i₁ <;> interval_cases i₂ <;>
      norm_num [lc51, lc52, lc53, lc54, lc55,
        bipartiteTangentRowQuotient, bipartiteTangentColumnQuotient] at hz <;>
      simp_all <;>
      nlinarith [sq_nonneg ((13 : ℤ) * n - 40 * d),
        mul_nonneg (show (0 : ℤ) ≤ n - 2811 by omega)
          (show (0 : ℤ) ≤ n by omega),
        mul_pos (show (0 : ℤ) < 13 * n - 40 * d by omega)
          (show (0 : ℤ) < 1320 * n + 559 * d by omega)]


set_option maxHeartbeats 2000000 in
-- Normalize the twenty ordered column configurations for this fixed row pair.
private theorem fixed_2_1
    {n d i₁ i₂ : ℕ}
    (hn : 2811 ≤ n) (hd : 5 ≤ d) (hratio : 40 * d < 13 * n)
    (hi₁ : i₁ ∈ Finset.Icc 1 5) (hi₂ : i₂ ∈ Finset.Icc 1 5)
    (hineq : i₁ ≠ i₂) :
    k5NormalizedTangentCombination n d 2 1 i₁ i₂ ≠ 0 := by
  have hi₁lo := (Finset.mem_Icc.mp hi₁).1
  have hi₁hi := (Finset.mem_Icc.mp hi₁).2
  have hi₂lo := (Finset.mem_Icc.mp hi₂).1
  have hi₂hi := (Finset.mem_Icc.mp hi₂).2
  have hnZ : (2811 : ℤ) ≤ n := by exact_mod_cast hn
  have hdZ : (5 : ℤ) ≤ d := by exact_mod_cast hd
  have hrZ : (40 : ℤ) * d < 13 * n := by exact_mod_cast hratio
  intro hz
  unfold k5NormalizedTangentCombination at hz
  dsimp only at hz
  unfold k5LowerTangentWeight at hz
  interval_cases i₁ <;> interval_cases i₂ <;>
      norm_num [lc51, lc52, lc53, lc54, lc55,
        bipartiteTangentRowQuotient, bipartiteTangentColumnQuotient] at hz <;>
      simp_all <;>
      nlinarith [sq_nonneg ((13 : ℤ) * n - 40 * d),
        mul_nonneg (show (0 : ℤ) ≤ n - 2811 by omega)
          (show (0 : ℤ) ≤ n by omega),
        mul_pos (show (0 : ℤ) < 13 * n - 40 * d by omega)
          (show (0 : ℤ) < 1320 * n + 559 * d by omega)]


set_option maxHeartbeats 2000000 in
-- Normalize the twenty ordered column configurations for this fixed row pair.
private theorem fixed_2_3
    {n d i₁ i₂ : ℕ}
    (hn : 2811 ≤ n) (hd : 5 ≤ d) (hratio : 40 * d < 13 * n)
    (hi₁ : i₁ ∈ Finset.Icc 1 5) (hi₂ : i₂ ∈ Finset.Icc 1 5)
    (hineq : i₁ ≠ i₂) :
    k5NormalizedTangentCombination n d 2 3 i₁ i₂ ≠ 0 := by
  have hi₁lo := (Finset.mem_Icc.mp hi₁).1
  have hi₁hi := (Finset.mem_Icc.mp hi₁).2
  have hi₂lo := (Finset.mem_Icc.mp hi₂).1
  have hi₂hi := (Finset.mem_Icc.mp hi₂).2
  have hnZ : (2811 : ℤ) ≤ n := by exact_mod_cast hn
  have hdZ : (5 : ℤ) ≤ d := by exact_mod_cast hd
  have hrZ : (40 : ℤ) * d < 13 * n := by exact_mod_cast hratio
  intro hz
  unfold k5NormalizedTangentCombination at hz
  dsimp only at hz
  unfold k5LowerTangentWeight at hz
  interval_cases i₁ <;> interval_cases i₂ <;>
      norm_num [lc51, lc52, lc53, lc54, lc55,
        bipartiteTangentRowQuotient, bipartiteTangentColumnQuotient] at hz <;>
      simp_all <;>
      nlinarith [sq_nonneg ((13 : ℤ) * n - 40 * d),
        mul_nonneg (show (0 : ℤ) ≤ n - 2811 by omega)
          (show (0 : ℤ) ≤ n by omega),
        mul_pos (show (0 : ℤ) < 13 * n - 40 * d by omega)
          (show (0 : ℤ) < 1320 * n + 559 * d by omega)]


set_option maxHeartbeats 2000000 in
-- Normalize the twenty ordered column configurations for this fixed row pair.
private theorem fixed_2_4
    {n d i₁ i₂ : ℕ}
    (hn : 2811 ≤ n) (hd : 5 ≤ d) (hratio : 40 * d < 13 * n)
    (hi₁ : i₁ ∈ Finset.Icc 1 5) (hi₂ : i₂ ∈ Finset.Icc 1 5)
    (hineq : i₁ ≠ i₂) :
    k5NormalizedTangentCombination n d 2 4 i₁ i₂ ≠ 0 := by
  have hi₁lo := (Finset.mem_Icc.mp hi₁).1
  have hi₁hi := (Finset.mem_Icc.mp hi₁).2
  have hi₂lo := (Finset.mem_Icc.mp hi₂).1
  have hi₂hi := (Finset.mem_Icc.mp hi₂).2
  have hnZ : (2811 : ℤ) ≤ n := by exact_mod_cast hn
  have hdZ : (5 : ℤ) ≤ d := by exact_mod_cast hd
  have hrZ : (40 : ℤ) * d < 13 * n := by exact_mod_cast hratio
  intro hz
  unfold k5NormalizedTangentCombination at hz
  dsimp only at hz
  unfold k5LowerTangentWeight at hz
  interval_cases i₁ <;> interval_cases i₂ <;>
      norm_num [lc51, lc52, lc53, lc54, lc55,
        bipartiteTangentRowQuotient, bipartiteTangentColumnQuotient] at hz <;>
      simp_all <;>
      nlinarith [sq_nonneg ((13 : ℤ) * n - 40 * d),
        mul_nonneg (show (0 : ℤ) ≤ n - 2811 by omega)
          (show (0 : ℤ) ≤ n by omega),
        mul_pos (show (0 : ℤ) < 13 * n - 40 * d by omega)
          (show (0 : ℤ) < 1320 * n + 559 * d by omega)]


set_option maxHeartbeats 2000000 in
-- Normalize the twenty ordered column configurations for this fixed row pair.
private theorem fixed_2_5
    {n d i₁ i₂ : ℕ}
    (hn : 2811 ≤ n) (hd : 5 ≤ d) (hratio : 40 * d < 13 * n)
    (hi₁ : i₁ ∈ Finset.Icc 1 5) (hi₂ : i₂ ∈ Finset.Icc 1 5)
    (hineq : i₁ ≠ i₂) :
    k5NormalizedTangentCombination n d 2 5 i₁ i₂ ≠ 0 := by
  have hi₁lo := (Finset.mem_Icc.mp hi₁).1
  have hi₁hi := (Finset.mem_Icc.mp hi₁).2
  have hi₂lo := (Finset.mem_Icc.mp hi₂).1
  have hi₂hi := (Finset.mem_Icc.mp hi₂).2
  have hnZ : (2811 : ℤ) ≤ n := by exact_mod_cast hn
  have hdZ : (5 : ℤ) ≤ d := by exact_mod_cast hd
  have hrZ : (40 : ℤ) * d < 13 * n := by exact_mod_cast hratio
  intro hz
  unfold k5NormalizedTangentCombination at hz
  dsimp only at hz
  unfold k5LowerTangentWeight at hz
  interval_cases i₁ <;> interval_cases i₂ <;>
      norm_num [lc51, lc52, lc53, lc54, lc55,
        bipartiteTangentRowQuotient, bipartiteTangentColumnQuotient] at hz <;>
      simp_all <;>
      nlinarith [sq_nonneg ((13 : ℤ) * n - 40 * d),
        mul_nonneg (show (0 : ℤ) ≤ n - 2811 by omega)
          (show (0 : ℤ) ≤ n by omega),
        mul_pos (show (0 : ℤ) < 13 * n - 40 * d by omega)
          (show (0 : ℤ) < 1320 * n + 559 * d by omega)]


set_option maxHeartbeats 2000000 in
-- Normalize the twenty ordered column configurations for this fixed row pair.
private theorem fixed_3_1
    {n d i₁ i₂ : ℕ}
    (hn : 2811 ≤ n) (hd : 5 ≤ d) (hratio : 40 * d < 13 * n)
    (hi₁ : i₁ ∈ Finset.Icc 1 5) (hi₂ : i₂ ∈ Finset.Icc 1 5)
    (hineq : i₁ ≠ i₂) :
    k5NormalizedTangentCombination n d 3 1 i₁ i₂ ≠ 0 := by
  have hi₁lo := (Finset.mem_Icc.mp hi₁).1
  have hi₁hi := (Finset.mem_Icc.mp hi₁).2
  have hi₂lo := (Finset.mem_Icc.mp hi₂).1
  have hi₂hi := (Finset.mem_Icc.mp hi₂).2
  have hnZ : (2811 : ℤ) ≤ n := by exact_mod_cast hn
  have hdZ : (5 : ℤ) ≤ d := by exact_mod_cast hd
  have hrZ : (40 : ℤ) * d < 13 * n := by exact_mod_cast hratio
  intro hz
  unfold k5NormalizedTangentCombination at hz
  dsimp only at hz
  unfold k5LowerTangentWeight at hz
  interval_cases i₁ <;> interval_cases i₂ <;>
      norm_num [lc51, lc52, lc53, lc54, lc55,
        bipartiteTangentRowQuotient, bipartiteTangentColumnQuotient] at hz <;>
      simp_all <;>
      nlinarith [sq_nonneg ((13 : ℤ) * n - 40 * d),
        mul_nonneg (show (0 : ℤ) ≤ n - 2811 by omega)
          (show (0 : ℤ) ≤ n by omega),
        mul_pos (show (0 : ℤ) < 13 * n - 40 * d by omega)
          (show (0 : ℤ) < 1320 * n + 559 * d by omega)]


set_option maxHeartbeats 2000000 in
-- Normalize the twenty ordered column configurations for this fixed row pair.
private theorem fixed_3_2
    {n d i₁ i₂ : ℕ}
    (hn : 2811 ≤ n) (hd : 5 ≤ d) (hratio : 40 * d < 13 * n)
    (hi₁ : i₁ ∈ Finset.Icc 1 5) (hi₂ : i₂ ∈ Finset.Icc 1 5)
    (hineq : i₁ ≠ i₂) :
    k5NormalizedTangentCombination n d 3 2 i₁ i₂ ≠ 0 := by
  have hi₁lo := (Finset.mem_Icc.mp hi₁).1
  have hi₁hi := (Finset.mem_Icc.mp hi₁).2
  have hi₂lo := (Finset.mem_Icc.mp hi₂).1
  have hi₂hi := (Finset.mem_Icc.mp hi₂).2
  have hnZ : (2811 : ℤ) ≤ n := by exact_mod_cast hn
  have hdZ : (5 : ℤ) ≤ d := by exact_mod_cast hd
  have hrZ : (40 : ℤ) * d < 13 * n := by exact_mod_cast hratio
  intro hz
  unfold k5NormalizedTangentCombination at hz
  dsimp only at hz
  unfold k5LowerTangentWeight at hz
  interval_cases i₁ <;> interval_cases i₂ <;>
      norm_num [lc51, lc52, lc53, lc54, lc55,
        bipartiteTangentRowQuotient, bipartiteTangentColumnQuotient] at hz <;>
      simp_all <;>
      nlinarith [sq_nonneg ((13 : ℤ) * n - 40 * d),
        mul_nonneg (show (0 : ℤ) ≤ n - 2811 by omega)
          (show (0 : ℤ) ≤ n by omega),
        mul_pos (show (0 : ℤ) < 13 * n - 40 * d by omega)
          (show (0 : ℤ) < 1320 * n + 559 * d by omega)]


set_option maxHeartbeats 2000000 in
-- Normalize the twenty ordered column configurations for this fixed row pair.
private theorem fixed_3_4
    {n d i₁ i₂ : ℕ}
    (hn : 2811 ≤ n) (hd : 5 ≤ d) (hratio : 40 * d < 13 * n)
    (hi₁ : i₁ ∈ Finset.Icc 1 5) (hi₂ : i₂ ∈ Finset.Icc 1 5)
    (hineq : i₁ ≠ i₂) :
    k5NormalizedTangentCombination n d 3 4 i₁ i₂ ≠ 0 := by
  have hi₁lo := (Finset.mem_Icc.mp hi₁).1
  have hi₁hi := (Finset.mem_Icc.mp hi₁).2
  have hi₂lo := (Finset.mem_Icc.mp hi₂).1
  have hi₂hi := (Finset.mem_Icc.mp hi₂).2
  have hnZ : (2811 : ℤ) ≤ n := by exact_mod_cast hn
  have hdZ : (5 : ℤ) ≤ d := by exact_mod_cast hd
  have hrZ : (40 : ℤ) * d < 13 * n := by exact_mod_cast hratio
  intro hz
  unfold k5NormalizedTangentCombination at hz
  dsimp only at hz
  unfold k5LowerTangentWeight at hz
  interval_cases i₁ <;> interval_cases i₂ <;>
      norm_num [lc51, lc52, lc53, lc54, lc55,
        bipartiteTangentRowQuotient, bipartiteTangentColumnQuotient] at hz <;>
      simp_all <;>
      nlinarith [sq_nonneg ((13 : ℤ) * n - 40 * d),
        mul_nonneg (show (0 : ℤ) ≤ n - 2811 by omega)
          (show (0 : ℤ) ≤ n by omega),
        mul_pos (show (0 : ℤ) < 13 * n - 40 * d by omega)
          (show (0 : ℤ) < 1320 * n + 559 * d by omega)]


set_option maxHeartbeats 2000000 in
-- Normalize the twenty ordered column configurations for this fixed row pair.
private theorem fixed_3_5
    {n d i₁ i₂ : ℕ}
    (hn : 2811 ≤ n) (hd : 5 ≤ d) (hratio : 40 * d < 13 * n)
    (hi₁ : i₁ ∈ Finset.Icc 1 5) (hi₂ : i₂ ∈ Finset.Icc 1 5)
    (hineq : i₁ ≠ i₂) :
    k5NormalizedTangentCombination n d 3 5 i₁ i₂ ≠ 0 := by
  have hi₁lo := (Finset.mem_Icc.mp hi₁).1
  have hi₁hi := (Finset.mem_Icc.mp hi₁).2
  have hi₂lo := (Finset.mem_Icc.mp hi₂).1
  have hi₂hi := (Finset.mem_Icc.mp hi₂).2
  have hnZ : (2811 : ℤ) ≤ n := by exact_mod_cast hn
  have hdZ : (5 : ℤ) ≤ d := by exact_mod_cast hd
  have hrZ : (40 : ℤ) * d < 13 * n := by exact_mod_cast hratio
  intro hz
  unfold k5NormalizedTangentCombination at hz
  dsimp only at hz
  unfold k5LowerTangentWeight at hz
  interval_cases i₁ <;> interval_cases i₂ <;>
      norm_num [lc51, lc52, lc53, lc54, lc55,
        bipartiteTangentRowQuotient, bipartiteTangentColumnQuotient] at hz <;>
      simp_all <;>
      nlinarith [sq_nonneg ((13 : ℤ) * n - 40 * d),
        mul_nonneg (show (0 : ℤ) ≤ n - 2811 by omega)
          (show (0 : ℤ) ≤ n by omega),
        mul_pos (show (0 : ℤ) < 13 * n - 40 * d by omega)
          (show (0 : ℤ) < 1320 * n + 559 * d by omega)]


set_option maxHeartbeats 2000000 in
-- Normalize the twenty ordered column configurations for this fixed row pair.
private theorem fixed_4_1
    {n d i₁ i₂ : ℕ}
    (hn : 2811 ≤ n) (hd : 5 ≤ d) (hratio : 40 * d < 13 * n)
    (hi₁ : i₁ ∈ Finset.Icc 1 5) (hi₂ : i₂ ∈ Finset.Icc 1 5)
    (hineq : i₁ ≠ i₂) :
    k5NormalizedTangentCombination n d 4 1 i₁ i₂ ≠ 0 := by
  have hi₁lo := (Finset.mem_Icc.mp hi₁).1
  have hi₁hi := (Finset.mem_Icc.mp hi₁).2
  have hi₂lo := (Finset.mem_Icc.mp hi₂).1
  have hi₂hi := (Finset.mem_Icc.mp hi₂).2
  have hnZ : (2811 : ℤ) ≤ n := by exact_mod_cast hn
  have hdZ : (5 : ℤ) ≤ d := by exact_mod_cast hd
  have hrZ : (40 : ℤ) * d < 13 * n := by exact_mod_cast hratio
  intro hz
  unfold k5NormalizedTangentCombination at hz
  dsimp only at hz
  unfold k5LowerTangentWeight at hz
  interval_cases i₁ <;> interval_cases i₂ <;>
      norm_num [lc51, lc52, lc53, lc54, lc55,
        bipartiteTangentRowQuotient, bipartiteTangentColumnQuotient] at hz <;>
      simp_all <;>
      nlinarith [sq_nonneg ((13 : ℤ) * n - 40 * d),
        mul_nonneg (show (0 : ℤ) ≤ n - 2811 by omega)
          (show (0 : ℤ) ≤ n by omega),
        mul_pos (show (0 : ℤ) < 13 * n - 40 * d by omega)
          (show (0 : ℤ) < 1320 * n + 559 * d by omega)]


set_option maxHeartbeats 2000000 in
-- Normalize the twenty ordered column configurations for this fixed row pair.
private theorem fixed_4_2
    {n d i₁ i₂ : ℕ}
    (hn : 2811 ≤ n) (hd : 5 ≤ d) (hratio : 40 * d < 13 * n)
    (hi₁ : i₁ ∈ Finset.Icc 1 5) (hi₂ : i₂ ∈ Finset.Icc 1 5)
    (hineq : i₁ ≠ i₂) :
    k5NormalizedTangentCombination n d 4 2 i₁ i₂ ≠ 0 := by
  have hi₁lo := (Finset.mem_Icc.mp hi₁).1
  have hi₁hi := (Finset.mem_Icc.mp hi₁).2
  have hi₂lo := (Finset.mem_Icc.mp hi₂).1
  have hi₂hi := (Finset.mem_Icc.mp hi₂).2
  have hnZ : (2811 : ℤ) ≤ n := by exact_mod_cast hn
  have hdZ : (5 : ℤ) ≤ d := by exact_mod_cast hd
  have hrZ : (40 : ℤ) * d < 13 * n := by exact_mod_cast hratio
  intro hz
  unfold k5NormalizedTangentCombination at hz
  dsimp only at hz
  unfold k5LowerTangentWeight at hz
  interval_cases i₁ <;> interval_cases i₂ <;>
      norm_num [lc51, lc52, lc53, lc54, lc55,
        bipartiteTangentRowQuotient, bipartiteTangentColumnQuotient] at hz <;>
      simp_all <;>
      nlinarith [sq_nonneg ((13 : ℤ) * n - 40 * d),
        mul_nonneg (show (0 : ℤ) ≤ n - 2811 by omega)
          (show (0 : ℤ) ≤ n by omega),
        mul_pos (show (0 : ℤ) < 13 * n - 40 * d by omega)
          (show (0 : ℤ) < 1320 * n + 559 * d by omega)]


set_option maxHeartbeats 2000000 in
-- Normalize the twenty ordered column configurations for this fixed row pair.
private theorem fixed_4_3
    {n d i₁ i₂ : ℕ}
    (hn : 2811 ≤ n) (hd : 5 ≤ d) (hratio : 40 * d < 13 * n)
    (hi₁ : i₁ ∈ Finset.Icc 1 5) (hi₂ : i₂ ∈ Finset.Icc 1 5)
    (hineq : i₁ ≠ i₂) :
    k5NormalizedTangentCombination n d 4 3 i₁ i₂ ≠ 0 := by
  have hi₁lo := (Finset.mem_Icc.mp hi₁).1
  have hi₁hi := (Finset.mem_Icc.mp hi₁).2
  have hi₂lo := (Finset.mem_Icc.mp hi₂).1
  have hi₂hi := (Finset.mem_Icc.mp hi₂).2
  have hnZ : (2811 : ℤ) ≤ n := by exact_mod_cast hn
  have hdZ : (5 : ℤ) ≤ d := by exact_mod_cast hd
  have hrZ : (40 : ℤ) * d < 13 * n := by exact_mod_cast hratio
  intro hz
  unfold k5NormalizedTangentCombination at hz
  dsimp only at hz
  unfold k5LowerTangentWeight at hz
  interval_cases i₁ <;> interval_cases i₂ <;>
      norm_num [lc51, lc52, lc53, lc54, lc55,
        bipartiteTangentRowQuotient, bipartiteTangentColumnQuotient] at hz <;>
      simp_all <;>
      nlinarith [sq_nonneg ((13 : ℤ) * n - 40 * d),
        mul_nonneg (show (0 : ℤ) ≤ n - 2811 by omega)
          (show (0 : ℤ) ≤ n by omega),
        mul_pos (show (0 : ℤ) < 13 * n - 40 * d by omega)
          (show (0 : ℤ) < 1320 * n + 559 * d by omega)]


set_option maxHeartbeats 2000000 in
-- Normalize the twenty ordered column configurations for this fixed row pair.
private theorem fixed_4_5
    {n d i₁ i₂ : ℕ}
    (hn : 2811 ≤ n) (hd : 5 ≤ d) (hratio : 40 * d < 13 * n)
    (hi₁ : i₁ ∈ Finset.Icc 1 5) (hi₂ : i₂ ∈ Finset.Icc 1 5)
    (hineq : i₁ ≠ i₂) :
    k5NormalizedTangentCombination n d 4 5 i₁ i₂ ≠ 0 := by
  have hi₁lo := (Finset.mem_Icc.mp hi₁).1
  have hi₁hi := (Finset.mem_Icc.mp hi₁).2
  have hi₂lo := (Finset.mem_Icc.mp hi₂).1
  have hi₂hi := (Finset.mem_Icc.mp hi₂).2
  have hnZ : (2811 : ℤ) ≤ n := by exact_mod_cast hn
  have hdZ : (5 : ℤ) ≤ d := by exact_mod_cast hd
  have hrZ : (40 : ℤ) * d < 13 * n := by exact_mod_cast hratio
  intro hz
  unfold k5NormalizedTangentCombination at hz
  dsimp only at hz
  unfold k5LowerTangentWeight at hz
  interval_cases i₁ <;> interval_cases i₂ <;>
      norm_num [lc51, lc52, lc53, lc54, lc55,
        bipartiteTangentRowQuotient, bipartiteTangentColumnQuotient] at hz <;>
      simp_all <;>
      nlinarith [sq_nonneg ((13 : ℤ) * n - 40 * d),
        mul_nonneg (show (0 : ℤ) ≤ n - 2811 by omega)
          (show (0 : ℤ) ≤ n by omega),
        mul_pos (show (0 : ℤ) < 13 * n - 40 * d by omega)
          (show (0 : ℤ) < 1320 * n + 559 * d by omega)]


set_option maxHeartbeats 2000000 in
-- Normalize the twenty ordered column configurations for this fixed row pair.
private theorem fixed_5_1
    {n d i₁ i₂ : ℕ}
    (hn : 2811 ≤ n) (hd : 5 ≤ d) (hratio : 40 * d < 13 * n)
    (hi₁ : i₁ ∈ Finset.Icc 1 5) (hi₂ : i₂ ∈ Finset.Icc 1 5)
    (hineq : i₁ ≠ i₂) :
    k5NormalizedTangentCombination n d 5 1 i₁ i₂ ≠ 0 := by
  have hi₁lo := (Finset.mem_Icc.mp hi₁).1
  have hi₁hi := (Finset.mem_Icc.mp hi₁).2
  have hi₂lo := (Finset.mem_Icc.mp hi₂).1
  have hi₂hi := (Finset.mem_Icc.mp hi₂).2
  have hnZ : (2811 : ℤ) ≤ n := by exact_mod_cast hn
  have hdZ : (5 : ℤ) ≤ d := by exact_mod_cast hd
  have hrZ : (40 : ℤ) * d < 13 * n := by exact_mod_cast hratio
  intro hz
  unfold k5NormalizedTangentCombination at hz
  dsimp only at hz
  unfold k5LowerTangentWeight at hz
  interval_cases i₁ <;> interval_cases i₂ <;>
      norm_num [lc51, lc52, lc53, lc54, lc55,
        bipartiteTangentRowQuotient, bipartiteTangentColumnQuotient] at hz <;>
      simp_all <;>
      nlinarith [sq_nonneg ((13 : ℤ) * n - 40 * d),
        mul_nonneg (show (0 : ℤ) ≤ n - 2811 by omega)
          (show (0 : ℤ) ≤ n by omega),
        mul_pos (show (0 : ℤ) < 13 * n - 40 * d by omega)
          (show (0 : ℤ) < 1320 * n + 559 * d by omega)]


set_option maxHeartbeats 2000000 in
-- Normalize the twenty ordered column configurations for this fixed row pair.
private theorem fixed_5_2
    {n d i₁ i₂ : ℕ}
    (hn : 2811 ≤ n) (hd : 5 ≤ d) (hratio : 40 * d < 13 * n)
    (hi₁ : i₁ ∈ Finset.Icc 1 5) (hi₂ : i₂ ∈ Finset.Icc 1 5)
    (hineq : i₁ ≠ i₂) :
    k5NormalizedTangentCombination n d 5 2 i₁ i₂ ≠ 0 := by
  have hi₁lo := (Finset.mem_Icc.mp hi₁).1
  have hi₁hi := (Finset.mem_Icc.mp hi₁).2
  have hi₂lo := (Finset.mem_Icc.mp hi₂).1
  have hi₂hi := (Finset.mem_Icc.mp hi₂).2
  have hnZ : (2811 : ℤ) ≤ n := by exact_mod_cast hn
  have hdZ : (5 : ℤ) ≤ d := by exact_mod_cast hd
  have hrZ : (40 : ℤ) * d < 13 * n := by exact_mod_cast hratio
  intro hz
  unfold k5NormalizedTangentCombination at hz
  dsimp only at hz
  unfold k5LowerTangentWeight at hz
  interval_cases i₁ <;> interval_cases i₂ <;>
      norm_num [lc51, lc52, lc53, lc54, lc55,
        bipartiteTangentRowQuotient, bipartiteTangentColumnQuotient] at hz <;>
      simp_all <;>
      nlinarith [sq_nonneg ((13 : ℤ) * n - 40 * d),
        mul_nonneg (show (0 : ℤ) ≤ n - 2811 by omega)
          (show (0 : ℤ) ≤ n by omega),
        mul_pos (show (0 : ℤ) < 13 * n - 40 * d by omega)
          (show (0 : ℤ) < 1320 * n + 559 * d by omega)]


set_option maxHeartbeats 2000000 in
-- Normalize the twenty ordered column configurations for this fixed row pair.
private theorem fixed_5_3
    {n d i₁ i₂ : ℕ}
    (hn : 2811 ≤ n) (hd : 5 ≤ d) (hratio : 40 * d < 13 * n)
    (hi₁ : i₁ ∈ Finset.Icc 1 5) (hi₂ : i₂ ∈ Finset.Icc 1 5)
    (hineq : i₁ ≠ i₂) :
    k5NormalizedTangentCombination n d 5 3 i₁ i₂ ≠ 0 := by
  have hi₁lo := (Finset.mem_Icc.mp hi₁).1
  have hi₁hi := (Finset.mem_Icc.mp hi₁).2
  have hi₂lo := (Finset.mem_Icc.mp hi₂).1
  have hi₂hi := (Finset.mem_Icc.mp hi₂).2
  have hnZ : (2811 : ℤ) ≤ n := by exact_mod_cast hn
  have hdZ : (5 : ℤ) ≤ d := by exact_mod_cast hd
  have hrZ : (40 : ℤ) * d < 13 * n := by exact_mod_cast hratio
  intro hz
  unfold k5NormalizedTangentCombination at hz
  dsimp only at hz
  unfold k5LowerTangentWeight at hz
  interval_cases i₁ <;> interval_cases i₂ <;>
      norm_num [lc51, lc52, lc53, lc54, lc55,
        bipartiteTangentRowQuotient, bipartiteTangentColumnQuotient] at hz <;>
      simp_all <;>
      nlinarith [sq_nonneg ((13 : ℤ) * n - 40 * d),
        mul_nonneg (show (0 : ℤ) ≤ n - 2811 by omega)
          (show (0 : ℤ) ≤ n by omega),
        mul_pos (show (0 : ℤ) < 13 * n - 40 * d by omega)
          (show (0 : ℤ) < 1320 * n + 559 * d by omega)]


set_option maxHeartbeats 2000000 in
-- Normalize the twenty ordered column configurations for this fixed row pair.
private theorem fixed_5_4
    {n d i₁ i₂ : ℕ}
    (hn : 2811 ≤ n) (hd : 5 ≤ d) (hratio : 40 * d < 13 * n)
    (hi₁ : i₁ ∈ Finset.Icc 1 5) (hi₂ : i₂ ∈ Finset.Icc 1 5)
    (hineq : i₁ ≠ i₂) :
    k5NormalizedTangentCombination n d 5 4 i₁ i₂ ≠ 0 := by
  have hi₁lo := (Finset.mem_Icc.mp hi₁).1
  have hi₁hi := (Finset.mem_Icc.mp hi₁).2
  have hi₂lo := (Finset.mem_Icc.mp hi₂).1
  have hi₂hi := (Finset.mem_Icc.mp hi₂).2
  have hnZ : (2811 : ℤ) ≤ n := by exact_mod_cast hn
  have hdZ : (5 : ℤ) ≤ d := by exact_mod_cast hd
  have hrZ : (40 : ℤ) * d < 13 * n := by exact_mod_cast hratio
  intro hz
  unfold k5NormalizedTangentCombination at hz
  dsimp only at hz
  unfold k5LowerTangentWeight at hz
  interval_cases i₁ <;> interval_cases i₂ <;>
      norm_num [lc51, lc52, lc53, lc54, lc55,
        bipartiteTangentRowQuotient, bipartiteTangentColumnQuotient] at hz <;>
      simp_all <;>
      nlinarith [sq_nonneg ((13 : ℤ) * n - 40 * d),
        mul_nonneg (show (0 : ℤ) ≤ n - 2811 by omega)
          (show (0 : ℤ) ≤ n by omega),
        mul_pos (show (0 : ℤ) < 13 * n - 40 * d by omega)
          (show (0 : ℤ) < 1320 * n + 559 * d by omega)]


/-!
The weaker cone `5 ≤ d < n` is not sufficient here.  For example, the
ordered tuple `(j₁,j₂,i₁,i₂,t)=(2,3,1,3,3)` has zero coefficient at
`(n,d)=(2996,989)`, and the tuple `(3,4,3,5,3)` has zero coefficient at
`(1120,369)`; both also satisfy `4 ∣ n+d+t`.  The strict ratio
`40*d < 13*n`, supplied below by the centered equation, excludes this
genuine cone-crossing family.
-/


private theorem dispatch_1
    {n d j₂ i₁ i₂ : ℕ}
    (hn : 2811 ≤ n) (hd : 5 ≤ d) (hratio : 40 * d < 13 * n)
    (hj₂ : j₂ ∈ Finset.Icc 1 5) (hjne : 1 ≠ j₂)
    (hi₁ : i₁ ∈ Finset.Icc 1 5) (hi₂ : i₂ ∈ Finset.Icc 1 5)
    (hineq : i₁ ≠ i₂) :
    k5NormalizedTangentCombination n d 1 j₂ i₁ i₂ ≠ 0 := by
  have hj₂lo := (Finset.mem_Icc.mp hj₂).1
  have hj₂hi := (Finset.mem_Icc.mp hj₂).2
  have hcases : j₂ = 2 ∨ j₂ = 3 ∨ j₂ = 4 ∨ j₂ = 5 := by omega
  rcases hcases with h1 | h2 | h3 | h4
  · subst j₂
    exact fixed_1_2 hn hd hratio hi₁ hi₂ hineq
  · subst j₂
    exact fixed_1_3 hn hd hratio hi₁ hi₂ hineq
  · subst j₂
    exact fixed_1_4 hn hd hratio hi₁ hi₂ hineq
  · subst j₂
    exact fixed_1_5 hn hd hratio hi₁ hi₂ hineq

private theorem dispatch_2
    {n d j₂ i₁ i₂ : ℕ}
    (hn : 2811 ≤ n) (hd : 5 ≤ d) (hratio : 40 * d < 13 * n)
    (hj₂ : j₂ ∈ Finset.Icc 1 5) (hjne : 2 ≠ j₂)
    (hi₁ : i₁ ∈ Finset.Icc 1 5) (hi₂ : i₂ ∈ Finset.Icc 1 5)
    (hineq : i₁ ≠ i₂) :
    k5NormalizedTangentCombination n d 2 j₂ i₁ i₂ ≠ 0 := by
  have hj₂lo := (Finset.mem_Icc.mp hj₂).1
  have hj₂hi := (Finset.mem_Icc.mp hj₂).2
  have hcases : j₂ = 1 ∨ j₂ = 3 ∨ j₂ = 4 ∨ j₂ = 5 := by omega
  rcases hcases with h1 | h2 | h3 | h4
  · subst j₂
    exact fixed_2_1 hn hd hratio hi₁ hi₂ hineq
  · subst j₂
    exact fixed_2_3 hn hd hratio hi₁ hi₂ hineq
  · subst j₂
    exact fixed_2_4 hn hd hratio hi₁ hi₂ hineq
  · subst j₂
    exact fixed_2_5 hn hd hratio hi₁ hi₂ hineq

private theorem dispatch_3
    {n d j₂ i₁ i₂ : ℕ}
    (hn : 2811 ≤ n) (hd : 5 ≤ d) (hratio : 40 * d < 13 * n)
    (hj₂ : j₂ ∈ Finset.Icc 1 5) (hjne : 3 ≠ j₂)
    (hi₁ : i₁ ∈ Finset.Icc 1 5) (hi₂ : i₂ ∈ Finset.Icc 1 5)
    (hineq : i₁ ≠ i₂) :
    k5NormalizedTangentCombination n d 3 j₂ i₁ i₂ ≠ 0 := by
  have hj₂lo := (Finset.mem_Icc.mp hj₂).1
  have hj₂hi := (Finset.mem_Icc.mp hj₂).2
  have hcases : j₂ = 1 ∨ j₂ = 2 ∨ j₂ = 4 ∨ j₂ = 5 := by omega
  rcases hcases with h1 | h2 | h3 | h4
  · subst j₂
    exact fixed_3_1 hn hd hratio hi₁ hi₂ hineq
  · subst j₂
    exact fixed_3_2 hn hd hratio hi₁ hi₂ hineq
  · subst j₂
    exact fixed_3_4 hn hd hratio hi₁ hi₂ hineq
  · subst j₂
    exact fixed_3_5 hn hd hratio hi₁ hi₂ hineq

private theorem dispatch_4
    {n d j₂ i₁ i₂ : ℕ}
    (hn : 2811 ≤ n) (hd : 5 ≤ d) (hratio : 40 * d < 13 * n)
    (hj₂ : j₂ ∈ Finset.Icc 1 5) (hjne : 4 ≠ j₂)
    (hi₁ : i₁ ∈ Finset.Icc 1 5) (hi₂ : i₂ ∈ Finset.Icc 1 5)
    (hineq : i₁ ≠ i₂) :
    k5NormalizedTangentCombination n d 4 j₂ i₁ i₂ ≠ 0 := by
  have hj₂lo := (Finset.mem_Icc.mp hj₂).1
  have hj₂hi := (Finset.mem_Icc.mp hj₂).2
  have hcases : j₂ = 1 ∨ j₂ = 2 ∨ j₂ = 3 ∨ j₂ = 5 := by omega
  rcases hcases with h1 | h2 | h3 | h4
  · subst j₂
    exact fixed_4_1 hn hd hratio hi₁ hi₂ hineq
  · subst j₂
    exact fixed_4_2 hn hd hratio hi₁ hi₂ hineq
  · subst j₂
    exact fixed_4_3 hn hd hratio hi₁ hi₂ hineq
  · subst j₂
    exact fixed_4_5 hn hd hratio hi₁ hi₂ hineq

private theorem dispatch_5
    {n d j₂ i₁ i₂ : ℕ}
    (hn : 2811 ≤ n) (hd : 5 ≤ d) (hratio : 40 * d < 13 * n)
    (hj₂ : j₂ ∈ Finset.Icc 1 5) (hjne : 5 ≠ j₂)
    (hi₁ : i₁ ∈ Finset.Icc 1 5) (hi₂ : i₂ ∈ Finset.Icc 1 5)
    (hineq : i₁ ≠ i₂) :
    k5NormalizedTangentCombination n d 5 j₂ i₁ i₂ ≠ 0 := by
  have hj₂lo := (Finset.mem_Icc.mp hj₂).1
  have hj₂hi := (Finset.mem_Icc.mp hj₂).2
  have hcases : j₂ = 1 ∨ j₂ = 2 ∨ j₂ = 3 ∨ j₂ = 4 := by omega
  rcases hcases with h1 | h2 | h3 | h4
  · subst j₂
    exact fixed_5_1 hn hd hratio hi₁ hi₂ hineq
  · subst j₂
    exact fixed_5_2 hn hd hratio hi₁ hi₂ hineq
  · subst j₂
    exact fixed_5_3 hn hd hratio hi₁ hi₂ hineq
  · subst j₂
    exact fixed_5_4 hn hd hratio hi₁ hi₂ hineq

theorem k5NormalizedTangentCombination_ne_zero_of_ratio
    {n d j₁ j₂ i₁ i₂ : ℕ}
    (hn : 2811 ≤ n) (hd : 5 ≤ d) (hratio : 40 * d < 13 * n)
    (hj₁ : j₁ ∈ Finset.Icc 1 5) (hj₂ : j₂ ∈ Finset.Icc 1 5)
    (hi₁ : i₁ ∈ Finset.Icc 1 5) (hi₂ : i₂ ∈ Finset.Icc 1 5)
    (hjneq : j₁ ≠ j₂) (hineq : i₁ ≠ i₂) :
    k5NormalizedTangentCombination n d j₁ j₂ i₁ i₂ ≠ 0 := by
  have hj₁lo := (Finset.mem_Icc.mp hj₁).1
  have hj₁hi := (Finset.mem_Icc.mp hj₁).2
  have hcases : j₁ = 1 ∨ j₁ = 2 ∨ j₁ = 3 ∨ j₁ = 4 ∨ j₁ = 5 := by omega
  rcases hcases with h1 | h2 | h3 | h4 | h5
  · subst j₁
    exact dispatch_1 hn hd hratio hj₂ hjneq hi₁ hi₂ hineq
  · subst j₁
    exact dispatch_2 hn hd hratio hj₂ hjneq hi₁ hi₂ hineq
  · subst j₁
    exact dispatch_3 hn hd hratio hj₂ hjneq hi₁ hi₂ hineq
  · subst j₁
    exact dispatch_4 hn hd hratio hj₂ hjneq hi₁ hi₂ hineq
  · subst j₁
    exact dispatch_5 hn hd hratio hj₂ hjneq hi₁ hi₂ hineq


theorem k5ProperTangentCombination_ne_zero_of_ratio
    {n d t j₁ j₂ i₁ i₂ : ℕ}
    (hn : 2811 ≤ n) (hd : 5 ≤ d) (hratio : 40 * d < 13 * n)
    (hfour : 4 ∣ n + d + t)
    (hj₁ : j₁ ∈ Finset.Icc 1 5) (hj₂ : j₂ ∈ Finset.Icc 1 5)
    (hi₁ : i₁ ∈ Finset.Icc 1 5) (hi₂ : i₂ ∈ Finset.Icc 1 5)
    (hjneq : j₁ ≠ j₂) (hineq : i₁ ≠ i₂) :
    k5ProperTangentCombination n d t j₁ j₂ i₁ i₂ ≠ 0 := by
  rw [k5ProperTangentCombination_eq_multiplier_mul_normalized hfour]
  apply mul_ne_zero
  · apply mul_ne_zero <;>
      unfold k5UpperFourMultiplier <;> split <;> norm_num
  · exact k5NormalizedTangentCombination_ne_zero_of_ratio
      hn hd hratio hj₁ hj₂ hi₁ hi₂ hjneq hineq

/-- Solution-facing form: the centered equation supplies the rational ratio,
so every one of the 2000 ordered `(t,j₁,j₂,i₁,i₂)` configurations has a
nonzero opposite-secant/tangent coefficient on the surviving tail. -/
theorem k5ProperTangentCombination_ne_zero_of_solution
    {n d t j₁ j₂ i₁ i₂ : ℕ}
    (hn : 2811 ≤ n) (hd : 5 ≤ d)
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n)
    (hfour : 4 ∣ n + d + t)
    (hj₁ : j₁ ∈ Finset.Icc 1 5) (hj₂ : j₂ ∈ Finset.Icc 1 5)
    (hi₁ : i₁ ∈ Finset.Icc 1 5) (hi₂ : i₂ ∈ Finset.Icc 1 5)
    (hjneq : j₁ ≠ j₂) (hineq : i₁ ≠ i₂) :
    k5ProperTangentCombination n d t j₁ j₂ i₁ i₂ ≠ 0 := by
  exact k5ProperTangentCombination_ne_zero_of_ratio hn hd
    (forty_gap_lt_thirteen_start_of_k5_solution (by omega) heq) hfour
    hj₁ hj₂ hi₁ hi₂ hjneq hineq


end Erdos686.Erdos686Variant
