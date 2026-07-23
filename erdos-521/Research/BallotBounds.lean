import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Erdos521

/-- The normalized central binomial coefficient at even length. -/
noncomputable def evenCentralMass (k : ℕ) : ℝ :=
  (Nat.centralBinom k : ℝ) / (4 : ℝ) ^ k

/-- The normalized middle binomial coefficient at arbitrary length. -/
noncomputable def ballotMass (n : ℕ) : ℝ :=
  (Nat.choose n (n / 2) : ℝ) / (2 : ℝ) ^ n

lemma evenCentralMass_nonneg (k : ℕ) : 0 ≤ evenCentralMass k := by
  exact div_nonneg (by positivity) (by positivity)

lemma evenCentralMass_succ (k : ℕ) :
    evenCentralMass (k + 1) =
      evenCentralMass k * ((2 * (k : ℝ) + 1) / (2 * (k + 1))) := by
  have hrec : ((k + 1) * Nat.centralBinom (k + 1) : ℕ) =
      2 * (2 * k + 1) * Nat.centralBinom k := Nat.succ_mul_centralBinom_succ k
  have hrecR : ((k + 1 : ℕ) : ℝ) * (Nat.centralBinom (k + 1) : ℝ) =
      2 * (2 * (k : ℝ) + 1) * (Nat.centralBinom k : ℝ) := by
    exact_mod_cast hrec
  norm_num at hrecR
  rw [evenCentralMass, evenCentralMass, pow_succ]
  field_simp
  nlinarith [hrecR]

lemma ratio_sq_lower (k : ℕ) (hk : 1 ≤ k) :
    (k : ℝ) / (k + 1) ≤ ((2 * (k : ℝ) + 1) / (2 * (k + 1))) ^ 2 := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk1 : (0 : ℝ) < k + 1 := by positivity
  field_simp
  nlinarith

/-- A fully elementary Wallis-type lower bound, obtained from the exact central-binomial
recurrence. -/
lemma evenCentralMass_sq_lower_succ (k : ℕ) :
    1 / (4 * ((k + 1 : ℕ) : ℝ)) ≤ evenCentralMass (k + 1) ^ 2 := by
  induction k with
  | zero =>
      norm_num [evenCentralMass, Nat.centralBinom]
  | succ k ih =>
      rw [evenCentralMass_succ]
      have hk : 1 ≤ k + 1 := by omega
      have hratio := ratio_sq_lower (k + 1) hk
      have hid : 1 / (4 * (((k + 1) + 1 : ℕ) : ℝ)) =
          (1 / (4 * (((k + 1 : ℕ)) : ℝ))) *
            (((k + 1 : ℕ) : ℝ) / ((k + 1 : ℕ) + 1)) := by
        norm_num
        field_simp
      rw [hid]
      calc
        (1 / (4 * (((k + 1 : ℕ)) : ℝ))) *
              (((k + 1 : ℕ) : ℝ) / ((k + 1 : ℕ) + 1)) ≤
            evenCentralMass (k + 1) ^ 2 *
              ((2 * (((k + 1 : ℕ)) : ℝ) + 1) /
                (2 * ((((k + 1 : ℕ)) : ℝ) + 1))) ^ 2 := by
          gcongr
        _ = (evenCentralMass (k + 1) *
              ((2 * (((k + 1 : ℕ)) : ℝ) + 1) /
                (2 * ((((k + 1 : ℕ)) : ℝ) + 1)))) ^ 2 := by ring

lemma evenCentralMass_sq_lower {k : ℕ} (hk : 1 ≤ k) :
    1 / (4 * (k : ℝ)) ≤ evenCentralMass k ^ 2 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    evenCentralMass_sq_lower_succ j

lemma ballotMass_even (k : ℕ) : ballotMass (2 * k) = evenCentralMass k := by
  rw [ballotMass, evenCentralMass, Nat.centralBinom_eq_two_mul_choose]
  have hdiv : 2 * k / 2 = k := by omega
  rw [hdiv, pow_mul]
  norm_num

lemma choose_odd_middle_mul (k : ℕ) :
    Nat.choose (2 * k) k * (2 * k + 1) = Nat.choose (2 * k + 1) k * (k + 1) := by
  have hsub : 2 * k + 1 - k = k + 1 := by omega
  simpa only [hsub] using Nat.choose_mul_succ_eq (2 * k) k

lemma ballotMass_odd (k : ℕ) :
    ballotMass (2 * k + 1) =
      evenCentralMass k * ((2 * (k : ℝ) + 1) / (2 * (k + 1))) := by
  have hchoose := choose_odd_middle_mul k
  have hchooseR : (Nat.choose (2 * k) k : ℝ) * (2 * (k : ℝ) + 1) =
      (Nat.choose (2 * k + 1) k : ℝ) * (k + 1) := by
    exact_mod_cast hchoose
  rw [ballotMass, evenCentralMass, Nat.centralBinom_eq_two_mul_choose]
  have hdiv : (2 * k + 1) / 2 = k := by omega
  rw [hdiv, pow_succ, pow_mul]
  norm_num
  field_simp
  nlinarith

lemma ballotMass_nonneg (n : ℕ) : 0 ≤ ballotMass n := by
  exact div_nonneg (by positivity) (by positivity)

/-- Uniform inverse-linear lower bound for the square of the one-dimensional ballot mass. -/
lemma ballotMass_sq_lower (n : ℕ) :
    1 / (16 * ((n : ℝ) + 1)) ≤ ballotMass n ^ 2 := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [ballotMass_even]
    by_cases hk0 : k = 0
    · subst k
      norm_num [evenCentralMass, Nat.centralBinom]
    · have hk : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
      have hmain := evenCentralMass_sq_lower hk
      have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
      calc
        1 / (16 * (((2 * k : ℕ) : ℝ) + 1)) ≤ 1 / (4 * (k : ℝ)) := by
          norm_num
          field_simp
          nlinarith
        _ ≤ evenCentralMass k ^ 2 := hmain
  · rw [ballotMass_odd]
    by_cases hk0 : k = 0
    · subst k
      norm_num [evenCentralMass, Nat.centralBinom]
    · have hk : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
      have hmain := evenCentralMass_sq_lower hk
      have hratio : (1 : ℝ) / 4 ≤
          ((2 * (k : ℝ) + 1) / (2 * (k + 1))) ^ 2 := by
        have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
        have hk1 : (0 : ℝ) < k + 1 := by positivity
        field_simp
        nlinarith
      calc
        1 / (16 * ((((2 * k + 1 : ℕ)) : ℝ) + 1)) ≤
            (1 / (4 * (k : ℝ))) * ((1 : ℝ) / 4) := by
          norm_num
          field_simp
          nlinarith
        _ ≤ evenCentralMass k ^ 2 *
            ((2 * (k : ℝ) + 1) / (2 * (k + 1))) ^ 2 := by
          gcongr
        _ = (evenCentralMass k *
            ((2 * (k : ℝ) + 1) / (2 * (k + 1)))) ^ 2 := by ring

/-- Two one-dimensional meander masses whose lengths sum to `r+s` have a uniform
inverse-linear product lower bound. -/
lemma ballotMass_mul_lower (r s : ℕ) :
    1 / (16 * (((r + s : ℕ) : ℝ) + 1)) ≤ ballotMass r * ballotMass s := by
  have hr0 : (0 : ℝ) ≤ r := by positivity
  have hs0 : (0 : ℝ) ≤ s := by positivity
  have hr1 : (0 : ℝ) < r + 1 := by positivity
  have hs1 : (0 : ℝ) < s + 1 := by positivity
  have hrs1 : (0 : ℝ) < (r + s : ℕ) + 1 := by positivity
  have hden : ((r : ℝ) + 1) * ((s : ℝ) + 1) ≤
      (((r + s : ℕ) : ℝ) + 1) ^ 2 := by
    norm_num
    nlinarith [mul_nonneg hr0 hs0, sq_nonneg ((r : ℝ) + s)]
  have hsq : (1 / (16 * (((r + s : ℕ) : ℝ) + 1))) ^ 2 ≤
      (ballotMass r * ballotMass s) ^ 2 := by
    calc
      (1 / (16 * (((r + s : ℕ) : ℝ) + 1))) ^ 2 ≤
          (1 / (16 * ((r : ℝ) + 1))) * (1 / (16 * ((s : ℝ) + 1))) := by
        field_simp
        nlinarith
      _ ≤ ballotMass r ^ 2 * ballotMass s ^ 2 := by
        gcongr
        · exact ballotMass_sq_lower r
        · exact ballotMass_sq_lower s
      _ = (ballotMass r * ballotMass s) ^ 2 := by ring
  exact (sq_le_sq₀ (by positivity)
    (mul_nonneg (ballotMass_nonneg r) (ballotMass_nonneg s))).mp hsq

end Erdos521
