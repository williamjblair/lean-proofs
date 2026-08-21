import Mathlib

/-!
# Erdős 399: Cambie's coprime fourth-power variant

This file proves the exact `cambie` occurrence from Formal Conjectures commit
`9c4d5821819656af53c5473ded2116ea14a7ff1c`. The target source is Apache-2.0;
these independently retained proof bytes are an original MIT-licensed
contribution to this repository.

The proof is the complete modulo-eight argument: every fourth power is
congruent modulo eight to its base modulo two, so all eight residue classes are
covered. The cases `n = 0, 1, 2, 3` are handled separately before using
`8 ∣ n !` for `4 ≤ n`.
-/

open Nat

namespace Erdos399

private theorem fourth_mod_eight (z : ℕ) : z ^ 4 % 8 = z % 2 := by
  rw [Nat.pow_mod]
  generalize hrdef : z % 8 = r
  have h2 : z % 2 = r % 2 := by
    rw [← hrdef, Nat.mod_mod_of_dvd z (by norm_num : 2 ∣ 8)]
  rw [h2]
  have hr : r < 8 := by
    rw [← hrdef]
    exact Nat.mod_lt z (by norm_num)
  interval_cases r <;> norm_num

private theorem coprime_not_both_even {x y : ℕ} (hcop : x.Coprime y) :
    ¬ (x % 2 = 0 ∧ y % 2 = 0) := by
  rintro ⟨hx, hy⟩
  have hd : 2 ∣ x.gcd y := Nat.dvd_gcd
    (Nat.dvd_of_mod_eq_zero hx) (Nat.dvd_of_mod_eq_zero hy)
  rw [hcop.gcd_eq_one] at hd
  norm_num at hd

/-- Cambie's modulo-eight exclusion for the exact coprime plus-sign
fourth-power occurrence in Erdős problem 399. -/
theorem erdos_399.variants.cambie {n x y : ℕ} :
    x.Coprime y → 1 < x * y → n ! ≠ x ^ 4 + y ^ 4 := by
  intro hcop hprod heq
  have hprodpos : 0 < x * y := by omega
  have hxpos : 0 < x := Nat.pos_of_mul_pos_right hprodpos
  have hypos : 0 < y := Nat.pos_of_mul_pos_left hprodpos
  have hxpow : 1 ≤ x ^ 4 := Nat.one_le_pow 4 x hxpos
  have hypow : 1 ≤ y ^ 4 := Nat.one_le_pow 4 y hypos
  by_cases hn : 4 ≤ n
  · have h8fac : 8 ∣ n ! := dvd_trans (by norm_num : 8 ∣ 4 !)
      (Nat.factorial_dvd_factorial hn)
    have hmod := congrArg (fun t : ℕ ↦ t % 8) heq
    change n ! % 8 = (x ^ 4 + y ^ 4) % 8 at hmod
    rw [Nat.dvd_iff_mod_eq_zero.mp h8fac, Nat.add_mod, fourth_mod_eight,
      fourth_mod_eight] at hmod
    have hxlt : x % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have hylt : y % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have hxe : x % 2 = 0 := by omega
    have hye : y % 2 = 0 := by omega
    exact coprime_not_both_even hcop ⟨hxe, hye⟩
  · have hn' : n ≤ 3 := by omega
    by_cases hn3 : n = 3
    · subst n
      have hmod := congrArg (fun t : ℕ ↦ t % 8) heq
      change 3 ! % 8 = (x ^ 4 + y ^ 4) % 8 at hmod
      norm_num [Nat.add_mod, fourth_mod_eight] at hmod
      have hxlt : x % 2 < 2 := Nat.mod_lt _ (by norm_num)
      have hylt : y % 2 < 2 := Nat.mod_lt _ (by norm_num)
      omega
    · have hn2 : n ≤ 2 := by omega
      have hfac : n ! ≤ 2 := by
        interval_cases n <;> norm_num
      rw [heq] at hfac
      have hxle : x ≤ 1 := by
        by_contra h
        have h16 : 2 ^ 4 ≤ x ^ 4 := Nat.pow_le_pow_left (by omega) 4
        norm_num at h16
        omega
      have hyle : y ≤ 1 := by
        by_contra h
        have h16 : 2 ^ 4 ≤ y ^ 4 := Nat.pow_le_pow_left (by omega) 4
        norm_num at h16
        omega
      have hxy : x * y ≤ 1 * 1 := Nat.mul_le_mul hxle hyle
      omega

end Erdos399
