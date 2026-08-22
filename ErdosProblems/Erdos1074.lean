import Mathlib

/-!
# Erdős 1074: initial EHS numbers

This file proves the exact `EHSNumbers_init` occurrence from Formal
Conjectures commit `9c4d5821819656af53c5473ded2116ea14a7ff1c`, source path
`FormalConjectures/ErdosProblems/1074.lean` (SHA-256
`72b74c90c3fbdf66fedcd744d6c90da05fdfc7e87673a016787ae4586c705c45`).
That target source is Apache-2.0; these independently retained proof bytes are
an original MIT-licensed contribution to this repository.

The proof checks both sides of the finite enumeration. Explicit prime
divisors witness membership for `8, 9, 13, 14, 15, 16, 17`; complete prime
factorizations exclude every other natural below `18`. `Nat.nth_count` then
turns those membership and exclusion facts into the required ordered
`Nat.nth` values before the image equality is proved.
-/

namespace Erdos1074

open scoped Nat
open Nat

/-- The exact Formal Conjectures definition of EHS numbers. -/
abbrev EHSNumbers : Set ℕ :=
  {m | 1 ≤ m ∧ ∃ p, p.Prime ∧ ¬p ≡ 1 [MOD m] ∧ p ∣ m ! + 1}

private theorem eq_of_prime_dvd_prime {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h : p ∣ q) : p = q := by
  rcases (Nat.dvd_prime hq).mp h with h | h
  · exact (hp.ne_one h).elim
  · exact h

private theorem prime_eq_of_dvd_product {p q r : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hr : r.Prime) (h : p ∣ q * r) : p = q ∨ p = r := by
  rcases hp.dvd_mul.mp h with h | h
  · exact Or.inl (eq_of_prime_dvd_prime hp hq h)
  · exact Or.inr (eq_of_prime_dvd_prime hp hr h)

private theorem notMem0 : ¬EHSNumbers 0 := by
  rintro ⟨h, _⟩
  omega

private theorem notMem1 : ¬EHSNumbers 1 := by
  rintro ⟨_, p, _, hmod, _⟩
  exact hmod (by simp only [Nat.ModEq, Nat.mod_one])

private theorem notMem2 : ¬EHSNumbers 2 := by
  rintro ⟨_, p, hp, hmod, hdvd⟩
  norm_num [Nat.factorial] at hdvd
  have : p = 3 := eq_of_prime_dvd_prime hp (by norm_num) hdvd
  subst p
  exact hmod (by norm_num [Nat.ModEq])

private theorem notMem3 : ¬EHSNumbers 3 := by
  rintro ⟨_, p, hp, hmod, hdvd⟩
  norm_num [Nat.factorial] at hdvd
  have : p = 7 := eq_of_prime_dvd_prime hp (by norm_num) hdvd
  subst p
  exact hmod (by norm_num [Nat.ModEq])

private theorem notMem4 : ¬EHSNumbers 4 := by
  rintro ⟨_, p, hp, hmod, hdvd⟩
  norm_num [Nat.factorial] at hdvd
  rw [show 25 = 5 ^ 2 by norm_num] at hdvd
  have hp5 : p ∣ 5 := hp.dvd_of_dvd_pow hdvd
  have : p = 5 := eq_of_prime_dvd_prime hp (by norm_num) hp5
  subst p
  exact hmod (by norm_num [Nat.ModEq])

private theorem notMem5 : ¬EHSNumbers 5 := by
  rintro ⟨_, p, hp, hmod, hdvd⟩
  norm_num [Nat.factorial] at hdvd
  rw [show 121 = 11 ^ 2 by norm_num] at hdvd
  have hp11 : p ∣ 11 := hp.dvd_of_dvd_pow hdvd
  have : p = 11 := eq_of_prime_dvd_prime hp (by norm_num) hp11
  subst p
  exact hmod (by norm_num [Nat.ModEq])

private theorem notMem6 : ¬EHSNumbers 6 := by
  rintro ⟨_, p, hp, hmod, hdvd⟩
  norm_num [Nat.factorial] at hdvd
  rw [show 721 = 7 * 103 by norm_num] at hdvd
  rcases prime_eq_of_dvd_product hp (by norm_num) (by norm_num) hdvd with h | h
  · subst p
    exact hmod (by norm_num [Nat.ModEq])
  · subst p
    exact hmod (by norm_num [Nat.ModEq])

private theorem notMem7 : ¬EHSNumbers 7 := by
  rintro ⟨_, p, hp, hmod, hdvd⟩
  norm_num [Nat.factorial] at hdvd
  rw [show 5041 = 71 ^ 2 by norm_num] at hdvd
  have hp71 : p ∣ 71 := hp.dvd_of_dvd_pow hdvd
  have : p = 71 := eq_of_prime_dvd_prime hp (by norm_num) hp71
  subst p
  exact hmod (by norm_num [Nat.ModEq])

private theorem mem8 : EHSNumbers 8 := by
  refine ⟨by norm_num, 61, by norm_num, ?_, ?_⟩
  · norm_num [Nat.ModEq]
  · norm_num [Nat.factorial]

private theorem mem9 : EHSNumbers 9 := by
  refine ⟨by norm_num, 71, by norm_num, ?_, ?_⟩
  · norm_num [Nat.ModEq]
  · norm_num [Nat.factorial]

private theorem notMem10 : ¬EHSNumbers 10 := by
  rintro ⟨_, p, hp, hmod, hdvd⟩
  norm_num [Nat.factorial] at hdvd
  rw [show 3628801 = 11 * 329891 by norm_num] at hdvd
  rcases prime_eq_of_dvd_product hp (by norm_num) (by norm_num) hdvd with h | h
  · subst p
    exact hmod (by norm_num [Nat.ModEq])
  · subst p
    exact hmod (by norm_num [Nat.ModEq])

private theorem notMem11 : ¬EHSNumbers 11 := by
  rintro ⟨_, p, hp, hmod, hdvd⟩
  norm_num [Nat.factorial] at hdvd
  have : p = 39916801 := eq_of_prime_dvd_prime hp (by norm_num) hdvd
  subst p
  exact hmod (by norm_num [Nat.ModEq])

private theorem notMem12 : ¬EHSNumbers 12 := by
  rintro ⟨_, p, hp, hmod, hdvd⟩
  norm_num [Nat.factorial] at hdvd
  rw [show 479001601 = 13 ^ 2 * 2834329 by norm_num] at hdvd
  rcases hp.dvd_mul.mp hdvd with h | h
  · have hp13 : p ∣ 13 := hp.dvd_of_dvd_pow h
    have : p = 13 := eq_of_prime_dvd_prime hp (by norm_num) hp13
    subst p
    exact hmod (by norm_num [Nat.ModEq])
  · have : p = 2834329 := eq_of_prime_dvd_prime hp (by norm_num) h
    subst p
    exact hmod (by norm_num [Nat.ModEq])

private theorem mem13 : EHSNumbers 13 := by
  refine ⟨by norm_num, 83, by norm_num, ?_, ?_⟩
  · norm_num [Nat.ModEq]
  · norm_num [Nat.factorial]

private theorem mem14 : EHSNumbers 14 := by
  refine ⟨by norm_num, 23, by norm_num, ?_, ?_⟩
  · norm_num [Nat.ModEq]
  · norm_num [Nat.factorial]

private theorem mem15 : EHSNumbers 15 := by
  refine ⟨by norm_num, 59, by norm_num, ?_, ?_⟩
  · norm_num [Nat.ModEq]
  · norm_num [Nat.factorial]

private theorem mem16 : EHSNumbers 16 := by
  refine ⟨by norm_num, 61, by norm_num, ?_, ?_⟩
  · norm_num [Nat.ModEq]
  · norm_num [Nat.factorial]

private theorem mem17 : EHSNumbers 17 := by
  refine ⟨by norm_num, 661, by norm_num, ?_, ?_⟩
  · norm_num [Nat.ModEq]
  · norm_num [Nat.factorial]

noncomputable local instance : DecidablePred EHSNumbers := fun _ => Classical.propDecidable _

private theorem nth0 : nth EHSNumbers 0 = 8 := by
  simpa [Nat.count_succ (p := EHSNumbers), notMem0, notMem1, notMem2, notMem3, notMem4, notMem5,
    notMem6, notMem7] using! Nat.nth_count mem8

private theorem nth1 : nth EHSNumbers 1 = 9 := by
  simpa [Nat.count_succ (p := EHSNumbers), notMem0, notMem1, notMem2, notMem3, notMem4, notMem5,
    notMem6, notMem7, mem8] using! Nat.nth_count mem9

private theorem nth2 : nth EHSNumbers 2 = 13 := by
  simpa [Nat.count_succ (p := EHSNumbers), notMem0, notMem1, notMem2, notMem3, notMem4, notMem5,
    notMem6, notMem7, mem8, mem9, notMem10, notMem11, notMem12] using!
      Nat.nth_count mem13

private theorem nth3 : nth EHSNumbers 3 = 14 := by
  simpa [Nat.count_succ (p := EHSNumbers), notMem0, notMem1, notMem2, notMem3, notMem4, notMem5,
    notMem6, notMem7, mem8, mem9, notMem10, notMem11, notMem12, mem13] using!
      Nat.nth_count mem14

private theorem nth4 : nth EHSNumbers 4 = 15 := by
  simpa [Nat.count_succ (p := EHSNumbers), notMem0, notMem1, notMem2, notMem3, notMem4, notMem5,
    notMem6, notMem7, mem8, mem9, notMem10, notMem11, notMem12, mem13, mem14] using!
      Nat.nth_count mem15

private theorem nth5 : nth EHSNumbers 5 = 16 := by
  simpa [Nat.count_succ (p := EHSNumbers), notMem0, notMem1, notMem2, notMem3, notMem4, notMem5,
    notMem6, notMem7, mem8, mem9, notMem10, notMem11, notMem12, mem13, mem14,
    mem15] using! Nat.nth_count mem16

private theorem nth6 : nth EHSNumbers 6 = 17 := by
  simpa [Nat.count_succ (p := EHSNumbers), Nat.count_zero (p := EHSNumbers), notMem0, notMem1,
    notMem2, notMem3, notMem4, notMem5,
    notMem6, notMem7, mem8, mem9, notMem10, notMem11, notMem12, mem13, mem14,
    mem15, mem16] using Nat.nth_count mem17

/-- The first seven EHS numbers, exactly as stated in Formal Conjectures. -/
theorem erdos_1074.variants.EHSNumbers_init :
    nth EHSNumbers '' (Set.Icc 0 6) = {8, 9, 13, 14, 15, 16, 17} := by
  ext m
  constructor
  · rintro ⟨i, ⟨hi0, hi6⟩, rfl⟩
    interval_cases i <;> simp [nth0, nth1, nth2, nth3, nth4, nth5, nth6]
  · intro hm
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, by simp, nth0⟩
    · exact ⟨1, by simp, nth1⟩
    · exact ⟨2, by simp, nth2⟩
    · exact ⟨3, by simp, nth3⟩
    · exact ⟨4, by simp, nth4⟩
    · exact ⟨5, by simp, nth5⟩
    · exact ⟨6, by simp, nth6⟩

end Erdos1074
