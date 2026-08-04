import Research.FiniteValidity
import Mathlib.NumberTheory.Padics.PadicVal.Basic

namespace Erdos321

/-- An element is exposed by the strict-valuation peeling rule when one prime
has strictly larger valuation on it than on every other denominator. -/
def HasStrictPadicLeader (A : Finset ℕ) (n : ℕ) : Prop :=
  ∃ p : ℕ, p.Prime ∧
    ∀ a ∈ A, a ≠ n → padicValNat p a < padicValNat p n

/-- A smallest convenient valid cycle with no strict p-adic leader. -/
def noPrivateLeaderSet : Finset ℕ := {6, 14, 21}

theorem noPrivateLeaderSet_valid : Valid noPrivateLeaderSet := by
  rw [valid_iff_finiteValid]
  native_decide

/-- No element of `{6,14,21}` has uniquely maximal valuation at any prime. -/
theorem noPrivateLeaderSet_has_no_strict_padic_leader :
    ∀ n ∈ noPrivateLeaderSet, ¬ HasStrictPadicLeader noPrivateLeaderSet n := by
  intro n hn hLeader
  rcases hLeader with ⟨p, hp, hdom⟩
  have hpn : p ∣ n := by
    have hnCases : n = 6 ∨ n = 14 ∨ n = 21 := by
      simpa [noPrivateLeaderSet] using hn
    rcases hnCases with rfl | rfl | rfl
    · have h := hdom 14 (by simp [noPrivateLeaderSet]) (by norm_num)
      exact dvd_of_one_le_padicValNat (by omega)
    · have h := hdom 6 (by simp [noPrivateLeaderSet]) (by norm_num)
      exact dvd_of_one_le_padicValNat (by omega)
    · have h := hdom 6 (by simp [noPrivateLeaderSet]) (by norm_num)
      exact dvd_of_one_le_padicValNat (by omega)
  have hnCases : n = 6 ∨ n = 14 ∨ n = 21 := by
    simpa [noPrivateLeaderSet] using hn
  rcases hnCases with rfl | rfl | rfl
  · rw [show 6 = 2 * 3 by norm_num] at hpn
    rcases hp.dvd_mul.mp hpn with hp2 | hp3
    · have hpEq : p = 2 :=
        (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hp2
      subst p
      have h := hdom 14 (by simp [noPrivateLeaderSet]) (by norm_num)
      exact (by native_decide : ¬padicValNat 2 14 < padicValNat 2 6) h
    · have hpEq : p = 3 :=
        (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hp3
      subst p
      have h := hdom 21 (by simp [noPrivateLeaderSet]) (by norm_num)
      exact (by native_decide : ¬padicValNat 3 21 < padicValNat 3 6) h
  · rw [show 14 = 2 * 7 by norm_num] at hpn
    rcases hp.dvd_mul.mp hpn with hp2 | hp7
    · have hpEq : p = 2 :=
        (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hp2
      subst p
      have h := hdom 6 (by simp [noPrivateLeaderSet]) (by norm_num)
      exact (by native_decide : ¬padicValNat 2 6 < padicValNat 2 14) h
    · have hpEq : p = 7 :=
        (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hp7
      subst p
      have h := hdom 21 (by simp [noPrivateLeaderSet]) (by norm_num)
      exact (by native_decide : ¬padicValNat 7 21 < padicValNat 7 14) h
  · rw [show 21 = 3 * 7 by norm_num] at hpn
    rcases hp.dvd_mul.mp hpn with hp3 | hp7
    · have hpEq : p = 3 :=
        (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hp3
      subst p
      have h := hdom 6 (by simp [noPrivateLeaderSet]) (by norm_num)
      exact (by native_decide : ¬padicValNat 3 6 < padicValNat 3 21) h
    · have hpEq : p = 7 :=
        (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hp7
      subst p
      have h := hdom 14 (by simp [noPrivateLeaderSet]) (by norm_num)
      exact (by native_decide : ¬padicValNat 7 14 < padicValNat 7 21) h

end Erdos321
