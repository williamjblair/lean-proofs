import Mathlib

namespace Erdos959

lemma hundred_mul_succ_le_two_pow (m : ℕ) (hm : 16 ≤ m) :
    100 * (m + 1) ≤ 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
      calc
        100 * (m + 1 + 1) ≤ 2 * (100 * (m + 1)) := by omega
        _ ≤ 2 * 2 ^ m := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (m + 1) := by ring

lemma succ_pow_hundred_le_two_pow (a : ℕ) (ha : 1600 ≤ a) :
    (a + 1) ^ 100 ≤ 2 ^ a := by
  let m := a / 100
  have hm : 16 ≤ m := by
    exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 100)).2 (by simpa using ha)
  have hmod : a % 100 < 100 := Nat.mod_lt _ (by norm_num)
  have hadecomp : 100 * m + a % 100 = a := by
    exact Nat.div_add_mod a 100
  have hasucc : a + 1 ≤ 100 * (m + 1) := by omega
  calc
    (a + 1) ^ 100 ≤ (100 * (m + 1)) ^ 100 := Nat.pow_le_pow_left hasucc _
    _ ≤ (2 ^ m) ^ 100 := Nat.pow_le_pow_left (hundred_mul_succ_le_two_pow m hm) _
    _ = 2 ^ (m * 100) := by rw [← pow_mul]
    _ ≤ 2 ^ a := by
      apply Nat.pow_le_pow_right (by norm_num)
      dsimp [m]
      exact Nat.div_mul_le_self a 100

/-- A deliberately enormous explicit constant for a fixed-power divisor bound. -/
def divisorThreshold : ℕ := 1600 ^ 100

/-- A deliberately enormous constant for a fixed-power divisor bound.  It is
chosen opaquely so the kernel never attempts to evaluate its astronomical
value. -/
noncomputable def divisorPowerConstant : ℕ :=
  Classical.choose (show ∃ C : ℕ, divisorThreshold ^ divisorThreshold ≤ C from
    ⟨divisorThreshold ^ divisorThreshold, le_rfl⟩)

lemma divisorPowerConstant_spec :
    divisorThreshold ^ divisorThreshold ≤ divisorPowerConstant := by
  unfold divisorPowerConstant
  exact Classical.choose_spec
    (show ∃ C : ℕ, divisorThreshold ^ divisorThreshold ≤ C from
      ⟨divisorThreshold ^ divisorThreshold, le_rfl⟩)

lemma divisorThreshold_pos : 0 < divisorThreshold := by
  dsimp only [divisorThreshold]
  positivity

lemma primeExponent_hundred_bound (p a : ℕ) (hp : 2 ≤ p) (ha : 0 < a) :
    (a + 1) ^ 100 ≤
      (if p < divisorThreshold then divisorThreshold else 1) * p ^ a := by
  by_cases haSmall : a < 1600
  · have hasucc : a + 1 ≤ 1600 := by omega
    have hpow : (a + 1) ^ 100 ≤ divisorThreshold := by
      exact Nat.pow_le_pow_left hasucc 100
    by_cases hpSmall : p < divisorThreshold
    · rw [if_pos hpSmall]
      exact hpow.trans (Nat.le_mul_of_pos_right _ (pow_pos (by omega) a))
    · rw [if_neg hpSmall, one_mul]
      have hthreshold : divisorThreshold ≤ p := le_of_not_gt hpSmall
      exact hpow.trans (hthreshold.trans (Nat.le_pow ha))
  · have haLarge : 1600 ≤ a := le_of_not_gt haSmall
    have htwo : (a + 1) ^ 100 ≤ 2 ^ a := succ_pow_hundred_le_two_pow a haLarge
    have hpPow : 2 ^ a ≤ p ^ a := Nat.pow_le_pow_left hp a
    by_cases hpSmall : p < divisorThreshold
    · rw [if_pos hpSmall]
      exact (htwo.trans hpPow).trans
        (Nat.le_mul_of_pos_left _ divisorThreshold_pos)
    · rw [if_neg hpSmall, one_mul]
      exact htwo.trans hpPow

theorem card_divisors_hundred_le_constant_mul (n : ℕ) :
    n.divisors.card ^ 100 ≤ divisorPowerConstant * n := by
  by_cases hn : n = 0
  · subst n
    simp
  · let S := n.primeFactors
    let coeff : ℕ → ℕ := fun p =>
      if p < divisorThreshold then divisorThreshold else 1
    have hlocal : ∀ p ∈ S,
        (n.factorization p + 1) ^ 100 ≤
          coeff p * p ^ n.factorization p := by
      intro p hpS
      have pp : p.Prime := Nat.prime_of_mem_primeFactors hpS
      have ha : 0 < n.factorization p :=
        pp.factorization_pos_of_dvd hn (Nat.dvd_of_mem_primeFactors hpS)
      exact primeExponent_hundred_bound p (n.factorization p) pp.two_le ha
    have hsmall : (S.filter fun p => p < divisorThreshold).card ≤ divisorThreshold := by
      have hsub : (S.filter fun p => p < divisorThreshold) ⊆
          Finset.range divisorThreshold := by
        intro p hp
        simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
        exact hp.2
      simpa using Finset.card_le_card hsub
    have hcoeff : (∏ p ∈ S, coeff p) =
        divisorThreshold ^ (S.filter fun p => p < divisorThreshold).card := by
      dsimp [coeff]
      simp only [Finset.prod_ite, Finset.prod_const, one_pow, mul_one]
    have hcoeff_le : (∏ p ∈ S, coeff p) ≤ divisorPowerConstant := by
      rw [hcoeff]
      exact (Nat.pow_le_pow_right divisorThreshold_pos hsmall).trans
        divisorPowerConstant_spec
    calc
      n.divisors.card ^ 100 =
          (∏ p ∈ S, (n.factorization p + 1)) ^ 100 := by
            rw [Nat.card_divisors hn]
      _ = ∏ p ∈ S, (n.factorization p + 1) ^ 100 := by
            rw [Finset.prod_pow]
      _ ≤ ∏ p ∈ S, coeff p * p ^ n.factorization p := by
            exact Finset.prod_le_prod (fun _ _ => Nat.zero_le _) hlocal
      _ = (∏ p ∈ S, coeff p) * (∏ p ∈ S, p ^ n.factorization p) := by
            rw [Finset.prod_mul_distrib]
      _ = (∏ p ∈ S, coeff p) * n := by
            congr 1
            rw [← Nat.prod_factorization_eq_prod_primeFactors]
            exact Nat.factorization_prod_pow_eq_self hn
      _ ≤ divisorPowerConstant * n := Nat.mul_le_mul_right n hcoeff_le

end Erdos959
