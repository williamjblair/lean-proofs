/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686ConsecutivePropertyMass
import ErdosProblems.Erdos686PadicLift

/-!
# Erdős 686: exact small-prime mass bound

For every prime at most `k`, valuation concentration leaves at most one copy
of `(k-1)!` outside a single block term.  Multiplying the retained prime
powers gives the exact bound

`B_{≤k}(k,n) ≤ (k-1)! * (n+k)^π(k)`.

This is the elementary mass estimate needed by the canonical all-`k` owner
program.
-/

namespace Erdos686
namespace Erdos686Variant

open scoped BigOperators

/-- The factor of `x` supported on prime bases strictly larger than `k`. -/
def kLargePart (k x : ℕ) : ℕ :=
  (Finsupp.filter (fun p : ℕ => k < p) x.factorization).prod (· ^ ·)

private lemma filtered_large_factorization_le (k x : ℕ) :
    Finsupp.filter (fun p : ℕ => k < p) x.factorization ≤ x.factorization := by
  intro p
  simp only [Finsupp.filter_apply]
  split <;> simp

lemma kLargePart_factorization {k x p : ℕ} :
    (kLargePart k x).factorization p =
      if k < p then x.factorization p else 0 := by
  unfold kLargePart
  rw [Nat.factorization_prod_pow_eq_self_of_le_factorization
    (filtered_large_factorization_le k x)]
  exact Finsupp.filter_apply _ _ _

lemma kLargePart_ne_zero (k x : ℕ) :
    kLargePart k x ≠ 0 := by
  unfold kLargePart
  rw [Finsupp.prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  have hpSupport : p ∈ x.factorization.support := by
    have hpLarge :
        (Finsupp.filter (fun q : ℕ => k < q) x.factorization) p ≠ 0 :=
      Finsupp.mem_support_iff.mp hp
    apply Finsupp.mem_support_iff.mpr
    simp only [Finsupp.filter_apply] at hpLarge
    split at hpLarge
    · exact hpLarge
    · simp at hpLarge
  have hpPrime := prime_of_mem_factorization_support hpSupport
  exact pow_ne_zero _ hpPrime.ne_zero

/-- Exact decomposition into prime bases at most `k` and prime bases above
`k`. -/
theorem kSmallPart_mul_kLargePart {k x : ℕ} (hx : x ≠ 0) :
    kSmallPart k x * kLargePart k x = x := by
  have hsmall0 := kSmallPart_ne_zero (k := k) hx
  have hlarge0 := kLargePart_ne_zero k x
  have hprod0 : kSmallPart k x * kLargePart k x ≠ 0 :=
    mul_ne_zero hsmall0 hlarge0
  apply Nat.factorization_inj hprod0 hx
  ext p
  rw [Nat.factorization_mul hsmall0 hlarge0, Finsupp.add_apply,
    kSmallPart_factorization, kLargePart_factorization]
  by_cases hpk : p ≤ k
  · rw [if_pos hpk, if_neg (by omega : ¬k < p)]
    omega
  · rw [if_neg hpk, if_pos (by omega : k < p)]
    omega

/-- The small-prime exponent retained after removing the universal
consecutive-block loss. -/
noncomputable def kSmallConcentrationExponent (k n : ℕ) : ℕ →₀ ℕ :=
  Finsupp.filter (fun p : ℕ => p ≤ k)
    ((blockProduct k n).factorization - (k - 1).factorial.factorization)

/-- Product of the retained concentrated small-prime powers. -/
noncomputable def kSmallConcentratedPart (k n : ℕ) : ℕ :=
  (kSmallConcentrationExponent k n).prod (· ^ ·)

private lemma kSmallConcentrationExponent_le_factorization (k n : ℕ) :
    kSmallConcentrationExponent k n ≤ (blockProduct k n).factorization := by
  intro p
  by_cases hpk : p ≤ k
  · simp only [kSmallConcentrationExponent, Finsupp.filter_apply,
      if_pos hpk, Finsupp.coe_tsub]
    exact Nat.sub_le _ _
  · simp [kSmallConcentrationExponent, hpk]

lemma kSmallConcentratedPart_factorization (k n : ℕ) :
    (kSmallConcentratedPart k n).factorization =
      kSmallConcentrationExponent k n := by
  unfold kSmallConcentratedPart
  exact Nat.factorization_prod_pow_eq_self_of_le_factorization
    (kSmallConcentrationExponent_le_factorization k n)

lemma kSmallConcentratedPart_ne_zero (k n : ℕ) :
    kSmallConcentratedPart k n ≠ 0 := by
  unfold kSmallConcentratedPart
  rw [Finsupp.prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  have hpSupport :
      p ∈ (blockProduct k n).factorization.support := by
    have hpRetained :
        (kSmallConcentrationExponent k n) p ≠ 0 :=
      Finsupp.mem_support_iff.mp hp
    apply Finsupp.mem_support_iff.mpr
    intro hzero
    have hle := kSmallConcentrationExponent_le_factorization k n p
    omega
  have hpPrime := prime_of_mem_factorization_support hpSupport
  exact pow_ne_zero _ hpPrime.ne_zero

private lemma kSmallConcentration_support_subset_primesBelow (k n : ℕ) :
    (kSmallConcentrationExponent k n).support ⊆ (k + 1).primesBelow := by
  intro p hp
  have hpRetained :
      (kSmallConcentrationExponent k n) p ≠ 0 :=
    Finsupp.mem_support_iff.mp hp
  have hpk : p ≤ k := by
    simp only [kSmallConcentrationExponent, Finsupp.filter_apply] at hpRetained
    split at hpRetained
    · assumption
    · simp at hpRetained
  have hpSupport :
      p ∈ (blockProduct k n).factorization.support := by
    apply Finsupp.mem_support_iff.mpr
    intro hzero
    have hle := kSmallConcentrationExponent_le_factorization k n p
    omega
  have hpPrime := prime_of_mem_factorization_support hpSupport
  exact Nat.mem_primesBelow.mpr ⟨by omega, hpPrime⟩

private lemma retained_small_prime_power_le
    {k n p : ℕ}
    (hk : 1 ≤ k)
    (hp : p ∈ (kSmallConcentrationExponent k n).support) :
    p ^ (kSmallConcentrationExponent k n p) ≤ n + k := by
  have hpBelow :=
    kSmallConcentration_support_subset_primesBelow k n hp
  have hpPrime := Nat.prime_of_mem_primesBelow hpBelow
  obtain ⟨i, hi, hconcentration⟩ :=
    exists_blockProduct_factorization_concentration hpPrime hk (n := n)
  have hpk : p ≤ k := by
    exact Nat.lt_succ_iff.mp (Nat.lt_of_mem_primesBelow hpBelow)
  have hexponent :
      kSmallConcentrationExponent k n p ≤ (n + i).factorization p := by
    simp only [kSmallConcentrationExponent, Finsupp.filter_apply,
      if_pos hpk, Finsupp.coe_tsub]
    change (blockProduct k n).factorization p -
        (k - 1).factorial.factorization p ≤ (n + i).factorization p
    omega
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hik : i ≤ k := (Finset.mem_Icc.mp hi).2
  have hterm0 : n + i ≠ 0 := by omega
  have hdvd : p ^ (kSmallConcentrationExponent k n p) ∣ n + i :=
    (hpPrime.pow_dvd_iff_le_factorization hterm0).mpr hexponent
  have hpowPos : 0 < p ^ (kSmallConcentrationExponent k n p) :=
    pow_pos hpPrime.pos _
  exact le_trans (Nat.le_of_dvd (by omega) hdvd) (by omega)

lemma kSmallConcentratedPart_le (k n : ℕ) (hk : 1 ≤ k) :
    kSmallConcentratedPart k n ≤
      (n + k) ^ (k + 1).primesBelow.card := by
  unfold kSmallConcentratedPart
  rw [Finsupp.prod]
  calc
    (∏ p ∈ (kSmallConcentrationExponent k n).support,
        p ^ (kSmallConcentrationExponent k n p))
        ≤ ∏ _p ∈ (kSmallConcentrationExponent k n).support, (n + k) := by
          refine Finset.prod_le_prod ?_ ?_
          · intro p hp
            exact Nat.zero_le _
          · intro p hp
            exact retained_small_prime_power_le hk hp
    _ = (n + k) ^ (kSmallConcentrationExponent k n).support.card := by
          simp [Finset.prod_const]
    _ ≤ (n + k) ^ (k + 1).primesBelow.card := by
          exact Nat.pow_le_pow_right (by omega)
            (Finset.card_le_card
              (kSmallConcentration_support_subset_primesBelow k n))

/-- Exact form of `HP2` from the canonical-owner handoff. -/
theorem kSmallPart_le_factorial_mul_pow_primeCounting
    (k n : ℕ) (hk : 1 ≤ k) :
    kSmallPart k (blockProduct k n) ≤
      (k - 1).factorial * (n + k) ^ (k + 1).primesBelow.card := by
  have hsmall0 :
      kSmallPart k (blockProduct k n) ≠ 0 :=
    kSmallPart_ne_zero (ne_of_gt (blockProduct_pos k n))
  have hconcentrated0 := kSmallConcentratedPart_ne_zero k n
  have hrhs0 :
      (k - 1).factorial * kSmallConcentratedPart k n ≠ 0 :=
    mul_ne_zero (Nat.factorial_ne_zero _) hconcentrated0
  have hdvd :
      kSmallPart k (blockProduct k n) ∣
        (k - 1).factorial * kSmallConcentratedPart k n := by
    apply (Nat.factorization_le_iff_dvd hsmall0 hrhs0).mp
    intro p
    rw [Nat.factorization_mul (Nat.factorial_ne_zero _) hconcentrated0,
      Finsupp.add_apply, kSmallPart_factorization,
      kSmallConcentratedPart_factorization]
    by_cases hpk : p ≤ k
    · rw [if_pos hpk]
      simp only [kSmallConcentrationExponent, Finsupp.filter_apply,
        if_pos hpk, Finsupp.coe_tsub]
      change (blockProduct k n).factorization p ≤
        (k - 1).factorial.factorization p +
          ((blockProduct k n).factorization p -
            (k - 1).factorial.factorization p)
      by_cases hle :
          (blockProduct k n).factorization p ≤
            (k - 1).factorial.factorization p <;> omega
    · rw [if_neg hpk]
      exact Nat.zero_le _
  have hfactorialPos : 0 < (k - 1).factorial := Nat.factorial_pos _
  calc
    kSmallPart k (blockProduct k n)
        ≤ (k - 1).factorial * kSmallConcentratedPart k n :=
          Nat.le_of_dvd (mul_pos hfactorialPos
            (Nat.pos_of_ne_zero hconcentrated0)) hdvd
    _ ≤ (k - 1).factorial *
        (n + k) ^ (k + 1).primesBelow.card :=
          Nat.mul_le_mul_left _ (kSmallConcentratedPart_le k n hk)

/-- Cross-multiplied exact form of the high-prime mass lower bound `HP3`.
The lower block is at most the explicit small-prime loss times its complete
large-prime part. -/
theorem blockProduct_le_smallLoss_mul_kLargePart
    (k n : ℕ) (hk : 1 ≤ k) :
    blockProduct k n ≤
      ((k - 1).factorial * (n + k) ^ (k + 1).primesBelow.card) *
        kLargePart k (blockProduct k n) := by
  have hblock0 : blockProduct k n ≠ 0 :=
    ne_of_gt (blockProduct_pos k n)
  calc
    blockProduct k n =
        kSmallPart k (blockProduct k n) *
          kLargePart k (blockProduct k n) :=
      (kSmallPart_mul_kLargePart hblock0).symm
    _ ≤ ((k - 1).factorial * (n + k) ^ (k + 1).primesBelow.card) *
        kLargePart k (blockProduct k n) :=
      Nat.mul_le_mul_right _
        (kSmallPart_le_factorial_mul_pow_primeCounting k n hk)

/-- Every prime base above the block length that actually occurs in the
lower block has one unique owner cell, and that cell carries the prime's
entire lower-block exponent on both sides of the exact equation. -/
theorem large_prime_has_unique_full_exponent_owner_cell
    {k n d p : ℕ}
    (hk4 : 4 ≤ k)
    (hp : p.Prime)
    (hkp : k < p)
    (hpLower : p ∣ blockProduct k n)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    ∃! cell : ℕ × ℕ,
      cell.1 ∈ Finset.Icc 1 k ∧
      cell.2 ∈ Finset.Icc 1 k ∧
      p ^ (blockProduct k n).factorization p ∣ n + cell.1 ∧
      p ^ (blockProduct k n).factorization p ∣ n + d + cell.2 := by
  have hlower0 : blockProduct k n ≠ 0 :=
    ne_of_gt (blockProduct_pos k n)
  have hupper0 : blockProduct k (n + d) ≠ 0 :=
    ne_of_gt (blockProduct_pos k (n + d))
  let e := (blockProduct k n).factorization p
  have he : 0 < e := hp.factorization_pos_of_dvd hlower0 hpLower
  have hpowLower : p ^ e ∣ blockProduct k n :=
    (hp.pow_dvd_iff_le_factorization hlower0).mpr le_rfl
  have hp4 : ¬p ∣ 4 := by
    intro hdiv
    have hple : p ≤ 4 := Nat.le_of_dvd (by norm_num) hdiv
    omega
  have hfourVal : (4 : ℕ).factorization p = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hp4
  have hvalEq :
      (blockProduct k (n + d)).factorization p =
        (blockProduct k n).factorization p := by
    have hfull := congrArg Nat.factorization heq
    have hpfull := DFunLike.congr_fun hfull p
    rw [Nat.factorization_mul (by norm_num : (4 : ℕ) ≠ 0) hlower0,
      Finsupp.add_apply, hfourVal, zero_add] at hpfull
    exact hpfull
  have hpowUpper : p ^ e ∣ blockProduct k (n + d) := by
    apply (hp.pow_dvd_iff_le_factorization hupper0).mpr
    dsimp [e]
    rw [hvalEq]
  obtain ⟨j, hj, hjUnique⟩ :=
    primePower_dvd_blockProduct_existsUnique hp he (by omega : k ≤ p) hpowLower
  obtain ⟨i, hi, hiUnique⟩ :=
    primePower_dvd_blockProduct_existsUnique hp he (by omega : k ≤ p) hpowUpper
  refine ⟨(j, i), ?_, ?_⟩
  · exact ⟨hj.1, hi.1, by simpa [e] using hj.2, by simpa [e] using hi.2⟩
  · intro cell hcell
    apply Prod.ext
    · exact hjUnique cell.1 ⟨hcell.1, by simpa [e] using hcell.2.2.1⟩
    · exact hiUnique cell.2 ⟨hcell.2.1, by simpa [e] using hcell.2.2.2⟩

#print axioms kSmallConcentratedPart_le
#print axioms kSmallPart_le_factorial_mul_pow_primeCounting
#print axioms kSmallPart_mul_kLargePart
#print axioms blockProduct_le_smallLoss_mul_kLargePart
#print axioms large_prime_has_unique_full_exponent_owner_cell

end Erdos686Variant
end Erdos686
