import Research.CommonDenominator
import Mathlib.NumberTheory.Chebyshev

/-!
# A small common denominator for the smooth remainder

When `N ≤ Q²`, every denominator left after removing the blocks for primes
above `Q` divides

`lcm(1,...,Q) * lcm(1,...,floor(sqrt N))²`.

This deliberately redundant common denominator is easier to verify than the
exact lcm and already has logarithm `O(Q + sqrt N)`.
-/

namespace Research

/-- A convenient common denominator for all `Q`-smooth integers up to `N`. -/
def smoothCommonDenominator (N Q : ℕ) : ℕ :=
  Nat.lcmUpto Q * (Nat.lcmUpto N.sqrt) ^ 2

/-- A prime dividing a denominator in the smooth remainder cannot exceed `Q`. -/
theorem prime_le_of_dvd_smoothRemainder {N Q n p : ℕ}
    (hn : n ∈ smoothRemainder N Q) (hp : p.Prime) (hpd : p ∣ n) :
    p ≤ Q := by
  rw [smoothRemainder, Finset.mem_sdiff] at hn
  by_contra hpQ
  have hQp : Q < p := Nat.lt_of_not_ge hpQ
  have hnBounds : n ∈ Finset.Icc 1 N := hn.1
  have hnPos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hnBounds).1
  have hpN : p ≤ N :=
    le_trans (Nat.le_of_dvd hnPos hpd) (Finset.mem_Icc.mp hnBounds).2
  have hpLarge : p ∈ largePrimes N Q := by
    rw [largePrimes, Finset.mem_filter]
    exact ⟨Finset.mem_Icc.mpr ⟨Nat.succ_le_iff.mpr hQp, hpN⟩, hp⟩
  have hkPos : 0 < n / p := Nat.div_pos (Nat.le_of_dvd hnPos hpd) hp.pos
  have hkLe : n / p ≤ N / p :=
    Nat.div_le_div_right (Finset.mem_Icc.mp hnBounds).2
  have hnBlock : n ∈ multipleBlock N p := by
    rw [multipleBlock, Finset.mem_image]
    refine ⟨n / p, Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr
      (Nat.ne_of_gt hkPos), hkLe⟩, ?_⟩
    exact Nat.mul_div_cancel' hpd
  apply hn.2
  rw [largePrimePart, Finset.mem_biUnion]
  exact ⟨p, hpLarge, hnBlock⟩

/-- Every positive denominator in the smooth remainder divides the convenient
common denominator. -/
theorem smoothRemainder_dvd_smoothCommonDenominator {N Q n : ℕ}
    (hn : n ∈ smoothRemainder N Q) :
    n ∣ smoothCommonDenominator N Q := by
  have hnBounds : n ∈ Finset.Icc 1 N := by
    exact (Finset.mem_sdiff.mp hn).1
  have hnPos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hnBounds).1
  have hn0 : n ≠ 0 := Nat.ne_of_gt hnPos
  have hL0 : smoothCommonDenominator N Q ≠ 0 := by
    rw [smoothCommonDenominator]
    exact Nat.mul_ne_zero (Nat.lcmUpto_ne_zero Q)
      (pow_ne_zero 2 (Nat.lcmUpto_ne_zero N.sqrt))
  rw [← (Nat.factorization_prime_le_iff_dvd hn0 hL0)]
  intro p hp
  by_cases hpn : p ∣ n
  · have hpQ : p ≤ Q := prime_le_of_dvd_smoothRemainder hn hp hpn
    let e := n.factorization p
    let r := e / 2
    have hpe : p ^ e ∣ n :=
      (hp.pow_dvd_iff_le_factorization hn0).mpr (le_refl e)
    have hpeN : p ^ e ≤ N :=
      le_trans (Nat.le_of_dvd hnPos hpe) (Finset.mem_Icc.mp hnBounds).2
    have htwoR : 2 * r ≤ e := by
      dsimp [r]
      omega
    have hpowR : p ^ (2 * r) ≤ N :=
      le_trans (Nat.pow_le_pow_right hp.pos htwoR) hpeN
    have hpowRsq : (p ^ r) ^ 2 ≤ N := by
      calc
        (p ^ r) ^ 2 = p ^ (r * 2) := by rw [pow_mul]
        _ = p ^ (2 * r) := by rw [Nat.mul_comm]
        _ ≤ N := hpowR
    have hrSqrt : p ^ r ≤ N.sqrt := Nat.le_sqrt'.mpr hpowRsq
    have hrLog : r ≤ Nat.log p N.sqrt :=
      Nat.le_log_of_pow_le hp.one_lt hrSqrt
    have honeLogQ : 1 ≤ Nat.log p Q := by
      apply Nat.le_log_of_pow_le hp.one_lt
      simpa using hpQ
    have heBound : e ≤ Nat.log p Q + 2 * Nat.log p N.sqrt := by
      have heParity : e ≤ 1 + 2 * r := by
        dsimp [r]
        omega
      omega
    rw [smoothCommonDenominator, Nat.factorization_mul
      (Nat.lcmUpto_ne_zero Q) (pow_ne_zero 2 (Nat.lcmUpto_ne_zero N.sqrt)),
      Nat.factorization_pow, Finsupp.add_apply, Finsupp.smul_apply,
      Nat.factorization_lcmUpto Q hp, Nat.factorization_lcmUpto N.sqrt hp]
    simpa [e, nsmul_eq_mul] using heBound
  · rw [Nat.factorization_eq_zero_of_not_dvd hpn]
    exact Nat.zero_le _

/-- The smooth remainder therefore has a support bound in terms of this small
common denominator. -/
theorem card_smoothRemainder_le_common (N Q : ℕ) :
    (subsetSumValues reciprocalWeight (smoothRemainder N Q)).card ≤
      (smoothRemainder N Q).card * smoothCommonDenominator N Q + 1 := by
  apply card_subsetSumValues_le_commonDenominator
  · exact Nat.mul_pos (Nat.lcmUpto_pos Q)
      (pow_pos (Nat.lcmUpto_pos N.sqrt) 2)
  · intro n hn
    have := (Finset.mem_sdiff.mp hn).1
    exact lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp this).1
  · intro n hn
    exact smoothRemainder_dvd_smoothCommonDenominator hn

/-- Fully explicit finite recurrence with the smooth support replaced by a
single elementary common-denominator factor. -/
theorem S_le_commonFactor_mul_primeProduct (N Q : ℕ) (hNQ : N ≤ Q * Q) :
    S N ≤ (N * smoothCommonDenominator N Q + 1) *
      ∏ p ∈ largePrimes N Q, S (N / p) := by
  let P := ∏ p ∈ largePrimes N Q, S (N / p)
  have hRsub : smoothRemainder N Q ⊆ Finset.Icc 1 N := by
    intro n hn
    exact (Finset.mem_sdiff.mp hn).1
  have hRcard : (smoothRemainder N Q).card ≤ N := by
    have hc := Finset.card_le_card hRsub
    simpa using hc
  have hsmooth := card_smoothRemainder_le_common N Q
  have hfactor :
      (subsetSumValues reciprocalWeight (smoothRemainder N Q)).card ≤
        N * smoothCommonDenominator N Q + 1 := by
    exact le_trans hsmooth (Nat.add_le_add_right
      (Nat.mul_le_mul_right (smoothCommonDenominator N Q) hRcard) 1)
  calc
    S N ≤ (subsetSumValues reciprocalWeight (smoothRemainder N Q)).card * P :=
      S_le_smooth_mul_prime_product N Q hNQ
    _ ≤ (N * smoothCommonDenominator N Q + 1) * P :=
      Nat.mul_le_mul_right P hfactor

/-- Exact logarithm of the convenient common denominator. -/
theorem log_smoothCommonDenominator (N Q : ℕ) :
    Real.log (smoothCommonDenominator N Q : ℝ) =
      Chebyshev.psi Q + 2 * Chebyshev.psi N.sqrt := by
  have hQ0 : (Nat.lcmUpto Q : ℝ) ≠ 0 := by
    exact_mod_cast Nat.lcmUpto_ne_zero Q
  have hS0 : (Nat.lcmUpto N.sqrt : ℝ) ≠ 0 := by
    exact_mod_cast Nat.lcmUpto_ne_zero N.sqrt
  rw [smoothCommonDenominator, Nat.cast_mul, Nat.cast_pow,
    Real.log_mul hQ0 (pow_ne_zero 2 hS0), Real.log_pow,
    ← Chebyshev.psi_eq_log_lcmUpto,
    ← Chebyshev.psi_eq_log_lcmUpto]
  ring

/-- A linear `Q + sqrt N` upper bound for that logarithm. -/
theorem log_smoothCommonDenominator_le (N Q : ℕ) :
    Real.log (smoothCommonDenominator N Q : ℝ) ≤
      (Real.log 4 + 4) * Q + 2 * (Real.log 4 + 4) * N.sqrt := by
  rw [log_smoothCommonDenominator]
  have hQ := Chebyshev.psi_le_const_mul_self (x := (Q : ℝ)) (by positivity)
  have hS := Chebyshev.psi_le_const_mul_self
    (x := (N.sqrt : ℝ)) (by positivity)
  nlinarith

end Research
