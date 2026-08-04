import Research.Compatibility

/-! # Exact finite lower recurrence for good denominators -/

namespace Research

noncomputable instance coeffGoodDecidable (d : ℕ) :
    Decidable (CoeffGoodDenominator d) := Classical.propDecidable _

/-- Arithmetic-good denominators up to `N`. -/
noncomputable def coeffGoodDenominators (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter CoeffGoodDenominator

/-- Simple compatibility threshold used in F-030. -/
def compatibilityThreshold (m : ℕ) : ℕ := Nat.lcmUpto m * m

/-- A deliberately coarse exponential majorant for the compatibility
threshold.  Its large base is chosen to make the proof entirely explicit. -/
theorem compatibilityThreshold_le_pow {m : ℕ} (hm : 0 < m) :
    compatibilityThreshold m ≤ 65536 ^ m := by
  have hpsi := Chebyshev.psi_le_const_mul_self
    (x := (m : ℝ)) (by positivity)
  rw [Chebyshev.psi_eq_log_lcmUpto] at hpsi
  have hL : (Nat.lcmUpto m : ℝ) ≤
      Real.exp ((Real.log 4 + 4) * m) := by
    have h := Real.exp_le_exp.mpr hpsi
    rw [Real.exp_log (by exact_mod_cast Nat.lcmUpto_pos m)] at h
    exact h
  have hmexp : (m : ℝ) ≤ Real.exp m := by
    have h := Real.add_one_le_exp (m : ℝ)
    linarith
  have hbase : Real.exp (Real.log 4 + 4 + 1) ≤ (65536 : ℝ) := by
    rw [show Real.log 4 + 4 + 1 = Real.log 4 + 5 by ring,
      Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
    have he : Real.exp (1 : ℝ) < 3 := Real.exp_one_lt_three
    have he5 : Real.exp (5 : ℝ) < 3 ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * (1 : ℝ) by norm_num,
        Real.exp_nat_mul]
      exact pow_lt_pow_left₀ he (by positivity) (by omega)
    norm_num at he5 ⊢
    linarith
  have hcast : (compatibilityThreshold m : ℝ) ≤ (65536 ^ m : ℕ) := by
    rw [compatibilityThreshold, Nat.cast_mul, Nat.cast_pow]
    calc
      (Nat.lcmUpto m : ℝ) * m ≤
          Real.exp ((Real.log 4 + 4) * m) * Real.exp m :=
        mul_le_mul hL hmexp (by positivity) (by positivity)
      _ = Real.exp ((Real.log 4 + 4 + 1) * m) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ = Real.exp (Real.log 4 + 4 + 1) ^ m := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      _ ≤ (65536 : ℝ) ^ m :=
        pow_le_pow_left₀ (by positivity) hbase m
  exact_mod_cast hcast

/-- Compatible large primes which can multiply `m` without exceeding `N`. -/
def compatiblePrimeSet (N m : ℕ) : Finset ℕ :=
  (Finset.Ioc (compatibilityThreshold m) (N / m)).filter Nat.Prime

/-- Products with two prime factors larger than their complementary cofactors
have a unique such representation. -/
theorem mul_prime_pair_injective {m n p q : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hp : p.Prime) (hq : q.Prime)
    (hmp : m < p) (hnq : n < q) (heq : m * p = n * q) :
    m = n ∧ p = q := by
  have hpDvd : p ∣ n * q := by
    rw [← heq]
    exact dvd_mul_left p m
  rcases (hp.dvd_mul.mp hpDvd) with hpn | hpq
  · have hpLeN : p ≤ n := Nat.le_of_dvd hn hpn
    have hpLtQ : p < q := lt_of_le_of_lt hpLeN hnq
    have hqDvd : q ∣ m * p := by
      rw [heq]
      exact dvd_mul_left q n
    rcases (hq.dvd_mul.mp hqDvd) with hqm | hqp
    · have hqLeM : q ≤ m := Nat.le_of_dvd hm hqm
      omega
    · rcases (Nat.dvd_prime hp).mp hqp with hq1 | hqpEq
      · exact False.elim (hq.ne_one hq1)
      · omega
  · rcases (Nat.dvd_prime hq).mp hpq with hp1 | hpqEq
    · exact False.elim (hp.ne_one hp1)
    · subst q
      exact ⟨Nat.eq_of_mul_eq_mul_right hp.pos heq, rfl⟩

/-- Products generated from distinct good cofactors occupy disjoint sets. -/
theorem generated_pairwise_disjoint (N y : ℕ) :
    ((coeffGoodDenominators y : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (fun m => (compatiblePrimeSet N m).image (fun p => m * p)) := by
  intro m hm n hn hmn
  change Disjoint ((compatiblePrimeSet N m).image (fun p => m * p))
    ((compatiblePrimeSet N n).image (fun p => n * p))
  rw [Finset.disjoint_left]
  intro z hzm hzn
  rw [Finset.mem_image] at hzm hzn
  obtain ⟨p, hpSet, rfl⟩ := hzm
  obtain ⟨q, hqSet, heq⟩ := hzn
  rw [compatiblePrimeSet, Finset.mem_filter, Finset.mem_Ioc] at hpSet hqSet
  change m ∈ coeffGoodDenominators y at hm
  change n ∈ coeffGoodDenominators y at hn
  rw [coeffGoodDenominators, Finset.mem_filter] at hm hn
  have hmPos := hm.2.1
  have hnPos := hn.2.1
  have hthm : m ≤ compatibilityThreshold m := by
    rw [compatibilityThreshold]
    nlinarith [Nat.lcmUpto_pos m]
  have hthn : n ≤ compatibilityThreshold n := by
    rw [compatibilityThreshold]
    nlinarith [Nat.lcmUpto_pos n]
  have hinj := mul_prime_pair_injective hmPos hnPos hpSet.2 hqSet.2
    (lt_of_le_of_lt hthm hpSet.1.1) (lt_of_le_of_lt hthn hqSet.1.1) heq.symm
  exact hmn hinj.1

/-- Every generated product is arithmetic-good and at most `N`. -/
theorem generated_subset_coeffGood (N y : ℕ) :
    (coeffGoodDenominators y).biUnion
        (fun m => (compatiblePrimeSet N m).image (fun p => m * p)) ⊆
      coeffGoodDenominators N := by
  intro z hz
  rw [Finset.mem_biUnion] at hz
  obtain ⟨m, hm, hzm⟩ := hz
  rw [Finset.mem_image] at hzm
  obtain ⟨p, hpSet, rfl⟩ := hzm
  rw [coeffGoodDenominators, Finset.mem_filter, Finset.mem_Icc] at hm
  rw [compatiblePrimeSet, Finset.mem_filter, Finset.mem_Ioc] at hpSet
  rw [coeffGoodDenominators, Finset.mem_filter, Finset.mem_Icc]
  have hmPos := hm.2.1
  have hpPos := hpSet.2.pos
  refine ⟨⟨Nat.mul_pos hmPos hpPos, ?_⟩, ?_⟩
  · have hpLe : p ≤ N / m := hpSet.1.2
    simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hmPos).mp hpLe
  · exact coeffGood_mul_prime_of_large hm.2 hpSet.2 hpSet.1.1

/-- Exact finite compatible-prime lower recurrence. -/
theorem sum_compatiblePrimeSet_card_le (N y : ℕ) :
    ∑ m ∈ coeffGoodDenominators y, (compatiblePrimeSet N m).card ≤
      (coeffGoodDenominators N).card := by
  let G := (coeffGoodDenominators y).biUnion
    (fun m => (compatiblePrimeSet N m).image (fun p => m * p))
  have hsubset : G ⊆ coeffGoodDenominators N := generated_subset_coeffGood N y
  have hcardG : G.card =
      ∑ m ∈ coeffGoodDenominators y, (compatiblePrimeSet N m).card := by
    rw [Finset.card_biUnion (generated_pairwise_disjoint N y)]
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.card_image_of_injective]
    intro p q hpq
    rw [coeffGoodDenominators, Finset.mem_filter] at hm
    exact Nat.mul_left_cancel hm.2.1 hpq
  rw [← hcardG]
  exact Finset.card_le_card hsubset

end Research
