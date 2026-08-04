import Research.LowerRecurrence

/-! # Discrete Abel transform for the lower recurrence -/

namespace Research

/-- Arithmetic-good denominators in `[2,N]`; denominator one is removed so
that all prime-counting main terms gain a positive logarithm. -/
noncomputable def tailCoeffGoodDenominators (N : ℕ) : Finset ℕ :=
  (Finset.Icc 2 N).filter CoeffGoodDenominator

noncomputable def tailGoodIndicator (m : ℕ) : ℝ :=
  if 2 ≤ m ∧ CoeffGoodDenominator m then 1 else 0

/-- Prefix sums of the indicator are exactly tail-good cardinalities. -/
theorem sum_tailGoodIndicator_range (N : ℕ) :
    ∑ m ∈ Finset.range (N + 1), tailGoodIndicator m =
      ((tailCoeffGoodDenominators N).card : ℝ) := by
  classical
  have hfilter : (Finset.range (N + 1)).filter
      (fun m => 2 ≤ m ∧ CoeffGoodDenominator m) =
      tailCoeffGoodDenominators N := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc,
      tailCoeffGoodDenominators]
    constructor
    · intro h
      exact ⟨⟨h.2.1, by omega⟩, h.2.2⟩
    · intro h
      exact ⟨by omega, h.1.1, h.2⟩
  unfold tailGoodIndicator
  rw [← hfilter]
  symm
  simpa using Finset.sum_filter (s := Finset.range (N + 1))
    (fun m => 2 ≤ m ∧ CoeffGoodDenominator m) (fun _m => (1 : ℝ))

/-- Summing against the indicator is the same as summing over the tail-good
finite set. -/
theorem sum_tailGood_eq_sum_indicator (N : ℕ) (f : ℕ → ℝ) :
    ∑ m ∈ tailCoeffGoodDenominators N, f m =
      ∑ m ∈ Finset.Ioc 1 N, f m * tailGoodIndicator m := by
  classical
  unfold tailCoeffGoodDenominators tailGoodIndicator
  let p : ℕ → Prop := fun m => 2 ≤ m ∧ CoeffGoodDenominator m
  calc
    ∑ m ∈ (Finset.Icc 2 N).filter CoeffGoodDenominator, f m =
        ∑ m ∈ (Finset.Ioc 1 N).filter p, f m := by
      apply Finset.sum_congr
      · ext m
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc, p]
        constructor
        · intro h
          exact ⟨⟨by omega, h.1.2⟩, h.1.1, h.2⟩
        · intro h
          exact ⟨⟨h.2.1, h.1.2⟩, h.2.2⟩
      · intro m hm
        rfl
    _ = ∑ m ∈ Finset.Ioc 1 N, f m * (if p m then 1 else 0) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro m hm
      by_cases hpm : p m <;> simp [p] at hpm ⊢ <;> simp [hpm]

/-- The exponential penalty used below is increasing. -/
theorem pow_add_one_mono (i : ℕ) :
    65536 ^ i + 1 ≤ 65536 ^ (i + 1) + 1 := by
  exact Nat.add_le_add_right
    (Nat.pow_le_pow_right (by omega) (Nat.le_succ i)) 1

/-- The tail count is already nonempty from denominator two. -/
theorem one_le_tailCoeffGood_card {N : ℕ} (hN : 2 ≤ N) :
    1 ≤ (tailCoeffGoodDenominators N).card := by
  apply Finset.one_le_card.mpr
  refine ⟨2, ?_⟩
  rw [tailCoeffGoodDenominators, Finset.mem_filter, Finset.mem_Icc]
  refine ⟨⟨by omega, hN⟩, ?_⟩
  have hlarge : Nat.lcmUpto 1 * 1 < 2 := by
    norm_num [Nat.lcmUpto]
  simpa using coeffGood_mul_prime_of_large coeffGood_one Nat.prime_two hlarge

/-- Discrete Abel transform.  A nonnegative endpoint and the monotonicity of
the exponential penalty leave the full unit-coefficient renewal kernel. -/
theorem sum_main_sub_pow_ge_abel (c : ℝ) (y : ℕ)
    (hc : 0 ≤ c) (hy : 2 ≤ y)
    (hend : 0 ≤ c / y - (65536 ^ y + 1 : ℕ)) :
    c * ∑ v ∈ Finset.Ico 2 y,
        ((tailCoeffGoodDenominators v).card : ℝ) /
          ((v : ℝ) * (v + 1)) ≤
      ∑ m ∈ tailCoeffGoodDenominators y,
        (c / m - (65536 ^ m + 1 : ℕ)) := by
  classical
  let f : ℕ → ℝ := fun m => c / m - (65536 ^ m + 1 : ℕ)
  let g : ℕ → ℝ := tailGoodIndicator
  have hparts := Finset.sum_Ioc_by_parts f g (show 1 < y by omega)
  have hprefix (v : ℕ) : ∑ j ∈ Finset.range (v + 1), g j =
      ((tailCoeffGoodDenominators v).card : ℝ) := by
    exact sum_tailGoodIndicator_range v
  have hgsmall : ∑ j ∈ Finset.range (1 + 1), g j = 0 := by
    simp [g, tailGoodIndicator]
  have hdiff (v : ℕ) (hv : 2 ≤ v) :
      c / ((v : ℝ) * (v + 1)) ≤ f v - f (v + 1) := by
    have hpow := pow_add_one_mono v
    have hvR : (0 : ℝ) < v := by positivity
    have hv1R : (0 : ℝ) < v + 1 := by positivity
    dsimp [f]
    have hrecip : c / (v : ℝ) - c / (v + 1 : ℕ) =
        c / ((v : ℝ) * (v + 1)) := by
      norm_num only [Nat.cast_add, Nat.cast_one]
      field_simp
      ring
    have hpowR : ((65536 ^ v + 1 : ℕ) : ℝ) ≤
        ((65536 ^ (v + 1) + 1 : ℕ) : ℝ) := by exact_mod_cast hpow
    calc
      c / ((v : ℝ) * (v + 1)) = c / (v : ℝ) - c / (v + 1 : ℕ) :=
        hrecip.symm
      _ ≤ c / (v : ℝ) - (65536 ^ v + 1 : ℕ) -
          (c / (v + 1 : ℕ) - (65536 ^ (v + 1) + 1 : ℕ)) := by
        linarith
  have hnonneg (v : ℕ) :
      0 ≤ ((tailCoeffGoodDenominators v).card : ℝ) := by positivity
  have hsumDiff :
      c * ∑ v ∈ Finset.Ico 2 y,
          ((tailCoeffGoodDenominators v).card : ℝ) /
            ((v : ℝ) * (v + 1)) ≤
        ∑ v ∈ Finset.Ioc 1 (y - 1),
          (f v - f (v + 1)) *
            ((tailCoeffGoodDenominators v).card : ℝ) := by
    have hsets : Finset.Ioc 1 (y - 1) = Finset.Ico 2 y := by
      ext v
      simp
      omega
    rw [hsets, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro v hv
    rw [Finset.mem_Ico] at hv
    have hmul := mul_le_mul_of_nonneg_right (hdiff v hv.1) (hnonneg v)
    convert hmul using 1 <;> ring
  rw [sum_tailGood_eq_sum_indicator]
  change (∑ m ∈ Finset.Ioc 1 y, f m * g m) = _ at hparts
  simp only [smul_eq_mul] at hparts
  rw [hprefix y, hgsmall] at hparts
  simp only [mul_zero, sub_zero] at hparts
  simp_rw [hprefix] at hparts
  have hsumNeg :
      -(∑ x ∈ Finset.Ioc 1 (y - 1),
          (f (x + 1) - f x) * ((tailCoeffGoodDenominators x).card : ℝ)) =
        ∑ x ∈ Finset.Ioc 1 (y - 1),
          (f x - f (x + 1)) * ((tailCoeffGoodDenominators x).card : ℝ) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  rw [sub_eq_add_neg, hsumNeg] at hparts
  rw [hparts]
  have hendpoint : 0 ≤ f y * ((tailCoeffGoodDenominators y).card : ℝ) :=
    mul_nonneg (by simpa [f] using hend) (hnonneg y)
  simpa [add_comm] using add_le_add hsumDiff hendpoint

/-- Tail-good products alone give a restricted version of F-031. -/
theorem sum_tail_compatiblePrimeSet_card_le (N y : ℕ) :
    ∑ m ∈ tailCoeffGoodDenominators y, (compatiblePrimeSet N m).card ≤
      (coeffGoodDenominators N).card := by
  classical
  apply le_trans ?_ (sum_compatiblePrimeSet_card_le N y)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro m hm
    simp only [tailCoeffGoodDenominators, coeffGoodDenominators,
      Finset.mem_filter, Finset.mem_Icc] at hm ⊢
    exact ⟨⟨by omega, hm.1.2⟩, hm.2⟩
  · intro i hiS hiT
    positivity

/-- The restricted generated products lie in the tail-good set, so the
right side can also omit denominator one. -/
theorem sum_tail_compatiblePrimeSet_card_le_tail (N y : ℕ) :
    ∑ m ∈ tailCoeffGoodDenominators y, (compatiblePrimeSet N m).card ≤
      (tailCoeffGoodDenominators N).card := by
  classical
  let G := (tailCoeffGoodDenominators y).biUnion
    (fun m => (compatiblePrimeSet N m).image (fun p => m * p))
  have hpair : ((tailCoeffGoodDenominators y : Finset ℕ) : Set ℕ).PairwiseDisjoint
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
    change m ∈ tailCoeffGoodDenominators y at hm
    change n ∈ tailCoeffGoodDenominators y at hn
    simp only [tailCoeffGoodDenominators, Finset.mem_filter,
      Finset.mem_Icc] at hm hn
    have hmPos : 0 < m := by omega
    have hnPos : 0 < n := by omega
    have hthm : m ≤ compatibilityThreshold m := by
      rw [compatibilityThreshold]
      nlinarith [Nat.lcmUpto_pos m]
    have hthn : n ≤ compatibilityThreshold n := by
      rw [compatibilityThreshold]
      nlinarith [Nat.lcmUpto_pos n]
    have hinj := mul_prime_pair_injective hmPos hnPos hpSet.2 hqSet.2
      (lt_of_le_of_lt hthm hpSet.1.1) (lt_of_le_of_lt hthn hqSet.1.1) heq.symm
    exact hmn hinj.1
  have hcardG : G.card =
      ∑ m ∈ tailCoeffGoodDenominators y, (compatiblePrimeSet N m).card := by
    rw [Finset.card_biUnion hpair]
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.card_image_of_injective]
    intro p q hpq
    rw [tailCoeffGoodDenominators, Finset.mem_filter, Finset.mem_Icc] at hm
    change m * p = m * q at hpq
    exact Nat.mul_left_cancel (by omega) hpq
  have hsubset : G ⊆ tailCoeffGoodDenominators N := by
    intro z hz
    rw [Finset.mem_biUnion] at hz
    obtain ⟨m, hm, hzm⟩ := hz
    rw [Finset.mem_image] at hzm
    obtain ⟨p, hp, rfl⟩ := hzm
    rw [tailCoeffGoodDenominators, Finset.mem_filter, Finset.mem_Icc] at hm
    rw [compatiblePrimeSet, Finset.mem_filter, Finset.mem_Ioc] at hp
    rw [tailCoeffGoodDenominators, Finset.mem_filter, Finset.mem_Icc]
    have hmPos : 0 < m := by omega
    have hpPos := hp.2.pos
    refine ⟨⟨by nlinarith, ?_⟩, ?_⟩
    · simpa [Nat.mul_comm] using
        (Nat.le_div_iff_mul_le hmPos).mp hp.1.2
    · exact coeffGood_mul_prime_of_large hm.2 hp.2 hp.1.1
  rw [← hcardG]
  exact Finset.card_le_card hsubset

/-- Arithmetic tail-good denominators are genuine exact-doubling
denominators. -/
theorem tailCoeffGood_subset_goodDenominators (N : ℕ) :
    tailCoeffGoodDenominators N ⊆ goodDenominators N := by
  intro m hm
  rw [tailCoeffGoodDenominators, Finset.mem_filter, Finset.mem_Icc] at hm
  rw [goodDenominators, Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨by omega, hm.1.2⟩, goodDenominator_of_coeffGood hm.2⟩

theorem tailCoeffGood_card_le_goodDenominators (N : ℕ) :
    (tailCoeffGoodDenominators N).card ≤ (goodDenominators N).card :=
  Finset.card_le_card (tailCoeffGood_subset_goodDenominators N)

end Research
