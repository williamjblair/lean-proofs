import ResearchPNT.LowerParameterChoice

/-! # Global lower height induction -/

open Filter Asymptotics Real

namespace ResearchPNT

/-- Prime denominators up to `N/2` are a subset of the tail-good set. -/
theorem primeCounting_half_le_tailGood (N : ℕ) (hN : 4 ≤ N) :
    Nat.primeCounting (N / 2) ≤
      (Research.tailCoeffGoodDenominators N).card := by
  let P := (Finset.Ioc 1 (N / 2)).filter Nat.Prime
  have hsub : P ⊆ Research.tailCoeffGoodDenominators N := by
    intro p hp
    simp only [P, Finset.mem_filter, Finset.mem_Ioc] at hp
    rw [Research.tailCoeffGoodDenominators, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨by omega, le_trans hp.1.2 (Nat.div_le_self N 2)⟩, ?_⟩
    have hlarge : Nat.lcmUpto 1 * 1 < p := by
      norm_num [Nat.lcmUpto]
      exact hp.2.one_lt
    simpa using Research.coeffGood_mul_prime_of_large Research.coeffGood_one hp.2 hlarge
  have hcard : P.card = Nat.primeCounting (N / 2) := by
    have h := card_prime_Ioc 1 (N / 2) (by omega)
    rw [Nat.primeCounting_eq_zero_iff.mpr (by omega : 1 ≤ 1)] at h
    simpa [P] using h
  rw [← hcard]
  exact Finset.card_le_card hsub

/-- Eventually one quarter of the height-zero adaptive benchmark is already
provided by prime denominators. -/
theorem eventually_quarter_adaptive_base :
    ∀ᶠ N : ℕ in atTop,
      (1 / 4 : ℝ) *
          Research.adaptiveLowerRenewalBenchmark Research.adaptiveLowerCutoff 0 N ≤
        ((Research.tailCoeffGoodDenominators N).card : ℝ) := by
  have hY2 : ∀ᶠ N : ℕ in atTop, 2 ≤ lowerY N := by
    filter_upwards [(eventually_ge_atTop ((65536 ^ 2) ^ 2) :
      ∀ᶠ N : ℕ in atTop, (65536 ^ 2) ^ 2 ≤ N)] with N hN
    exact Nat.le_log_of_pow_le (by norm_num : 1 < 65536 ^ 2) hN
  have hN2 : ∀ᶠ N : ℕ in atTop, 4 ≤ N := eventually_ge_atTop 4
  have hlogTend : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_primeCounting_floor_div_ge_main, hY2, hN2,
    hlogTend.eventually (eventually_gt_atTop 0)] with N hp hY hN hlog
  have hprime := hp 2 (by omega) hY
  have htail : (N : ℝ) / (2 * Real.log N) ≤
      ((Research.tailCoeffGoodDenominators N).card : ℝ) :=
    le_trans hprime (by exact_mod_cast primeCounting_half_le_tailGood N hN)
  have hcut : Research.cutoffAtIteratedLogProduct
      (Research.adaptiveLowerCutoff 0) 0 (Research.logLogNat (N + 1)) ≤ 1 := by
    rw [Research.cutoffAtIteratedLogProduct]
    split_ifs <;> simp [Research.iteratedLogProduct]
  have hbench : Research.adaptiveLowerRenewalBenchmark
      Research.adaptiveLowerCutoff 0 N ≤ (N + 1 : ℕ) / Real.log N := by
    rw [Research.adaptiveLowerRenewalBenchmark]
    have hf : 0 ≤ (((N + 1 : ℕ) : ℝ) / Real.log N) :=
      div_nonneg (by positivity) hlog.le
    simpa using mul_le_mul_of_nonneg_left hcut hf
  calc
    (1 / 4 : ℝ) * Research.adaptiveLowerRenewalBenchmark
        Research.adaptiveLowerCutoff 0 N ≤
      (1 / 4 : ℝ) * (((N + 1 : ℕ) : ℝ) / Real.log N) :=
      mul_le_mul_of_nonneg_left hbench (by norm_num)
    _ ≤ (N : ℝ) / (2 * Real.log N) := by
      field_simp [ne_of_gt hlog]
      norm_num only [Nat.cast_add, Nat.cast_one]
      have hNR : (4 : ℝ) ≤ N := by exact_mod_cast hN
      nlinarith
    _ ≤ ((Research.tailCoeffGoodDenominators N).card : ℝ) := htail

/-- The adaptive benchmark vanishes above linear height for a fixed `N`. -/
theorem adaptiveLowerRenewalBenchmark_eq_zero_of_large_height
    {N k : ℕ} (hN : 2 ≤ N) (hk : N + 2 ≤ k) :
    Research.adaptiveLowerRenewalBenchmark Research.adaptiveLowerCutoff k N = 0 := by
  have hlogN1 : Research.logLogNat (N + 1) ≤ (N + 1 : ℕ) := by
    have hlogPos : 0 < Real.log ((N + 1 : ℕ) : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < N + 1 by omega))
    have h1 := Real.log_le_sub_one_of_pos hlogPos
    have h2 := Real.log_le_sub_one_of_pos
      (by exact_mod_cast (show 0 < N + 1 by omega) : (0 : ℝ) < (N + 1 : ℕ))
    dsimp [Research.logLogNat]
    nlinarith
  have hcutLarge : Research.logLogNat (N + 1) <
      Research.adaptiveLowerCutoff k := by
    have hlin := Research.nat_add_two_le_realTower k
    have hfloor := Research.tower_two_le_adaptiveLowerCutoff k
    have : ((N + 1 : ℕ) : ℝ) < (k + 2 : ℕ) := by exact_mod_cast (by omega)
    exact lt_of_le_of_lt hlogN1 (lt_of_lt_of_le this (le_trans hlin hfloor))
  rw [Research.adaptiveLowerRenewalBenchmark,
    Research.cutoffAtIteratedLogProduct]
  rw [if_neg (not_le.mpr hcutLarge)]
  simp

/-- A single positive constant works at every adaptive logarithmic height. -/
theorem exists_global_adaptive_lower :
    ∃ K : ℝ, 0 < K ∧ ∀ k N : ℕ, 2 ≤ N →
      K * Research.lowerHeightCoefficient k *
          Research.adaptiveLowerRenewalBenchmark
            Research.adaptiveLowerCutoff k N ≤
        ((Research.tailCoeffGoodDenominators N).card : ℝ) := by
  have hY3 : ∀ᶠ N : ℕ in atTop, 3 ≤ lowerY N := by
    filter_upwards [(eventually_ge_atTop ((65536 ^ 2) ^ 3) :
      ∀ᶠ N : ℕ in atTop, (65536 ^ 2) ^ 3 ≤ N)] with N hN
    exact Nat.le_log_of_pow_le (by norm_num : 1 < 65536 ^ 2) hN
  have hallEv : ∀ᶠ N : ℕ in atTop,
      (1 / 4 : ℝ) * Research.adaptiveLowerRenewalBenchmark
          Research.adaptiveLowerCutoff 0 N ≤
          ((Research.tailCoeffGoodDenominators N).card : ℝ) ∧
      ((N : ℝ) / Real.log N) *
          ∑ v ∈ Finset.Ico 2 (lowerY N),
            ((Research.tailCoeffGoodDenominators v).card : ℝ) /
              ((v : ℝ) * (v + 1)) ≤
          ((Research.tailCoeffGoodDenominators N).card : ℝ) ∧
      3 ≤ lowerY N ∧ 3 ≤ N := by
    filter_upwards [eventually_quarter_adaptive_base,
      eventually_tailGood_lower_renewal, hY3,
      (eventually_ge_atTop 3 : ∀ᶠ N : ℕ in atTop, 3 ≤ N)] with
        N hb hr hy hN
    exact ⟨hb, hr, hy, hN⟩
  obtain ⟨N0, hN0⟩ := (eventually_atTop.1 hallEv)
  let B : ℝ := ∑ N ∈ Finset.Icc 2 N0,
    ∑ k ∈ Finset.range (N + 2),
      Research.lowerHeightCoefficient k *
        Research.adaptiveLowerRenewalBenchmark
          Research.adaptiveLowerCutoff k N
  let K : ℝ := min (1 / 4) (1 / (B + 1))
  have hterm0 (k N : ℕ) : 0 ≤
      Research.lowerHeightCoefficient k *
        Research.adaptiveLowerRenewalBenchmark
          Research.adaptiveLowerCutoff k N := by
    apply mul_nonneg (Research.lowerHeightCoefficient_nonneg k)
    by_cases hN : 2 ≤ N
    · exact Research.adaptiveLowerRenewalBenchmark_nonneg
        (Research.tower_two_le_adaptiveLowerCutoff k) N hN
    · interval_cases N <;>
        simp [Research.adaptiveLowerRenewalBenchmark,
          Research.cutoffAtIteratedLogProduct]
  have hB0 : 0 ≤ B := by
    dsimp [B]
    apply Finset.sum_nonneg
    intro N hN
    apply Finset.sum_nonneg
    intro k hk
    exact hterm0 k N
  have hKpos : 0 < K := by
    dsimp [K]
    apply lt_min (by norm_num)
    positivity
  have hKquarter : K ≤ 1 / 4 := by
    simpa [K] using (min_le_left (1 / 4 : ℝ) (1 / (B + 1)))
  have hKfrac : K ≤ 1 / (B + 1) := by
    simpa [K] using (min_le_right (1 / 4 : ℝ) (1 / (B + 1)))
  have hfinite (N k : ℕ) (hN2 : 2 ≤ N) (hNN0 : N ≤ N0)
      (hk : k < N + 2) :
      K * Research.lowerHeightCoefficient k *
          Research.adaptiveLowerRenewalBenchmark
            Research.adaptiveLowerCutoff k N ≤
        ((Research.tailCoeffGoodDenominators N).card : ℝ) := by
    have hNmem : N ∈ Finset.Icc 2 N0 := Finset.mem_Icc.mpr ⟨hN2, hNN0⟩
    have hkmem : k ∈ Finset.range (N + 2) := Finset.mem_range.mpr hk
    have hinner0 (M : ℕ) : 0 ≤ ∑ j ∈ Finset.range (M + 2),
        Research.lowerHeightCoefficient j *
          Research.adaptiveLowerRenewalBenchmark
            Research.adaptiveLowerCutoff j M := by
      apply Finset.sum_nonneg
      intro j hj
      exact hterm0 j M
    have htermLeInner :
        Research.lowerHeightCoefficient k *
            Research.adaptiveLowerRenewalBenchmark
              Research.adaptiveLowerCutoff k N ≤
          ∑ j ∈ Finset.range (N + 2),
            Research.lowerHeightCoefficient j *
              Research.adaptiveLowerRenewalBenchmark
                Research.adaptiveLowerCutoff j N :=
      Finset.single_le_sum (fun j hj => hterm0 j N) hkmem
    have hinnerLeB :
        (∑ j ∈ Finset.range (N + 2),
          Research.lowerHeightCoefficient j *
            Research.adaptiveLowerRenewalBenchmark
              Research.adaptiveLowerCutoff j N) ≤ B := by
      dsimp [B]
      exact Finset.single_le_sum (fun M hM => hinner0 M) hNmem
    have htermLeB := le_trans htermLeInner hinnerLeB
    have htermNonneg := hterm0 k N
    have hKB : K *
        (Research.lowerHeightCoefficient k *
          Research.adaptiveLowerRenewalBenchmark
            Research.adaptiveLowerCutoff k N) ≤ 1 := by
      calc
        K * (Research.lowerHeightCoefficient k *
            Research.adaptiveLowerRenewalBenchmark
              Research.adaptiveLowerCutoff k N) ≤
          (1 / (B + 1)) * B :=
            mul_le_mul hKfrac htermLeB htermNonneg (by positivity)
        _ ≤ 1 := by
          rw [one_div_mul_eq_div]
          exact (div_le_one (by linarith)).mpr (by linarith)
    have htail := Research.one_le_tailCoeffGood_card hN2
    exact le_trans (by simpa [mul_assoc] using hKB) (by exact_mod_cast htail)
  refine ⟨K, hKpos, ?_⟩
  intro k
  induction k with
  | zero =>
      intro N hN2
      by_cases hlarge : N0 ≤ N
      · have hb := (hN0 N hlarge).1
        have hbench0 := Research.adaptiveLowerRenewalBenchmark_nonneg
          (Research.tower_two_le_adaptiveLowerCutoff 0) N hN2
        rw [Research.lowerHeightCoefficient_zero]
        calc
          K * 1 * Research.adaptiveLowerRenewalBenchmark
              Research.adaptiveLowerCutoff 0 N ≤
            (1 / 4) * Research.adaptiveLowerRenewalBenchmark
              Research.adaptiveLowerCutoff 0 N := by
                simpa using mul_le_mul_of_nonneg_right hKquarter hbench0
          _ ≤ ((Research.tailCoeffGoodDenominators N).card : ℝ) := hb
      · exact hfinite N 0 hN2 (by omega) (by omega)
  | succ k ih =>
      intro N hN2
      by_cases hlarge : N0 ≤ N
      · by_cases htarget : Research.adaptiveLowerCutoff (k + 1) ≤
          Research.logLogNat (N + 1)
        · have hall := hN0 N hlarge
          have hN3 : 3 ≤ N := hall.2.2.2
          have hc := lowerStepConditions_of_target N k hN3 hall.2.2.1 htarget
          have hstep := adaptive_tail_lower_height_step
            Research.adaptiveLowerCutoff N (lowerY N) k
              (K * Research.lowerHeightCoefficient k) (Research.lowerEpsilon k)
            (Research.tower_two_le_adaptiveLowerCutoff k)
            (Research.tower_two_le_adaptiveLowerCutoff (k + 1))
            (Research.exp_cutoff_le_succ k)
            (mul_nonneg hKpos.le (Research.lowerHeightCoefficient_nonneg k))
            hc.hlog hc.hy hall.2.1
            (fun v hv => ih v (Finset.mem_Ico.mp hv).1)
            (Research.lowerEpsilon_pos k) (Research.lowerEpsilon_le_half k)
            hc.hx1 hc.htlow hc.htower hc.hratio hc.horbitX hc.hz1
            hc.hendpoint hc.horbitL htarget hc.hmesh
          rw [Research.lowerHeightCoefficient_succ]
          simpa [mul_assoc] using hstep
        · rw [Research.adaptiveLowerRenewalBenchmark,
            Research.cutoffAtIteratedLogProduct, if_neg htarget]
          simp
      · by_cases hk : k + 1 < N + 2
        · exact hfinite N (k + 1) hN2 (by omega) hk
        · rw [adaptiveLowerRenewalBenchmark_eq_zero_of_large_height hN2 (by omega)]
          simp

#print axioms exists_global_adaptive_lower

end ResearchPNT
