import ResearchPNT.LowerGlobal

/-! # Comparing the adaptive benchmark with the fully stopped product -/

open Filter Asymptotics Real

namespace ResearchPNT

noncomputable def activeAdaptiveHeights (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 2)).filter
    (fun k => Research.adaptiveLowerCutoff k ≤ Research.logLogNat (N + 1))

noncomputable def chosenAdaptiveHeight (N : ℕ) : ℕ :=
  if h : (activeAdaptiveHeights N).Nonempty then
    (activeAdaptiveHeights N).max' h
  else 0

/-- The double logarithm is below its natural argument. -/
theorem logLogNat_succ_le (N : ℕ) (hN : 2 ≤ N) :
    Research.logLogNat (N + 1) ≤ (N + 1 : ℕ) := by
  have hlogPos : 0 < Real.log ((N + 1 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N + 1 by omega))
  have h1 := Real.log_le_sub_one_of_pos hlogPos
  have h2 := Real.log_le_sub_one_of_pos
    (by exact_mod_cast (show 0 < N + 1 by omega) : (0 : ℝ) < (N + 1 : ℕ))
  dsimp [Research.logLogNat]
  nlinarith

/-- Maximal-height properties. -/
theorem chosenAdaptiveHeight_spec (N : ℕ) (hN : 2 ≤ N)
    (hzero : Research.adaptiveLowerCutoff 0 ≤ Research.logLogNat (N + 1)) :
    Research.adaptiveLowerCutoff (chosenAdaptiveHeight N) ≤
        Research.logLogNat (N + 1) ∧
      Research.logLogNat (N + 1) <
        Research.adaptiveLowerCutoff (chosenAdaptiveHeight N + 1) ∧
      chosenAdaptiveHeight N ≤ N := by
  let S := activeAdaptiveHeights N
  have hSne : S.Nonempty := by
    refine ⟨0, ?_⟩
    change 0 ∈ (Finset.range (N + 2)).filter
      (fun k => Research.adaptiveLowerCutoff k ≤ Research.logLogNat (N + 1))
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hzero⟩
  have hchosen : chosenAdaptiveHeight N = S.max' hSne := by
    rw [chosenAdaptiveHeight, dif_pos]
  have hmem : chosenAdaptiveHeight N ∈ S := by
    rw [hchosen]
    exact Finset.max'_mem S hSne
  change chosenAdaptiveHeight N ∈
    (Finset.range (N + 2)).filter
      (fun k => Research.adaptiveLowerCutoff k ≤ Research.logLogNat (N + 1)) at hmem
  rw [Finset.mem_filter, Finset.mem_range] at hmem
  have hlogUpper := logLogNat_succ_le N hN
  have hN1inactive : Research.logLogNat (N + 1) <
      Research.adaptiveLowerCutoff (N + 1) := by
    have htower := Research.tower_two_succ_le_cutoff (N + 1)
    have hlin := Research.nat_add_two_le_realTower (N + 2)
    have hcast : ((N + 1 : ℕ) : ℝ) < (N + 4 : ℕ) := by exact_mod_cast (by omega)
    exact lt_of_le_of_lt hlogUpper
      (lt_of_lt_of_le hcast (le_trans hlin htower))
  have hkN : chosenAdaptiveHeight N ≤ N := by
    have hkBound : chosenAdaptiveHeight N < N + 2 := hmem.1
    by_contra hnot
    have hkEq : chosenAdaptiveHeight N = N + 1 := by omega
    rw [hkEq] at hmem
    exact (not_lt_of_ge hmem.2) hN1inactive
  have hnextInactive : Research.logLogNat (N + 1) <
      Research.adaptiveLowerCutoff (chosenAdaptiveHeight N + 1) := by
    by_contra hnot
    have hnextMem : chosenAdaptiveHeight N + 1 ∈ S := by
      change chosenAdaptiveHeight N + 1 ∈ (Finset.range (N + 2)).filter
        (fun k => Research.adaptiveLowerCutoff k ≤ Research.logLogNat (N + 1))
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, le_of_not_gt hnot⟩
    have hmax := Finset.le_max' S (chosenAdaptiveHeight N + 1) hnextMem
    rw [← hchosen] at hmax
    omega
  exact ⟨hmem.2, hnextInactive, hkN⟩

/-- The first `k` ordinary renewal factors are active at a chosen adaptive
height. -/
theorem chosen_initial_segment_active {N k : ℕ}
    (hactive : Research.adaptiveLowerCutoff k ≤ Research.logLogNat (N + 1)) :
    ∀ j, j < k → Research.renewalThreshold <
      Research.iteratedLog j (Research.logLogNat (N + 1)) := by
  intro j hj
  have hbaseTower := Research.analysisBaseTower_le_cutoff k
  have hx : Research.realTower Research.lowerAnalysisBase k ≤
      Research.logLogNat (N + 1) := le_trans hbaseTower hactive
  have hjk : j ≤ k := by omega
  have hfloor : Research.realTower 2 j ≤
      Research.realTower Research.lowerAnalysisBase k := by
    exact le_trans (Research.realTower_mono hjk)
      (Research.realTower_mono_base k Research.two_le_lowerAnalysisBase)
  have hmono := Research.iteratedLog_mono_on (k := j)
    (x := Research.realTower Research.lowerAnalysisBase k)
    (y := Research.logLogNat (N + 1)) hfloor hx
  have hcancel : Research.iteratedLog j
      (Research.realTower Research.lowerAnalysisBase k) =
      Research.realTower Research.lowerAnalysisBase (k - j) := by
    have heq : j + (k - j) = k := Nat.add_sub_of_le hjk
    calc
      Research.iteratedLog j (Research.realTower Research.lowerAnalysisBase k) =
          Research.iteratedLog j
            (Research.realTower Research.lowerAnalysisBase (j + (k - j))) := by rw [heq]
      _ = Research.realTower Research.lowerAnalysisBase (k - j) :=
        Research.iteratedLog_realTower_add _ _ _
  rw [hcancel] at hmono
  have hremain : 1 ≤ k - j := by omega
  have hbaseExp : Real.exp Research.lowerAnalysisBase ≤
      Research.realTower Research.lowerAnalysisBase (k - j) := by
    have hb0 : 0 ≤ Research.lowerAnalysisBase :=
      le_trans (by norm_num) Research.two_le_lowerAnalysisBase
    have hmonoHeight : Research.realTower Research.lowerAnalysisBase 1 ≤
        Research.realTower Research.lowerAnalysisBase (k - j) :=
      Research.realTower_mono_height_of_nonneg hb0 hremain
    simpa [Research.realTower] using hmonoHeight
  have hTbase : Research.renewalThreshold < Real.exp Research.lowerAnalysisBase := by
    rw [Research.renewalThreshold]
    apply Real.exp_lt_exp.mpr
    have h3base : (3 : ℝ) < Research.lowerAnalysisBase := by
      rw [Research.lowerAnalysisBase,
        ← Real.exp_log (by norm_num : (0 : ℝ) < 3)]
      apply Real.exp_lt_exp.mpr
      have hlog := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
      norm_num at hlog ⊢
      linarith
    exact h3base
  exact lt_of_lt_of_le hTbase (le_trans hbaseExp hmono)

/-- The first inactive cutoff bounds the next iterated logarithm by one
fixed constant. -/
theorem chosen_next_iteratedLog_le_upperBase (N : ℕ) (hN : 2 ≤ N)
    (hzero : Research.adaptiveLowerCutoff 0 ≤ Research.logLogNat (N + 1)) :
    Research.iteratedLog (chosenAdaptiveHeight N + 1)
        (Research.logLogNat (N + 1)) ≤ Research.lowerUpperTowerBase := by
  obtain ⟨hactive, hnext, hkN⟩ := chosenAdaptiveHeight_spec N hN hzero
  let k := chosenAdaptiveHeight N
  have hfloor : Research.realTower 2 (k + 1) ≤
      Research.logLogNat (N + 1) :=
    le_trans (Research.tower_two_succ_le_cutoff k) hactive
  have hupper : Research.logLogNat (N + 1) ≤
      Research.realTower Research.lowerUpperTowerBase (k + 1) :=
    le_trans hnext.le (Research.cutoff_le_upperTower (k + 1))
  have hmono := Research.iteratedLog_mono_on (k := k + 1)
    (x := Research.logLogNat (N + 1))
    (y := Research.realTower Research.lowerUpperTowerBase (k + 1))
    hfloor hupper
  rw [Research.iteratedLog_realTower_same] at hmono
  exact hmono

noncomputable def remainingUpperArgument : ℝ :=
  Real.exp Research.lowerUpperTowerBase

noncomputable def remainingUpperHeight : ℕ :=
  Nat.ceil remainingUpperArgument + 1

noncomputable def remainingProductConstant : ℝ :=
  Research.renewalProduct remainingUpperHeight remainingUpperArgument

/-- The fully stopped product is at most a fixed terminal constant times the
adaptive initial product. -/
theorem full_product_le_adaptive_initial (N : ℕ) (hN : 2 ≤ N)
    (hzero : Research.adaptiveLowerCutoff 0 ≤ Research.logLogNat (N + 1)) :
    Research.renewalProduct N (Research.logLogNat N) ≤
      Research.iteratedLogProduct (chosenAdaptiveHeight N)
          (Research.logLogNat (N + 1)) * remainingProductConstant := by
  obtain ⟨hactive, hnext, hkN⟩ := chosenAdaptiveHeight_spec N hN hzero
  let k := chosenAdaptiveHeight N
  let z := Research.logLogNat (N + 1)
  let u := Research.iteratedLog k z
  have hwz : Research.logLogNat N ≤ z := by
    dsimp [z]
    exact Research.logLogNat_mono hN (by omega)
  have hfirst := Research.monotone_renewalProduct N hwz
  have hsegment := chosen_initial_segment_active hactive
  have hdecomp : Research.renewalProduct N z =
      Research.iteratedLogProduct k z *
        Research.renewalProduct (N - k) u := by
    have hNk : k + (N - k) = N := Nat.add_sub_of_le hkN
    calc
      Research.renewalProduct N z =
          Research.renewalProduct (k + (N - k)) z := by rw [hNk]
      _ = Research.iteratedLogProduct k z *
          Research.renewalProduct (N - k) (Research.iteratedLog k z) :=
        Research.renewalProduct_add_eq_iteratedLogProduct_mul
          k (N - k) z hsegment
  have hu2 : 2 ≤ u := by
    have hfloor : Research.realTower 2 k ≤ z :=
      le_trans (Research.tower_two_le_adaptiveLowerCutoff k) hactive
    exact Research.two_le_iteratedLog_of_tower_le hfloor k le_rfl
  have hlogu : Real.log u ≤ Research.lowerUpperTowerBase := by
    have hnextBound := chosen_next_iteratedLog_le_upperBase N hN hzero
    rw [← Research.iteratedLog_succ_last]
    simpa [k, z, u] using hnextBound
  have huU : u ≤ remainingUpperArgument := by
    rw [remainingUpperArgument, ← Real.exp_log (by linarith : 0 < u)]
    exact Real.exp_le_exp.mpr hlogu
  have hremain : Research.renewalProduct (N - k) u ≤
      remainingProductConstant := by
    rw [remainingProductConstant, remainingUpperHeight]
    exact Research.renewalProduct_le_fixed_of_le
      (by rw [remainingUpperArgument]; positivity) huU (N - k)
  have hPnonneg : 0 ≤ Research.iteratedLogProduct k z := by
    have h := Research.cutoffAtIteratedLogProduct_nonneg
      (Research.tower_two_le_adaptiveLowerCutoff k) z
    rw [Research.cutoffAtIteratedLogProduct_eq hactive] at h
    exact h
  calc
    Research.renewalProduct N (Research.logLogNat N) ≤
        Research.renewalProduct N z := hfirst
    _ = Research.iteratedLogProduct k z *
        Research.renewalProduct (N - k) u := hdecomp
    _ ≤ Research.iteratedLogProduct k z * remainingProductConstant :=
      mul_le_mul_of_nonneg_left hremain hPnonneg

/-- The terminal constant is positive. -/
theorem remainingProductConstant_pos : 0 < remainingProductConstant := by
  rw [remainingProductConstant]
  exact lt_of_lt_of_le zero_lt_one
    (Research.one_le_renewalProduct remainingUpperHeight remainingUpperArgument)

/-- Eventual matching lower bound for the fully stopped product. -/
theorem exists_eventual_full_product_tail_lower :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      C * ((N : ℝ) / Real.log N) *
          Research.renewalProduct N (Research.logLogNat N) ≤
        ((Research.tailCoeffGoodDenominators N).card : ℝ) := by
  obtain ⟨K, hK, hglobal⟩ := exists_global_adaptive_lower
  let D := remainingProductConstant
  let C := K / (2 * D)
  have hD : 0 < D := by simpa [D] using remainingProductConstant_pos
  have hC : 0 < C := by dsimp [C]; positivity
  have hsuccTend : Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ)) atTop atTop := by
    apply Filter.tendsto_atTop_mono' atTop
      (f₁ := fun N : ℕ => (N : ℝ))
    · filter_upwards [] with N
      norm_num
    · exact tendsto_natCast_atTop_atTop
  have hzTend : Tendsto (fun N : ℕ => Research.logLogNat (N + 1))
      atTop atTop := by
    exact Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp hsuccTend)
  have hzeroEv : ∀ᶠ N : ℕ in atTop,
      Research.adaptiveLowerCutoff 0 ≤ Research.logLogNat (N + 1) :=
    hzTend.eventually (eventually_ge_atTop _)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hzeroEv,
    (eventually_ge_atTop 3 : ∀ᶠ N : ℕ in atTop, 3 ≤ N)] with N hzero hN
  let k := chosenAdaptiveHeight N
  obtain ⟨hactive, hnext, hkN⟩ := chosenAdaptiveHeight_spec N (by omega) hzero
  have hfull := full_product_le_adaptive_initial N (by omega) hzero
  have hmain := hglobal k N (by omega)
  have hcoef := Research.coefficient_ge_half k
  have hPnonneg : 0 ≤ Research.iteratedLogProduct k
      (Research.logLogNat (N + 1)) := by
    have h := Research.cutoffAtIteratedLogProduct_nonneg
      (Research.tower_two_le_adaptiveLowerCutoff k)
      (Research.logLogNat (N + 1))
    rw [Research.cutoffAtIteratedLogProduct_eq hactive] at h
    exact h
  have hbench : Research.adaptiveLowerRenewalBenchmark
      Research.adaptiveLowerCutoff k N =
      ((N + 1 : ℕ) : ℝ) / Real.log N *
        Research.iteratedLogProduct k (Research.logLogNat (N + 1)) := by
    rw [Research.adaptiveLowerRenewalBenchmark,
      Research.cutoffAtIteratedLogProduct_eq hactive]
  rw [hbench] at hmain
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hscale :
      (K / 2) * ((N : ℝ) / Real.log N) *
          Research.iteratedLogProduct k (Research.logLogNat (N + 1)) ≤
        K * Research.lowerHeightCoefficient k *
          (((N + 1 : ℕ) : ℝ) / Real.log N *
            Research.iteratedLogProduct k (Research.logLogNat (N + 1))) := by
    have hNle : (N : ℝ) ≤ (N + 1 : ℕ) := by exact_mod_cast (Nat.le_succ N)
    have hfrac : (N : ℝ) / Real.log N ≤
        ((N + 1 : ℕ) : ℝ) / Real.log N :=
      div_le_div_of_nonneg_right hNle hlog.le
    have hcoefK : K / 2 ≤ K * Research.lowerHeightCoefficient k := by
      nlinarith [mul_le_mul_of_nonneg_left hcoef hK.le]
    have hfirst : (K / 2) * ((N : ℝ) / Real.log N) ≤
        (K * Research.lowerHeightCoefficient k) *
          (((N + 1 : ℕ) : ℝ) / Real.log N) :=
      mul_le_mul hcoefK hfrac (by positivity)
        (mul_nonneg hK.le (Research.lowerHeightCoefficient_nonneg k))
    simpa [mul_assoc] using mul_le_mul_of_nonneg_right hfirst hPnonneg
  have hPD : Research.renewalProduct N (Research.logLogNat N) / D ≤
      Research.iteratedLogProduct k (Research.logLogNat (N + 1)) := by
    rw [div_le_iff₀ hD]
    simpa [D, mul_comm] using hfull
  have hleft : C * ((N : ℝ) / Real.log N) *
      Research.renewalProduct N (Research.logLogNat N) ≤
      (K / 2) * ((N : ℝ) / Real.log N) *
        Research.iteratedLogProduct k (Research.logLogNat (N + 1)) := by
    dsimp [C]
    have hfactor : 0 ≤ (K / 2) * ((N : ℝ) / Real.log N) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hPD hfactor
    field_simp [ne_of_gt hD] at hmul ⊢
    nlinarith
  exact le_trans hleft (le_trans hscale hmain)

#print axioms exists_eventual_full_product_tail_lower

end ResearchPNT
