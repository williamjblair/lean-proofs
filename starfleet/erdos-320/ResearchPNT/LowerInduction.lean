import ResearchPNT.LowerRenewal
import Research.LowerBenchmark

/-! # One lower height-induction step -/

open Filter Asymptotics Real

namespace ResearchPNT

/-- One unit-coefficient renewal step advances the iterated-log height.  The
only multiplicative loss is the explicit summable factor `(1-e)^(2k+3)`. -/
theorem lower_height_step
    (N y k : ℕ) (K e : ℝ)
    (hK : 0 ≤ K) (hlog : 0 < Real.log (N : ℝ))
    (hy : 3 ≤ y)
    (hrec : ((N : ℝ) / Real.log N) *
        ∑ v ∈ Finset.Ico 2 y,
          ((Research.tailCoeffGoodDenominators v).card : ℝ) /
            ((v : ℝ) * (v + 1)) ≤
      ((Research.coeffGoodDenominators N).card : ℝ))
    (hind : ∀ v ∈ Finset.Ico 2 y,
      K * Research.lowerRenewalBenchmark k v ≤
        ((Research.tailCoeffGoodDenominators v).card : ℝ))
    (he0 : 0 < e) (he2 : e ≤ 1 / 2)
    (hx1 : 1 < Research.logLogNat y)
    (htlow : Research.logLogNat 2 ≤ Research.logLogNat y ^ (1 - e))
    (htowerX : Research.realTower 2 k ≤
      Research.logLogNat y ^ (1 - e))
    (hratio : Research.logLogNat y ^ (1 - e) ≤
      e * Research.logLogNat y)
    (horbitX : ∀ j, 1 ≤ j → j ≤ k →
      2 ≤ Research.iteratedLog j (Research.logLogNat y))
    (hz1 : 1 < Research.logLogNat (N + 1))
    (hendpoint : (1 - e) * Real.log (Research.logLogNat (N + 1)) ≤
      Research.logLogNat y)
    (horbitL : ∀ j, 1 ≤ j → j ≤ k →
      2 ≤ Research.iteratedLog j
        (Real.log (Research.logLogNat (N + 1))))
    (htarget : Research.realTower 2 (k + 1) ≤
      Research.logLogNat (N + 1))
    (hmeshFactor : (1 - e) * (N + 1 : ℕ) ≤ (N : ℝ)) :
    K * (1 - e) ^ (2 * k + 3) *
        Research.lowerRenewalBenchmark (k + 1) N ≤
      ((Research.coeffGoodDenominators N).card : ℝ) := by
  let cN : ℝ := (N : ℝ) / Real.log N
  let x : ℝ := Research.logLogNat y
  let z : ℝ := Research.logLogNat (N + 1)
  let L : ℝ := Real.log z
  have hcN : 0 ≤ cN := by dsimp [cN]; positivity
  have htrans := Research.iteratedLogProduct_le_lowerBenchmark_transform
    k y e hy he0 he2 hx1 htlow htowerX hratio horbitX
  have hsumInd : K *
      (∑ v ∈ Finset.Ico 2 y,
        Research.lowerRenewalBenchmark k v / ((v : ℝ) * (v + 1))) ≤
      ∑ v ∈ Finset.Ico 2 y,
        ((Research.tailCoeffGoodDenominators v).card : ℝ) /
          ((v : ℝ) * (v + 1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro v hv
    have hv2 : 2 ≤ v := (Finset.mem_Ico.mp hv).1
    have hden : (0 : ℝ) < (v : ℝ) * (v + 1) := by positivity
    rw [← mul_div_assoc]
    exact (div_le_div_iff_of_pos_right hden).mpr (hind v hv)
  have hrenew : K * cN *
      ((1 - e) ^ (k + 1) * x *
        Research.iteratedLogProduct k x) ≤
      ((Research.coeffGoodDenominators N).card : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_left htrans hK
    have h2 := mul_le_mul_of_nonneg_left hsumInd hcN
    have h3 := hrec
    dsimp [cN, x] at h1 h2 h3 ⊢
    calc
      K * ((N : ℝ) / Real.log N) *
          ((1 - e) ^ (k + 1) * Research.logLogNat y *
            Research.iteratedLogProduct k (Research.logLogNat y)) =
        ((N : ℝ) / Real.log N) *
          (K * ((1 - e) ^ (k + 1) * Research.logLogNat y *
            Research.iteratedLogProduct k (Research.logLogNat y))) := by ring
      _ ≤ ((N : ℝ) / Real.log N) *
          (K * ∑ v ∈ Finset.Ico 2 y,
            Research.lowerRenewalBenchmark k v / ((v : ℝ) * (v + 1))) :=
        mul_le_mul_of_nonneg_left h1 hcN
      _ ≤ ((N : ℝ) / Real.log N) *
          ∑ v ∈ Finset.Ico 2 y,
            ((Research.tailCoeffGoodDenominators v).card : ℝ) /
              ((v : ℝ) * (v + 1)) := h2
      _ ≤ ((Research.coeffGoodDenominators N).card : ℝ) := h3
  have hLpos : 0 < L := by
    dsimp [L, z]
    exact Real.log_pos hz1
  have hscale := Research.iteratedLogProduct_scale_lower k he0.le he2
    hLpos hendpoint horbitL
  have hxNonneg : 0 ≤ x := by dsimp [x]; linarith
  have hLNonneg : 0 ≤ L := hLpos.le
  have hPx : 0 ≤ Research.iteratedLogProduct k x := by
    have ht : Research.realTower 2 k ≤ x :=
      le_trans htowerX (le_of_lt (Real.rpow_lt_self_of_one_lt hx1 (by linarith)))
    have h := Research.clampedIteratedLogProduct_nonneg k x
    rw [Research.clampedIteratedLogProduct_eq ht] at h
    exact h
  have hPL : 0 ≤ Research.iteratedLogProduct k L := by
    have h := Research.clampedIteratedLogProduct_nonneg k L
    have htL : Research.realTower 2 k ≤ L := by
      rw [Research.realTower_succ] at htarget
      rw [← Real.log_exp (Research.realTower 2 k)]
      exact Real.log_le_log (by positivity) htarget
    rw [Research.clampedIteratedLogProduct_eq htL] at h
    exact h
  have hendpointProd :
      (1 - e) ^ (k + 1) * L * Research.iteratedLogProduct k L ≤
        x * Research.iteratedLogProduct k x := by
    have hmul := mul_le_mul hscale hendpoint
      (mul_nonneg (by linarith) hLNonneg)
      (by nlinarith [hPx])
    rw [pow_succ]
    nlinarith
  have htargetEq : Research.lowerRenewalBenchmark (k + 1) N =
      ((N + 1 : ℕ) : ℝ) / Real.log N *
        (L * Research.iteratedLogProduct k L) := by
    rw [Research.lowerRenewalBenchmark]
    have hclamp : Research.clampedIteratedLogProduct (k + 1) z =
        Research.iteratedLogProduct (k + 1) z :=
      Research.clampedIteratedLogProduct_eq htarget
    rw [hclamp, Research.iteratedLogProduct_succ]
  rw [htargetEq]
  have hone : 0 ≤ 1 - e := by linarith
  have hmeshScaled : (1 - e) * (((N + 1 : ℕ) : ℝ) / Real.log N) ≤ cN := by
    dsimp [cN]
    simpa [mul_div_assoc] using
      div_le_div_of_nonneg_right hmeshFactor hlog.le
  have hfinalScale := mul_le_mul hmeshScaled hendpointProd
    (by positivity) (by positivity)
  have hloss : 0 ≤ (1 - e) ^ (k + 1) := pow_nonneg hone _
  have hfinalLoss := mul_le_mul_of_nonneg_left hfinalScale hloss
  have hfinalK := mul_le_mul_of_nonneg_left hfinalLoss hK
  dsimp [cN, x, z, L] at hrenew hfinalK ⊢
  have hrenew' :
      K * ((1 - e) ^ (k + 1) *
        ((N : ℝ) / Real.log N *
          (Research.logLogNat y *
            Research.iteratedLogProduct k (Research.logLogNat y)))) ≤
        ((Research.coeffGoodDenominators N).card : ℝ) := by
    convert hrenew using 1 <;> ring
  have hchain := le_trans hfinalK hrenew'
  rw [show 2 * k + 3 = (k + 1) + 1 + (k + 1) by omega,
    pow_add, pow_add, pow_one]
  calc
    K * (((1 - e) ^ (k + 1) * (1 - e)) * (1 - e) ^ (k + 1)) *
        (((N + 1 : ℕ) : ℝ) / Real.log N *
          (Real.log (Research.logLogNat (N + 1)) *
            Research.iteratedLogProduct k
              (Real.log (Research.logLogNat (N + 1))))) =
      K * ((1 - e) ^ (k + 1) *
        (((1 - e) * (((N + 1 : ℕ) : ℝ) / Real.log N)) *
          ((1 - e) ^ (k + 1) *
            (Real.log (Research.logLogNat (N + 1)) *
              Research.iteratedLogProduct k
                (Real.log (Research.logLogNat (N + 1))))))) := by ring
    _ ≤ ((Research.coeffGoodDenominators N).card : ℝ) := by
      simpa only [mul_assoc] using hchain


/-- High-cutoff variant used for uniform iteration. -/
theorem high_lower_height_step
    (H : ℝ) (N y k : ℕ) (K e : ℝ)
    (hH : 2 ≤ H)
    (hK : 0 ≤ K) (hlog : 0 < Real.log (N : ℝ))
    (hy : 3 ≤ y)
    (hrec : ((N : ℝ) / Real.log N) *
        ∑ v ∈ Finset.Ico 2 y,
          ((Research.tailCoeffGoodDenominators v).card : ℝ) /
            ((v : ℝ) * (v + 1)) ≤
      ((Research.coeffGoodDenominators N).card : ℝ))
    (hind : ∀ v ∈ Finset.Ico 2 y,
      K * Research.highLowerRenewalBenchmark H k v ≤
        ((Research.tailCoeffGoodDenominators v).card : ℝ))
    (he0 : 0 < e) (he2 : e ≤ 1 / 2)
    (hx1 : 1 < Research.logLogNat y)
    (htlow : Research.logLogNat 2 ≤ Research.logLogNat y ^ (1 - e))
    (htowerX : Research.realTower H k ≤
      Research.logLogNat y ^ (1 - e))
    (hratio : Research.logLogNat y ^ (1 - e) ≤
      e * Research.logLogNat y)
    (horbitX : ∀ j, 1 ≤ j → j ≤ k →
      2 ≤ Research.iteratedLog j (Research.logLogNat y))
    (hz1 : 1 < Research.logLogNat (N + 1))
    (hendpoint : (1 - e) * Real.log (Research.logLogNat (N + 1)) ≤
      Research.logLogNat y)
    (horbitL : ∀ j, 1 ≤ j → j ≤ k →
      2 ≤ Research.iteratedLog j
        (Real.log (Research.logLogNat (N + 1))))
    (htarget : Research.realTower H (k + 1) ≤
      Research.logLogNat (N + 1))
    (hmeshFactor : (1 - e) * (N + 1 : ℕ) ≤ (N : ℝ)) :
    K * (1 - e) ^ (2 * k + 3) *
        Research.highLowerRenewalBenchmark H (k + 1) N ≤
      ((Research.coeffGoodDenominators N).card : ℝ) := by
  let cN : ℝ := (N : ℝ) / Real.log N
  let x : ℝ := Research.logLogNat y
  let z : ℝ := Research.logLogNat (N + 1)
  let L : ℝ := Real.log z
  have hcN : 0 ≤ cN := by dsimp [cN]; positivity
  have htrans := Research.iteratedLogProduct_le_highLowerBenchmark_transform
    H k y e hH hy he0 he2 hx1 htlow htowerX hratio horbitX
  have hsumInd : K *
      (∑ v ∈ Finset.Ico 2 y,
        Research.highLowerRenewalBenchmark H k v / ((v : ℝ) * (v + 1))) ≤
      ∑ v ∈ Finset.Ico 2 y,
        ((Research.tailCoeffGoodDenominators v).card : ℝ) /
          ((v : ℝ) * (v + 1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro v hv
    have hv2 : 2 ≤ v := (Finset.mem_Ico.mp hv).1
    have hden : (0 : ℝ) < (v : ℝ) * (v + 1) := by positivity
    rw [← mul_div_assoc]
    exact (div_le_div_iff_of_pos_right hden).mpr (hind v hv)
  have hrenew : K * cN *
      ((1 - e) ^ (k + 1) * x *
        Research.iteratedLogProduct k x) ≤
      ((Research.coeffGoodDenominators N).card : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_left htrans hK
    have h2 := mul_le_mul_of_nonneg_left hsumInd hcN
    have h3 := hrec
    dsimp [cN, x] at h1 h2 h3 ⊢
    calc
      K * ((N : ℝ) / Real.log N) *
          ((1 - e) ^ (k + 1) * Research.logLogNat y *
            Research.iteratedLogProduct k (Research.logLogNat y)) =
        ((N : ℝ) / Real.log N) *
          (K * ((1 - e) ^ (k + 1) * Research.logLogNat y *
            Research.iteratedLogProduct k (Research.logLogNat y))) := by ring
      _ ≤ ((N : ℝ) / Real.log N) *
          (K * ∑ v ∈ Finset.Ico 2 y,
            Research.highLowerRenewalBenchmark H k v / ((v : ℝ) * (v + 1))) :=
        mul_le_mul_of_nonneg_left h1 hcN
      _ ≤ ((N : ℝ) / Real.log N) *
          ∑ v ∈ Finset.Ico 2 y,
            ((Research.tailCoeffGoodDenominators v).card : ℝ) /
              ((v : ℝ) * (v + 1)) := h2
      _ ≤ ((Research.coeffGoodDenominators N).card : ℝ) := h3
  have hLpos : 0 < L := by
    dsimp [L, z]
    exact Real.log_pos hz1
  have hscale := Research.iteratedLogProduct_scale_lower k he0.le he2
    hLpos hendpoint horbitL
  have hxNonneg : 0 ≤ x := by dsimp [x]; linarith
  have hLNonneg : 0 ≤ L := hLpos.le
  have hPx : 0 ≤ Research.iteratedLogProduct k x := by
    have ht : Research.realTower H k ≤ x :=
      le_trans htowerX (le_of_lt (Real.rpow_lt_self_of_one_lt hx1 (by linarith)))
    have h := Research.cutoffIteratedLogProduct_nonneg hH k x
    rw [Research.cutoffIteratedLogProduct_eq ht] at h
    exact h
  have hPL : 0 ≤ Research.iteratedLogProduct k L := by
    have h := Research.cutoffIteratedLogProduct_nonneg hH k L
    have htL : Research.realTower H k ≤ L := by
      rw [Research.realTower_succ] at htarget
      rw [← Real.log_exp (Research.realTower H k)]
      exact Real.log_le_log (by positivity) htarget
    rw [Research.cutoffIteratedLogProduct_eq htL] at h
    exact h
  have hendpointProd :
      (1 - e) ^ (k + 1) * L * Research.iteratedLogProduct k L ≤
        x * Research.iteratedLogProduct k x := by
    have hmul := mul_le_mul hscale hendpoint
      (mul_nonneg (by linarith) hLNonneg)
      (by nlinarith [hPx])
    rw [pow_succ]
    nlinarith
  have htargetEq : Research.highLowerRenewalBenchmark H (k + 1) N =
      ((N + 1 : ℕ) : ℝ) / Real.log N *
        (L * Research.iteratedLogProduct k L) := by
    rw [Research.highLowerRenewalBenchmark]
    have hclamp : Research.cutoffIteratedLogProduct H (k + 1) z =
        Research.iteratedLogProduct (k + 1) z :=
      Research.cutoffIteratedLogProduct_eq htarget
    rw [hclamp, Research.iteratedLogProduct_succ]
  rw [htargetEq]
  have hone : 0 ≤ 1 - e := by linarith
  have hmeshScaled : (1 - e) * (((N + 1 : ℕ) : ℝ) / Real.log N) ≤ cN := by
    dsimp [cN]
    simpa [mul_div_assoc] using
      div_le_div_of_nonneg_right hmeshFactor hlog.le
  have hfinalScale := mul_le_mul hmeshScaled hendpointProd
    (by positivity) (by positivity)
  have hloss : 0 ≤ (1 - e) ^ (k + 1) := pow_nonneg hone _
  have hfinalLoss := mul_le_mul_of_nonneg_left hfinalScale hloss
  have hfinalK := mul_le_mul_of_nonneg_left hfinalLoss hK
  dsimp [cN, x, z, L] at hrenew hfinalK ⊢
  have hrenew' :
      K * ((1 - e) ^ (k + 1) *
        ((N : ℝ) / Real.log N *
          (Research.logLogNat y *
            Research.iteratedLogProduct k (Research.logLogNat y)))) ≤
        ((Research.coeffGoodDenominators N).card : ℝ) := by
    convert hrenew using 1 <;> ring
  have hchain := le_trans hfinalK hrenew'
  rw [show 2 * k + 3 = (k + 1) + 1 + (k + 1) by omega,
    pow_add, pow_add, pow_one]
  calc
    K * (((1 - e) ^ (k + 1) * (1 - e)) * (1 - e) ^ (k + 1)) *
        (((N + 1 : ℕ) : ℝ) / Real.log N *
          (Real.log (Research.logLogNat (N + 1)) *
            Research.iteratedLogProduct k
              (Real.log (Research.logLogNat (N + 1))))) =
      K * ((1 - e) ^ (k + 1) *
        (((1 - e) * (((N + 1 : ℕ) : ℝ) / Real.log N)) *
          ((1 - e) ^ (k + 1) *
            (Real.log (Research.logLogNat (N + 1)) *
              Research.iteratedLogProduct k
                (Real.log (Research.logLogNat (N + 1))))))) := by ring
    _ ≤ ((Research.coeffGoodDenominators N).card : ℝ) := by
      simpa only [mul_assoc] using hchain


/-- Adaptive-cutoff variant used for the final uniform iteration. -/
theorem adaptive_lower_height_step
    (R : ℕ → ℝ) (N y k : ℕ) (K e : ℝ)
    (hfloorK : Research.realTower 2 k ≤ R k)
    (hfloorNext : Research.realTower 2 (k + 1) ≤ R (k + 1))
    (hcutoffStep : Real.exp (R k) ≤ R (k + 1))
    (hK : 0 ≤ K) (hlog : 0 < Real.log (N : ℝ))
    (hy : 3 ≤ y)
    (hrec : ((N : ℝ) / Real.log N) *
        ∑ v ∈ Finset.Ico 2 y,
          ((Research.tailCoeffGoodDenominators v).card : ℝ) /
            ((v : ℝ) * (v + 1)) ≤
      ((Research.coeffGoodDenominators N).card : ℝ))
    (hind : ∀ v ∈ Finset.Ico 2 y,
      K * Research.adaptiveLowerRenewalBenchmark R k v ≤
        ((Research.tailCoeffGoodDenominators v).card : ℝ))
    (he0 : 0 < e) (he2 : e ≤ 1 / 2)
    (hx1 : 1 < Research.logLogNat y)
    (htlow : Research.logLogNat 2 ≤ Research.logLogNat y ^ (1 - e))
    (htowerX : R k ≤
      Research.logLogNat y ^ (1 - e))
    (hratio : Research.logLogNat y ^ (1 - e) ≤
      e * Research.logLogNat y)
    (horbitX : ∀ j, 1 ≤ j → j ≤ k →
      2 ≤ Research.iteratedLog j (Research.logLogNat y))
    (hz1 : 1 < Research.logLogNat (N + 1))
    (hendpoint : (1 - e) * Real.log (Research.logLogNat (N + 1)) ≤
      Research.logLogNat y)
    (horbitL : ∀ j, 1 ≤ j → j ≤ k →
      2 ≤ Research.iteratedLog j
        (Real.log (Research.logLogNat (N + 1))))
    (htarget : R (k + 1) ≤
      Research.logLogNat (N + 1))
    (hmeshFactor : (1 - e) * (N + 1 : ℕ) ≤ (N : ℝ)) :
    K * (1 - e) ^ (2 * k + 3) *
        Research.adaptiveLowerRenewalBenchmark R (k + 1) N ≤
      ((Research.coeffGoodDenominators N).card : ℝ) := by
  let cN : ℝ := (N : ℝ) / Real.log N
  let x : ℝ := Research.logLogNat y
  let z : ℝ := Research.logLogNat (N + 1)
  let L : ℝ := Real.log z
  have hcN : 0 ≤ cN := by dsimp [cN]; positivity
  have htrans := Research.iteratedLogProduct_le_adaptiveLowerBenchmark_transform
    R k y e hfloorK hy he0 he2 hx1 htlow htowerX hratio horbitX
  have hsumInd : K *
      (∑ v ∈ Finset.Ico 2 y,
        Research.adaptiveLowerRenewalBenchmark R k v / ((v : ℝ) * (v + 1))) ≤
      ∑ v ∈ Finset.Ico 2 y,
        ((Research.tailCoeffGoodDenominators v).card : ℝ) /
          ((v : ℝ) * (v + 1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro v hv
    have hv2 : 2 ≤ v := (Finset.mem_Ico.mp hv).1
    have hden : (0 : ℝ) < (v : ℝ) * (v + 1) := by positivity
    rw [← mul_div_assoc]
    exact (div_le_div_iff_of_pos_right hden).mpr (hind v hv)
  have hrenew : K * cN *
      ((1 - e) ^ (k + 1) * x *
        Research.iteratedLogProduct k x) ≤
      ((Research.coeffGoodDenominators N).card : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_left htrans hK
    have h2 := mul_le_mul_of_nonneg_left hsumInd hcN
    have h3 := hrec
    dsimp [cN, x] at h1 h2 h3 ⊢
    calc
      K * ((N : ℝ) / Real.log N) *
          ((1 - e) ^ (k + 1) * Research.logLogNat y *
            Research.iteratedLogProduct k (Research.logLogNat y)) =
        ((N : ℝ) / Real.log N) *
          (K * ((1 - e) ^ (k + 1) * Research.logLogNat y *
            Research.iteratedLogProduct k (Research.logLogNat y))) := by ring
      _ ≤ ((N : ℝ) / Real.log N) *
          (K * ∑ v ∈ Finset.Ico 2 y,
            Research.adaptiveLowerRenewalBenchmark R k v / ((v : ℝ) * (v + 1))) :=
        mul_le_mul_of_nonneg_left h1 hcN
      _ ≤ ((N : ℝ) / Real.log N) *
          ∑ v ∈ Finset.Ico 2 y,
            ((Research.tailCoeffGoodDenominators v).card : ℝ) /
              ((v : ℝ) * (v + 1)) := h2
      _ ≤ ((Research.coeffGoodDenominators N).card : ℝ) := h3
  have hLpos : 0 < L := by
    dsimp [L, z]
    exact Real.log_pos hz1
  have hscale := Research.iteratedLogProduct_scale_lower k he0.le he2
    hLpos hendpoint horbitL
  have hxNonneg : 0 ≤ x := by dsimp [x]; linarith
  have hLNonneg : 0 ≤ L := hLpos.le
  have hPx : 0 ≤ Research.iteratedLogProduct k x := by
    have ht : R k ≤ x :=
      le_trans htowerX (le_of_lt (Real.rpow_lt_self_of_one_lt hx1 (by linarith)))
    have h := Research.cutoffAtIteratedLogProduct_nonneg hfloorK x
    rw [Research.cutoffAtIteratedLogProduct_eq ht] at h
    exact h
  have hPL : 0 ≤ Research.iteratedLogProduct k L := by
    have h := Research.cutoffAtIteratedLogProduct_nonneg hfloorK L
    have htL : R k ≤ L := by
      rw [← Real.log_exp (R k)]
      exact Real.log_le_log (by positivity)
        (le_trans hcutoffStep htarget)
    rw [Research.cutoffAtIteratedLogProduct_eq htL] at h
    exact h
  have hendpointProd :
      (1 - e) ^ (k + 1) * L * Research.iteratedLogProduct k L ≤
        x * Research.iteratedLogProduct k x := by
    have hmul := mul_le_mul hscale hendpoint
      (mul_nonneg (by linarith) hLNonneg)
      (by nlinarith [hPx])
    rw [pow_succ]
    nlinarith
  have htargetEq : Research.adaptiveLowerRenewalBenchmark R (k + 1) N =
      ((N + 1 : ℕ) : ℝ) / Real.log N *
        (L * Research.iteratedLogProduct k L) := by
    rw [Research.adaptiveLowerRenewalBenchmark]
    have hclamp : Research.cutoffAtIteratedLogProduct (R (k + 1)) (k + 1) z =
        Research.iteratedLogProduct (k + 1) z :=
      Research.cutoffAtIteratedLogProduct_eq htarget
    rw [hclamp, Research.iteratedLogProduct_succ]
  rw [htargetEq]
  have hone : 0 ≤ 1 - e := by linarith
  have hmeshScaled : (1 - e) * (((N + 1 : ℕ) : ℝ) / Real.log N) ≤ cN := by
    dsimp [cN]
    simpa [mul_div_assoc] using
      div_le_div_of_nonneg_right hmeshFactor hlog.le
  have hfinalScale := mul_le_mul hmeshScaled hendpointProd
    (by positivity) (by positivity)
  have hloss : 0 ≤ (1 - e) ^ (k + 1) := pow_nonneg hone _
  have hfinalLoss := mul_le_mul_of_nonneg_left hfinalScale hloss
  have hfinalK := mul_le_mul_of_nonneg_left hfinalLoss hK
  dsimp [cN, x, z, L] at hrenew hfinalK ⊢
  have hrenew' :
      K * ((1 - e) ^ (k + 1) *
        ((N : ℝ) / Real.log N *
          (Research.logLogNat y *
            Research.iteratedLogProduct k (Research.logLogNat y)))) ≤
        ((Research.coeffGoodDenominators N).card : ℝ) := by
    convert hrenew using 1 <;> ring
  have hchain := le_trans hfinalK hrenew'
  rw [show 2 * k + 3 = (k + 1) + 1 + (k + 1) by omega,
    pow_add, pow_add, pow_one]
  calc
    K * (((1 - e) ^ (k + 1) * (1 - e)) * (1 - e) ^ (k + 1)) *
        (((N + 1 : ℕ) : ℝ) / Real.log N *
          (Real.log (Research.logLogNat (N + 1)) *
            Research.iteratedLogProduct k
              (Real.log (Research.logLogNat (N + 1))))) =
      K * ((1 - e) ^ (k + 1) *
        (((1 - e) * (((N + 1 : ℕ) : ℝ) / Real.log N)) *
          ((1 - e) ^ (k + 1) *
            (Real.log (Research.logLogNat (N + 1)) *
              Research.iteratedLogProduct k
                (Real.log (Research.logLogNat (N + 1))))))) := by ring
    _ ≤ ((Research.coeffGoodDenominators N).card : ℝ) := by
      simpa only [mul_assoc] using hchain


/-- Adaptive-cutoff step whose output is the tail-good count. -/
theorem adaptive_tail_lower_height_step
    (R : ℕ → ℝ) (N y k : ℕ) (K e : ℝ)
    (hfloorK : Research.realTower 2 k ≤ R k)
    (hfloorNext : Research.realTower 2 (k + 1) ≤ R (k + 1))
    (hcutoffStep : Real.exp (R k) ≤ R (k + 1))
    (hK : 0 ≤ K) (hlog : 0 < Real.log (N : ℝ))
    (hy : 3 ≤ y)
    (hrec : ((N : ℝ) / Real.log N) *
        ∑ v ∈ Finset.Ico 2 y,
          ((Research.tailCoeffGoodDenominators v).card : ℝ) /
            ((v : ℝ) * (v + 1)) ≤
      ((Research.tailCoeffGoodDenominators N).card : ℝ))
    (hind : ∀ v ∈ Finset.Ico 2 y,
      K * Research.adaptiveLowerRenewalBenchmark R k v ≤
        ((Research.tailCoeffGoodDenominators v).card : ℝ))
    (he0 : 0 < e) (he2 : e ≤ 1 / 2)
    (hx1 : 1 < Research.logLogNat y)
    (htlow : Research.logLogNat 2 ≤ Research.logLogNat y ^ (1 - e))
    (htowerX : R k ≤
      Research.logLogNat y ^ (1 - e))
    (hratio : Research.logLogNat y ^ (1 - e) ≤
      e * Research.logLogNat y)
    (horbitX : ∀ j, 1 ≤ j → j ≤ k →
      2 ≤ Research.iteratedLog j (Research.logLogNat y))
    (hz1 : 1 < Research.logLogNat (N + 1))
    (hendpoint : (1 - e) * Real.log (Research.logLogNat (N + 1)) ≤
      Research.logLogNat y)
    (horbitL : ∀ j, 1 ≤ j → j ≤ k →
      2 ≤ Research.iteratedLog j
        (Real.log (Research.logLogNat (N + 1))))
    (htarget : R (k + 1) ≤
      Research.logLogNat (N + 1))
    (hmeshFactor : (1 - e) * (N + 1 : ℕ) ≤ (N : ℝ)) :
    K * (1 - e) ^ (2 * k + 3) *
        Research.adaptiveLowerRenewalBenchmark R (k + 1) N ≤
      ((Research.tailCoeffGoodDenominators N).card : ℝ) := by
  let cN : ℝ := (N : ℝ) / Real.log N
  let x : ℝ := Research.logLogNat y
  let z : ℝ := Research.logLogNat (N + 1)
  let L : ℝ := Real.log z
  have hcN : 0 ≤ cN := by dsimp [cN]; positivity
  have htrans := Research.iteratedLogProduct_le_adaptiveLowerBenchmark_transform
    R k y e hfloorK hy he0 he2 hx1 htlow htowerX hratio horbitX
  have hsumInd : K *
      (∑ v ∈ Finset.Ico 2 y,
        Research.adaptiveLowerRenewalBenchmark R k v / ((v : ℝ) * (v + 1))) ≤
      ∑ v ∈ Finset.Ico 2 y,
        ((Research.tailCoeffGoodDenominators v).card : ℝ) /
          ((v : ℝ) * (v + 1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro v hv
    have hv2 : 2 ≤ v := (Finset.mem_Ico.mp hv).1
    have hden : (0 : ℝ) < (v : ℝ) * (v + 1) := by positivity
    rw [← mul_div_assoc]
    exact (div_le_div_iff_of_pos_right hden).mpr (hind v hv)
  have hrenew : K * cN *
      ((1 - e) ^ (k + 1) * x *
        Research.iteratedLogProduct k x) ≤
      ((Research.tailCoeffGoodDenominators N).card : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_left htrans hK
    have h2 := mul_le_mul_of_nonneg_left hsumInd hcN
    have h3 := hrec
    dsimp [cN, x] at h1 h2 h3 ⊢
    calc
      K * ((N : ℝ) / Real.log N) *
          ((1 - e) ^ (k + 1) * Research.logLogNat y *
            Research.iteratedLogProduct k (Research.logLogNat y)) =
        ((N : ℝ) / Real.log N) *
          (K * ((1 - e) ^ (k + 1) * Research.logLogNat y *
            Research.iteratedLogProduct k (Research.logLogNat y))) := by ring
      _ ≤ ((N : ℝ) / Real.log N) *
          (K * ∑ v ∈ Finset.Ico 2 y,
            Research.adaptiveLowerRenewalBenchmark R k v / ((v : ℝ) * (v + 1))) :=
        mul_le_mul_of_nonneg_left h1 hcN
      _ ≤ ((N : ℝ) / Real.log N) *
          ∑ v ∈ Finset.Ico 2 y,
            ((Research.tailCoeffGoodDenominators v).card : ℝ) /
              ((v : ℝ) * (v + 1)) := h2
      _ ≤ ((Research.tailCoeffGoodDenominators N).card : ℝ) := h3
  have hLpos : 0 < L := by
    dsimp [L, z]
    exact Real.log_pos hz1
  have hscale := Research.iteratedLogProduct_scale_lower k he0.le he2
    hLpos hendpoint horbitL
  have hxNonneg : 0 ≤ x := by dsimp [x]; linarith
  have hLNonneg : 0 ≤ L := hLpos.le
  have hPx : 0 ≤ Research.iteratedLogProduct k x := by
    have ht : R k ≤ x :=
      le_trans htowerX (le_of_lt (Real.rpow_lt_self_of_one_lt hx1 (by linarith)))
    have h := Research.cutoffAtIteratedLogProduct_nonneg hfloorK x
    rw [Research.cutoffAtIteratedLogProduct_eq ht] at h
    exact h
  have hPL : 0 ≤ Research.iteratedLogProduct k L := by
    have h := Research.cutoffAtIteratedLogProduct_nonneg hfloorK L
    have htL : R k ≤ L := by
      rw [← Real.log_exp (R k)]
      exact Real.log_le_log (by positivity)
        (le_trans hcutoffStep htarget)
    rw [Research.cutoffAtIteratedLogProduct_eq htL] at h
    exact h
  have hendpointProd :
      (1 - e) ^ (k + 1) * L * Research.iteratedLogProduct k L ≤
        x * Research.iteratedLogProduct k x := by
    have hmul := mul_le_mul hscale hendpoint
      (mul_nonneg (by linarith) hLNonneg)
      (by nlinarith [hPx])
    rw [pow_succ]
    nlinarith
  have htargetEq : Research.adaptiveLowerRenewalBenchmark R (k + 1) N =
      ((N + 1 : ℕ) : ℝ) / Real.log N *
        (L * Research.iteratedLogProduct k L) := by
    rw [Research.adaptiveLowerRenewalBenchmark]
    have hclamp : Research.cutoffAtIteratedLogProduct (R (k + 1)) (k + 1) z =
        Research.iteratedLogProduct (k + 1) z :=
      Research.cutoffAtIteratedLogProduct_eq htarget
    rw [hclamp, Research.iteratedLogProduct_succ]
  rw [htargetEq]
  have hone : 0 ≤ 1 - e := by linarith
  have hmeshScaled : (1 - e) * (((N + 1 : ℕ) : ℝ) / Real.log N) ≤ cN := by
    dsimp [cN]
    simpa [mul_div_assoc] using
      div_le_div_of_nonneg_right hmeshFactor hlog.le
  have hfinalScale := mul_le_mul hmeshScaled hendpointProd
    (by positivity) (by positivity)
  have hloss : 0 ≤ (1 - e) ^ (k + 1) := pow_nonneg hone _
  have hfinalLoss := mul_le_mul_of_nonneg_left hfinalScale hloss
  have hfinalK := mul_le_mul_of_nonneg_left hfinalLoss hK
  dsimp [cN, x, z, L] at hrenew hfinalK ⊢
  have hrenew' :
      K * ((1 - e) ^ (k + 1) *
        ((N : ℝ) / Real.log N *
          (Research.logLogNat y *
            Research.iteratedLogProduct k (Research.logLogNat y)))) ≤
        ((Research.tailCoeffGoodDenominators N).card : ℝ) := by
    convert hrenew using 1 <;> ring
  have hchain := le_trans hfinalK hrenew'
  rw [show 2 * k + 3 = (k + 1) + 1 + (k + 1) by omega,
    pow_add, pow_add, pow_one]
  calc
    K * (((1 - e) ^ (k + 1) * (1 - e)) * (1 - e) ^ (k + 1)) *
        (((N + 1 : ℕ) : ℝ) / Real.log N *
          (Real.log (Research.logLogNat (N + 1)) *
            Research.iteratedLogProduct k
              (Real.log (Research.logLogNat (N + 1))))) =
      K * ((1 - e) ^ (k + 1) *
        (((1 - e) * (((N + 1 : ℕ) : ℝ) / Real.log N)) *
          ((1 - e) ^ (k + 1) *
            (Real.log (Research.logLogNat (N + 1)) *
              Research.iteratedLogProduct k
                (Real.log (Research.logLogNat (N + 1))))))) := by ring
    _ ≤ ((Research.tailCoeffGoodDenominators N).card : ℝ) := by
      simpa only [mul_assoc] using hchain

end ResearchPNT
