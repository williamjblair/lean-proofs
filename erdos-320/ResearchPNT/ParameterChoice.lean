import ResearchPNT.Combined

/-! # Natural parameter choices for the renewal induction -/

open Filter Asymptotics

namespace ResearchPNT

/-- We use the base-three natural logarithm so that the quotient range lies
below the natural logarithm without an asymptotic constant loss. -/
def chosenY (N : ℕ) : ℕ := Nat.log 3 N

/-- Relative denominator loss used in the uniform prime-bin kernel. -/
noncomputable def chosenDelta (N : ℕ) : ℝ :=
  4 * Research.logLogNat N / Real.log (N : ℝ)

/-- The natural logarithm of three is strictly larger than one. -/
theorem one_lt_log_three : (1 : ℝ) < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)]
  exact Real.exp_one_lt_three

/-- The base-three natural logarithm is no larger than the natural logarithm. -/
theorem chosenY_le_log (N : ℕ) (hN : 1 ≤ N) :
    (chosenY N : ℝ) ≤ Real.log (N : ℝ) := by
  have hnat := Real.natLog_le_logb N 3
  have hlogN : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hN)
  have hdiv : Real.log (N : ℝ) / Real.log 3 ≤ Real.log (N : ℝ) :=
    div_le_self hlogN one_lt_log_three.le
  exact le_trans hnat hdiv

/-- The base-three natural logarithm is also bounded below by a fixed
multiple of the natural logarithm (up to the harmless floor). -/
theorem log_le_two_log_three_mul_chosenY (N : ℕ)
    (hy : 1 ≤ chosenY N) :
    Real.log (N : ℝ) ≤ 2 * Real.log 3 * (chosenY N : ℝ) := by
  have hfloor : ⌊Real.logb 3 (N : ℝ)⌋₊ = chosenY N := by
    simpa [chosenY] using Real.natFloor_logb_natCast 3 N
  have hlt : Real.logb 3 (N : ℝ) < (chosenY N : ℝ) + 1 := by
    calc
      Real.logb 3 (N : ℝ) <
          ((⌊Real.logb 3 (N : ℝ)⌋₊.succ : ℕ) : ℝ) :=
        Nat.lt_succ_floor (Real.logb 3 (N : ℝ))
      _ = (chosenY N : ℝ) + 1 := by
        simp [hfloor]
  have hlog3 : 0 < Real.log 3 := lt_trans zero_lt_one one_lt_log_three
  rw [Real.logb] at hlt
  have hmul := (div_lt_iff₀ hlog3).mp hlt
  have hsucc : (chosenY N : ℝ) + 1 ≤ 2 * (chosenY N : ℝ) := by
    exact_mod_cast (by omega : chosenY N + 1 ≤ 2 * chosenY N)
  have hmul2 := mul_le_mul_of_nonneg_right hsucc hlog3.le
  calc
    Real.log (N : ℝ) ≤ ((chosenY N : ℝ) + 1) * Real.log 3 := hmul.le
    _ ≤ (2 * (chosenY N : ℝ)) * Real.log 3 := hmul2
    _ = 2 * Real.log 3 * (chosenY N : ℝ) := by ring

/-- Consequently the chosen quotient cutoff has the required `N/log N`
upper scale. -/
theorem cast_div_chosenY_le (N : ℕ) (hy : 1 ≤ chosenY N)
    (hell : 0 < Real.log (N : ℝ)) :
    ((N / chosenY N : ℕ) : ℝ) ≤
      2 * Real.log 3 * (N : ℝ) / Real.log (N : ℝ) := by
  have hyPos : (0 : ℝ) < chosenY N := by positivity
  have hNnonneg : (0 : ℝ) ≤ N := by positivity
  have hlower := log_le_two_log_three_mul_chosenY N hy
  calc
    ((N / chosenY N : ℕ) : ℝ) ≤ (N : ℝ) / chosenY N := Nat.cast_div_le
    _ ≤ 2 * Real.log 3 * (N : ℝ) / Real.log (N : ℝ) := by
      rw [div_le_div_iff₀ hyPos hell]
      nlinarith

/-- The endpoint double logarithm for `chosenY` lies below the next logarithm
of the ambient double logarithm. -/
theorem logLog_chosenY_le (N : ℕ) (hy2 : 2 ≤ chosenY N) :
    Research.logLogNat (chosenY N) ≤
      Real.log (Research.logLogNat N) := by
  have hN : 1 ≤ N := by
    by_contra h
    interval_cases N <;> norm_num [chosenY] at hy2
  have hyPos : (0 : ℝ) < chosenY N := by positivity
  have hyLogPos : 0 < Real.log (chosenY N : ℝ) :=
    Real.log_pos (by exact_mod_cast hy2)
  have hlogNPos : 0 < Real.log (N : ℝ) := by
    have hNne : N ≠ 0 := by
      intro h
      subst N
      norm_num [chosenY] at hy2
    have hpow : 3 ^ 2 ≤ 3 ^ chosenY N :=
      Nat.pow_le_pow_right (by omega) hy2
    have hself : 3 ^ chosenY N ≤ N := by
      simpa [chosenY] using Nat.pow_log_le_self 3 hNne
    have hN3 : 3 ≤ N := by omega
    exact Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hyLe : (chosenY N : ℝ) ≤ Real.log (N : ℝ) := chosenY_le_log N hN
  have hfirst : Real.log (chosenY N : ℝ) ≤
      Real.log (Real.log (N : ℝ)) :=
    Real.log_le_log hyPos hyLe
  exact Real.log_le_log hyLogPos hfirst

/-- The chosen relative loss is nonnegative. -/
theorem chosenDelta_nonneg (N : ℕ)
    (hz : 0 ≤ Research.logLogNat N) (hlog : 0 < Real.log (N : ℝ)) :
    0 ≤ chosenDelta N := by
  rw [chosenDelta]
  positivity

/-- Once `4 log₂ N ≤ log N`, the chosen loss is at most one. -/
theorem chosenDelta_le_one (N : ℕ)
    (hlog : 0 < Real.log (N : ℝ))
    (hsmall : 4 * Research.logLogNat N ≤ Real.log (N : ℝ)) :
    chosenDelta N ≤ 1 := by
  rw [chosenDelta]
  exact (div_le_one hlog).mpr hsmall

/-- The explicit denominator hypotheses required by F-015 hold uniformly for
all quotient indices below `chosenY`. -/
theorem chosen_denominator_bounds (N m : ℕ)
    (hm : m ∈ Finset.Ico 1 (chosenY N))
    (hlog : 0 < Real.log (N : ℝ))
    (hz2 : Real.log 2 ≤ Research.logLogNat N)
    (hsmall : 4 * Research.logLogNat N ≤ Real.log (N : ℝ)) :
    Real.log (N : ℝ) ≤
        (1 + chosenDelta N) * binLogLower N m ∧
      Real.log (N : ℝ) ≤ 2 * binLogLower N m := by
  let ell : ℝ := Real.log (N : ℝ)
  let z : ℝ := Research.logLogNat N
  let a : ℝ := Real.log (m + 1 : ℕ) + Real.log 2
  let δ : ℝ := chosenDelta N
  have hmBounds := Finset.mem_Ico.mp hm
  have hsucc : m + 1 ≤ chosenY N := Nat.succ_le_iff.mpr hmBounds.2
  have hyLe : (chosenY N : ℝ) ≤ ell :=
    chosenY_le_log N (by
      have hyPos : 0 < chosenY N := by omega
      exact Nat.one_le_iff_ne_zero.mpr (by
        intro hN
        subst N
        norm_num [chosenY] at hyPos))
  have hsuccPos : (0 : ℝ) < (m + 1 : ℕ) := by positivity
  have hlogSucc : Real.log (m + 1 : ℕ) ≤ z := by
    have hsell : ((m + 1 : ℕ) : ℝ) ≤ ell :=
      le_trans (by exact_mod_cast hsucc) hyLe
    have := Real.log_le_log hsuccPos hsell
    simpa [z, Research.logLogNat, ell] using this
  have ha : a ≤ 2 * z := by
    dsimp [a, z]
    linarith
  have hzNonneg : 0 ≤ z := le_trans (Real.log_nonneg (by norm_num)) hz2
  have hδNonneg : 0 ≤ δ := by
    exact chosenDelta_nonneg N hzNonneg hlog
  have hδLe : δ ≤ 1 := chosenDelta_le_one N hlog hsmall
  have hδeq : δ * ell = 4 * z := by
    dsimp [δ, chosenDelta, ell, z]
    field_simp [hlog.ne']
  have haNonneg : 0 ≤ a := by
    dsimp [a]
    exact add_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ m + 1 by omega)))
      (Real.log_nonneg (by norm_num))
  have hhalf : ell ≤ 2 * (ell - a) := by nlinarith
  have hscale : ell ≤ (1 + δ) * (ell - a) := by
    have hmul : (1 + δ) * a ≤ 4 * z := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hδLe) (sub_nonneg.mpr ha)]
    nlinarith
  have hL : binLogLower N m = ell - a := by
    dsimp [binLogLower, ell, a]
    ring
  rw [hL]
  exact ⟨hscale, hhalf⟩

/-- The double logarithm is eventually at most one quarter of the first
logarithm, exactly the growth condition used by `chosen_denominator_bounds`. -/
theorem eventually_four_logLogNat_le_log :
    ∀ᶠ N : ℕ in atTop,
      4 * Research.logLogNat N ≤ Real.log (N : ℝ) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hw : Tendsto Research.logLogNat atTop atTop := by
    exact Real.tendsto_log_atTop.comp hlog
  have hreal : (fun x : ℝ => Real.log (Real.log x)) =o[atTop]
      (fun x : ℝ => Real.log x) := by
    simpa [Function.comp_def] using
      Real.isLittleO_log_id_atTop.comp_tendsto Real.tendsto_log_atTop
  have hnat : Research.logLogNat =o[atTop]
      (fun N : ℕ => Real.log (N : ℝ)) := by
    change (fun N : ℕ => Real.log (Real.log (N : ℝ))) =o[atTop]
      (fun N : ℕ => Real.log (N : ℝ))
    exact hreal.comp_tendsto (tendsto_natCast_atTop_atTop (R := ℝ))
  have hb := hnat.bound (by norm_num : (0 : ℝ) < 1 / 4)
  filter_upwards [hb, hlog.eventually (eventually_ge_atTop 0),
    hw.eventually (eventually_ge_atTop 0)] with N hbound hln hwN
  rw [Real.norm_eq_abs, abs_of_nonneg hwN,
    Real.norm_eq_abs, abs_of_nonneg hln] at hbound
  norm_num at hbound ⊢
  linarith

/-- The base-three quotient range is eventually much smaller than the natural
square root. -/
theorem eventually_two_chosenY_le_sqrt :
    ∀ᶠ N : ℕ in atTop, 2 * chosenY N ≤ N.sqrt := by
  have hNpos : ∀ᶠ N : ℕ in atTop, 1 ≤ N := eventually_ge_atTop 1
  have hsqrtReal :
      (fun x : ℝ => Real.log x) =o[atTop] (fun x : ℝ => Real.sqrt x) := by
    simpa [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (r := (1 / 2 : ℝ)) (by norm_num))
  have hsqrtNat : (fun N : ℕ => Real.log (N : ℝ)) =o[atTop]
      (fun N : ℕ => Real.sqrt (N : ℝ)) :=
    hsqrtReal.comp_tendsto (tendsto_natCast_atTop_atTop (R := ℝ))
  have hb := hsqrtNat.bound (by norm_num : (0 : ℝ) < 1 / 8)
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hNpos, hb,
    hlog.eventually (eventually_ge_atTop 0)] with N hN hbound hln
  rw [Real.norm_eq_abs, abs_of_nonneg hln,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] at hbound
  have hylog := chosenY_le_log N hN
  have hySqrt : (8 : ℝ) * chosenY N ≤ Real.sqrt (N : ℝ) := by
    norm_num at hbound
    nlinarith
  have hsqrtLt := Real.real_sqrt_lt_nat_sqrt_succ (a := N)
  have hnat : 8 * chosenY N < N.sqrt + 1 := by
    exact_mod_cast (lt_of_le_of_lt hySqrt hsqrtLt)
  omega

/-- Deterministic consequences of making the quotient range at most half
of the integer square root. -/
theorem chosenY_structural_bounds (N : ℕ)
    (hy2 : 2 ≤ chosenY N) (hsmall : 2 * chosenY N ≤ N.sqrt) :
    N.sqrt + 1 ≤ N / chosenY N ∧
      N ≤ (N / chosenY N) * (N / chosenY N) := by
  let s := N.sqrt
  let y := chosenY N
  have hyPos : 0 < y := by dsimp [y]; omega
  have hs2 : 2 ≤ s := by dsimp [s, y] at *; omega
  have hsy : (s + 1) * y ≤ N := by
    calc
      (s + 1) * y ≤ (2 * s) * y :=
        Nat.mul_le_mul_right y (by omega)
      _ = s * (2 * y) := by ring
      _ ≤ s * s := Nat.mul_le_mul_left s hsmall
      _ ≤ N := Nat.sqrt_le N
  have hsQ : s + 1 ≤ N / y :=
    (Nat.le_div_iff_mul_le hyPos).mpr hsy
  refine ⟨hsQ, ?_⟩
  exact le_of_lt (lt_of_lt_of_le (Nat.lt_succ_sqrt N)
    (Nat.mul_le_mul hsQ hsQ))

/-- A coarse bound, uniform in each fixed low quotient index. -/
theorem uniformBinMajorant_le_low_constant
    (C δ : ℝ) (N m : ℕ) (hC : 0 ≤ C) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hN : 1 ≤ N) (hm : 1 ≤ m) (hlog1 : 1 ≤ Real.log (N : ℝ)) :
    uniformBinMajorant C δ N m ≤
      (4 + 16 * C) * (N : ℝ) / Real.log (N : ℝ) := by
  have hlog : 0 < Real.log (N : ℝ) := lt_of_lt_of_le zero_lt_one hlog1
  have henv := uniformBinMajorant_le_envelope C δ N m hC hm hlog
  have hden : (1 : ℝ) ≤ (m : ℝ) * (m + 1) := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ m)
      (by positivity : (0 : ℝ) ≤ (m : ℝ) + 1)]
  have hdiv : (N : ℝ) / ((m : ℝ) * (m + 1)) ≤ (N : ℝ) :=
    div_le_self (by positivity) hden
  have hbracket : (N : ℝ) / ((m : ℝ) * (m + 1)) + 1 ≤
      2 * (N : ℝ) := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hfirst : (1 + δ) *
        ((N : ℝ) / ((m : ℝ) * (m + 1)) + 1) /
          Real.log (N : ℝ) ≤
      4 * (N : ℝ) / Real.log (N : ℝ) := by
    rw [div_le_div_iff_of_pos_right hlog]
    nlinarith [mul_nonneg (sub_nonneg.mpr hδ1) (sub_nonneg.mpr hbracket)]
  have hcube : Real.log (N : ℝ) ≤ Real.log (N : ℝ) ^ 3 := by
    nlinarith [sq_nonneg (Real.log (N : ℝ) - 1)]
  have hpnt : 16 * C * (N : ℝ) / Real.log (N : ℝ) ^ 3 ≤
      16 * C * (N : ℝ) / Real.log (N : ℝ) :=
    div_le_div_of_nonneg_left (by positivity) hlog hcube
  calc
    uniformBinMajorant C δ N m ≤ renewalKernelEnvelope C δ N m := henv
    _ ≤ 4 * (N : ℝ) / Real.log (N : ℝ) +
        16 * C * (N : ℝ) / Real.log (N : ℝ) := by
      rw [renewalKernelEnvelope]
      exact add_le_add hfirst hpnt
    _ = (4 + 16 * C) * (N : ℝ) / Real.log (N : ℝ) := by ring

/-- Fixed coefficient controlling the smooth and low-index contribution. -/
noncomputable def lowContributionConstant (C : ℝ) (M : ℕ) : ℝ :=
  (2 + 2 * (Real.log 4 + 4) * Real.log 3 + 2 * (Real.log 4 + 4)) +
    (4 + 16 * C) * (∑ m ∈ Finset.Ico 1 M, Research.logS m)

/-- Deterministic low-contribution estimate under elementary large-`N`
conditions. -/
theorem lowContribution_le_constant (C : ℝ) (N M : ℕ)
    (hC : 0 ≤ C) (hN : 1 ≤ N) (hy : 1 ≤ chosenY N)
    (hlog1 : 1 ≤ Real.log (N : ℝ))
    (hfour : 4 * Research.logLogNat N ≤ Real.log (N : ℝ))
    (hsq : Real.log (N : ℝ) ^ 2 ≤ (N : ℝ))
    (hsqrt : Real.log (N : ℝ) ≤ Real.sqrt (N : ℝ)) :
    renewalBaseError N (chosenY N) +
        ∑ m ∈ Finset.Ico 1 M,
          uniformBinMajorant C (chosenDelta N) N m * Research.logS m ≤
      lowContributionConstant C M *
        ((N : ℝ) / Real.log (N : ℝ)) := by
  let ell : ℝ := Real.log (N : ℝ)
  let T : ℝ := (N : ℝ) / ell
  have hell : 0 < ell := lt_of_lt_of_le zero_lt_one hlog1
  have hNR : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hT : 0 ≤ T := (div_pos hNR hell).le
  have hellT : ell ≤ T := by
    rw [le_div_iff₀ hell]
    simpa [pow_two, ell] using hsq
  have hlog2ell : Real.log 2 ≤ ell := by
    have hlog2one := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hlog2one
    exact le_trans hlog2one hlog1
  have hQ : ((N / chosenY N : ℕ) : ℝ) ≤ 2 * Real.log 3 * T := by
    convert cast_div_chosenY_le N hy hell using 1 <;>
      dsimp [T, ell] <;> ring
  have hsqrtT : Real.sqrt (N : ℝ) ≤ T := by
    rw [le_div_iff₀ hell]
    calc
      Real.sqrt (N : ℝ) * ell ≤ Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) :=
        mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg _)
      _ = (N : ℝ) := by
        simpa [pow_two] using Real.sq_sqrt (show (0 : ℝ) ≤ N by positivity)
  have hnatSqrtT : ((N.sqrt : ℕ) : ℝ) ≤ T :=
    le_trans Real.nat_sqrt_le_real_sqrt hsqrtT
  have ha : 0 ≤ Real.log 4 + 4 := by positivity
  have hbase : renewalBaseError N (chosenY N) ≤
      (2 + 2 * (Real.log 4 + 4) * Real.log 3 +
        2 * (Real.log 4 + 4)) * T := by
    rw [renewalBaseError]
    have hfirst : Real.log 2 + ell ≤ 2 * T := by linarith
    have hqmul := mul_le_mul_of_nonneg_left hQ ha
    have hsmul := mul_le_mul_of_nonneg_left hnatSqrtT (by positivity :
      (0 : ℝ) ≤ 2 * (Real.log 4 + 4))
    nlinarith
  have hz0 : 0 ≤ Research.logLogNat N := by
    dsimp [Research.logLogNat, ell]
    exact Real.log_nonneg hlog1
  have hδ0 := chosenDelta_nonneg N hz0 hell
  have hδ1 : chosenDelta N ≤ 1 :=
    chosenDelta_le_one N hell hfour
  have hlowTerms :
      ∑ m ∈ Finset.Ico 1 M,
          uniformBinMajorant C (chosenDelta N) N m * Research.logS m ≤
        (4 + 16 * C) * T *
          (∑ m ∈ Finset.Ico 1 M, Research.logS m) := by
    calc
      ∑ m ∈ Finset.Ico 1 M,
          uniformBinMajorant C (chosenDelta N) N m * Research.logS m ≤
        ∑ m ∈ Finset.Ico 1 M,
          ((4 + 16 * C) * T) * Research.logS m := by
            apply Finset.sum_le_sum
            intro m hm
            have hm1 : 1 ≤ m := (Finset.mem_Ico.mp hm).1
            apply mul_le_mul_of_nonneg_right _ (logS_nonneg m)
            calc
              uniformBinMajorant C (chosenDelta N) N m ≤
                  (4 + 16 * C) * (N : ℝ) / Real.log (N : ℝ) :=
                uniformBinMajorant_le_low_constant C (chosenDelta N) N m
                  hC hδ0 hδ1 hN hm1 hlog1
              _ = (4 + 16 * C) * T := by
                dsimp [T, ell]
                ring
      _ = (4 + 16 * C) * T *
          (∑ m ∈ Finset.Ico 1 M, Research.logS m) := by
            rw [Finset.mul_sum]
  rw [lowContributionConstant]
  nlinarith

/-- Reserve allocated to the smooth and fixed low-index terms. -/
noncomputable def chosenReserve (M N : ℕ) : ℝ :=
  (N : ℝ) / Real.log (N : ℝ) * Research.logLogNat M / 4

/-- Global induction constant selected after the fixed cutoff. -/
noncomputable def chosenK (C : ℝ) (M : ℕ) : ℝ :=
  max 1 (4 * lowContributionConstant C M / Research.logLogNat M)

/-- The selected induction constant is positive and large enough to turn the
`N/log N` low bound into the reserve from F-023. -/
theorem lowConstant_mul_le_chosenK_reserve
    (C : ℝ) (M N k : ℕ) (hC : 0 ≤ C) (hM : 3 ≤ M)
    (hN : 0 < N) (hell : 0 < Real.log (N : ℝ)) :
    lowContributionConstant C M * ((N : ℝ) / Real.log (N : ℝ)) ≤
      chosenK C M * Research.renewalProduct k
        (Real.log (Research.logLogNat N)) * chosenReserve M N := by
  have hwPos : 0 < Research.logLogNat M := by
    have hlog3 : 1 < Real.log (M : ℝ) :=
      lt_of_lt_of_le one_lt_log_three
        (Real.log_le_log (by norm_num) (by exact_mod_cast hM))
    exact Real.log_pos hlog3
  have hH : 0 ≤ lowContributionConstant C M := by
    rw [lowContributionConstant]
    have hsum : 0 ≤ ∑ m ∈ Finset.Ico 1 M, Research.logS m :=
      Finset.sum_nonneg (fun m _ => logS_nonneg m)
    have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    positivity
  have hK : 0 ≤ chosenK C M := le_trans (by norm_num) (le_max_left _ _)
  have hKlarge : 4 * lowContributionConstant C M ≤
      chosenK C M * Research.logLogNat M := by
    have := le_max_right (1 : ℝ)
      (4 * lowContributionConstant C M / Research.logLogNat M)
    rw [chosenK]
    rw [div_le_iff₀ hwPos] at this
    exact this
  have hP : 1 ≤ Research.renewalProduct k
      (Real.log (Research.logLogNat N)) :=
    Research.one_le_renewalProduct k _
  have hT : 0 ≤ (N : ℝ) / Real.log (N : ℝ) := by positivity
  rw [chosenReserve]
  have hbase := mul_le_mul_of_nonneg_right hKlarge hT
  have hfirst : lowContributionConstant C M *
      ((N : ℝ) / Real.log (N : ℝ)) ≤
      chosenK C M * Research.logLogNat M *
        ((N : ℝ) / Real.log (N : ℝ)) / 4 := by
    nlinarith
  have hKP : chosenK C M ≤ chosenK C M *
      Research.renewalProduct k (Real.log (Research.logLogNat N)) := by
    nlinarith [mul_nonneg hK (sub_nonneg.mpr hP)]
  have hfac : 0 ≤ ((N : ℝ) / Real.log (N : ℝ)) *
      Research.logLogNat M / 4 := by positivity
  have hsecond := mul_le_mul_of_nonneg_right hKP hfac
  change lowContributionConstant C M * ((N : ℝ) / Real.log (N : ℝ)) ≤
    chosenK C M * Research.renewalProduct k
      (Real.log (Research.logLogNat N)) *
        ((N : ℝ) / Real.log (N : ℝ) * Research.logLogNat M / 4)
  calc
    lowContributionConstant C M * ((N : ℝ) / Real.log (N : ℝ)) ≤
        chosenK C M * Research.logLogNat M *
          ((N : ℝ) / Real.log (N : ℝ)) / 4 := hfirst
    _ ≤ chosenK C M *
        Research.renewalProduct k (Real.log (Research.logLogNat N)) *
          ((N : ℝ) / Real.log (N : ℝ) * Research.logLogNat M / 4) := by
      nlinarith
    _ = _ := by ring

/-- The elementary large-`N` conditions used by the fixed low-index bound
hold eventually. -/
theorem eventually_low_contribution_conditions :
    ∀ᶠ N : ℕ in atTop,
      1 ≤ Real.log (N : ℝ) ∧
      Real.log (N : ℝ) ^ 2 ≤ (N : ℝ) ∧
      Real.log (N : ℝ) ≤ Real.sqrt (N : ℝ) := by
  have hpow : (fun N : ℕ => Real.log (N : ℝ) ^ 2) =o[atTop]
      (fun N : ℕ => (N : ℝ)) :=
    Real.isLittleO_pow_log_id_atTop.comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hsqrtReal : Real.log =o[atTop] (fun x : ℝ => Real.sqrt x) := by
    simpa [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (r := (1 / 2 : ℝ)) (by norm_num))
  have hsqrt : (fun N : ℕ => Real.log (N : ℝ)) =o[atTop]
      (fun N : ℕ => Real.sqrt (N : ℝ)) :=
    hsqrtReal.comp_tendsto (tendsto_natCast_atTop_atTop (R := ℝ))
  have hpowB := hpow.bound (by norm_num : (0 : ℝ) < 1)
  have hsqrtB := hsqrt.bound (by norm_num : (0 : ℝ) < 1)
  have hlogTend : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hpowB, hsqrtB,
    hlogTend.eventually (eventually_ge_atTop 1)] with N hp hs hlog1
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
    Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ N)] at hp
  rw [Real.norm_eq_abs, abs_of_nonneg (le_trans (by norm_num) hlog1),
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] at hs
  norm_num at hp hs
  exact ⟨hlog1, hp, hs⟩

/-- The smooth and all fixed low quotient indices are eventually bounded by
one explicit multiple of `N/log N`. -/
theorem eventually_lowContribution_le_constant (C : ℝ) (M : ℕ)
    (hC : 0 ≤ C) :
    ∀ᶠ N : ℕ in atTop,
      renewalBaseError N (chosenY N) +
          ∑ m ∈ Finset.Ico 1 M,
            uniformBinMajorant C (chosenDelta N) N m * Research.logS m ≤
        lowContributionConstant C M *
          ((N : ℝ) / Real.log (N : ℝ)) := by
  filter_upwards [eventually_ge_atTop (9 : ℕ),
    eventually_four_logLogNat_le_log,
    eventually_low_contribution_conditions] with N hN9 hfour hc
  have hN : 1 ≤ N := by omega
  have hy2 : 2 ≤ chosenY N := by
    have hlogMon := Nat.log_monotone (show 9 ≤ N by omega) (b := 3)
    norm_num [chosenY] at hlogMon ⊢
    exact hlogMon
  exact lowContribution_le_constant C N M hC hN (le_trans (by omega) hy2)
    hc.1 hfour hc.2.1 hc.2.2

/-- With the selected global constant, the smooth and fixed low-index part
fits inside the F-020 reserve, uniformly in logarithmic height. -/
theorem eventually_lowContribution_le_reserve
    (C : ℝ) (M : ℕ) (hC : 0 ≤ C) (hM : 3 ≤ M) :
    ∀ᶠ N : ℕ in atTop, ∀ k : ℕ,
      renewalBaseError N (chosenY N) +
          ∑ m ∈ Finset.Ico 1 M,
            uniformBinMajorant C (chosenDelta N) N m * Research.logS m ≤
        chosenK C M * Research.renewalProduct k
          (Real.log (Research.logLogNat N)) * chosenReserve M N := by
  filter_upwards [eventually_lowContribution_le_constant C M hC,
    eventually_ge_atTop (9 : ℕ)] with N hlow hN9
  intro k
  have hNpos : 0 < N := by omega
  have hell : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  exact le_trans hlow
    (lowConstant_mul_le_chosenK_reserve C M N k hC hM hNpos hell)

/-- A normalized four-error test implying the scalar reserve budget in F-020.
The hypotheses are deliberately separated so each can be discharged by a
standard limit. -/
theorem scalar_reserve_of_normalized_bounds
    (C δ : ℝ) (N M y : ℕ)
    (hNpos : 0 < N) (hell : 0 < Real.log (N : ℝ))
    (hell1 : 0 < Real.log (N + 1 : ℕ))
    (hlogM : 0 < Real.log (M : ℝ))
    (hδ : 0 ≤ δ) (hw : 0 ≤ Research.logLogNat M)
    (hδL : δ * Real.log (Research.logLogNat N) ≤
      Research.logLogNat M / 8)
    (hfinite : (1 + δ) * (y : ℝ) ^ 2 /
        ((N : ℝ) * Real.log M) ≤ Research.logLogNat M / 8)
    (hpnt : 16 * C * (y : ℝ) ^ 2 /
        (Real.log (N : ℝ) ^ 2 * Real.log M) ≤
          Research.logLogNat M / 8)
    (hright : Real.log (Research.logLogNat N) -
        Research.logLogNat M / 8 ≤
      Real.log (N : ℝ) / Real.log (N + 1 : ℕ) *
        Real.log (Research.logLogNat N)) :
    renewalPrincipal δ N *
          (Real.log (Research.logLogNat N) - Research.logLogNat M) +
        renewalError C δ N * ((y : ℝ) ^ 2 / Real.log M) +
        chosenReserve M N ≤
      (N : ℝ) / Real.log (N + 1 : ℕ) *
        Real.log (Research.logLogNat N) := by
  let ell : ℝ := Real.log (N : ℝ)
  let ell1 : ℝ := Real.log (N + 1 : ℕ)
  let L : ℝ := Real.log (Research.logLogNat N)
  let w : ℝ := Research.logLogNat M
  let Y : ℝ := y
  let F : ℝ := ell / N
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hF : 0 < F := div_pos hell hNR
  have hell0 : ell ≠ 0 := hell.ne'
  have hell10 : ell1 ≠ 0 := hell1.ne'
  have hN0 : (N : ℝ) ≠ 0 := hNR.ne'
  have hlogM0 : Real.log (M : ℝ) ≠ 0 := hlogM.ne'
  have hleft : F * (renewalPrincipal δ N * (L - w) +
        renewalError C δ N * (Y ^ 2 / Real.log M) +
        chosenReserve M N) =
      (1 + δ) * (L - w) +
        (1 + δ) * Y ^ 2 / ((N : ℝ) * Real.log M) +
        16 * C * Y ^ 2 / (ell ^ 2 * Real.log M) + w / 4 := by
    dsimp [F, ell, L, w, Y, renewalPrincipal, renewalError, chosenReserve]
    field_simp [hN0, hell0, hlogM0]
    ring
  have hrightEq : F * ((N : ℝ) / ell1 * L) = ell / ell1 * L := by
    dsimp [F]
    field_simp [hN0, hell10]
  apply (mul_le_mul_iff_of_pos_left hF).mp
  rw [hleft, hrightEq]
  have hδw : 0 ≤ δ * w := mul_nonneg hδ hw
  dsimp [L, w, Y, ell, ell1] at hδL hfinite hpnt hright ⊢
  nlinarith

/-- A fixed low-index cutoff can be chosen large enough to absorb any
fixed PNT error constant. -/
theorem exists_renewal_cutoff (C : ℝ) :
    ∃ M : ℕ, 3 ≤ M ∧
      128 * C ≤ Real.log (M : ℝ) * Research.logLogNat M := by
  have hlog : Tendsto (fun M : ℕ => Real.log (M : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hw : Tendsto Research.logLogNat atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  have hprod : Tendsto (fun M : ℕ =>
      Real.log (M : ℝ) * Research.logLogNat M) atTop atTop :=
    hlog.atTop_mul_atTop₀ hw
  have hlarge := hprod.eventually (eventually_ge_atTop (128 * C))
  have hM3 : ∀ᶠ M : ℕ in atTop, 3 ≤ M := eventually_ge_atTop 3
  exact (hlarge.and hM3).exists.imp (fun M h => ⟨h.2, h.1⟩)

/-- The cutoff condition is exactly what is needed for the normalized PNT
error in the scalar budget. -/
theorem normalized_pnt_error_le (C : ℝ) (M N : ℕ)
    (hC : 0 ≤ C) (hM : 3 ≤ M)
    (hcut : 128 * C ≤ Real.log (M : ℝ) * Research.logLogNat M)
    (hN : 1 ≤ N) (hell : 0 < Real.log (N : ℝ)) :
    16 * C * (chosenY N : ℝ) ^ 2 /
        (Real.log (N : ℝ) ^ 2 * Real.log M) ≤
      Research.logLogNat M / 8 := by
  have hlogM : 0 < Real.log (M : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  have hyLe := chosenY_le_log N hN
  have hyNonneg : (0 : ℝ) ≤ chosenY N := by positivity
  have hsq : (chosenY N : ℝ) ^ 2 ≤ Real.log (N : ℝ) ^ 2 :=
    (sq_le_sq₀ hyNonneg hell.le).mpr hyLe
  have hw : 0 ≤ Research.logLogNat M := by
    have hlog3 : 1 < Real.log (M : ℝ) :=
      lt_of_lt_of_le one_lt_log_three
        (Real.log_le_log (by norm_num) (by exact_mod_cast hM))
    exact (Real.log_pos hlog3).le
  have hratio : (chosenY N : ℝ) ^ 2 / Real.log (N : ℝ) ^ 2 ≤ 1 := by
    rw [div_le_one (sq_pos_of_pos hell)]
    exact hsq
  have hcut' : 16 * C / Real.log M ≤ Research.logLogNat M / 8 := by
    rw [div_le_iff₀ hlogM]
    nlinarith
  calc
    16 * C * (chosenY N : ℝ) ^ 2 /
        (Real.log (N : ℝ) ^ 2 * Real.log M) =
      (16 * C / Real.log M) *
        ((chosenY N : ℝ) ^ 2 / Real.log (N : ℝ) ^ 2) := by ring
    _ ≤ (16 * C / Real.log M) * 1 := by
      apply mul_le_mul_of_nonneg_left hratio
      positivity
    _ ≤ Research.logLogNat M / 8 := by simpa using hcut'

/-- One logarithmic mesh increment is at most `1/N`. -/
theorem log_nat_succ_sub_le_inv (N : ℕ) (hN : 1 ≤ N) :
    Real.log (N + 1 : ℕ) - Real.log (N : ℝ) ≤ 1 / (N : ℝ) := by
  have hNpos : (0 : ℝ) < N := by positivity
  have hspos : (0 : ℝ) < (N + 1 : ℕ) := by positivity
  calc
    Real.log (N + 1 : ℕ) - Real.log (N : ℝ) =
        Real.log (((N + 1 : ℕ) : ℝ) / N) := by
      rw [Real.log_div hspos.ne' hNpos.ne']
    _ ≤ (((N + 1 : ℕ) : ℝ) / N) - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hspos hNpos)
    _ = 1 / (N : ℝ) := by
      field_simp
      norm_num

/-- The small change from `log N` to `log(N+1)` eventually costs less than
one eighth of the fixed renewal saving. -/
theorem eventually_right_normalized_bound (M : ℕ) (hM : 3 ≤ M) :
    ∀ᶠ N : ℕ in atTop,
      Real.log (Research.logLogNat N) - Research.logLogNat M / 8 ≤
        Real.log (N : ℝ) / Real.log (N + 1 : ℕ) *
          Real.log (Research.logLogNat N) := by
  have hwPos : 0 < Research.logLogNat M := by
    have hlog3 : 1 < Real.log (M : ℝ) :=
      lt_of_lt_of_le one_lt_log_three
        (Real.log_le_log (by norm_num) (by exact_mod_cast hM))
    exact Real.log_pos hlog3
  have hinv : Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hinvSmall : ∀ᶠ N : ℕ in atTop,
      1 / (N : ℝ) < Research.logLogNat M / 8 :=
    hinv.eventually_lt_const (by positivity)
  have hlogTend : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hzTend : Tendsto Research.logLogNat atTop atTop :=
    Real.tendsto_log_atTop.comp hlogTend
  filter_upwards [hinvSmall, eventually_ge_atTop (1 : ℕ),
    hlogTend.eventually (eventually_ge_atTop 1),
    hzTend.eventually (eventually_ge_atTop 1)] with N hinvN hN hell1 hz1
  let ell : ℝ := Real.log (N : ℝ)
  let ell1 : ℝ := Real.log (N + 1 : ℕ)
  let z : ℝ := Research.logLogNat N
  let L : ℝ := Real.log z
  have hellPos : 0 < ell := lt_of_lt_of_le zero_lt_one hell1
  have hell1Pos : 0 < ell1 := by
    exact Real.log_pos (by exact_mod_cast (show 1 < N + 1 by omega))
  have hellLe : ell ≤ ell1 :=
    Real.log_le_log (by positivity) (by exact_mod_cast (Nat.le_succ N))
  have hLleZ : L ≤ z := by
    have h := Real.log_le_sub_one_of_pos (lt_of_lt_of_le zero_lt_one hz1)
    linarith
  have hzLeEll : z ≤ ell := by
    have h := Real.log_le_sub_one_of_pos hellPos
    dsimp [z, Research.logLogNat, ell]
    linarith
  have hLle : L ≤ ell1 := le_trans hLleZ (le_trans hzLeEll hellLe)
  have hd : ell1 - ell ≤ 1 / (N : ℝ) := by
    exact log_nat_succ_sub_le_inv N hN
  have hd0 : 0 ≤ ell1 - ell := sub_nonneg.mpr hellLe
  have hfrac : L / ell1 ≤ 1 := (div_le_one hell1Pos).mpr hLle
  have hloss : (ell1 - ell) / ell1 * L ≤ ell1 - ell := by
    calc
      (ell1 - ell) / ell1 * L = (ell1 - ell) * (L / ell1) := by ring
      _ ≤ (ell1 - ell) * 1 := mul_le_mul_of_nonneg_left hfrac hd0
      _ = ell1 - ell := by ring
  have hid : L - ell / ell1 * L = (ell1 - ell) / ell1 * L := by
    field_simp [hell1Pos.ne']
  dsimp [L, z, ell, ell1] at hid ⊢
  nlinarith

/-- The relative denominator loss times the next logarithm tends to zero. -/
theorem eventually_chosenDelta_mul_log_logLog_le (M : ℕ) (hM : 3 ≤ M) :
    ∀ᶠ N : ℕ in atTop,
      chosenDelta N * Real.log (Research.logLogNat N) ≤
        Research.logLogNat M / 8 := by
  have hwPos : 0 < Research.logLogNat M := by
    have hlog3 : 1 < Real.log (M : ℝ) :=
      lt_of_lt_of_le one_lt_log_three
        (Real.log_le_log (by norm_num) (by exact_mod_cast hM))
    exact Real.log_pos hlog3
  have hlogTend : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hreal : (fun x : ℝ => Real.log x ^ 2) =o[atTop] (fun x : ℝ => x) :=
    Real.isLittleO_pow_log_id_atTop
  have hnat : (fun N : ℕ => Research.logLogNat N ^ 2) =o[atTop]
      (fun N : ℕ => Real.log (N : ℝ)) := by
    change (fun N : ℕ => Real.log (Real.log (N : ℝ)) ^ 2) =o[atTop]
      (fun N : ℕ => Real.log (N : ℝ))
    exact hreal.comp_tendsto hlogTend
  have hb := hnat.bound (show (0 : ℝ) < Research.logLogNat M / 32 by positivity)
  have hzTend : Tendsto Research.logLogNat atTop atTop :=
    Real.tendsto_log_atTop.comp hlogTend
  filter_upwards [hb,
    hlogTend.eventually (eventually_gt_atTop 0),
    hzTend.eventually (eventually_ge_atTop 1)] with N hbound hell hz1
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
    Real.norm_eq_abs, abs_of_nonneg hell.le] at hbound
  have hLle : Real.log (Research.logLogNat N) ≤ Research.logLogNat N := by
    have h := Real.log_le_sub_one_of_pos (lt_of_lt_of_le zero_lt_one hz1)
    linarith
  rw [chosenDelta]
  rw [div_mul_eq_mul_div, div_le_iff₀ hell]
  have hz0 : 0 ≤ Research.logLogNat N := le_trans (by norm_num) hz1
  have hmul : 4 * Research.logLogNat N *
      Real.log (Research.logLogNat N) ≤
      4 * Research.logLogNat N * Research.logLogNat N :=
    mul_le_mul_of_nonneg_left hLle
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hz0)
  nlinarith

/-- The finite-cardinality part of the normalized scalar error tends to
zero for every fixed cutoff. -/
theorem eventually_normalized_finite_error (M : ℕ) (hM : 3 ≤ M) :
    ∀ᶠ N : ℕ in atTop,
      (1 + chosenDelta N) * (chosenY N : ℝ) ^ 2 /
          ((N : ℝ) * Real.log M) ≤ Research.logLogNat M / 8 := by
  have hlogM : 0 < Real.log (M : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  have hwPos : 0 < Research.logLogNat M := by
    have hlog3 : 1 < Real.log (M : ℝ) :=
      lt_of_lt_of_le one_lt_log_three
        (Real.log_le_log (by norm_num) (by exact_mod_cast hM))
    exact Real.log_pos hlog3
  let c : ℝ := Research.logLogNat M * Real.log M / 16
  have hc : 0 < c := by dsimp [c]; positivity
  have hpNat : (fun N : ℕ => Real.log (N : ℝ) ^ 2) =o[atTop]
      (fun N : ℕ => (N : ℝ)) := by
    exact Real.isLittleO_pow_log_id_atTop.comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hb := hpNat.bound hc
  have hlogTend : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hwTend : Tendsto Research.logLogNat atTop atTop :=
    Real.tendsto_log_atTop.comp hlogTend
  filter_upwards [hb, eventually_ge_atTop (1 : ℕ),
    eventually_four_logLogNat_le_log,
    hlogTend.eventually (eventually_gt_atTop 0),
    hwTend.eventually (eventually_ge_atTop 0)] with N hpow hN hfour hell hz
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
    Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ N)] at hpow
  have hδ0 := chosenDelta_nonneg N hz hell
  have hδ1 := chosenDelta_le_one N hell hfour
  have hyLe := chosenY_le_log N hN
  have hysq : (chosenY N : ℝ) ^ 2 ≤ Real.log (N : ℝ) ^ 2 :=
    (sq_le_sq₀ (by positivity) hell.le).mpr hyLe
  have hprod : (1 + chosenDelta N) * (chosenY N : ℝ) ^ 2 ≤
      2 * Real.log (N : ℝ) ^ 2 :=
    mul_le_mul (by linarith) hysq (sq_nonneg _) (by positivity)
  rw [div_le_iff₀ (mul_pos (by exact_mod_cast hN) hlogM)]
  dsimp [c] at hpow
  nlinarith

/-- All size and PNT-threshold hypotheses needed by the base-three recurrence
hold eventually. -/
theorem eventually_chosen_recurrence_parameters (X : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      1 ≤ N ∧ 2 ≤ chosenY N ∧
      N ≤ (N / chosenY N) * (N / chosenY N) ∧
      X ≤ ((N / chosenY N : ℕ) : ℝ) ∧
      Real.log 2 ≤ Research.logLogNat N ∧
      4 * Research.logLogNat N ≤ Real.log (N : ℝ) := by
  obtain ⟨B, hXB⟩ := exists_nat_ge X
  have hN : ∀ᶠ N : ℕ in atTop, max 9 (B ^ 2) ≤ N :=
    eventually_ge_atTop (max 9 (B ^ 2))
  have hzTend : Tendsto Research.logLogNat atTop atTop := by
    exact Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hz : ∀ᶠ N : ℕ in atTop,
      Real.log 2 ≤ Research.logLogNat N :=
    hzTend.eventually (eventually_ge_atTop (Real.log 2))
  filter_upwards [hN, hz, eventually_four_logLogNat_le_log,
    eventually_two_chosenY_le_sqrt] with N hNB hzN hfour hsqrt
  have hN1 : 1 ≤ N := by omega
  have hy2 : 2 ≤ chosenY N := by
    have hlogMon := Nat.log_monotone (show 9 ≤ N by omega) (b := 3)
    norm_num [chosenY] at hlogMon ⊢
    exact hlogMon
  have hstruct := chosenY_structural_bounds N hy2 hsqrt
  have hBsqrt : B ≤ N.sqrt := (Nat.le_sqrt').mpr (by omega)
  have hXQ : X ≤ ((N / chosenY N : ℕ) : ℝ) :=
    le_trans hXB (by exact_mod_cast (le_trans hBsqrt (le_trans (Nat.le_succ _) hstruct.1)))
  exact ⟨hN1, hy2, hstruct.2, hXQ, hzN, hfour⟩

/-- For a cutoff satisfying the single fixed PNT inequality, the complete
scalar reserve budget required by F-020 holds eventually. -/
theorem eventually_scalar_reserve_budget (C : ℝ) (M : ℕ)
    (hC : 0 ≤ C) (hM : 3 ≤ M)
    (hcut : 128 * C ≤ Real.log (M : ℝ) * Research.logLogNat M) :
    ∀ᶠ N : ℕ in atTop,
      renewalPrincipal (chosenDelta N) N *
          (Real.log (Research.logLogNat N) - Research.logLogNat M) +
        renewalError C (chosenDelta N) N *
          ((chosenY N : ℝ) ^ 2 / Real.log M) +
        chosenReserve M N ≤
      (N : ℝ) / Real.log (N + 1 : ℕ) *
        Real.log (Research.logLogNat N) := by
  have hparams := eventually_chosen_recurrence_parameters (0 : ℝ)
  filter_upwards [hparams,
    eventually_chosenDelta_mul_log_logLog_le M hM,
    eventually_normalized_finite_error M hM,
    eventually_right_normalized_bound M hM] with N hp hδL hfinite hright
  rcases hp with ⟨hN, hy2, _hNQ, _hQ, hz2, hfour⟩
  have hNpos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one hN
  have hNne : N ≠ 0 := Nat.ne_of_gt hNpos
  have hpow : 3 ^ 2 ≤ 3 ^ chosenY N :=
    Nat.pow_le_pow_right (by omega) hy2
  have hself : 3 ^ chosenY N ≤ N := by
    simpa [chosenY] using Nat.pow_log_le_self 3 hNne
  have hN9 : 9 ≤ N := by norm_num at hpow; omega
  have hell : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hell1 : 0 < Real.log (N + 1 : ℕ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N + 1 by omega))
  have hlogM : 0 < Real.log (M : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  have hz0 : 0 ≤ Research.logLogNat N :=
    le_trans (Real.log_nonneg (by norm_num)) hz2
  have hδ0 : 0 ≤ chosenDelta N := chosenDelta_nonneg N hz0 hell
  have hw0 : 0 ≤ Research.logLogNat M := by
    have hlog3 : 1 < Real.log (M : ℝ) :=
      lt_of_lt_of_le one_lt_log_three
        (Real.log_le_log (by norm_num) (by exact_mod_cast hM))
    exact (Real.log_pos hlog3).le
  have hpnt := normalized_pnt_error_le C M N hC hM hcut hN hell
  exact scalar_reserve_of_normalized_bounds C (chosenDelta N) N M (chosenY N)
    hNpos hell hell1 hlogM hδ0 hw0 hδL hfinite hpnt hright

/-- Elementary global entropy bound used only to cover the finite base
range of the final induction. -/
theorem logS_le_nat_mul_log_two (N : ℕ) :
    Research.logS N ≤ (N : ℝ) * Real.log 2 := by
  change Real.log (Research.S N : ℝ) ≤ _
  have hSpos : (0 : ℝ) < Research.S N := by
    exact_mod_cast Research.S_pos N
  have hcast : (Research.S N : ℝ) ≤ (((2 : ℕ) ^ N : ℕ) : ℝ) := by
    exact_mod_cast Research.S_le_two_pow N
  have hlog := Real.log_le_log hSpos hcast
  norm_num only [Nat.cast_pow, Nat.cast_ofNat] at hlog
  rw [Real.log_pow] at hlog
  exact hlog

/-- A single explicit constant covers every member of a finite initial
interval, at every benchmark height. -/
theorem logS_le_discrete_of_lt
    (K : ℝ) (N N₀ k : ℕ) (hN : 2 ≤ N) (hNN₀ : N < N₀)
    (hK : Real.log 2 * Real.log (N₀ : ℝ) ≤ K) :
    Research.logS N ≤ K * Research.discreteRenewalBenchmark k N := by
  have hlogN : 0 < Real.log (N + 1 : ℕ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N + 1 by omega))
  have hN₀pos : (0 : ℝ) < N₀ := by
    exact_mod_cast (show 0 < N₀ by omega)
  have hlogLe : Real.log (N + 1 : ℕ) ≤ Real.log (N₀ : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast (show N + 1 ≤ N₀ by omega))
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hK' : Real.log 2 * Real.log (N + 1 : ℕ) ≤ K :=
    le_trans (mul_le_mul_of_nonneg_left hlogLe hlog2) hK
  have hcont : (N : ℝ) * Real.log 2 ≤
      K * ((N : ℝ) / Real.log (N + 1 : ℕ)) := by
    have hkdiv : Real.log 2 ≤ K / Real.log (N + 1 : ℕ) := by
      rw [le_div_iff₀ hlogN]
      simpa [mul_comm] using hK'
    calc
      (N : ℝ) * Real.log 2 ≤ (N : ℝ) *
          (K / Real.log (N + 1 : ℕ)) :=
        mul_le_mul_of_nonneg_left hkdiv (by positivity)
      _ = K * ((N : ℝ) / Real.log (N + 1 : ℕ)) := by ring
  have hbench := Research.div_log_succ_mul_renewalProduct_le_discrete k N hN
  have hP : 1 ≤ Research.renewalProduct k (Research.logLogNat N) :=
    Research.one_le_renewalProduct k _
  have hKnonneg : 0 ≤ K := le_trans
    (mul_nonneg hlog2 (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N₀ by omega)))) hK
  have hscale : K * ((N : ℝ) / Real.log (N + 1 : ℕ)) ≤
      K * ((N : ℝ) / Real.log (N + 1 : ℕ) *
        Research.renewalProduct k (Research.logLogNat N)) := by
    apply mul_le_mul_of_nonneg_left _ hKnonneg
    have hq : 0 ≤ (N : ℝ) / Real.log (N + 1 : ℕ) := by positivity
    nlinarith [mul_nonneg hq (sub_nonneg.mpr hP)]
  exact le_trans (logS_le_nat_mul_log_two N)
    (le_trans hcont (le_trans hscale
      (mul_le_mul_of_nonneg_left hbench hKnonneg)))

/-- All preceding estimates combine into a uniform, eventual induction step
which decreases logarithmic height by one. The step remains valid after
increasing the global induction constant. -/
theorem exists_eventual_height_step_mono :
    ∃ C : ℝ, ∃ M : ℕ, ∃ K₀ : ℝ,
      0 < C ∧ 3 ≤ M ∧ 0 < K₀ ∧
      ∀ᶠ N : ℕ in atTop, ∀ K : ℝ, K₀ ≤ K → ∀ k : ℕ,
        (∀ m ∈ Finset.Ico M (chosenY N),
          Research.logS m ≤ K * Research.discreteRenewalBenchmark k m) →
        Research.logS N ≤ K * Research.discreteRenewalBenchmark (k + 1) N := by
  obtain ⟨C, hC, X, hX, hrec⟩ := exists_logS_le_uniform_binSum
  obtain ⟨M, hM, hcut⟩ := exists_renewal_cutoff C
  let K := chosenK C M
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨C, M, K, hC, hM, hK, ?_⟩
  have hparams := eventually_chosen_recurrence_parameters X
  have hscalar := eventually_scalar_reserve_budget C M hC.le hM hcut
  have hlow := eventually_lowContribution_le_reserve C M hC.le hM
  have hMle : ∀ᶠ N : ℕ in atTop, M ≤ chosenY N := by
    filter_upwards [eventually_ge_atTop (3 ^ M)] with N hNpow
    have hNne : N ≠ 0 := by
      have : 0 < 3 ^ M := pow_pos (by omega) M
      omega
    exact (Nat.le_log_iff_pow_le (by omega : 1 < 3) hNne).mpr hNpow
  have hzTend : Tendsto Research.logLogNat atTop atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hzLarge : ∀ᶠ N : ℕ in atTop,
      Research.renewalThreshold < Research.logLogNat N :=
    hzTend.eventually (eventually_gt_atTop Research.renewalThreshold)
  filter_upwards [hparams, hscalar, hlow, hMle, hzLarge] with
      N hp hscalarN hlowN hMy hzLargeN
  intro K' hKK k hInd
  have hK' : 0 < K' := lt_of_lt_of_le hK hKK
  rcases hp with ⟨hN, hy2, hNQ, hQX, hz2, hfour⟩
  have hN2 : 2 ≤ N := by
    have hNne : N ≠ 0 := by omega
    have hpow : 3 ^ 2 ≤ 3 ^ chosenY N :=
      Nat.pow_le_pow_right (by omega) hy2
    have hself : 3 ^ chosenY N ≤ N := by
      simpa [chosenY] using Nat.pow_log_le_self 3 hNne
    omega
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hz0 : 0 ≤ Research.logLogNat N :=
    le_trans (Real.log_nonneg (by norm_num)) hz2
  have hδ0 : 0 ≤ chosenDelta N := chosenDelta_nonneg N hz0 hlog
  have hden := fun m hm => chosen_denominator_bounds N m hm hlog hz2 hfour
  have hrecN : Research.logS N ≤ renewalBaseError N (chosenY N) +
      ∑ m ∈ Finset.Ico 1 (chosenY N),
        uniformBinMajorant C (chosenDelta N) N m * Research.logS m := by
    simpa [renewalBaseError] using
      hrec N (chosenY N) (chosenDelta N) hN (by omega) hNQ hQX hδ0 hlog
        (fun m hm => (hden m hm).1) (fun m hm => (hden m hm).2)
  have hD : 0 ≤ chosenReserve M N := by
    rw [chosenReserve]
    have hwM : 0 ≤ Research.logLogNat M := by
      have hlog3M : 1 < Real.log (M : ℝ) :=
        lt_of_lt_of_le one_lt_log_three
          (Real.log_le_log (by norm_num) (by exact_mod_cast hM))
      exact (Real.log_pos hlog3M).le
    positivity
  have hPnonneg : 0 ≤ Research.renewalProduct k
      (Real.log (Research.logLogNat N)) :=
    le_trans (by norm_num) (Research.one_le_renewalProduct k _)
  have hlow' : renewalBaseError N (chosenY N) +
        ∑ m ∈ Finset.Ico 1 M,
          uniformBinMajorant C (chosenDelta N) N m * Research.logS m ≤
      K' * Research.renewalProduct k
        (Real.log (Research.logLogNat N)) * chosenReserve M N := by
    have hKP := mul_le_mul_of_nonneg_right hKK hPnonneg
    exact le_trans (hlowN k) (mul_le_mul_of_nonneg_right hKP hD)
  exact logS_le_next_discreteBenchmark_of_recurrence
    C (chosenDelta N) K' (chosenReserve M N) N k M (chosenY N)
    hC.le hδ0 hK'.le hD hlog hN2 (le_trans (by omega) hM) hMy
    hrecN hInd hzLargeN (logLog_chosenY_le N hy2) hscalarN hlow'

/-- Fixed-constant specialization recorded in F-025. -/
theorem exists_eventual_height_step :
    ∃ C : ℝ, ∃ M : ℕ, ∃ K : ℝ,
      0 < C ∧ 3 ≤ M ∧ 0 < K ∧
      ∀ᶠ N : ℕ in atTop, ∀ k : ℕ,
        (∀ m ∈ Finset.Ico M (chosenY N),
          Research.logS m ≤ K * Research.discreteRenewalBenchmark k m) →
        Research.logS N ≤ K * Research.discreteRenewalBenchmark (k + 1) N := by
  obtain ⟨C, M, K, hC, hM, hK, hstep⟩ := exists_eventual_height_step_mono
  refine ⟨C, M, K, hC, hM, hK, ?_⟩
  filter_upwards [hstep] with N hN
  exact hN K le_rfl

/-- Global upper bound by a fully stabilized discrete renewal benchmark. -/
theorem exists_global_discrete_upper :
    ∃ K : ℝ, 0 < K ∧ ∃ M : ℕ, 3 ≤ M ∧
      ∀ N : ℕ, M ≤ N →
        Research.logS N ≤ K * Research.discreteRenewalBenchmark N N := by
  obtain ⟨C, M, K₀, hC, hM, hK₀, hstep⟩ :=
    exists_eventual_height_step_mono
  obtain ⟨N₀, hstepN₀⟩ := eventually_atTop.mp hstep
  let Nbar := max N₀ (max M 3)
  let K := max K₀ (Real.log 2 * Real.log (Nbar : ℝ))
  have hKK₀ : K₀ ≤ K := le_max_left _ _
  have hK : 0 < K := lt_of_lt_of_le hK₀ hKK₀
  have hKbase : Real.log 2 * Real.log (Nbar : ℝ) ≤ K := le_max_right _ _
  refine ⟨K, hK, M, hM, ?_⟩
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
      intro hMN
      by_cases hbase : N < Nbar
      · exact logS_le_discrete_of_lt K N Nbar N
          (le_trans (by omega) (le_trans hM hMN)) hbase hKbase
      · have hNbar : Nbar ≤ N := by omega
        have hN₀N : N₀ ≤ N := le_trans (le_max_left _ _) hNbar
        have hstepN := hstepN₀ N hN₀N K hKK₀ (N - 1)
        have hNne : N ≠ 0 := by omega
        have hyN : chosenY N < N := by
          exact Nat.log_lt_self 3 hNne
        have hInd : ∀ m ∈ Finset.Ico M (chosenY N),
            Research.logS m ≤
              K * Research.discreteRenewalBenchmark (N - 1) m := by
          intro m hm
          have hmBounds := Finset.mem_Ico.mp hm
          have hmN : m < N := lt_trans hmBounds.2 hyN
          have him := ih m hmN hmBounds.1
          have hm2 : 2 ≤ m := le_trans (by omega) (le_trans hM hmBounds.1)
          have hheight : m ≤ N - 1 := by omega
          have hbench := Research.discreteRenewalBenchmark_mono_height m hm2 hheight
          exact le_trans him (mul_le_mul_of_nonneg_left hbench hK.le)
        have hout := hstepN hInd
        have heq : N - 1 + 1 = N := by omega
        simpa only [heq] using hout

/-- Conventional continuous-scale form of the full-depth upper bound. -/
theorem exists_full_depth_product_upper :
    ∃ K : ℝ, 0 < K ∧ ∃ M : ℕ, 3 ≤ M ∧
      ∀ N : ℕ, M ≤ N →
        Research.logS N ≤ K *
          (((N + 1 : ℕ) : ℝ) / Real.log N *
            Research.renewalProduct N (Research.logLogNat N)) := by
  obtain ⟨K, hK, M, hM, hupper⟩ := exists_global_discrete_upper
  refine ⟨K, hK, M, hM, ?_⟩
  intro N hMN
  have hN2 : 2 ≤ N := le_trans (by omega) (le_trans hM hMN)
  exact le_trans (hupper N hMN)
    (mul_le_mul_of_nonneg_left
      (Research.discreteRenewalBenchmark_le_succ_div_log N N hN2) hK.le)

#print axioms exists_eventual_height_step
#print axioms exists_eventual_height_step_mono
#print axioms exists_global_discrete_upper
#print axioms exists_full_depth_product_upper

end ResearchPNT
