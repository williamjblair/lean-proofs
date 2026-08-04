import ResearchPNT.LowerInduction
import Research.LowerParameters

/-! # Parameter verification for the lower height step -/

open Filter Asymptotics Real

namespace ResearchPNT

/-- Natural base used by `lowerY`. -/
def lowerNaturalBase : ℕ := 65536 ^ 2

/-- The cutoff is within one floor unit of its real logarithm. -/
theorem log_le_two_log_base_mul_lowerY (N : ℕ)
    (hy : 1 ≤ lowerY N) :
    Real.log (N : ℝ) ≤
      2 * Real.log (lowerNaturalBase : ℝ) * (lowerY N : ℝ) := by
  have hfloor : ⌊Real.logb lowerNaturalBase (N : ℝ)⌋₊ = lowerY N := by
    simpa [lowerY, lowerNaturalBase] using
      Real.natFloor_logb_natCast lowerNaturalBase N
  have hlt : Real.logb lowerNaturalBase (N : ℝ) < (lowerY N : ℝ) + 1 := by
    calc
      Real.logb lowerNaturalBase (N : ℝ) <
          ((⌊Real.logb lowerNaturalBase (N : ℝ)⌋₊.succ : ℕ) : ℝ) :=
        Nat.lt_succ_floor _
      _ = (lowerY N : ℝ) + 1 := by simp [hfloor]
  have hlogBase : 0 < Real.log (lowerNaturalBase : ℝ) :=
    Real.log_pos (by norm_num [lowerNaturalBase])
  rw [Real.logb] at hlt
  have hmul := (div_lt_iff₀ hlogBase).mp hlt
  have hsucc : (lowerY N : ℝ) + 1 ≤ 2 * (lowerY N : ℝ) := by
    exact_mod_cast (show lowerY N + 1 ≤ 2 * lowerY N by omega)
  have hmul2 := mul_le_mul_of_nonneg_right hsucc hlogBase.le
  calc
    Real.log (N : ℝ) ≤ ((lowerY N : ℝ) + 1) *
        Real.log (lowerNaturalBase : ℝ) := hmul.le
    _ ≤ (2 * (lowerY N : ℝ)) * Real.log (lowerNaturalBase : ℝ) := hmul2
    _ = _ := by ring

/-- Fixed shift introduced by the base of the natural logarithm cutoff. -/
noncomputable def lowerLogShift : ℝ :=
  Real.log (2 * Real.log (lowerNaturalBase : ℝ))

/-- The shift is nonnegative and very crudely at most 64. -/
theorem lowerLogShift_bounds : 0 ≤ lowerLogShift ∧ lowerLogShift ≤ 64 := by
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    linarith
  have hbaseEq : ((lowerNaturalBase : ℕ) : ℝ) = (2 : ℝ) ^ 32 := by
    norm_num [lowerNaturalBase]
  have hlogBase : Real.log (lowerNaturalBase : ℝ) = 32 * Real.log 2 := by
    rw [hbaseEq, Real.log_pow]
    norm_num
  have harg1 : 1 ≤ 2 * Real.log (lowerNaturalBase : ℝ) := by
    rw [hlogBase]
    have hlog2low : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have h := Real.log_two_gt_d9
      norm_num at h ⊢
      linarith
    linarith
  have harg64 : 2 * Real.log (lowerNaturalBase : ℝ) ≤ 64 := by
    rw [hlogBase]
    linarith
  constructor
  · exact Real.log_nonneg harg1
  · rw [lowerLogShift]
    have hlogle := Real.log_le_sub_one_of_pos
      (lt_of_lt_of_le zero_lt_one harg1)
    linarith

/-- Lower bound for the first logarithm of `lowerY`. -/
theorem log_lowerY_ge_sub_shift (N : ℕ) (hy : 1 ≤ lowerY N)
    (hlogN : 0 < Real.log (N : ℝ)) :
    Research.logLogNat N - lowerLogShift ≤
      Real.log (lowerY N : ℝ) := by
  have hcut := log_le_two_log_base_mul_lowerY N hy
  have hyR : (0 : ℝ) < lowerY N := by positivity
  have hbaseLog : 0 < Real.log (lowerNaturalBase : ℝ) :=
    Real.log_pos (by norm_num [lowerNaturalBase])
  have hprodPos : 0 < 2 * Real.log (lowerNaturalBase : ℝ) * lowerY N := by
    positivity
  have hlog := Real.log_le_log hlogN hcut
  rw [Real.log_mul (by positivity : (2 * Real.log (lowerNaturalBase : ℝ)) ≠ 0)
    (ne_of_gt hyR)] at hlog
  simpa [Research.logLogNat, lowerLogShift, add_comm] using
    (sub_le_iff_le_add.mpr hlog)

/-- A convenient endpoint comparison.  The proof deliberately uses very
coarse constants; the adaptive cutoff has enormous reserve. -/
theorem lowerY_endpoint_comparison (N k : ℕ)
    (hN : 3 ≤ N) (hy : 3 ≤ lowerY N)
    (htarget : Research.adaptiveLowerCutoff (k + 1) ≤
      Research.logLogNat (N + 1)) :
    (1 - Research.lowerEpsilon k) *
        Real.log (Research.logLogNat (N + 1)) ≤
      Research.logLogNat (lowerY N) := by
  let w := Research.logLogNat N
  let z := Research.logLogNat (N + 1)
  let L := Real.log z
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hwShift := log_lowerY_ge_sub_shift N (by omega) hlogN
  have hdelta := Research.logLogNat_sub_le_one_div_mul_log N (by omega)
  have hden : (1 : ℝ) ≤ (N : ℝ) * Real.log N := by
    have hlog3 : 1 < Real.log (N : ℝ) :=
      lt_of_lt_of_le one_lt_log_three
        (Real.log_le_log (by norm_num) (by exact_mod_cast hN))
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    have hmul := mul_le_mul hN1 hlog3.le (by norm_num : (0 : ℝ) ≤ 1)
      (by positivity : (0 : ℝ) ≤ N)
    simpa using hmul
  have hdelta1 : z ≤ w + 1 := by
    dsimp [z, w]
    have : 1 / ((N : ℝ) * Real.log N) ≤ 1 :=
      (div_le_one (by positivity)).mpr hden
    linarith
  have hzBase : Research.lowerAnalysisBase ≤ z :=
    le_trans (Research.base_le_adaptiveLowerCutoff (k + 1)) htarget
  have hbaseBig : (130 : ℝ) ≤ Research.lowerAnalysisBase := by
    rw [Research.lowerAnalysisBase,
      ← Real.exp_log (by norm_num : (0 : ℝ) < 130)]
    apply Real.exp_le_exp.mpr
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 130)
    norm_num at h ⊢
    linarith
  have hz130 : 130 ≤ z := le_trans hbaseBig hzBase
  have hw129 : 129 ≤ w := by linarith
  have hshift := lowerLogShift_bounds
  have hwTwoShift : 2 * lowerLogShift ≤ w := by linarith
  have hw1 : 1 ≤ w := by linarith
  have hlogYhalf : w / 2 ≤ Real.log (lowerY N : ℝ) := by
    dsimp [w] at hwShift hwTwoShift ⊢
    linarith
  have hlogYPos : 0 < Real.log (lowerY N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < lowerY N by omega))
  have hlogWPos : 0 < w := by linarith
  have hxLower : Real.log w - Real.log 2 ≤
      Research.logLogNat (lowerY N) := by
    have h := Real.log_le_log (by positivity : 0 < w / 2) hlogYhalf
    rw [Real.log_div (ne_of_gt hlogWPos) (by norm_num : (2 : ℝ) ≠ 0)] at h
    exact h
  have hz2w : z ≤ 2 * w := by linarith
  have hLUpper : L ≤ Real.log w + Real.log 2 := by
    dsimp [L]
    have h := Real.log_le_log (by positivity : 0 < z) hz2w
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hlogWPos)] at h
    nlinarith
  have hgap : L - 2 ≤ Research.logLogNat (lowerY N) := by
    have hlog2 : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at h
      linarith
    linarith
  have hLcut : Research.adaptiveLowerCutoff k ≤ L := by
    dsimp [L, z]
    rw [← Real.log_exp (Research.adaptiveLowerCutoff k)]
    exact Real.log_le_log (Real.exp_pos _)
      (le_trans (Research.exp_cutoff_le_succ k) htarget)
  have heL : 2 ≤ Research.lowerEpsilon k * L :=
    le_trans (Research.two_le_epsilon_mul_cutoff k)
      (mul_le_mul_of_nonneg_left hLcut (Research.lowerEpsilon_pos k).le)
  dsimp [L] at hgap heL ⊢
  nlinarith

/-- Bundle of deterministic hypotheses consumed by the adaptive one-step
lemma. -/
structure LowerStepConditions (N k : ℕ) : Prop where
  hy : 3 ≤ lowerY N
  hlog : 0 < Real.log (N : ℝ)
  hx1 : 1 < Research.logLogNat (lowerY N)
  htlow : Research.logLogNat 2 ≤
    Research.logLogNat (lowerY N) ^ (1 - Research.lowerEpsilon k)
  htower : Research.adaptiveLowerCutoff k ≤
    Research.logLogNat (lowerY N) ^ (1 - Research.lowerEpsilon k)
  hratio : Research.logLogNat (lowerY N) ^ (1 - Research.lowerEpsilon k) ≤
    Research.lowerEpsilon k * Research.logLogNat (lowerY N)
  horbitX : ∀ j, 1 ≤ j → j ≤ k →
    2 ≤ Research.iteratedLog j (Research.logLogNat (lowerY N))
  hz1 : 1 < Research.logLogNat (N + 1)
  hendpoint : (1 - Research.lowerEpsilon k) *
    Real.log (Research.logLogNat (N + 1)) ≤ Research.logLogNat (lowerY N)
  horbitL : ∀ j, 1 ≤ j → j ≤ k →
    2 ≤ Research.iteratedLog j
      (Real.log (Research.logLogNat (N + 1)))
  hmesh : (1 - Research.lowerEpsilon k) * (N + 1 : ℕ) ≤ (N : ℝ)

/-- The next adaptive cutoff supplies every one-step hypothesis. -/
theorem lowerStepConditions_of_target (N k : ℕ) (hN : 3 ≤ N)
    (hy : 3 ≤ lowerY N)
    (htarget : Research.adaptiveLowerCutoff (k + 1) ≤
      Research.logLogNat (N + 1)) :
    LowerStepConditions N k := by
  let e := Research.lowerEpsilon k
  let x := Research.logLogNat (lowerY N)
  let z := Research.logLogNat (N + 1)
  let L := Real.log z
  have he0 : 0 < e := Research.lowerEpsilon_pos k
  have he2 : e ≤ 1 / 2 := Research.lowerEpsilon_le_half k
  have hendpoint0 := lowerY_endpoint_comparison N k hN hy htarget
  have hendpoint : (1 - e) * L ≤ x := by
    simpa [e, x, z, L] using hendpoint0
  have hLcut : Research.adaptiveLowerCutoff k ≤ L := by
    dsimp [L, z]
    rw [← Real.log_exp (Research.adaptiveLowerCutoff k)]
    exact Real.log_le_log (Real.exp_pos _)
      (le_trans (Research.exp_cutoff_le_succ k) htarget)
  have hx1 : 1 < x := by
    have hRbig : 2 < Research.adaptiveLowerCutoff k :=
      lt_of_lt_of_le Research.two_lt_lowerAnalysisBase
        (Research.base_le_adaptiveLowerCutoff k)
    have hone : 1 / 2 ≤ 1 - e := by linarith
    have hprod : 1 < (1 - e) * L := by
      have : 2 < L := lt_of_lt_of_le hRbig hLcut
      nlinarith
    exact lt_of_lt_of_le hprod hendpoint
  have htower0 := Research.cutoff_le_rpow_of_next_cutoff htarget hendpoint0
  have htower : Research.adaptiveLowerCutoff k ≤ x ^ (1 - e) := by
    simpa [e, x] using htower0
  have htlt : x ^ (1 - e) < x :=
    Real.rpow_lt_self_of_one_lt hx1 (by linarith)
  have hRleX : Research.adaptiveLowerCutoff k ≤ x :=
    le_trans htower (le_of_lt htlt)
  have hratio : x ^ (1 - e) ≤ e * x := by
    exact Research.rpow_one_sub_le_epsilon_mul hRleX
  have hfloorX : Research.realTower 2 k ≤ x :=
    le_trans (Research.tower_two_le_adaptiveLowerCutoff k) hRleX
  have horbitX : ∀ j, 1 ≤ j → j ≤ k →
      2 ≤ Research.iteratedLog j x := by
    intro j hj1 hjk
    exact Research.two_le_iteratedLog_of_tower_le hfloorX j hjk
  have htlow : Research.logLogNat 2 ≤ x ^ (1 - e) := by
    have hll2 : Research.logLogNat 2 ≤ 1 := by
      have hlog2pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
      have hlog2le : Real.log 2 ≤ 1 := by
        have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        norm_num at h
        linarith
      have h := Real.log_le_sub_one_of_pos hlog2pos
      dsimp [Research.logLogNat]
      linarith
    have hR1 : 1 ≤ Research.adaptiveLowerCutoff k :=
      le_trans (by norm_num) (le_trans Research.two_le_lowerAnalysisBase
        (Research.base_le_adaptiveLowerCutoff k))
    exact le_trans hll2 (le_trans hR1 htower)
  have hzBase : Research.lowerAnalysisBase ≤ z :=
    le_trans (Research.base_le_adaptiveLowerCutoff (k + 1)) htarget
  have hz1 : 1 < z :=
    lt_of_lt_of_le (by
      have := Research.two_le_lowerAnalysisBase
      linarith) hzBase
  have hfloorL : Research.realTower 2 k ≤ L :=
    le_trans (Research.tower_two_le_adaptiveLowerCutoff k) hLcut
  have horbitL : ∀ j, 1 ≤ j → j ≤ k → 2 ≤ Research.iteratedLog j L := by
    intro j hj1 hjk
    exact Research.two_le_iteratedLog_of_tower_le hfloorL j hjk
  have hNp1log : z ≤ (N + 1 : ℕ) := by
    have hN1 : 1 < (N + 1 : ℕ) := by omega
    have hlogPos : 0 < Real.log ((N + 1 : ℕ) : ℝ) :=
      Real.log_pos (by exact_mod_cast hN1)
    have h1 := Real.log_le_sub_one_of_pos hlogPos
    have h2 := Real.log_le_sub_one_of_pos
      (by exact_mod_cast (show 0 < N + 1 by omega) : (0 : ℝ) < (N + 1 : ℕ))
    dsimp [z, Research.logLogNat]
    nlinarith
  have hez : 2 ≤ e * z := by
    have hR : Research.adaptiveLowerCutoff k ≤ z :=
      le_trans (le_trans (by
        have hRpos := Research.adaptiveLowerCutoff_pos k
        have h := Real.add_one_le_exp (Research.adaptiveLowerCutoff k)
        linarith) (Research.exp_cutoff_le_succ k)) htarget
    exact le_trans (Research.two_le_epsilon_mul_cutoff k)
      (mul_le_mul_of_nonneg_left hR he0.le)
  have hmesh : (1 - e) * ((N + 1 : ℕ) : ℝ) ≤ N := by
    have : 1 ≤ e * ((N + 1 : ℕ) : ℝ) :=
      le_trans (by norm_num) (le_trans hez
        (mul_le_mul_of_nonneg_left hNp1log he0.le))
    have hcast : (((N + 1 : ℕ) : ℝ)) = (N : ℝ) + 1 := by norm_num
    rw [hcast] at this ⊢
    nlinarith
  refine ⟨hy, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  · simpa [x] using hx1
  · simpa [e, x] using htlow
  · simpa [e, x] using htower
  · simpa [e, x] using hratio
  · simpa [x] using horbitX
  · simpa [z] using hz1
  · simpa [e, x, z, L] using hendpoint
  · simpa [z, L] using horbitL
  · simpa [e] using hmesh

end ResearchPNT
