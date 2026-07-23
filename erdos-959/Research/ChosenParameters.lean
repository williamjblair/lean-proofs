import Research.AsymptoticParameters

noncomputable section
open Filter Asymptotics
namespace Erdos959

/-- Parameter selected as a slowly scaled logarithm of the requested
cardinality. -/
def asymptoticM (n : ℕ) : ℕ :=
  ⌊(parameterScale : ℝ) * Real.log n / 40⌋₊

lemma tendsto_asymptoticM : Tendsto asymptoticM atTop atTop := by
  have htlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hc : (0 : ℝ) < (parameterScale : ℝ) / 40 := by
    exact div_pos (by exact_mod_cast parameterScale_pos) (by norm_num)
  have htscale : Tendsto
      (fun n : ℕ => ((parameterScale : ℝ) / 40) * Real.log n) atTop atTop :=
    htlog.const_mul_atTop hc
  have htfloor := tendsto_nat_floor_atTop.comp htscale
  change Tendsto (fun n : ℕ =>
    ⌊(parameterScale : ℝ) * Real.log n / 40⌋₊) atTop atTop
  convert htfloor using 1
  funext n
  simp only [Function.comp_apply]
  congr 1
  ring

/-- The chosen parameter both fits in every sufficiently large requested
cardinality and has the required logarithmic size. -/
theorem eventually_asymptotic_parameter_properties :
    ∃ N : ℕ, ∀ n ≥ N,
      64 ≤ parameterH (asymptoticM n) ∧
      10 * parameterBlockCount (asymptoticM n) * parameterQ (asymptoticM n) ≤ n ∧
      Real.log n ≤ 2560 * parameterH (asymptoticM n) * Real.log (Real.log n) := by
  obtain ⟨Nden, hden⟩ := eventually_splitPrimes_card_mul_log_lower
  obtain ⟨Ncard, hcard⟩ := eventually_parameterUniverse_card_log_upper
  obtain ⟨Nh, hh⟩ := parameterH_eventually_ge 64
  let M0 := max 2 (max Nden (max Ncard Nh))
  have hmLarge : ∀ᶠ n : ℕ in atTop, M0 ≤ asymptoticM n :=
    tendsto_asymptoticM.eventually (eventually_ge_atTop M0)
  have htlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have htloglog : Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp htlog
  have hxLarge : ∀ᶠ n : ℕ in atTop,
      2 ≤ (parameterScale : ℝ) * Real.log n / 40 := by
    have hc : (0 : ℝ) < (parameterScale : ℝ) / 40 := by
      exact div_pos (by exact_mod_cast parameterScale_pos) (by norm_num)
    have hs := htlog.const_mul_atTop hc
    have he := hs.eventually (eventually_ge_atTop (2 : ℝ))
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using he
  have hloglogLarge : ∀ᶠ n : ℕ in atTop,
      Real.log (parameterScale : ℝ) ≤ Real.log (Real.log n) :=
    htloglog.eventually (eventually_ge_atTop (Real.log (parameterScale : ℝ)))
  have hlog10 : ∀ᶠ n : ℕ in atTop,
      Real.log 10 ≤ Real.log n / 4 := by
    have he := htlog.eventually (eventually_ge_atTop (4 * Real.log 10))
    filter_upwards [he] with n hn
    linarith
  have hn2 : ∀ᶠ n : ℕ in atTop, 2 ≤ n := eventually_ge_atTop 2
  have hall : ∀ᶠ n : ℕ in atTop,
      64 ≤ parameterH (asymptoticM n) ∧
      10 * parameterBlockCount (asymptoticM n) * parameterQ (asymptoticM n) ≤ n ∧
      Real.log n ≤ 2560 * parameterH (asymptoticM n) * Real.log (Real.log n) := by
    filter_upwards [hmLarge, hxLarge, hloglogLarge, hlog10, hn2] with
      n hm0 hx2 hll hten hn
    let m := asymptoticM n
    let x : ℝ := (parameterScale : ℝ) * Real.log n / 40
    have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
    have hxpos : 0 ≤ x := by dsimp [x]; positivity
    have hmUpper : (m : ℝ) ≤ x := by
      exact Nat.floor_le hxpos
    have hxfloor := Nat.lt_floor_add_one x
    have hx2' : 2 ≤ x := by simpa [x] using hx2
    have hmLower : x / 2 ≤ (m : ℝ) := by
      change x < (m : ℝ) + 1 at hxfloor
      nlinarith
    have hmM0 : M0 ≤ m := hm0
    have hm2 : 2 ≤ m := le_trans (le_max_left 2 (max Nden (max Ncard Nh))) hmM0
    have hmDen : Nden ≤ m := by
      exact le_trans (le_trans (le_max_left Nden (max Ncard Nh))
        (le_max_right 2 (max Nden (max Ncard Nh)))) hmM0
    have hmCard : Ncard ≤ m := by
      have : Ncard ≤ max Ncard Nh := le_max_left _ _
      exact le_trans (le_trans (this.trans (le_max_right Nden (max Ncard Nh)))
        (le_max_right 2 (max Nden (max Ncard Nh)))) hmM0
    have hmH : Nh ≤ m := by
      have : Nh ≤ max Ncard Nh := le_max_right _ _
      exact le_trans (le_trans (this.trans (le_max_right Nden (max Ncard Nh)))
        (le_max_right 2 (max Nden (max Ncard Nh)))) hmM0
    have hh64 : 64 ≤ parameterH m := hh m hmH
    have hmSq : Nden ≤ m ^ 2 := hmDen.trans (by nlinarith [Nat.zero_le m])
    have hdens0 := hden (m ^ 2) hmSq
    have hdens : (m : ℝ) ^ 2 / 4 ≤
        ((parameterUniverse m).card : ℝ) * Real.log ((m ^ 2 : ℕ) : ℝ) := by
      simpa [parameterUniverse, Nat.cast_pow] using hdens0
    have hlower := parameterH_lower_of_density hm2 (by omega : 1 ≤ parameterH m) hdens
    have hcardm := hcard m hmCard
    have hupper := parameterH_upper_of_card_log (by omega : 1 ≤ m) hcardm
    have hscalePos : (0 : ℝ) < parameterScale := by exact_mod_cast parameterScale_pos
    have hlogm : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast hm2)
    have hxLe : x ≤ (parameterScale : ℝ) * Real.log n := by
      dsimp [x]
      nlinarith
    have hmLe : (m : ℝ) ≤ (parameterScale : ℝ) * Real.log n := hmUpper.trans hxLe
    have hprodPos : 0 < (parameterScale : ℝ) * Real.log n := mul_pos hscalePos hlogn
    have hlogmono : Real.log (m : ℝ) ≤
        Real.log ((parameterScale : ℝ) * Real.log n) :=
      Real.strictMonoOn_log.monotoneOn
        (show 0 < (m : ℝ) by positivity) hprodPos hmLe
    have hlogprod : Real.log ((parameterScale : ℝ) * Real.log n) =
        Real.log (parameterScale : ℝ) + Real.log (Real.log n) :=
      Real.log_mul (ne_of_gt hscalePos) (ne_of_gt hlogn)
    have hlogmUpper : Real.log (m : ℝ) ≤ 2 * Real.log (Real.log n) := by
      rw [hlogprod] at hlogmono
      linarith
    have hquant : Real.log (n : ℝ) ≤
        2560 * parameterH m * Real.log (Real.log n) := by
      have hmLower' : (parameterScale : ℝ) * Real.log n / 80 ≤ (m : ℝ) := by
        dsimp [x] at hmLower
        nlinarith
      have hcoef : 0 ≤ (16 : ℝ) * parameterScale * parameterH m := by positivity
      have hscaled := mul_le_mul_of_nonneg_left hlogmUpper hcoef
      have hmQuant : (m : ℝ) ≤
          32 * parameterScale * parameterH m * Real.log (Real.log n) := by
        calc
          (m : ℝ) ≤ 16 * parameterScale * parameterH m * Real.log m := hlower
          _ ≤ 32 * parameterScale * parameterH m * Real.log (Real.log n) := by
            nlinarith
      have hchain := hmLower'.trans hmQuant
      nlinarith
    have hfit := parameter_minimum_fits hm2 hn hupper hmUpper hten
    exact ⟨by simpa [m] using hh64,
      by simpa [m] using hfit,
      by simpa [m] using hquant⟩
  exact eventually_atTop.1 hall

end Erdos959
