import Research.FourthCrossingFirstMomentGate
import Mathlib.Tactic

open Filter MeasureTheory Set
open scoped BigOperators Topology

namespace Erdos521

noncomputable local instance fourthRelaxedDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- Near-sharp finite Markov conversion.  Once `L ≥ 2500`, mean at most `0.59 L` still leaves at
least one percent of the population below the `0.6 L - 10` crossing threshold. -/
lemma card_le_hundred_card_low_of_sum_le_relaxed {α : Type*} [Fintype α]
    (C : α → ℕ) (L : ℝ) (hL : 2500 ≤ L)
    (hsum : (∑ x : α, (C x : ℝ)) ≤
      (59 : ℝ) / 100 * Fintype.card α * L) :
    Fintype.card α ≤ 100 * Fintype.card {x : α //
      (C x : ℝ) + 10 ≤ (3 : ℝ) / 5 * L} := by
  let G : Finset α := Finset.univ.filter fun x ↦
    (C x : ℝ) + 10 ≤ (3 : ℝ) / 5 * L
  let B : Finset α := Finset.univ \ G
  have hlow (x : α) (hx : x ∈ B) : (149 : ℝ) / 250 * L ≤ (C x : ℝ) := by
    have hxnot : ¬((C x : ℝ) + 10 ≤ (3 : ℝ) / 5 * L) := by
      have hxG : x ∉ G := by simpa [B] using hx
      simpa [G] using hxG
    have hthreshold : (149 : ℝ) / 250 * L + 10 ≤ (3 : ℝ) / 5 * L := by
      nlinarith
    linarith
  have hBsum : (B.card : ℝ) * ((149 : ℝ) / 250 * L) ≤
      ∑ x ∈ B, (C x : ℝ) := by
    calc
      (B.card : ℝ) * ((149 : ℝ) / 250 * L) =
          ∑ x ∈ B, (149 : ℝ) / 250 * L := by simp [mul_comm]
      _ ≤ ∑ x ∈ B, (C x : ℝ) := Finset.sum_le_sum fun x hx ↦ hlow x hx
  have hsubsum : (∑ x ∈ B, (C x : ℝ)) ≤ ∑ x : α, (C x : ℝ) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset)
      (fun _ _ _ ↦ by positivity)
  have hBG : B.card + G.card = Fintype.card α := by
    have h := Finset.card_sdiff_add_card (Finset.univ : Finset α) G
    rw [Finset.union_eq_left.mpr (Finset.subset_univ G)] at h
    simpa [B] using h
  have hcardR : (Fintype.card α : ℝ) ≤ 100 * (G.card : ℝ) := by
    have hLpos : 0 < L := by linarith
    have hBG' : (B.card : ℝ) + (G.card : ℝ) = Fintype.card α := by exact_mod_cast hBG
    nlinarith [hBsum.trans (hsubsum.trans hsum)]
  have hGcard : G.card = Fintype.card {x : α //
      (C x : ℝ) + 10 ≤ (3 : ℝ) / 5 * L} := by
    rw [Fintype.card_subtype]
  rw [← hGcard]
  exact_mod_cast hcardR

/-- Relaxed conditional first-moment gate: the asymptotically maximal usable constant is `0.594`,
and `0.59` suffices after the fixed endpoint cost is absorbed. -/
theorem erdos_521_negative_of_fourthCrossing_firstMoment_relaxed
    (hmean : ∀ᶠ n : ℕ in atTop,
      (∑ p : AxisGoodPath n, (axisFourthCrossingCount p : ℝ)) ≤
        (59 : ℝ) / 100 * Fintype.card (AxisGoodPath n) *
          Real.log (recordDegree n : ℝ)) :
    ¬ Claim := by
  apply erdos_521_negative_of_fourthCrossingRecord_mass
  have hlogNat : ∀ᶠ n : ℕ in atTop, (2500 : ℝ) ≤ Real.log (n : ℝ) := by
    have ht : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    exact ht.eventually (eventually_ge_atTop 2500)
  filter_upwards [hmean, hlogNat, eventually_ge_atTop (3 : ℕ)] with n hn hlogn hn3
  have hnrec : n ≤ recordDegree n := by unfold recordDegree; omega
  have hlogmono : Real.log (n : ℝ) ≤ Real.log (recordDegree n : ℝ) := by
    apply Real.strictMonoOn_log.monotoneOn
    · exact Set.mem_Ioi.mpr (by positivity)
    · apply Set.mem_Ioi.mpr
      have : 0 < recordDegree n := by unfold recordDegree; omega
      exact_mod_cast this
    · exact_mod_cast hnrec
  have hlog : (2500 : ℝ) ≤ Real.log (recordDegree n : ℝ) := hlogn.trans hlogmono
  have hcard := card_le_hundred_card_low_of_sum_le_relaxed
    (α := AxisGoodPath n) axisFourthCrossingCount
    (Real.log (recordDegree n : ℝ)) hlog hn
  rw [coneRecordProbability_eq_axisGood_ratio,
    lowFourthCrossingRecord_measure_eq n hn3]
  change Fintype.card (AxisGoodPath n) ≤
    100 * Fintype.card (LowFourthAxisPath n) at hcard
  have hcardR : (Fintype.card (AxisGoodPath n) : ℝ) ≤
      100 * Fintype.card (LowFourthAxisPath n) := by exact_mod_cast hcard
  calc
    (Fintype.card (AxisGoodPath n) : ℝ) / (4 : ℝ) ^ n ≤
        (100 * Fintype.card (LowFourthAxisPath n) : ℝ) / (4 : ℝ) ^ n := by
      exact div_le_div_of_nonneg_right hcardR (by positivity)
    _ = 100 * ((Fintype.card (LowFourthAxisPath n) : ℝ) / (4 : ℝ) ^ n) := by ring

end Erdos521
