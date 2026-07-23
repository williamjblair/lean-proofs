import Research.HighThresholdFourthCrossingGate
import Mathlib.Tactic

open Filter MeasureTheory Set
open scoped BigOperators Topology

namespace Erdos521

noncomputable local instance highFirstMomentDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- At logarithmic scale at least `100000`, mean `0.623 L` leaves more than one percent of a finite
population below the `0.63 L-10` crossing threshold. -/
lemma card_le_hundred_highThreshold_of_sum_le {α : Type*} [Fintype α]
    (C : α → ℕ) (L : ℝ) (hL : 100000 ≤ L)
    (hsum : (∑ x : α, (C x : ℝ)) ≤
      (623 : ℝ) / 1000 * Fintype.card α * L) :
    Fintype.card α ≤ 100 * Fintype.card {x : α //
      (C x : ℝ) + 10 ≤ (63 : ℝ) / 100 * L} := by
  let G : Finset α := Finset.univ.filter fun x ↦
    (C x : ℝ) + 10 ≤ (63 : ℝ) / 100 * L
  let B : Finset α := Finset.univ \ G
  have hlow (x : α) (hx : x ∈ B) :
      (6299 : ℝ) / 10000 * L ≤ (C x : ℝ) := by
    have hxnot : ¬((C x : ℝ) + 10 ≤ (63 : ℝ) / 100 * L) := by
      have hxG : x ∉ G := by simpa [B] using hx
      simpa [G] using hxG
    have hthreshold : (6299 : ℝ) / 10000 * L + 10 ≤
        (63 : ℝ) / 100 * L := by nlinarith
    linarith
  have hBsum : (B.card : ℝ) * ((6299 : ℝ) / 10000 * L) ≤
      ∑ x ∈ B, (C x : ℝ) := by
    calc
      (B.card : ℝ) * ((6299 : ℝ) / 10000 * L) =
          ∑ x ∈ B, (6299 : ℝ) / 10000 * L := by simp [mul_comm]
      _ ≤ ∑ x ∈ B, (C x : ℝ) := Finset.sum_le_sum fun x hx ↦ hlow x hx
  have hsubsum : (∑ x ∈ B, (C x : ℝ)) ≤ ∑ x : α, (C x : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset)
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
      (C x : ℝ) + 10 ≤ (63 : ℝ) / 100 * L} := by
    rw [Fintype.card_subtype]
  rw [← hGcard]
  exact_mod_cast hcardR

/-- Improved conditional first-moment gate: `0.623 log(2n-1)` suffices. -/
theorem erdos_521_negative_of_highThreshold_firstMoment
    (hmean : ∀ᶠ n : ℕ in atTop,
      (∑ p : AxisGoodPath n, (axisFourthCrossingCount p : ℝ)) ≤
        (623 : ℝ) / 1000 * Fintype.card (AxisGoodPath n) *
          Real.log (recordDegree n : ℝ)) :
    ¬ Claim := by
  apply erdos_521_negative_of_highThresholdFourthCrossing_mass
  have hlogNat : ∀ᶠ n : ℕ in atTop, (100000 : ℝ) ≤ Real.log (n : ℝ) := by
    have ht : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    exact ht.eventually (eventually_ge_atTop 100000)
  filter_upwards [hmean, hlogNat, eventually_ge_atTop (3 : ℕ)] with n hn hlogn hn3
  have hnrec : n ≤ recordDegree n := by unfold recordDegree; omega
  have hlogmono : Real.log (n : ℝ) ≤ Real.log (recordDegree n : ℝ) := by
    apply Real.strictMonoOn_log.monotoneOn
    · exact Set.mem_Ioi.mpr (by positivity)
    · apply Set.mem_Ioi.mpr
      have : 0 < recordDegree n := by unfold recordDegree; omega
      exact_mod_cast this
    · exact_mod_cast hnrec
  have hlog : (100000 : ℝ) ≤ Real.log (recordDegree n : ℝ) := hlogn.trans hlogmono
  have hcard := card_le_hundred_highThreshold_of_sum_le
    (α := AxisGoodPath n) axisFourthCrossingCount
    (Real.log (recordDegree n : ℝ)) hlog hn
  have hpathsCard : (highThresholdFourthAxisPaths n).card =
      Fintype.card {p : AxisGoodPath n //
        (axisFourthCrossingCount p : ℝ) + 10 ≤
          (63 : ℝ) / 100 * Real.log (recordDegree n : ℝ)} := by
    rw [Fintype.card_subtype]
    rfl
  rw [coneRecordProbability_eq_axisGood_ratio,
    highThresholdFourthCrossingRecord_measure_eq]
  rw [← hpathsCard] at hcard
  have hcardR : (Fintype.card (AxisGoodPath n) : ℝ) ≤
      100 * (highThresholdFourthAxisPaths n).card := by exact_mod_cast hcard
  calc
    (Fintype.card (AxisGoodPath n) : ℝ) / (4 : ℝ) ^ n ≤
        (100 * (highThresholdFourthAxisPaths n).card : ℝ) / (4 : ℝ) ^ n := by
      exact div_le_div_of_nonneg_right hcardR (by positivity)
    _ = 100 * (((highThresholdFourthAxisPaths n).card : ℝ) / (4 : ℝ) ^ n) := by ring

end Erdos521
