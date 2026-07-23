import Research.FourthCrossingMassGate
import Research.ConeCrossingTransfer
import Research.RademacherBallotExact
import Mathlib.Tactic

open Filter MeasureTheory Set
open scoped BigOperators Topology

namespace Erdos521

noncomputable local instance fourthFirstMomentDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- A deliberately slack finite Markov bound.  A mean below `0.39 L`, once `L ≥ 100`, leaves
far more than one percent of the finite population below the `0.6 L - 10` threshold. -/
lemma card_le_hundred_card_low_of_sum_le {α : Type*} [Fintype α]
    (C : α → ℕ) (L : ℝ) (hL : 100 ≤ L)
    (hsum : (∑ x : α, (C x : ℝ)) ≤
      (39 : ℝ) / 100 * Fintype.card α * L) :
    Fintype.card α ≤ 100 * Fintype.card {x : α //
      (C x : ℝ) + 10 ≤ (3 : ℝ) / 5 * L} := by
  let G : Finset α := Finset.univ.filter fun x ↦
    (C x : ℝ) + 10 ≤ (3 : ℝ) / 5 * L
  let B : Finset α := Finset.univ \ G
  have hlow (x : α) (hx : x ∈ B) : L / 2 ≤ (C x : ℝ) := by
    have hxnot : ¬((C x : ℝ) + 10 ≤ (3 : ℝ) / 5 * L) := by
      have hxG : x ∉ G := by simpa [B] using hx
      simpa [G] using hxG
    have hhalf : L / 2 + 10 ≤ (3 : ℝ) / 5 * L := by nlinarith
    linarith
  have hBsum : (B.card : ℝ) * (L / 2) ≤ ∑ x ∈ B, (C x : ℝ) := by
    calc
      (B.card : ℝ) * (L / 2) = ∑ x ∈ B, L / 2 := by
        simp [mul_comm]
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

local instance fourthFirstMomentFairProbability : IsProbabilityMeasure fairCoin := by
  unfold fairCoin
  infer_instance

local instance fourthFirstMomentRademacherProbability :
    IsProbabilityMeasure rademacherMeasure := by
  unfold rademacherMeasure
  infer_instance

/-- Regard a good schedule/sign path as the corresponding unconstrained Boolean axis word. -/
def axisPathWord {n : ℕ} (p : AxisGoodPath n) : AxisWord n :=
  (axisWordDataEquiv n).symm p.1

lemma axisWordBits_axisPathWord {n : ℕ} (p : AxisGoodPath n) :
    axisWordBits (axisPathWord p) = (bitsAxisEquiv n).symm p.1 := by
  simp [axisWordBits, axisWordBitsEquiv, axisPathWord]

/-- Infinite low-to-high coefficient sequence reconstructed from a good axis path. -/
def axisPathCoefficients {n : ℕ} (p : AxisGoodPath n) : ℕ → Bool :=
  axisWordCoefficients (axisPathWord p)

lemma axisPathCoefficients_eq {n : ℕ} (p : AxisGoodPath n) :
    axisPathCoefficients p = extendBits n ((bitsAxisEquiv n).symm p.1) := by
  unfold axisPathCoefficients axisWordCoefficients
  rw [axisWordBits_axisPathWord]

/-- The finite crossing statistic whose first moment remains to be estimated analytically. -/
noncomputable def axisFourthCrossingCount {n : ℕ} (p : AxisGoodPath n) : ℕ :=
  twoSidedFourthCrossingCount (axisPathCoefficients p) n

/-- Good axis paths which pass the final fourth-crossing budget. -/
abbrev LowFourthAxisPath (n : ℕ) := {p : AxisGoodPath n //
  (axisFourthCrossingCount p : ℝ) + 10 ≤
    (3 : ℝ) / 5 * Real.log (recordDegree n : ℝ)}

lemma twoSidedFourthCrossingCount_eq_of_prefix {ω η : ℕ → Bool} {n : ℕ}
    (hn : 3 ≤ n) (h : ∀ i < 2 * n, ω i = η i) :
    twoSidedFourthCrossingCount ω n = twoSidedFourthCrossingCount η n := by
  unfold twoSidedFourthCrossingCount
  congr 1
  · apply fourthIntegratedCrossingCount_eq_of_prefix
    intro i hi
    exact h i (by omega)
  · apply fourthIntegratedCrossingCount_eq_of_prefix
    intro i hi
    unfold oddTwist
    rw [h i (by omega)]

lemma lowFourthCrossingConeRecordEvent_iff_of_prefix {ω η : ℕ → Bool} {n : ℕ}
    (hn : 3 ≤ n) (h : ∀ i < 2 * n, ω i = η i) :
    ω ∈ lowFourthCrossingConeRecordEvent n ↔
      η ∈ lowFourthCrossingConeRecordEvent n := by
  simp only [lowFourthCrossingConeRecordEvent, coneRecordEvent, Set.mem_inter_iff,
    Set.mem_setOf_eq]
  rw [isConeRecord_iff_of_prefix h]
  rw [twoSidedFourthCrossingCount_eq_of_prefix hn h]

/-- The low-crossing record event is exactly the inverse image of its finite prefix image. -/
lemma lowFourthEvent_eq_prefix_preimage (n : ℕ) (hn : 3 ≤ n) :
    lowFourthCrossingConeRecordEvent n =
      (fun (ω : ℕ → Bool) (i : (Finset.range (2 * n) : Finset ℕ)) ↦ ω i) ⁻¹'
        ((fun (ω : ℕ → Bool) (i : (Finset.range (2 * n) : Finset ℕ)) ↦ ω i) ''
          lowFourthCrossingConeRecordEvent n) := by
  let S := Finset.range (2 * n)
  let f : (ℕ → Bool) → (S → Bool) := fun ω i ↦ ω i
  change lowFourthCrossingConeRecordEvent n = f ⁻¹' (f '' lowFourthCrossingConeRecordEvent n)
  ext ω
  constructor
  · exact fun hω ↦ ⟨ω, hω, rfl⟩
  · rintro ⟨η, hη, hηω⟩
    apply (lowFourthCrossingConeRecordEvent_iff_of_prefix (ω := η) (η := ω) hn ?_).mp hη
    intro k hk
    have hkS : k ∈ S := by simpa [S] using hk
    exact congrFun hηω ⟨k, hkS⟩

/-- Prefix assignment associated with a low-crossing good axis path. -/
noncomputable def lowFourthAxisPrefixMap (n : ℕ) :
    LowFourthAxisPath n → ((Finset.range (2 * n) : Finset ℕ) → Bool) :=
  fun p ↦ axisGoodPrefixMap n p.1

lemma lowFourthAxisPrefixMap_injective (n : ℕ) :
    Function.Injective (lowFourthAxisPrefixMap n) := by
  intro p q h
  apply Subtype.ext
  exact axisGoodPrefixMap_injective n h

lemma lowFourthAxisPrefixMap_mem_image {n : ℕ} (p : LowFourthAxisPath n) :
    lowFourthAxisPrefixMap n p ∈
      (fun (ω : ℕ → Bool) (i : (Finset.range (2 * n) : Finset ℕ)) ↦ ω i) ''
        lowFourthCrossingConeRecordEvent n := by
  refine ⟨axisPathCoefficients p.1, ?_, ?_⟩
  · constructor
    · rw [axisPathCoefficients_eq]
      exact (coneRecord_extend_iff_axisGood _).mpr (by simpa using p.1.property)
    · exact p.property
  · funext i
    unfold lowFourthAxisPrefixMap axisGoodPrefixMap bitsToRangePrefix
    rw [axisPathCoefficients_eq]
    exact extendBits_of_lt _ (Finset.mem_range.mp i.property)

lemma lowFourthAxisPrefixMap_surjective_image (n : ℕ) (hn : 3 ≤ n) :
    ∀ y ∈ ((fun (ω : ℕ → Bool) (i : (Finset.range (2 * n) : Finset ℕ)) ↦ ω i) ''
        lowFourthCrossingConeRecordEvent n),
      ∃ p : LowFourthAxisPath n, lowFourthAxisPrefixMap n p = y := by
  intro y hy
  obtain ⟨ω, hω, rfl⟩ := hy
  let x : Fin (2 * n) → Bool := fun j ↦ ω j.val
  have hgood : AxisGood (bitsAxisEquiv n x).1 (bitsAxisEquiv n x).2 := by
    apply (coneRecord_extend_iff_axisGood x).mp
    apply (isConeRecord_iff_of_prefix (ω := extendBits n x) (η := ω) ?_).mpr hω.1
    intro k hk
    simp [x, extendBits, hk]
  let p0 : AxisGoodPath n := ⟨bitsAxisEquiv n x, hgood⟩
  have hpcoeff : axisPathCoefficients p0 = extendBits n x := by
    rw [axisPathCoefficients_eq]
    congr 1
    exact (bitsAxisEquiv n).symm_apply_apply x
  have hcount : axisFourthCrossingCount p0 = twoSidedFourthCrossingCount ω n := by
    unfold axisFourthCrossingCount
    apply twoSidedFourthCrossingCount_eq_of_prefix hn
    intro i hi
    rw [hpcoeff]
    simp [x, extendBits, hi]
  let p : LowFourthAxisPath n := ⟨p0, by simpa [hcount] using hω.2⟩
  refine ⟨p, ?_⟩
  funext i
  change ((bitsAxisEquiv n).symm p0.1) ⟨i.val, Finset.mem_range.mp i.property⟩ = ω i.val
  simp [p0, x]

lemma card_lowFourth_prefixImage_eq (n : ℕ) (hn : 3 ≤ n) :
    ((fun (ω : ℕ → Bool) (i : (Finset.range (2 * n) : Finset ℕ)) ↦ ω i) ''
        lowFourthCrossingConeRecordEvent n).ncard =
      Fintype.card (LowFourthAxisPath n) := by
  let f := lowFourthAxisPrefixMap n
  let E := (fun (ω : ℕ → Bool) (i : (Finset.range (2 * n) : Finset ℕ)) ↦ ω i) ''
    lowFourthCrossingConeRecordEvent n
  have himage : f '' (Set.univ : Set (LowFourthAxisPath n)) = E := by
    apply Set.Subset.antisymm
    · rintro y ⟨p, hp, rfl⟩
      exact lowFourthAxisPrefixMap_mem_image p
    · intro y hy
      obtain ⟨p, hp⟩ := lowFourthAxisPrefixMap_surjective_image n hn y hy
      exact ⟨p, Set.mem_univ p, hp⟩
  change E.ncard = Fintype.card (LowFourthAxisPath n)
  rw [← himage, Set.ncard_image_of_injective _ (lowFourthAxisPrefixMap_injective n),
    Set.ncard_univ, Nat.card_eq_fintype_card]

/-- Exact finite-cardinality formula for the low-fourth-crossing record mass. -/
lemma lowFourthCrossingRecord_measure_eq (n : ℕ) (hn : 3 ≤ n) :
    rademacherMeasure.real (lowFourthCrossingConeRecordEvent n) =
      (Fintype.card (LowFourthAxisPath n) : ℝ) / (4 : ℝ) ^ n := by
  let S := Finset.range (2 * n)
  let E : Set (S → Bool) :=
    (fun (ω : ℕ → Bool) (i : S) ↦ ω i) '' lowFourthCrossingConeRecordEvent n
  have hm := rademacherMeasure_prefix_preimage S E
  rw [← lowFourthEvent_eq_prefix_preimage n hn] at hm
  rw [Measure.real, hm]
  rw [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  change (E.ncard : ℝ) / ((2 ^ S.card : ℕ) : ℝ) =
    (Fintype.card (LowFourthAxisPath n) : ℝ) / (4 : ℝ) ^ n
  rw [card_lowFourth_prefixImage_eq n hn]
  rw [show S.card = 2 * n by simp [S]]
  congr 1
  push_cast
  rw [pow_mul]
  norm_num

/-- A conditional first-moment estimate with any eventual constant at most `0.39` closes the
one-percent crossing-mass gate, hence disproves the proposed limit. -/
theorem erdos_521_negative_of_fourthCrossing_firstMoment
    (hmean : ∀ᶠ n : ℕ in atTop,
      (∑ p : AxisGoodPath n, (axisFourthCrossingCount p : ℝ)) ≤
        (39 : ℝ) / 100 * Fintype.card (AxisGoodPath n) *
          Real.log (recordDegree n : ℝ)) :
    ¬ Claim := by
  apply erdos_521_negative_of_fourthCrossingRecord_mass
  have hlogNat : ∀ᶠ n : ℕ in atTop, (100 : ℝ) ≤ Real.log (n : ℝ) := by
    have ht : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    exact ht.eventually (eventually_ge_atTop 100)
  filter_upwards [hmean, hlogNat, eventually_ge_atTop (3 : ℕ)] with n hn hlogn hn3
  have hnrec : n ≤ recordDegree n := by unfold recordDegree; omega
  have hlogmono : Real.log (n : ℝ) ≤ Real.log (recordDegree n : ℝ) := by
    apply Real.strictMonoOn_log.monotoneOn
    · exact Set.mem_Ioi.mpr (by positivity)
    · apply Set.mem_Ioi.mpr
      have : 0 < recordDegree n := by unfold recordDegree; omega
      exact_mod_cast this
    · exact_mod_cast hnrec
  have hlog : (100 : ℝ) ≤ Real.log (recordDegree n : ℝ) := hlogn.trans hlogmono
  have hcard := card_le_hundred_card_low_of_sum_le
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
