import Research.FourthIidTwistSymmetry
import Research.HighThresholdAnalyticSplit

open Filter
open scoped BigOperators Topology

namespace Erdos521

noncomputable local instance wideIidGateDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- Wider finite local-limit target enabled by F-058. -/
def IidFourthWidePointwiseRate : Prop :=
  ∃ K : ℕ, ∀ (r k : ℕ), K ≤ k → k < 2 * r - 1 →
    (∑ w : AxisWord r, (terminalTwoSidedFourthIndicator w k : ℝ)) /
        (4 : ℝ) ^ r ≤ (57 : ℝ) / (100 * (k + 1 : ℝ))

/-- Equivalent practical one-sided target: `0.285/(k+1)` on the shortest containing word. -/
def IidFourthWideOneSidedRate : Prop :=
  ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
    (∑ x : Fin (2 * fourthEdgePairLength k) → Bool,
        (fourthIntegratedCrossingIndicator
          (extendBits (fourthEdgePairLength k) x) k : ℝ)) /
        (2 : ℝ) ^ (2 * fourthEdgePairLength k) ≤
      (57 : ℝ) / (200 * (k + 1 : ℝ))

lemma iidFourthWidePointwise_of_oneSided
    (h : IidFourthWideOneSidedRate) : IidFourthWidePointwiseRate := by
  obtain ⟨K, hK⟩ := h
  refine ⟨K, fun r k hk hkr ↦ ?_⟩
  have hcontain : k + 2 ≤ 2 * r := by omega
  have hmin := fourthEdgePairLength_minimal hcontain
  obtain ⟨s, hrs⟩ := Nat.exists_eq_add_of_le hmin
  subst r
  rw [iidFourthIndicator_probability_length_independent
    (fourthEdgePairLength k) s k (fourthEdgePairLength_contains k)]
  rw [sum_twoSidedFourthIndicator_eq_two_mul _ _ (fourthEdgePairLength_contains k)]
  rw [show (4 : ℝ) ^ fourthEdgePairLength k =
      (2 : ℝ) ^ (2 * fourthEdgePairLength k) by rw [pow_mul]; norm_num]
  calc
    (2 * ∑ x : Fin (2 * fourthEdgePairLength k) → Bool,
      (fourthIntegratedCrossingIndicator
        (extendBits (fourthEdgePairLength k) x) k : ℝ)) /
        (2 : ℝ) ^ (2 * fourthEdgePairLength k) =
      2 * ((∑ x : Fin (2 * fourthEdgePairLength k) → Bool,
        (fourthIntegratedCrossingIndicator
          (extendBits (fourthEdgePairLength k) x) k : ℝ)) /
        (2 : ℝ) ^ (2 * fourthEdgePairLength k)) := by ring
    _ ≤ 2 * ((57 : ℝ) / (200 * (k + 1 : ℝ))) :=
      mul_le_mul_of_nonneg_left (hK k hk) (by norm_num)
    _ = (57 : ℝ) / (100 * (k + 1 : ℝ)) := by
      have hkpos : (0 : ℝ) < k + 1 := by positivity
      field_simp
      norm_num

/-- The pointwise `0.57/(k+1)` rate yields the cumulative iid `0.58 log` hypothesis in F-059;
the strict `0.01` logarithmic margin absorbs all finitely many initial edges. -/
lemma iidFourthWideBound_of_pointwise (hpoint : IidFourthWidePointwiseRate) :
    ∀ᶠ n : ℕ in atTop,
      (∑ w : AxisWord (earlyPairBlock n),
          (terminalTwoSidedFourthCount (earlyFourthCutoff n) w : ℝ)) /
          (4 : ℝ) ^ earlyPairBlock n ≤
        (29 : ℝ) / 50 * Real.log (recordDegree n : ℝ) := by
  obtain ⟨K0, hK0⟩ := hpoint
  have hlog : ∀ᶠ n : ℕ in atTop,
      (200 * K0 + 60 : ℝ) ≤ Real.log (recordDegree n : ℝ) := by
    have hdeg : Tendsto (fun n : ℕ ↦ (recordDegree n : ℝ)) atTop atTop := by
      apply Filter.tendsto_atTop_mono' atTop _ tendsto_natCast_atTop_atTop
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      have hndeg : n ≤ recordDegree n := by
        unfold recordDegree
        omega
      exact_mod_cast hndeg
    exact (Real.tendsto_log_atTop.comp hdeg).eventually
      (eventually_ge_atTop (200 * K0 + 60 : ℝ))
  filter_upwards [hlog, eventually_ge_atTop (100 * (K0 + 2) : ℕ)] with n hlogn hn
  let r := earlyPairBlock n
  let M := earlyFourthCutoff n
  have hK0M : K0 ≤ M := by
    dsimp [M, r, earlyFourthCutoff, earlyPairBlock]
    have hdiv : K0 + 2 ≤ n / 100 :=
      (Nat.le_div_iff_mul_le (by norm_num)).2 (by simpa [Nat.mul_comm] using hn)
    omega
  have hMr : M < 2 * r := earlyFourthCutoff_lt_bits n
  have hMpos : 0 < M := by
    dsimp [M, earlyFourthCutoff, earlyPairBlock]
    have hdiv : K0 + 2 ≤ n / 100 :=
      (Nat.le_div_iff_mul_le (by norm_num)).2 (by simpa [Nat.mul_comm] using hn)
    omega
  have hlate :
      (∑ k ∈ Finset.Ico K0 M,
        ∑ w : AxisWord r, (terminalTwoSidedFourthIndicator w k : ℝ)) /
          (4 : ℝ) ^ r ≤
        (57 : ℝ) / 100 * ∑ k ∈ Finset.Ico K0 M, (1 : ℝ) / (k + 1 : ℝ) := by
    rw [Finset.mul_sum]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (4 : ℝ) ^ r)).2
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro k hk
    have hk0 : K0 ≤ k := (Finset.mem_Ico.mp hk).1
    have hkM : k < M := (Finset.mem_Ico.mp hk).2
    have hp := hK0 r k hk0 (by omega)
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (4 : ℝ) ^ r)).1 at hp
    calc
      (∑ w : AxisWord r, (terminalTwoSidedFourthIndicator w k : ℝ)) ≤
          ((57 : ℝ) / (100 * (k + 1 : ℝ))) * (4 : ℝ) ^ r := hp
      _ = ((57 : ℝ) / 100 * ((1 : ℝ) / (k + 1 : ℝ))) * (4 : ℝ) ^ r := by
        have hkpos : (0 : ℝ) < k + 1 := by positivity
        field_simp
  have hIco :
      (∑ k ∈ Finset.Ico K0 M, (1 : ℝ) / (k + 1 : ℝ)) ≤ (harmonic M : ℝ) := by
    rw [← sum_recip_eq_harmonic]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro k hk
      simp only [Finset.mem_Ico, Finset.mem_range] at hk ⊢
      omega
    · exact fun _ _ _ ↦ by positivity
  have hharm : (harmonic M : ℝ) ≤ 1 + Real.log M := by
    exact_mod_cast harmonic_le_one_add_log M
  have hMdeg : M ≤ recordDegree n := by
    dsimp [M, earlyFourthCutoff, earlyPairBlock, recordDegree]
    omega
  have hlogmono : Real.log (M : ℝ) ≤ Real.log (recordDegree n : ℝ) := by
    exact Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr (by exact_mod_cast hMpos))
      (Set.mem_Ioi.mpr (by
        have hnpos : 0 < n := by omega
        have hdegpos : 0 < recordDegree n := by
          unfold recordDegree
          omega
        exact_mod_cast hdegpos))
      (by exact_mod_cast hMdeg)
  have hearly := sum_terminalIndicator_early_le r K0
  rw [show (∑ w : AxisWord r, (terminalTwoSidedFourthCount M w : ℝ)) =
      ∑ k ∈ Finset.range M,
        ∑ w : AxisWord r, (terminalTwoSidedFourthIndicator w k : ℝ) by
    simp_rw [terminalTwoSidedFourthCount_eq_sum]
    push_cast
    rw [Finset.sum_comm]]
  have hsplit :
      (∑ k ∈ Finset.range M,
        ∑ w : AxisWord r, (terminalTwoSidedFourthIndicator w k : ℝ)) =
      (∑ k ∈ Finset.range K0,
        ∑ w : AxisWord r, (terminalTwoSidedFourthIndicator w k : ℝ)) +
      (∑ k ∈ Finset.Ico K0 M,
        ∑ w : AxisWord r, (terminalTwoSidedFourthIndicator w k : ℝ)) := by
    exact (Finset.sum_range_add_sum_Ico _ hK0M).symm
  rw [hsplit, add_div]
  calc
    _ ≤ (2 * K0 * (4 : ℝ) ^ r) / (4 : ℝ) ^ r +
        (57 / 100 : ℝ) * ∑ k ∈ Finset.Ico K0 M, (1 : ℝ) / (k + 1 : ℝ) :=
      add_le_add (div_le_div_of_nonneg_right hearly (by positivity)) hlate
    _ = 2 * K0 + (57 / 100 : ℝ) *
        ∑ k ∈ Finset.Ico K0 M, (1 : ℝ) / (k + 1 : ℝ) := by
      field_simp
    _ ≤ 2 * K0 + (57 / 100 : ℝ) * (harmonic M : ℝ) := by gcongr
    _ ≤ 2 * K0 + (57 / 100 : ℝ) * (1 + Real.log M) := by gcongr
    _ ≤ 2 * K0 + (57 / 100 : ℝ) *
        (1 + Real.log (recordDegree n : ℝ)) := by gcongr
    _ ≤ (29 : ℝ) / 50 * Real.log (recordDegree n : ℝ) := by
      push_cast at hlogn
      linarith

/-- A wider local-limit proof plus the late cone estimate proves the
negative answer to Erdős 521. -/
theorem erdos_521_negative_of_wideIidPointwise_and_late
    (hpoint : IidFourthWidePointwiseRate)
    (hlate : ∀ᶠ n : ℕ in atTop,
      (∑ p : AxisGoodPath n, (lateAxisFourthCount (earlyFourthCutoff n) p : ℝ)) ≤
        (3 : ℝ) / 100 * Fintype.card (AxisGoodPath n) * Real.log (recordDegree n : ℝ)) :
    ¬ Claim :=
  erdos_521_negative_of_highThreshold_split
    (iidFourthWideBound_of_pointwise hpoint) hlate

/-- Final one-sided local-limit formulation with `0.285/(k+1)` allowance. -/
theorem erdos_521_negative_of_wideIidOneSided_and_late
    (hpoint : IidFourthWideOneSidedRate)
    (hlate : ∀ᶠ n : ℕ in atTop,
      (∑ p : AxisGoodPath n, (lateAxisFourthCount (earlyFourthCutoff n) p : ℝ)) ≤
        (3 : ℝ) / 100 * Fintype.card (AxisGoodPath n) * Real.log (recordDegree n : ℝ)) :
    ¬ Claim :=
  erdos_521_negative_of_wideIidPointwise_and_late
    (iidFourthWidePointwise_of_oneSided hpoint) hlate

end Erdos521
