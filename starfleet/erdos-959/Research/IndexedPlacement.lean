import Research.ListPlacement

noncomputable section
namespace Erdos959

/-- Protected internal spectrum of a finite indexed family of blocks. -/
def indexedBlockSpectrum
    {ι : Type*} [DecidableEq ι] (I : Finset ι) (A : ι → Finset Point) : Finset ℝ :=
  I.biUnion fun i => pointDistanceSpectrum (A i)

lemma pointDistanceSpectrum_subset_indexed
    {ι : Type*} [DecidableEq ι] (I : Finset ι) (A : ι → Finset Point)
    {i : ι} (hi : i ∈ I) :
    pointDistanceSpectrum (A i) ⊆ indexedBlockSpectrum I A := by
  intro d hd
  exact Finset.mem_biUnion.mpr ⟨i, hi, hd⟩

/-- Indexed-family version of F-026 with a supplied uniform block-size cap. -/
theorem exists_isolated_placement_of_indexed_family_bounded
    {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (A : ι → Finset Point) (M : ℕ)
    (hsize : ∀ i ∈ I, (A i).card ≤ M) :
    ∃ Y : Finset Point,
      Y.card = ∑ i ∈ I, (A i).card ∧
      (∀ d ∈ indexedBlockSpectrum I A,
        (orderedRealDistancePairs Y d).card =
          ∑ i ∈ I, (orderedRealDistancePairs (A i) d).card) ∧
      (∀ d ∉ indexedBlockSpectrum I A,
        (orderedRealDistancePairs Y d).card ≤ 2 * M) := by
  let G := indexedBlockSpectrum I A
  have hspec : ∀ i ∈ I, pointDistanceSpectrum (A i) ⊆ G := by
    intro i hi
    exact pointDistanceSpectrum_subset_indexed I A hi
  suffices H : ∀ (J : Finset ι), J ⊆ I →
      ∃ Y : Finset Point,
        Y.card = ∑ i ∈ J, (A i).card ∧
        (∀ d ∈ G, (orderedRealDistancePairs Y d).card =
          ∑ i ∈ J, (orderedRealDistancePairs (A i) d).card) ∧
        (∀ d ∉ G, (orderedRealDistancePairs Y d).card ≤ 2 * M) by
    obtain ⟨Y, hcard, hfreq, hoff⟩ := H I (fun _ h => h)
    exact ⟨Y, hcard, fun d hd => hfreq d hd, fun d hd => hoff d hd⟩
  intro J hJI
  induction J using Finset.induction_on with
  | empty =>
      refine ⟨∅, by simp, ?_, ?_⟩
      · intro d hd
        simp [orderedRealDistancePairs]
      · intro d hd
        simp [orderedRealDistancePairs]
  | @insert i J hiJ ih =>
      have hJsub : J ⊆ I := fun x hx => hJI (Finset.mem_insert_of_mem hx)
      obtain ⟨Y, hYcard, hYfreq, hYoff⟩ := ih hJsub
      have hiI : i ∈ I := hJI (Finset.mem_insert_self i J)
      have hAiG : pointDistanceSpectrum (A i) ⊆ G := hspec i hiI
      obtain ⟨t, hdisj, hprotected, hoffstep⟩ :=
        exists_globally_avoiding_frequency_step (A i) Y G hAiG
      let Z := translatedFinset t (A i) ∪ Y
      refine ⟨Z, ?_, ?_, ?_⟩
      · dsimp [Z]
        rw [Finset.card_union_of_disjoint hdisj, card_translatedFinset,
          hYcard, Finset.sum_insert hiJ]
      · intro d hdG
        dsimp [Z]
        rw [hprotected d hdG, hYfreq d hdG, Finset.sum_insert hiJ]
      · intro d hdG
        by_cases hdY : d ∈ pointDistanceSpectrum Y
        · dsimp [Z]
          rw [(hoffstep d hdG).1 hdY]
          exact hYoff d hdG
        · dsimp [Z]
          exact ((hoffstep d hdG).2 hdY).trans
            (Nat.mul_le_mul_left 2 (hsize i hiI))

end Erdos959
