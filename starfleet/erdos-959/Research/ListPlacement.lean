import Research.DistanceUnion

noncomputable section
namespace Erdos959

lemma mem_pointDistanceSpectrum_iff_nonempty
    (X : Finset Point) (d : ℝ) :
    d ∈ pointDistanceSpectrum X ↔ (orderedRealDistancePairs X d).Nonempty := by
  constructor
  · intro hd
    rcases Finset.mem_image.mp hd with ⟨xy, hxy, hdist⟩
    refine ⟨xy, ?_⟩
    have hm := Finset.mem_filter.mp hxy
    apply Finset.mem_filter.mpr
    exact ⟨hm.1, hm.2, hdist⟩
  · rintro ⟨xy, hxy⟩
    have hm := Finset.mem_filter.mp hxy
    apply Finset.mem_image.mpr
    exact ⟨xy, Finset.mem_filter.mpr ⟨hm.1, hm.2.1⟩, hm.2.2⟩

lemma orderedRealDistancePairs_card_eq_zero_of_not_mem
    (X : Finset Point) (d : ℝ) (hd : d ∉ pointDistanceSpectrum X) :
    (orderedRealDistancePairs X d).card = 0 := by
  rw [Finset.card_eq_zero]
  apply Finset.not_nonempty_iff_eq_empty.mp
  intro hn
  exact hd ((mem_pointDistanceSpectrum_iff_nonempty X d).mpr hn)

/-- Place a block while avoiding an arbitrary global protected spectrum as
well as every distance already born in the old union. -/
theorem exists_globally_avoiding_block_translation
    (A Y : Finset Point) (G : Finset ℝ) :
    ∃ t : Point,
      Disjoint (translatedFinset t A) Y ∧
      (∀ d ∈ G ∪ pointDistanceSpectrum Y,
        (crossDistanceFiber A Y t d).card = 0) ∧
      (∀ d : ℝ, (crossDistanceFiber A Y t d).card ≤ A.card) := by
  let D : Finset ℝ := insert 0 (G ∪ pointDistanceSpectrum Y)
  obtain ⟨t, havoid, hsep⟩ := exists_separating_translation A Y D
  refine ⟨t, ?_, ?_, fun d => crossDistanceFiber_card_le_newBlock A Y t hsep d⟩
  · rw [Finset.disjoint_left]
    intro z hzA hzY
    rcases Finset.mem_image.mp hzA with ⟨a, ha, rfl⟩
    have hne := havoid a ha (translatePoint t a) hzY 0 (Finset.mem_insert_self 0 _)
    apply hne
    dsimp [translatedCrossSqDist, sqDist]
    ring
  · intro d hd
    apply Finset.card_eq_zero.mpr
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro hn
    rcases hn with ⟨ay, hay⟩
    have hm := Finset.mem_filter.mp hay
    have hp := Finset.mem_product.mp hm.1
    have hne := havoid ay.1 hp.1 ay.2 hp.2 d (Finset.mem_insert_of_mem hd)
    exact hne hm.2

/-- Frequency form of globally protected placement. -/
theorem exists_globally_avoiding_frequency_step
    (A Y : Finset Point) (G : Finset ℝ)
    (hAG : pointDistanceSpectrum A ⊆ G) :
    ∃ t : Point,
      Disjoint (translatedFinset t A) Y ∧
      (∀ d ∈ G,
        (orderedRealDistancePairs (translatedFinset t A ∪ Y) d).card =
          (orderedRealDistancePairs A d).card +
          (orderedRealDistancePairs Y d).card) ∧
      (∀ d ∉ G,
        (d ∈ pointDistanceSpectrum Y →
          (orderedRealDistancePairs (translatedFinset t A ∪ Y) d).card =
            (orderedRealDistancePairs Y d).card) ∧
        (d ∉ pointDistanceSpectrum Y →
          (orderedRealDistancePairs (translatedFinset t A ∪ Y) d).card ≤
            2 * A.card)) := by
  obtain ⟨t, hdisj, hzero, hcross⟩ :=
    exists_globally_avoiding_block_translation A Y G
  refine ⟨t, hdisj, ?_, ?_⟩
  · intro d hdG
    have hcross0 : (realCrossDistancePairs (translatedFinset t A) Y d).card = 0 := by
      rw [translated_cross_fiber_card]
      exact hzero d (Finset.mem_union_left _ hdG)
    have hrev0 : (realCrossDistancePairs Y (translatedFinset t A) d).card = 0 := by
      rw [← card_realCrossDistancePairs_comm]
      exact hcross0
    apply Nat.le_antisymm
    · calc
        (orderedRealDistancePairs (translatedFinset t A ∪ Y) d).card ≤
            (orderedRealDistancePairs (translatedFinset t A) d).card +
            (orderedRealDistancePairs Y d).card +
            (realCrossDistancePairs (translatedFinset t A) Y d).card +
            (realCrossDistancePairs Y (translatedFinset t A) d).card :=
          orderedRealDistancePairs_union_card_upper _ _ hdisj _
        _ = (orderedRealDistancePairs A d).card +
            (orderedRealDistancePairs Y d).card := by
          rw [translated_internal_fiber_card, hcross0, hrev0]
          omega
    · rw [← translated_internal_fiber_card A t d]
      exact orderedRealDistancePairs_internal_card_lower _ _ hdisj d
  · intro d hdG
    have hA0 : (orderedRealDistancePairs A d).card = 0 :=
      orderedRealDistancePairs_card_eq_zero_of_not_mem A d (fun hdA => hdG (hAG hdA))
    constructor
    · intro hdY
      have hcross0 : (realCrossDistancePairs (translatedFinset t A) Y d).card = 0 := by
        rw [translated_cross_fiber_card]
        exact hzero d (Finset.mem_union_right _ hdY)
      have hrev0 : (realCrossDistancePairs Y (translatedFinset t A) d).card = 0 := by
        rw [← card_realCrossDistancePairs_comm]
        exact hcross0
      apply Nat.le_antisymm
      · calc
          (orderedRealDistancePairs (translatedFinset t A ∪ Y) d).card ≤
              (orderedRealDistancePairs (translatedFinset t A) d).card +
              (orderedRealDistancePairs Y d).card +
              (realCrossDistancePairs (translatedFinset t A) Y d).card +
              (realCrossDistancePairs Y (translatedFinset t A) d).card :=
            orderedRealDistancePairs_union_card_upper _ _ hdisj _
          _ = (orderedRealDistancePairs Y d).card := by
            rw [translated_internal_fiber_card, hA0, hcross0, hrev0]
            omega
      · have hlower := orderedRealDistancePairs_internal_card_lower
          (translatedFinset t A) Y hdisj d
        rw [translated_internal_fiber_card, hA0] at hlower
        omega
    · intro hdY
      have hY0 := orderedRealDistancePairs_card_eq_zero_of_not_mem Y d hdY
      have hcrossBound :
          (realCrossDistancePairs (translatedFinset t A) Y d).card ≤ A.card := by
        rw [translated_cross_fiber_card]
        exact hcross d
      have hrevBound :
          (realCrossDistancePairs Y (translatedFinset t A) d).card ≤ A.card := by
        rw [← card_realCrossDistancePairs_comm]
        exact hcrossBound
      calc
        (orderedRealDistancePairs (translatedFinset t A ∪ Y) d).card ≤
            (orderedRealDistancePairs (translatedFinset t A) d).card +
            (orderedRealDistancePairs Y d).card +
            (realCrossDistancePairs (translatedFinset t A) Y d).card +
            (realCrossDistancePairs Y (translatedFinset t A) d).card :=
          orderedRealDistancePairs_union_card_upper _ _ hdisj _
        _ ≤ 0 + 0 + A.card + A.card := by
          rw [translated_internal_fiber_card, hA0, hY0]
          omega
        _ = 2 * A.card := by omega

/-- Union of all protected internal spectra in a list of blocks. -/
def listBlockSpectrum : List (Finset Point) → Finset ℝ
  | [] => ∅
  | A :: L => pointDistanceSpectrum A ∪ listBlockSpectrum L

/-- Sum of internal ordered frequencies of all listed blocks. -/
def listBlockFrequency (L : List (Finset Point)) (d : ℝ) : ℕ :=
  L.foldr (fun A n => (orderedRealDistancePairs A d).card + n) 0

/-- Total number of points before disjoint placement. -/
def listBlockCard : List (Finset Point) → ℕ
  | [] => 0
  | A :: L => A.card + listBlockCard L

/-- Largest block size. -/
def listMaxBlockCard : List (Finset Point) → ℕ
  | [] => 0
  | A :: L => max A.card (listMaxBlockCard L)

lemma listBlockSpectrum_tail_subset (A : Finset Point) (L : List (Finset Point)) :
    listBlockSpectrum L ⊆ listBlockSpectrum (A :: L) := by
  intro d hd
  exact Finset.mem_union_right _ hd

/-- Any finite list of blocks admits a disjoint generic placement: every
protected internal frequency adds exactly, and every other class has frequency
at most twice the largest block. -/
theorem exists_isolated_placement_of_list (L : List (Finset Point)) :
    ∃ Y : Finset Point,
      Y.card = listBlockCard L ∧
      (∀ d ∈ listBlockSpectrum L,
        (orderedRealDistancePairs Y d).card = listBlockFrequency L d) ∧
      (∀ d ∉ listBlockSpectrum L,
        (orderedRealDistancePairs Y d).card ≤ 2 * listMaxBlockCard L) := by
  let G := listBlockSpectrum L
  have hLG : listBlockSpectrum L ⊆ G := fun _ h => h
  suffices H : ∀ (M : List (Finset Point)), listBlockSpectrum M ⊆ G →
      ∃ Y : Finset Point,
        Y.card = listBlockCard M ∧
        (∀ d ∈ G, (orderedRealDistancePairs Y d).card = listBlockFrequency M d) ∧
        (∀ d ∉ G, (orderedRealDistancePairs Y d).card ≤ 2 * listMaxBlockCard M) by
    obtain ⟨Y, hcard, hfreq, hoff⟩ := H L hLG
    exact ⟨Y, hcard, fun d hd => hfreq d hd, fun d hd => hoff d hd⟩
  intro M hMG
  induction M with
  | nil =>
      refine ⟨∅, by simp [listBlockCard], ?_, ?_⟩
      · intro d hd
        simp [orderedRealDistancePairs, listBlockFrequency]
      · intro d hd
        simp [orderedRealDistancePairs, listMaxBlockCard]
  | cons A M ih =>
      have hMsub : listBlockSpectrum M ⊆ G := by
        intro d hd
        exact hMG (Finset.mem_union_right _ hd)
      obtain ⟨Y, hYcard, hYfreq, hYoff⟩ := ih hMsub
      have hAsub : pointDistanceSpectrum A ⊆ G := by
        intro d hd
        exact hMG (Finset.mem_union_left _ hd)
      obtain ⟨t, hdisj, hprotected, hoffstep⟩ :=
        exists_globally_avoiding_frequency_step A Y G hAsub
      let Z := translatedFinset t A ∪ Y
      refine ⟨Z, ?_, ?_, ?_⟩
      · dsimp [Z]
        rw [Finset.card_union_of_disjoint hdisj, card_translatedFinset, hYcard]
        rfl
      · intro d hdG
        dsimp [Z]
        rw [hprotected d hdG, hYfreq d hdG]
        rfl
      · intro d hdG
        by_cases hdY : d ∈ pointDistanceSpectrum Y
        · dsimp [Z]
          rw [(hoffstep d hdG).1 hdY]
          exact (hYoff d hdG).trans (by
            have hm : listMaxBlockCard M ≤ max A.card (listMaxBlockCard M) :=
              Nat.le_max_right _ _
            exact Nat.mul_le_mul_left 2 hm)
        · dsimp [Z]
          exact ((hoffstep d hdG).2 hdY).trans (by
            have hm : A.card ≤ max A.card (listMaxBlockCard M) := Nat.le_max_left _ _
            exact Nat.mul_le_mul_left 2 hm)

end Erdos959
