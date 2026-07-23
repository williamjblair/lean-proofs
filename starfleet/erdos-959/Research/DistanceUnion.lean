import Research.GenericPlacement

noncomputable section
namespace Erdos959

/-- Ordered pairs of distinct real points at squared distance `d`. -/
def orderedRealDistancePairs (X : Finset Point) (d : ℝ) :
    Finset (Point × Point) :=
  (X.product X).filter fun xy => xy.1 ≠ xy.2 ∧ sqDist xy.1 xy.2 = d

/-- Oriented cross pairs from `X` to `Y` at squared distance `d`. -/
def realCrossDistancePairs (X Y : Finset Point) (d : ℝ) :
    Finset (Point × Point) :=
  (X.product Y).filter fun xy => sqDist xy.1 xy.2 = d

lemma sqDist_comm (x y : Point) : sqDist x y = sqDist y x := by
  dsimp [sqDist]
  ring

lemma orderedRealDistancePairs_union_decomposition
    (X Y : Finset Point) (hdisj : Disjoint X Y) (d : ℝ) :
    orderedRealDistancePairs (X ∪ Y) d =
      orderedRealDistancePairs X d ∪ orderedRealDistancePairs Y d ∪
        realCrossDistancePairs X Y d ∪ realCrossDistancePairs Y X d := by
  have hd := Finset.disjoint_left.mp hdisj
  ext xy
  simp [orderedRealDistancePairs, realCrossDistancePairs]
  aesop

lemma orderedRealDistancePairs_union_card_upper
    (X Y : Finset Point) (hdisj : Disjoint X Y) (d : ℝ) :
    (orderedRealDistancePairs (X ∪ Y) d).card ≤
      (orderedRealDistancePairs X d).card +
      (orderedRealDistancePairs Y d).card +
      (realCrossDistancePairs X Y d).card +
      (realCrossDistancePairs Y X d).card := by
  rw [orderedRealDistancePairs_union_decomposition X Y hdisj d]
  have h1 := Finset.card_union_le
    (orderedRealDistancePairs X d ∪ orderedRealDistancePairs Y d ∪
      realCrossDistancePairs X Y d) (realCrossDistancePairs Y X d)
  have h2 := Finset.card_union_le
    (orderedRealDistancePairs X d ∪ orderedRealDistancePairs Y d)
      (realCrossDistancePairs X Y d)
  have h3 := Finset.card_union_le
    (orderedRealDistancePairs X d) (orderedRealDistancePairs Y d)
  omega

lemma orderedRealDistancePairs_internal_card_lower
    (X Y : Finset Point) (hdisj : Disjoint X Y) (d : ℝ) :
    (orderedRealDistancePairs X d).card +
      (orderedRealDistancePairs Y d).card ≤
      (orderedRealDistancePairs (X ∪ Y) d).card := by
  have hpairDisj : Disjoint (X.product X) (Y.product Y) :=
    Finset.disjoint_product.mpr (Or.inl hdisj)
  have hfiberDisj : Disjoint (orderedRealDistancePairs X d)
      (orderedRealDistancePairs Y d) :=
    Finset.disjoint_filter_filter hpairDisj
  rw [← Finset.card_union_of_disjoint hfiberDisj]
  apply Finset.card_le_card
  intro xy hxy
  simp [orderedRealDistancePairs] at hxy ⊢
  aesop

lemma card_realCrossDistancePairs_comm (X Y : Finset Point) (d : ℝ) :
    (realCrossDistancePairs X Y d).card =
      (realCrossDistancePairs Y X d).card := by
  let swap : Point × Point → Point × Point := fun xy => (xy.2, xy.1)
  have hswap : Function.Injective swap := by
    intro xy uv h
    exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
  let I := (realCrossDistancePairs X Y d).image swap
  have hcard : I.card = (realCrossDistancePairs X Y d).card :=
    Finset.card_image_of_injective _ hswap
  have hI : I = realCrossDistancePairs Y X d := by
    ext yx
    constructor
    · intro hyx
      rcases Finset.mem_image.mp hyx with ⟨xy, hxy, rfl⟩
      have hm := Finset.mem_filter.mp hxy
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_product.mpr ⟨(Finset.mem_product.mp hm.1).2,
        (Finset.mem_product.mp hm.1).1⟩, (sqDist_comm xy.2 xy.1).trans hm.2⟩
    · intro hyx
      have hm := Finset.mem_filter.mp hyx
      apply Finset.mem_image.mpr
      refine ⟨(yx.2, yx.1), ?_, by simp [swap]⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_product.mpr ⟨(Finset.mem_product.mp hm.1).2,
        (Finset.mem_product.mp hm.1).1⟩, (sqDist_comm yx.2 yx.1).trans hm.2⟩
  rw [← hI, hcard]

lemma translated_cross_fiber_card
    (A Y : Finset Point) (t : Point) (d : ℝ) :
    (realCrossDistancePairs (translatedFinset t A) Y d).card =
      (crossDistanceFiber A Y t d).card := by
  let f : Point × Point → Point × Point := fun ay => (translatePoint t ay.1, ay.2)
  have hf : Function.Injective f := by
    intro ay bz h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    dsimp [f] at h1 h2
    apply Prod.ext
    · exact (translatePoint_injective t) h1
    · exact h2
  let I := (crossDistanceFiber A Y t d).image f
  have hcard : I.card = (crossDistanceFiber A Y t d).card :=
    Finset.card_image_of_injective _ hf
  have hI : I = realCrossDistancePairs (translatedFinset t A) Y d := by
    ext zy
    constructor
    · intro hzy
      rcases Finset.mem_image.mp hzy with ⟨ay, hay, rfl⟩
      have hm := Finset.mem_filter.mp hay
      have hp := Finset.mem_product.mp hm.1
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_product.mpr
        ⟨Finset.mem_image.mpr ⟨ay.1, hp.1, rfl⟩, hp.2⟩, hm.2⟩
    · intro hzy
      have hm := Finset.mem_filter.mp hzy
      have hp := Finset.mem_product.mp hm.1
      rcases Finset.mem_image.mp hp.1 with ⟨a, ha, hat⟩
      apply Finset.mem_image.mpr
      refine ⟨(a, zy.2), ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_product.mpr ⟨ha, hp.2⟩, by
          simpa [translatedCrossSqDist, hat] using hm.2⟩
      · exact Prod.ext hat (by rfl)
  rw [← hI, hcard]

lemma translated_internal_fiber_card
    (A : Finset Point) (t : Point) (d : ℝ) :
    (orderedRealDistancePairs (translatedFinset t A) d).card =
      (orderedRealDistancePairs A d).card := by
  let f : Point × Point → Point × Point := fun ab =>
    (translatePoint t ab.1, translatePoint t ab.2)
  have hf : Function.Injective f := by
    intro ab cd h
    apply Prod.ext
    · exact (translatePoint_injective t) (congrArg Prod.fst h)
    · exact (translatePoint_injective t) (congrArg Prod.snd h)
  let I := (orderedRealDistancePairs A d).image f
  have hcard : I.card = (orderedRealDistancePairs A d).card :=
    Finset.card_image_of_injective _ hf
  have hI : I = orderedRealDistancePairs (translatedFinset t A) d := by
    ext uv
    constructor
    · intro huv
      rcases Finset.mem_image.mp huv with ⟨ab, hab, rfl⟩
      have hm := Finset.mem_filter.mp hab
      have hp := Finset.mem_product.mp hm.1
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_product.mpr
        ⟨Finset.mem_image.mpr ⟨ab.1, hp.1, rfl⟩,
         Finset.mem_image.mpr ⟨ab.2, hp.2, rfl⟩⟩,
        fun heq => hm.2.1 ((translatePoint_injective t) heq),
        (sqDist_translatePoint t ab.1 ab.2).trans hm.2.2⟩
    · intro huv
      have hm := Finset.mem_filter.mp huv
      have hp := Finset.mem_product.mp hm.1
      rcases Finset.mem_image.mp hp.1 with ⟨a, ha, hau⟩
      rcases Finset.mem_image.mp hp.2 with ⟨b, hb, hbv⟩
      apply Finset.mem_image.mpr
      refine ⟨(a, b), ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_product.mpr ⟨ha, hb⟩,
          fun hab => by
            change a = b at hab
            apply hm.2.1
            rw [← hau, ← hbv, hab]
          , by
            rw [← sqDist_translatePoint t a b, hau, hbv]
            exact hm.2.2⟩
      · exact Prod.ext hau hbv
  rw [← hI, hcard]

/-- The one-step placement theorem directly at the level of all ordered
frequency fibers. -/
theorem exists_translation_frequency_dichotomy (A Y : Finset Point) :
    ∃ t : Point,
      Disjoint (translatedFinset t A) Y ∧
      ∀ d : ℝ,
        (d ∈ pointDistanceSpectrum A ∪ pointDistanceSpectrum Y →
          (orderedRealDistancePairs (translatedFinset t A ∪ Y) d).card =
            (orderedRealDistancePairs A d).card +
            (orderedRealDistancePairs Y d).card) ∧
        (d ∉ pointDistanceSpectrum A ∪ pointDistanceSpectrum Y →
          (orderedRealDistancePairs (translatedFinset t A ∪ Y) d).card ≤
            2 * A.card) := by
  obtain ⟨t, hdisj, hzero, hcross⟩ := exists_isolated_block_translation A Y
  refine ⟨t, hdisj, fun d => ⟨?_, ?_⟩⟩
  · intro hd
    have hcross0 : (realCrossDistancePairs (translatedFinset t A) Y d).card = 0 := by
      rw [translated_cross_fiber_card]
      exact hzero d hd
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
  · intro hd
    have hA0 : (orderedRealDistancePairs A d).card = 0 := by
      apply Finset.card_eq_zero.mpr
      apply Finset.not_nonempty_iff_eq_empty.mp
      intro hn
      rcases hn with ⟨ab, hab⟩
      apply hd
      apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      have hm := Finset.mem_filter.mp hab
      exact ⟨ab, Finset.mem_filter.mpr ⟨hm.1, hm.2.1⟩, hm.2.2⟩
    have hY0 : (orderedRealDistancePairs Y d).card = 0 := by
      apply Finset.card_eq_zero.mpr
      apply Finset.not_nonempty_iff_eq_empty.mp
      intro hn
      rcases hn with ⟨ab, hab⟩
      apply hd
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      have hm := Finset.mem_filter.mp hab
      exact ⟨ab, Finset.mem_filter.mpr ⟨hm.1, hm.2.1⟩, hm.2.2⟩
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

end Erdos959
