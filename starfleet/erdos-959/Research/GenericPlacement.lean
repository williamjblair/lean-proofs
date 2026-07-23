import Research.PolynomialPlacement

noncomputable section
namespace Erdos959

/-- The set of positive squared distances occurring internally in a finite set. -/
def pointDistanceSpectrum (X : Finset Point) : Finset ℝ :=
  ((X.product X).filter fun xy => xy.1 ≠ xy.2).image fun xy => sqDist xy.1 xy.2

/-- A translated finite block. -/
def translatedFinset (t : Point) (A : Finset Point) : Finset Point :=
  A.image (translatePoint t)

lemma translatePoint_injective (t : Point) : Function.Injective (translatePoint t) := by
  intro a b h
  apply Prod.ext
  · have hx := congrArg Prod.fst h
    dsimp [translatePoint] at hx
    linarith
  · have hy := congrArg Prod.snd h
    dsimp [translatePoint] at hy
    linarith

lemma card_translatedFinset (t : Point) (A : Finset Point) :
    (translatedFinset t A).card = A.card := by
  exact Finset.card_image_of_injective A (translatePoint_injective t)

lemma sqDist_translatePoint (t a b : Point) :
    sqDist (translatePoint t a) (translatePoint t b) = sqDist a b := by
  dsimp [sqDist, translatePoint]
  ring

lemma pointDistanceSpectrum_translated (t : Point) (A : Finset Point) :
    pointDistanceSpectrum (translatedFinset t A) = pointDistanceSpectrum A := by
  ext d
  constructor
  · intro hd
    rcases Finset.mem_image.mp hd with ⟨uv, huv, rfl⟩
    have huv' := Finset.mem_filter.mp huv
    have hu := Finset.mem_image.mp (Finset.mem_product.mp huv'.1).1
    have hv := Finset.mem_image.mp (Finset.mem_product.mp huv'.1).2
    rcases hu with ⟨a, ha, hua⟩
    rcases hv with ⟨b, hb, hvb⟩
    have huvEq : uv = (translatePoint t a, translatePoint t b) :=
      Prod.ext hua.symm hvb.symm
    subst uv
    apply Finset.mem_image.mpr
    refine ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, ?_⟩, ?_⟩
    · intro hab
      apply huv'.2
      change a = b at hab
      change translatePoint t a = translatePoint t b
      exact congrArg (translatePoint t) hab
    · simpa using (sqDist_translatePoint t a b).symm
  · intro hd
    rcases Finset.mem_image.mp hd with ⟨ab, hab, rfl⟩
    have hab' := Finset.mem_filter.mp hab
    apply Finset.mem_image.mpr
    refine ⟨(translatePoint t ab.1, translatePoint t ab.2),
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩, ?_⟩
    · exact Finset.mem_image.mpr ⟨ab.1, (Finset.mem_product.mp hab'.1).1, rfl⟩
    · exact Finset.mem_image.mpr ⟨ab.2, (Finset.mem_product.mp hab'.1).2, rfl⟩
    · exact fun h => hab'.2 ((translatePoint_injective t) h)
    · exact sqDist_translatePoint t ab.1 ab.2

/-- One can place a new finite block disjointly so that all new cross distances
avoid both internal spectra and every cross fiber has at most one pair per new
point. This is the induction step needed for arbitrarily many blocks. -/
theorem exists_isolated_block_translation (A Y : Finset Point) :
    ∃ t : Point,
      Disjoint (translatedFinset t A) Y ∧
      (∀ d ∈ pointDistanceSpectrum A ∪ pointDistanceSpectrum Y,
        (crossDistanceFiber A Y t d).card = 0) ∧
      (∀ d : ℝ, (crossDistanceFiber A Y t d).card ≤ A.card) := by
  let D : Finset ℝ := insert 0 (pointDistanceSpectrum A ∪ pointDistanceSpectrum Y)
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
    intro hnonempty
    rcases hnonempty with ⟨ay, hay⟩
    have hm := Finset.mem_filter.mp hay
    have hp := Finset.mem_product.mp hm.1
    have hne := havoid ay.1 hp.1 ay.2 hp.2 d (Finset.mem_insert_of_mem hd)
    exact hne hm.2

end Erdos959
