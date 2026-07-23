import Research.Basic

noncomputable section
namespace Erdos959

/-- Translate a planar point by a vector. -/
def translatePoint (t a : Point) : Point := (t.1 + a.1, t.2 + a.2)

/-- The un-translated displacement attached to a cross-block pair. -/
def crossDisplacement (a y : Point) : Point := (a.1 - y.1, a.2 - y.2)

/-- Squared distance from a translated new-block point to an old point. -/
def translatedCrossSqDist (t a y : Point) : ℝ := sqDist (translatePoint t a) y

lemma translatedCrossSqDist_eq_normSq (t a y : Point) :
    translatedCrossSqDist t a y =
      (t.1 + (a.1 - y.1)) ^ 2 + (t.2 + (a.2 - y.2)) ^ 2 := by
  dsimp [translatedCrossSqDist, translatePoint, sqDist]
  ring

/-- Cross pairs realizing a specified squared distance after translation. -/
def crossDistanceFiber (A Y : Finset Point) (t : Point) (d : ℝ) :
    Finset (Point × Point) :=
  (A.product Y).filter fun ay => translatedCrossSqDist t ay.1 ay.2 = d

/-- If translation has removed equal-distance coincidences between distinct
local displacements, every cross-distance fiber has at most one pair per point
of the newly added block. -/
lemma crossDistanceFiber_card_le_newBlock
    (A Y : Finset Point) (t : Point)
    (hsep : ∀ a ∈ A, ∀ y ∈ Y, ∀ a' ∈ A, ∀ y' ∈ Y,
      translatedCrossSqDist t a y = translatedCrossSqDist t a' y' →
        crossDisplacement a y = crossDisplacement a' y')
    (d : ℝ) :
    (crossDistanceFiber A Y t d).card ≤ A.card := by
  let F := crossDistanceFiber A Y t d
  have hinj : Set.InjOn Prod.fst (F : Set (Point × Point)) := by
    intro ay hay ay' hay' hab
    have hayMem := Finset.mem_filter.mp hay
    have hayMem' := Finset.mem_filter.mp hay'
    have hayProd := Finset.mem_product.mp hayMem.1
    have hayProd' := Finset.mem_product.mp hayMem'.1
    have hdist : translatedCrossSqDist t ay.1 ay.2 =
        translatedCrossSqDist t ay'.1 ay'.2 := hayMem.2.trans hayMem'.2.symm
    have hdisp := hsep ay.1 hayProd.1 ay.2 hayProd.2
      ay'.1 hayProd'.1 ay'.2 hayProd'.2 hdist
    apply Prod.ext hab
    have hfirst : ay.1 = ay'.1 := hab
    apply Prod.ext
    · have hx := congrArg Prod.fst hdisp
      dsimp [crossDisplacement] at hx
      have hfx := congrArg Prod.fst hfirst
      nlinarith
    · have hy := congrArg Prod.snd hdisp
      dsimp [crossDisplacement] at hy
      have hfy := congrArg Prod.snd hfirst
      nlinarith
  have hcardImage : F.card = (F.image Prod.fst).card :=
    (Finset.card_image_iff.mpr hinj).symm
  have hsub : F.image Prod.fst ⊆ A := by
    intro a ha
    rcases Finset.mem_image.mp ha with ⟨ay, hay, rfl⟩
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hay).1).1
  change F.card ≤ A.card
  rw [hcardImage]
  exact Finset.card_le_card hsub

end Erdos959
