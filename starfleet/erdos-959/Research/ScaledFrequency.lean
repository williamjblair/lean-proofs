import Research.ListPlacement
import Research.ScaledBlock

noncomputable section
namespace Erdos959

/-- A finite lattice disk scaled so target squared norm `s` becomes one. -/
def scaledLatticeBlock (s R : ℕ) : Finset Point :=
  (latticeDisk R).image (scaledIntPoint s)

lemma scaledIntPoint_injective {s : ℕ} (hs : 1 ≤ s) :
    Function.Injective (scaledIntPoint s) := by
  intro x y h
  have hsqrt : Real.sqrt (s : ℝ) ≠ 0 := sqrt_nat_ne_zero hs
  apply Prod.ext
  · have hx := congrArg Prod.fst h
    dsimp [scaledIntPoint] at hx
    have : (x.1 : ℝ) = (y.1 : ℝ) := (div_left_inj' hsqrt).mp hx
    exact_mod_cast this
  · have hy := congrArg Prod.snd h
    dsimp [scaledIntPoint] at hy
    have : (x.2 : ℝ) = (y.2 : ℝ) := (div_left_inj' hsqrt).mp hy
    exact_mod_cast this

lemma card_scaledLatticeBlock {s : ℕ} (hs : 1 ≤ s) (R : ℕ) :
    (scaledLatticeBlock s R).card = (latticeDisk R).card := by
  exact Finset.card_image_of_injective _ (scaledIntPoint_injective hs)

lemma intNormSq_sub_comm (x y : IntPoint) :
    intNormSq (x - y) = intNormSq (y - x) := by
  dsimp [intNormSq]
  ring

lemma sqDist_scaledIntPoint_ordered {s : ℕ} (hs : 1 ≤ s)
    (x y : IntPoint) :
    sqDist (scaledIntPoint s x) (scaledIntPoint s y) =
      (intNormSq (y - x) : ℝ) / s := by
  rw [sqDist_scaledIntPoint hs, intNormSq_sub_comm]

lemma scaled_ordered_fiber_card
    {s : ℕ} (hs : 1 ≤ s) (R t : ℕ) :
    (orderedRealDistancePairs (scaledLatticeBlock s R) ((t : ℝ) / s)).card =
      (orderedDistancePairs (latticeDisk R) t).card := by
  let f : IntPoint × IntPoint → Point × Point := fun xy =>
    (scaledIntPoint s xy.1, scaledIntPoint s xy.2)
  have hf : Function.Injective f := by
    intro xy uv h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    dsimp [f] at h1 h2
    exact Prod.ext ((scaledIntPoint_injective hs) h1)
      ((scaledIntPoint_injective hs) h2)
  let I := (orderedDistancePairs (latticeDisk R) t).image f
  have hcard : I.card = (orderedDistancePairs (latticeDisk R) t).card :=
    Finset.card_image_of_injective _ hf
  have hI : I = orderedRealDistancePairs (scaledLatticeBlock s R) ((t : ℝ) / s) := by
    ext uv
    constructor
    · intro huv
      rcases Finset.mem_image.mp huv with ⟨xy, hxy, rfl⟩
      have hm := (mem_orderedDistancePairs_iff xy.1 xy.2).mp hxy
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_product.mpr
        ⟨Finset.mem_image.mpr ⟨xy.1, hm.1, rfl⟩,
         Finset.mem_image.mpr ⟨xy.2, hm.2.1, rfl⟩⟩,
        fun heq => hm.2.2.1 ((scaledIntPoint_injective hs) heq), by
          rw [sqDist_scaledIntPoint_ordered hs]
          have hcast : (intNormSq (xy.2 - xy.1) : ℝ) = (t : ℝ) := by
            exact_mod_cast hm.2.2.2
          rw [hcast]⟩
    · intro huv
      have hm := Finset.mem_filter.mp huv
      have hp := Finset.mem_product.mp hm.1
      rcases Finset.mem_image.mp hp.1 with ⟨x, hx, hxu⟩
      rcases Finset.mem_image.mp hp.2 with ⟨y, hy, hyv⟩
      have hratio : (intNormSq (y - x) : ℝ) / s = (t : ℝ) / s := by
        rw [← sqDist_scaledIntPoint_ordered hs, hxu, hyv]
        exact hm.2.2
      have hnormR : (intNormSq (y - x) : ℝ) = t := by
        exact (div_left_inj' (by positivity : (s : ℝ) ≠ 0)).mp hratio
      have hnorm : intNormSq (y - x) = t := by exact_mod_cast hnormR
      apply Finset.mem_image.mpr
      refine ⟨(x, y), ?_, Prod.ext hxu hyv⟩
      apply (mem_orderedDistancePairs_iff x y).mpr
      exact ⟨hx, hy, fun hxy => hm.2.1 (by rw [← hxu, ← hyv, hxy]), hnorm⟩
  rw [← hI, hcard]

lemma scaled_target_fiber_card
    {s : ℕ} (hs : 1 ≤ s) (R : ℕ) :
    (orderedRealDistancePairs (scaledLatticeBlock s R) 1).card =
      (orderedDistancePairs (latticeDisk R) s).card := by
  have hone : ((s : ℝ) / s) = 1 := div_self (by positivity)
  rw [← hone]
  exact scaled_ordered_fiber_card hs R s

end Erdos959
