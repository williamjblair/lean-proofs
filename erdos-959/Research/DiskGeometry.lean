import Research.Basic

noncomputable section
namespace Erdos959

/-- Squared Euclidean norm in the Cartesian model used for the problem. -/
def normSq (p : Point) : ℝ := p.1 ^ 2 + p.2 ^ 2

lemma sqDist_le_four_mul_sq
    (p q : Point) (R : ℝ)
    (hp : normSq p ≤ R ^ 2) (hq : normSq q ≤ R ^ 2) :
    sqDist p q ≤ 4 * R ^ 2 := by
  dsimp [normSq] at hp hq
  dsimp [sqDist]
  nlinarith [sq_nonneg (p.1 + q.1), sq_nonneg (p.2 + q.2)]

lemma disk_distance_ratio_lt_two
    (p q : Point) (R s : ℝ)
    (hp : normSq p ≤ R ^ 2) (hq : normSq q ≤ R ^ 2)
    (hs : 2 * R ^ 2 < s) :
    sqDist p q < 2 * s := by
  have hd := sqDist_le_four_mul_sq p q R hp hq
  nlinarith

/-- If a displacement vector has length at most `3R/2`, then the intersection
of the two radius-`R` disks whose centers differ by that vector contains the
radius-`R/4` disk centered at their midpoint.  This squared-coordinate version
avoids all square-root side conditions. -/
lemma lens_contains_quarter_disk
    (w v : Point) (R : ℝ)
    (hw : normSq w ≤ (R / 4) ^ 2)
    (hv : normSq v ≤ (3 * R / 2) ^ 2) :
    normSq (w.1 - v.1 / 2, w.2 - v.2 / 2) ≤ R ^ 2 ∧
    normSq (w.1 + v.1 / 2, w.2 + v.2 / 2) ≤ R ^ 2 := by
  dsimp [normSq] at hw hv ⊢
  constructor
  · nlinarith [sq_nonneg (3 * w.1 + v.1 / 2),
      sq_nonneg (3 * w.2 + v.2 / 2)]
  · nlinarith [sq_nonneg (3 * w.1 - v.1 / 2),
      sq_nonneg (3 * w.2 - v.2 / 2)]

/-- The axis-parallel box of half-side `R/8` lies in the radius-`R/4` disk. -/
lemma eighth_box_subset_quarter_disk
    (w : Point) (R : ℝ) (hR : 0 ≤ R)
    (hx : |w.1| ≤ R / 8) (hy : |w.2| ≤ R / 8) :
    normSq w ≤ (R / 4) ^ 2 := by
  rw [abs_le] at hx hy
  dsimp [normSq]
  nlinarith [sq_nonneg (w.1 - R / 8), sq_nonneg (w.1 + R / 8),
    sq_nonneg (w.2 - R / 8), sq_nonneg (w.2 + R / 8)]

/-- A midpoint/displacement parametrization really has squared separation
`normSq v`; this connects the lens lemma to distance frequencies. -/
lemma sqDist_midpoint_endpoints (w v : Point) :
    sqDist (w.1 - v.1 / 2, w.2 - v.2 / 2)
      (w.1 + v.1 / 2, w.2 + v.2 / 2) = normSq v := by
  dsimp [sqDist, normSq]
  ring

end Erdos959
