import Research.ScaledBlock
import Research.BlockRadius

namespace Erdos959

lemma intNormSq_sub_real (x y : IntPoint) :
    (intNormSq (y - x) : ℝ) =
      sqDist (intPointToReal x) (intPointToReal y) := by
  dsimp [intNormSq, sqDist, intPointToReal]
  push_cast
  ring

lemma positive_intNormSq_of_ne (x y : IntPoint) (hxy : x ≠ y) :
    0 < intNormSq (y - x) := by
  have hdiff : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
  dsimp [intNormSq]
  have hcoord : (y.1 - x.1) ≠ 0 ∨ (y.2 - x.2) ≠ 0 := by
    contrapose! hdiff
    exact Prod.ext hdiff.1 hdiff.2
  rcases hcoord with hx | hy
  · have : 0 < (y.1 - x.1) ^ 2 := sq_pos_of_ne_zero hx
    nlinarith [sq_nonneg (y.2 - x.2)]
  · have : 0 < (y.2 - x.2) ^ 2 := sq_pos_of_ne_zero hy
    nlinarith [sq_nonneg (y.1 - x.1)]

lemma block_internal_distance_lt_twice_target
    (s : ℕ) (hs : 2049 ≤ s) (hodd : s % 2 = 1)
    {x y : IntPoint}
    (hx : x ∈ latticeDisk (blockRadius s))
    (hy : y ∈ latticeDisk (blockRadius s))
    {t : ℕ} (ht : intNormSq (y - x) = t) :
    t < 2 * s := by
  have hxr := (mem_latticeDisk_iff x (blockRadius s)).mp hx
  have hyr := (mem_latticeDisk_iff y (blockRadius s)).mp hy
  have hwindow := (blockRadius_real_target_window s hs hodd).1
  have hd := disk_distance_ratio_lt_two (intPointToReal x) (intPointToReal y)
    (blockRadius s) s hxr hyr hwindow
  have htR : (t : ℝ) = sqDist (intPointToReal x) (intPointToReal y) := by
    rw [← intNormSq_sub_real x y]
    exact_mod_cast ht.symm
  rw [← htR] at hd
  exact_mod_cast hd

lemma reduced_block_competitor_bounds
    (s : ℕ) (hs : 2049 ≤ s) (hodd : s % 2 = 1)
    {x y : IntPoint}
    (hx : x ∈ latticeDisk (blockRadius s))
    (hy : y ∈ latticeDisk (blockRadius s))
    (hxy : x ≠ y)
    {t A D : ℕ} (ht : intNormSq (y - x) = t)
    (hD : 1 ≤ D) (href : D * t = A * s) :
    1 ≤ A ∧ A < 2 * D ∧ (t ≠ s → 1 < D) := by
  have htPosInt := positive_intNormSq_of_ne x y hxy
  have htPos : 1 ≤ t := by
    rw [ht] at htPosInt
    exact_mod_cast htPosInt
  have hsPos : 1 ≤ s := by omega
  have hAPos : 1 ≤ A := by
    by_contra h
    have hA0 : A = 0 := by omega
    rw [hA0, zero_mul] at href
    have : 0 < D * t := Nat.mul_pos (by omega) (by omega)
    omega
  have htlt : t < 2 * s := block_internal_distance_lt_twice_target
    s hs hodd hx hy ht
  have hmul : D * t < D * (2 * s) :=
    Nat.mul_lt_mul_of_pos_left htlt (by omega)
  have hAs : A * s < (2 * D) * s := by
    calc
      A * s = D * t := href.symm
      _ < D * (2 * s) := hmul
      _ = (2 * D) * s := by ring
  have hAlt : A < 2 * D := Nat.lt_of_mul_lt_mul_right hAs
  refine ⟨hAPos, hAlt, ?_⟩
  intro hne
  by_contra hnot
  have hDone : D = 1 := by omega
  have hAone : A = 1 := by omega
  rw [hDone, one_mul, hAone, one_mul] at href
  exact hne href

end Erdos959
