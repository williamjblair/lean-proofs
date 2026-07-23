import Research.OrderedUnordered

noncomputable section
namespace Erdos959

lemma sqDist_pos_of_ne (a b : Point) (hab : a ≠ b) : 0 < sqDist a b := by
  have hc : a.1 ≠ b.1 ∨ a.2 ≠ b.2 := by
    contrapose! hab
    exact Prod.ext hab.1 hab.2
  dsimp [sqDist]
  rcases hc with hx | hy
  · have hs : 0 < (a.1 - b.1) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hx)
    nlinarith [sq_nonneg (a.2 - b.2)]
  · have hs : 0 < (a.2 - b.2) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hy)
    nlinarith [sq_nonneg (a.1 - b.1)]

/-- Four distinct planar points cannot be pairwise equidistant. -/
lemma four_points_not_all_equidistant
    (a b c e : Point)
    (hab : a ≠ b)
    (hU : sqDist a c = sqDist a b)
    (hW : sqDist a e = sqDist a b)
    (hBC : sqDist b c = sqDist a b)
    (hBE : sqDist b e = sqDist a b)
    (hCE : sqDist c e = sqDist a b) : False := by
  let ux := b.1 - a.1
  let uy := b.2 - a.2
  let vx := c.1 - a.1
  let vy := c.2 - a.2
  let wx := e.1 - a.1
  let wy := e.2 - a.2
  let U := ux ^ 2 + uy ^ 2
  let V := vx ^ 2 + vy ^ 2
  let W := wx ^ 2 + wy ^ 2
  let UV := ux * vx + uy * vy
  let UW := ux * wx + uy * wy
  let VW := vx * wx + vy * wy
  let r := sqDist a b
  have hUr : U = r := by dsimp [U, ux, uy, r, sqDist]; ring
  have hVr : V = r := by
    dsimp [V, vx, vy, r, sqDist] at hU ⊢
    nlinarith
  have hWr : W = r := by
    dsimp [W, wx, wy, r, sqDist] at hW ⊢
    nlinarith
  have hUVr : 2 * UV = r := by
    dsimp [UV, ux, uy, vx, vy, r, sqDist] at hBC hU ⊢
    nlinarith
  have hUWr : 2 * UW = r := by
    dsimp [UW, ux, uy, wx, wy, r, sqDist] at hBE hW ⊢
    nlinarith
  have hVWr : 2 * VW = r := by
    dsimp [VW, vx, vy, wx, wy, r, sqDist] at hCE hU hW ⊢
    nlinarith
  have hGram :
      (2 * U) * (2 * V) * (2 * W) +
          2 * (2 * UV) * (2 * UW) * (2 * VW) =
        (2 * U) * (2 * VW) ^ 2 +
          (2 * V) * (2 * UW) ^ 2 +
          (2 * W) * (2 * UV) ^ 2 := by
    dsimp [U, V, W, UV, UW, VW]
    ring
  rw [hUr, hVr, hWr, hUVr, hUWr, hVWr] at hGram
  have hrpos : 0 < r := sqDist_pos_of_ne a b hab
  have hcube : 0 < r ^ 3 := pow_pos hrpos 3
  nlinarith

lemma indexPair_mem_distanceValues {n : ℕ} (P : Fin n → Point)
    {i j : Fin n} (hij : i < j) :
    sqDist (P i) (P j) ∈ distanceValues P := by
  apply Finset.mem_image.mpr
  exact ⟨(i, j), by simp [indexPairs, hij], rfl⟩

/-- Every injective planar configuration of at least four points determines at
least two distances. -/
lemma distanceValues_card_ge_two_of_four_le
    {n : ℕ} (hn : 4 ≤ n) (P : Fin n → Point) (hP : Function.Injective P) :
    2 ≤ (distanceValues P).card := by
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  let i2 : Fin n := ⟨2, by omega⟩
  let i3 : Fin n := ⟨3, by omega⟩
  have h01 : i0 < i1 := by simp [i0, i1]
  have h02 : i0 < i2 := by simp [i0, i2]
  have h03 : i0 < i3 := by simp [i0, i3]
  have h12 : i1 < i2 := by simp [i1, i2]
  have h13 : i1 < i3 := by simp [i1, i3]
  have h23 : i2 < i3 := by simp [i2, i3]
  by_contra hcard
  have hle : (distanceValues P).card ≤ 1 := by omega
  have hall := Finset.card_le_one.mp hle
  have hm01 := indexPair_mem_distanceValues P h01
  have hm02 := indexPair_mem_distanceValues P h02
  have hm03 := indexPair_mem_distanceValues P h03
  have hm12 := indexPair_mem_distanceValues P h12
  have hm13 := indexPair_mem_distanceValues P h13
  have hm23 := indexPair_mem_distanceValues P h23
  have hab : P i0 ≠ P i1 := fun heq => (ne_of_lt h01) (hP heq)
  exact four_points_not_all_equidistant (P i0) (P i1) (P i2) (P i3) hab
    (hall _ hm02 _ hm01) (hall _ hm03 _ hm01)
    (hall _ hm12 _ hm01) (hall _ hm13 _ hm01) (hall _ hm23 _ hm01)

lemma enumerateFinset_admissible_of_four_le
    (Y : Finset Point) (hY : 4 ≤ Y.card) :
    Admissible (enumerateFinset Y) := by
  exact ⟨enumerateFinset_injective Y,
    distanceValues_card_ge_two_of_four_le hY _ (enumerateFinset_injective Y)⟩

end Erdos959
