import Research.Grid

/-!
# Substitution of one cubical tiling into a tile

This formalizes the basic count operation used by all numerical-semigroup
upper bounds: replacing one tile in a `k`-tiling by a scaled `m`-tiling gives
a `k + m - 1` tiling.
-/

namespace Erdos769

/-- Affinely scale a unit-cube tile into an outer cube. -/
noncomputable def Cube.embed {n : ℕ} (outer inner : Cube n) : Cube n where
  lower j := outer.lower j + outer.side * inner.lower j
  side := outer.side * inner.side

/-- Coordinates of a point after normalizing an outer cube to the unit cube. -/
noncomputable def Cube.normalize {n : ℕ} (outer : Cube n) (x : Fin n → ℝ) :
    Fin n → ℝ := fun j => (x j - outer.lower j) / outer.side

lemma Cube.embed_mem_iff_normalize_mem {n : ℕ} {outer inner : Cube n}
    (hs : 0 < outer.side) (x : Fin n → ℝ) :
    (outer.embed inner).Mem x ↔ inner.Mem (outer.normalize x) := by
  constructor
  · intro h j
    have hj := h j
    dsimp [Cube.embed, Cube.normalize] at hj ⊢
    constructor
    · rw [le_div_iff₀ hs]
      nlinarith [hj.1]
    · rw [div_lt_iff₀ hs]
      nlinarith [hj.2]
  · intro h j
    have hj := h j
    dsimp [Cube.embed, Cube.normalize] at hj ⊢
    constructor
    · rw [le_div_iff₀ hs] at hj
      nlinarith [hj.1]
    · rw [div_lt_iff₀ hs] at hj
      nlinarith [hj.2]

lemma Cube.normalize_inUnit {n : ℕ} {outer : Cube n} {x : Fin n → ℝ}
    (ho : outer.InsideUnit) (hx : outer.Mem x) :
    InUnit (outer.normalize x) := by
  intro j
  have hs := ho.1
  have hj := hx j
  dsimp [Cube.normalize]
  constructor
  · exact div_nonneg (sub_nonneg.mpr hj.1) hs.le
  · rw [div_lt_one hs]
    nlinarith [hj.2]

lemma Cube.embed_inside {n : ℕ} {outer inner : Cube n}
    (ho : outer.InsideUnit) (hi : inner.InsideUnit) :
    (outer.embed inner).InsideUnit := by
  constructor
  · dsimp [Cube.embed]
    exact mul_pos ho.1 hi.1
  · intro j
    have hos := ho.1
    have his := hi.1
    have hoj := ho.2 j
    have hij := hi.2 j
    dsimp [Cube.embed]
    constructor
    · nlinarith [mul_nonneg hos.le hij.1]
    · have hmul : outer.side * (inner.lower j + inner.side) ≤ outer.side := by
        nlinarith [mul_le_mul_of_nonneg_left hij.2 hos.le]
      nlinarith [hoj.2]

lemma Cube.embed_mem_outer {n : ℕ} {outer inner : Cube n} {x : Fin n → ℝ}
    (ho : outer.InsideUnit) (hi : inner.InsideUnit)
    (hx : (outer.embed inner).Mem x) : outer.Mem x := by
  intro j
  have hos := ho.1
  have hij := hi.2 j
  have hxj := hx j
  dsimp [Cube.embed] at hxj
  constructor
  · nlinarith [mul_nonneg hos.le hij.1]
  · have hmul : outer.side * (inner.lower j + inner.side) ≤ outer.side := by
      nlinarith [mul_le_mul_of_nonneg_left hij.2 hos.le]
    nlinarith [hxj.2]

/-- Replacing a selected tile of a `k`-tiling by a scaled copy of an
`m`-tiling gives a `k+m-1` tiling. -/
theorem admissible_substitute {n k m : ℕ}
    (hk : Admissible n k) (hm : Admissible n m) (i0 : Fin k) :
    Admissible n (k + m - 1) := by
  classical
  obtain ⟨outer, houter⟩ := hk
  obtain ⟨inner, hinner⟩ := hm
  let ι := {i : Fin k // i ≠ i0} ⊕ Fin m
  let newTiles : ι → Cube n
    | Sum.inl i => outer i.1
    | Sum.inr b => (outer i0).embed (inner b)
  have hkpos : 0 < k := Nat.zero_lt_of_lt i0.isLt
  apply admissible_of_fintype_tiling (ι := ι) (k := k + m - 1)
      (by dsimp [ι]; simp; omega) newTiles
  · intro z
    cases z with
    | inl i =>
        exact houter.1 i.1
    | inr b =>
        exact Cube.embed_inside (houter.1 i0) (hinner.1 b)
  · intro x hx
    obtain ⟨i, hi, hui⟩ := houter.2 x hx
    by_cases hio : i = i0
    · subst i
      let y := (outer i0).normalize x
      have hy : InUnit y := Cube.normalize_inUnit (houter.1 i0) hi
      obtain ⟨b, hb, hub⟩ := hinner.2 y hy
      refine ⟨Sum.inr b, ?_, ?_⟩
      · exact (Cube.embed_mem_iff_normalize_mem (houter.1 i0).1 x).2 hb
      · intro z hz
        cases z with
        | inl a =>
            have haold : (outer a.1).Mem x := hz
            have hae : a.1 = i0 := hui a.1 haold
            exact (a.2 hae).elim
        | inr b' =>
            have hb' : (inner b').Mem y :=
              (Cube.embed_mem_iff_normalize_mem (houter.1 i0).1 x).1 hz
            have hbe : b' = b := hub b' hb'
            simp [hbe]
    · let a : {i : Fin k // i ≠ i0} := ⟨i, hio⟩
      refine ⟨Sum.inl a, hi, ?_⟩
      intro z hz
      cases z with
      | inl a' =>
          have haold : (outer a'.1).Mem x := hz
          have hae : a'.1 = i := hui a'.1 haold
          have hasub : a' = a := Subtype.ext hae
          simp [hasub]
      | inr b =>
          have hbold : (outer i0).Mem x :=
            Cube.embed_mem_outer (houter.1 i0) (hinner.1 b) hz
          have hbe : i0 = i := hui i0 hbold
          exact (hio hbe.symm).elim

/-- In particular, substituting a regular base-`m` grid increases the count by
exactly `m^n-1`. -/
theorem admissible_add_regular_increment {n k m : ℕ}
    (hk : Admissible n k) (i0 : Fin k) (hm : 0 < m) :
    Admissible n (k + (m ^ n - 1)) := by
  have hs := admissible_substitute hk (regularGrid_admissible n m hm) i0
  convert hs using 1 <;> have hp : 0 < m ^ n := pow_pos hm n <;> omega

end Erdos769
