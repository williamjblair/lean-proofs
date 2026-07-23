import Research.Erdos769

/-!
# Regular cubical grids

A direct construction, in the canonical half-open model, of the regular
`m^n`-tile grid of the unit `n`-cube.
-/

namespace Erdos769

/-- Reindex a tiling carried by any finite type into the canonical `Fin k`
indexing used by `Admissible`. -/
theorem admissible_of_fintype_tiling {n k : ℕ} {ι : Type*} [Fintype ι]
    (hcard : Fintype.card ι = k) (tiles : ι → Cube n)
    (hinside : ∀ i, (tiles i).InsideUnit)
    (hcover : ∀ x, InUnit x → ∃! i, (tiles i).Mem x) :
    Admissible n k := by
  classical
  let e : ι ≃ Fin k := (Fintype.equivFin ι).trans (finCongr hcard)
  refine ⟨fun i => tiles (e.symm i), ?_⟩
  constructor
  · intro i
    exact hinside (e.symm i)
  · intro x hx
    obtain ⟨i, hi, hui⟩ := hcover x hx
    refine ⟨e i, ?_, ?_⟩
    · simpa [e] using hi
    · intro j hj
      have heq : e.symm j = i := hui (e.symm j) (by simpa [e] using hj)
      apply e.symm.injective
      simpa using heq

/-- The cube in position `q` of the regular base-`m` grid. -/
noncomputable def regularGridCube {n m : ℕ} (q : Fin n → Fin m) : Cube n where
  lower j := (q j : ℝ) / m
  side := 1 / (m : ℝ)

/-- Every positive-base regular grid is an exact canonical tiling. -/
theorem regularGrid_admissible (n m : ℕ) (hm : 0 < m) :
    Admissible n (m ^ n) := by
  classical
  let tiles : (Fin n → Fin m) → Cube n := regularGridCube
  apply admissible_of_fintype_tiling (ι := Fin n → Fin m)
      (k := m ^ n) (by simp) tiles
  · intro q
    constructor
    · dsimp [tiles, regularGridCube]
      positivity
    · intro j
      dsimp [tiles, regularGridCube]
      constructor
      · positivity
      · have hq : (q j : ℕ) + 1 ≤ m := q j |>.isLt
        have hmR : (0 : ℝ) < m := by exact_mod_cast hm
        rw [← add_div]
        rw [div_le_one hmR]
        exact_mod_cast hq
  · intro x hx
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    let q : Fin n → Fin m := fun j =>
      ⟨⌊(m : ℝ) * x j⌋₊, (Nat.floor_lt (mul_nonneg hmR.le (hx j).1)).2 <| by
        nlinarith [(hx j).2]⟩
    have hqmem : (tiles q).Mem x := by
      intro j
      have hmx0 : (0 : ℝ) ≤ (m : ℝ) * x j := mul_nonneg hmR.le (hx j).1
      have hf := (Nat.floor_eq_iff hmx0).1 rfl
      dsimp [tiles, regularGridCube]
      constructor <;> (field_simp; nlinarith [hf.1, hf.2])
    refine ⟨q, hqmem, ?_⟩
    intro r hr
    funext j
    apply Fin.ext
    change (r j : ℕ) = ⌊(m : ℝ) * x j⌋₊
    symm
    have hmx0 : (0 : ℝ) ≤ (m : ℝ) * x j := mul_nonneg hmR.le (hx j).1
    apply (Nat.floor_eq_iff hmx0).2
    have hrj := hr j
    dsimp [tiles, regularGridCube] at hrj
    constructor <;> (field_simp at hrj ⊢; nlinarith [hrj.1, hrj.2])

end Erdos769
