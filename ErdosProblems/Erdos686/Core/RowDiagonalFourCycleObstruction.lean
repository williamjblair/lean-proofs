/- leanprover/lean4:v4.29.1 mathlib v4.29.1 -/
import ErdosProblems.Erdos686.Core.RowDiagonalFourCycle

/-!
# Erdős 686: exact obstruction to four-cycle globalization

For every `k >= 3` this file constructs a row/signed-diagonal incidence
support which is one cycle of length `2*k`.  Every row has degree two and
every used signed diagonal has degree two, but no two distinct rows share
both of their diagonals.  Thus degree or multiplicative diffuseness alone
cannot supply any positive packing of the four-cycles used by the local
secant-or-crowding theorem.
-/

namespace Erdos686
namespace Erdos686Variant

/-- Predecessor in the cyclic order `1, ..., k`. -/
def longCyclePrev (k j : ℕ) : ℕ :=
  if j = 1 then k else j - 1

/-- Successor in the cyclic order `1, ..., k`. -/
def longCycleNext (k j : ℕ) : ℕ :=
  if j = k then 1 else j + 1

/-- The `k` distinct signed diagonals used by the long-cycle support.

For `1 <= t <= k-2` the offset is `k-t-1`; the last two offsets are
`2-k` and `0`. -/
def longCycleOffset (k t : ℕ) : ℤ :=
  if t = k then 0
  else if t = k - 1 then 2 - (k : ℤ)
  else (k : ℤ) - (t : ℤ) - 1

/-- The two signed diagonals incident to row `j` in the long cycle. -/
def longCycleRowOffsets (k j : ℕ) : Finset ℤ :=
  {longCycleOffset k j, longCycleOffset k (longCyclePrev k j)}

/-- Rows incident to a given signed offset. -/
def longCycleRowsAtOffset (k : ℕ) (rho : ℤ) : Finset ℕ :=
  (Finset.Icc 1 k).filter (fun j => rho ∈ longCycleRowOffsets k j)

private theorem longCyclePrev_mem
    {k j : ℕ} (hk : 3 <= k) (hj : j ∈ Finset.Icc 1 k) :
    longCyclePrev k j ∈ Finset.Icc 1 k := by
  simp only [Finset.mem_Icc] at hj ⊢
  unfold longCyclePrev
  split <;> omega

private theorem longCycleNext_mem
    {k j : ℕ} (hk : 3 <= k) (hj : j ∈ Finset.Icc 1 k) :
    longCycleNext k j ∈ Finset.Icc 1 k := by
  simp only [Finset.mem_Icc] at hj ⊢
  unfold longCycleNext
  split <;> omega

private theorem longCyclePrev_ne
    {k j : ℕ} (hk : 3 <= k) (hj : j ∈ Finset.Icc 1 k) :
    longCyclePrev k j ≠ j := by
  simp only [Finset.mem_Icc] at hj
  unfold longCyclePrev
  split <;> omega

private theorem longCycleNext_ne
    {k j : ℕ} (hk : 3 <= k) :
    longCycleNext k j ≠ j := by
  unfold longCycleNext
  split <;> omega

private theorem longCyclePrev_next
    {k j : ℕ} (hk : 3 <= k) (hj : j ∈ Finset.Icc 1 k) :
    longCyclePrev k (longCycleNext k j) = j := by
  simp only [Finset.mem_Icc] at hj
  unfold longCyclePrev longCycleNext
  split <;> split <;> omega

private theorem longCycleNext_prev
    {k j : ℕ} (hj : j ∈ Finset.Icc 1 k) :
    longCycleNext k (longCyclePrev k j) = j := by
  simp only [Finset.mem_Icc] at hj
  unfold longCyclePrev longCycleNext
  split <;> split <;> omega

private theorem longCycleNext_ne_prev
    {k j : ℕ} (hk : 3 <= k) (hj : j ∈ Finset.Icc 1 k) :
    longCycleNext k j ≠ longCyclePrev k j := by
  simp only [Finset.mem_Icc] at hj
  unfold longCyclePrev longCycleNext
  split <;> split <;> omega

/-- The displayed signed offsets are pairwise distinct. -/
theorem longCycleOffset_injective
    {k a b : ℕ} (hk : 3 <= k)
    (ha : a ∈ Finset.Icc 1 k) (hb : b ∈ Finset.Icc 1 k)
    (hoff : longCycleOffset k a = longCycleOffset k b) :
    a = b := by
  simp only [Finset.mem_Icc] at ha hb
  by_cases haK : a = k <;> by_cases haKm : a = k - 1 <;>
    by_cases hbK : b = k <;> by_cases hbKm : b = k - 1
  all_goals simp [longCycleOffset, haK, haKm, hbK, hbKm] at hoff
  all_goals omega

private theorem longCycleOffset_endpoint_cells
    {k t : ℕ} (hk : 3 <= k) (ht : t ∈ Finset.Icc 1 k) :
    ∃ i₁ ∈ Finset.Icc 1 k, ∃ i₂ ∈ Finset.Icc 1 k,
      ownerDiagonalOffset i₁ t = longCycleOffset k t ∧
        ownerDiagonalOffset i₂ (longCycleNext k t) =
          longCycleOffset k t := by
  have ht' := Finset.mem_Icc.mp ht
  by_cases htK : t = k
  · subst t
    refine ⟨k, ht, 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    simp [ownerDiagonalOffset, longCycleOffset, longCycleNext]
  · by_cases htKm : t = k - 1
    · subst t
      refine ⟨1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
        2, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
      simp [ownerDiagonalOffset, longCycleOffset, longCycleNext]
      omega
    · refine ⟨k - 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
        k, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
      simp [ownerDiagonalOffset, longCycleOffset, longCycleNext, htK, htKm]
      omega

/-- Every incidence in the long-cycle row/offset model is realized by an
actual cell of the `k x k` owner square. -/
theorem longCycleRowOffset_realizable
    {k j : ℕ} (hk : 3 <= k) (hj : j ∈ Finset.Icc 1 k)
    {rho : ℤ} (hrho : rho ∈ longCycleRowOffsets k j) :
    ∃ i ∈ Finset.Icc 1 k, ownerDiagonalOffset i j = rho := by
  simp only [longCycleRowOffsets, Finset.mem_insert,
    Finset.mem_singleton] at hrho
  rcases hrho with rfl | rfl
  · obtain ⟨i, hi, _i', _hi', hfirst, _hsecond⟩ :=
      longCycleOffset_endpoint_cells hk hj
    exact ⟨i, hi, hfirst⟩
  · have hp := longCyclePrev_mem hk hj
    obtain ⟨_i, _hi, i, hi, _hfirst, hsecond⟩ :=
      longCycleOffset_endpoint_cells hk hp
    rw [longCycleNext_prev hj] at hsecond
    exact ⟨i, hi, hsecond⟩

/-- Every row of the explicit long-cycle support has degree exactly two. -/
theorem longCycleRowOffsets_card
    {k j : ℕ} (hk : 3 <= k) (hj : j ∈ Finset.Icc 1 k) :
    (longCycleRowOffsets k j).card = 2 := by
  have hp := longCyclePrev_mem hk hj
  have hne := longCyclePrev_ne hk hj
  have hoff : longCycleOffset k j ≠
      longCycleOffset k (longCyclePrev k j) := by
    intro h
    exact hne (longCycleOffset_injective hk hj hp h).symm
  simp [longCycleRowOffsets, hoff]

private theorem longCycle_offset_mem_row_iff
    {k t j : ℕ} (hk : 3 <= k)
    (ht : t ∈ Finset.Icc 1 k) (hj : j ∈ Finset.Icc 1 k) :
    longCycleOffset k t ∈ longCycleRowOffsets k j <->
      j = t ∨ j = longCycleNext k t := by
  have hpj := longCyclePrev_mem hk hj
  constructor
  · intro h
    simp only [longCycleRowOffsets, Finset.mem_insert,
      Finset.mem_singleton] at h
    rcases h with h | h
    · exact Or.inl (longCycleOffset_injective hk ht hj h).symm
    · have hprev : longCyclePrev k j = t :=
        (longCycleOffset_injective hk ht hpj h).symm
      right
      rw [<- hprev]
      exact (longCycleNext_prev hj).symm
  · intro h
    rcases h with rfl | rfl
    · simp [longCycleRowOffsets]
    · have hn := longCycleNext_mem hk ht
      have hp := longCyclePrev_next hk ht
      simp [longCycleRowOffsets, hp]

/-- The fibre of every used signed offset is exactly its two consecutive
rows. -/
theorem longCycleRowsAtOffset_eq_pair
    {k t : ℕ} (hk : 3 <= k) (ht : t ∈ Finset.Icc 1 k) :
    longCycleRowsAtOffset k (longCycleOffset k t) =
      {t, longCycleNext k t} := by
  ext j
  simp only [longCycleRowsAtOffset, Finset.mem_filter,
    Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    exact (longCycle_offset_mem_row_iff hk ht
      (Finset.mem_Icc.mpr h.1)).mp h.2
  · intro h
    have ht' := Finset.mem_Icc.mp ht
    rcases h with rfl | rfl
    · exact ⟨ht', (longCycle_offset_mem_row_iff hk ht ht).mpr (Or.inl rfl)⟩
    · have hn := longCycleNext_mem hk ht
      exact ⟨Finset.mem_Icc.mp hn,
        (longCycle_offset_mem_row_iff hk ht hn).mpr (Or.inr rfl)⟩

/-- Every used signed diagonal of the explicit support has degree exactly
two. -/
theorem longCycleRowsAtOffset_card
    {k t : ℕ} (hk : 3 <= k) (ht : t ∈ Finset.Icc 1 k) :
    (longCycleRowsAtOffset k (longCycleOffset k t)).card = 2 := by
  rw [longCycleRowsAtOffset_eq_pair hk ht]
  have hne : t ≠ longCycleNext k t := (longCycleNext_ne hk).symm
  simp [hne]

private theorem longCycle_incident_index_mem
    {k j t : ℕ} (hk : 3 <= k)
    (hj : j ∈ Finset.Icc 1 k) (ht : t ∈ Finset.Icc 1 k)
    (h : longCycleOffset k t ∈ longCycleRowOffsets k j) :
    t = j ∨ t = longCyclePrev k j := by
  simp only [longCycleRowOffsets, Finset.mem_insert,
    Finset.mem_singleton] at h
  have hp := longCyclePrev_mem hk hj
  rcases h with h | h
  · exact Or.inl (longCycleOffset_injective hk ht hj h)
  · exact Or.inr (longCycleOffset_injective hk ht hp h)

/-- Two distinct rows never share two distinct signed offsets.  This is the
exact absence of a row/diagonal four-cycle. -/
theorem longCycle_no_four_cycle
    {k j l : ℕ} (hk : 3 <= k)
    (hj : j ∈ Finset.Icc 1 k) (hl : l ∈ Finset.Icc 1 k)
    (hjl : j ≠ l)
    {rho sigma : ℤ}
    (hrhoj : rho ∈ longCycleRowOffsets k j)
    (hrhol : rho ∈ longCycleRowOffsets k l)
    (hsigmaj : sigma ∈ longCycleRowOffsets k j)
    (hsigmal : sigma ∈ longCycleRowOffsets k l) :
    rho = sigma := by
  have hpj := longCyclePrev_mem hk hj
  have hpl := longCyclePrev_mem hk hl
  have classify : ∀ {x : ℤ},
      x ∈ longCycleRowOffsets k j ->
      x ∈ longCycleRowOffsets k l ->
      (j = longCyclePrev k l ∧ x = longCycleOffset k j) ∨
        (longCyclePrev k j = l ∧
          x = longCycleOffset k (longCyclePrev k j)) := by
    intro x hxj hxl
    simp only [longCycleRowOffsets, Finset.mem_insert,
      Finset.mem_singleton] at hxj hxl
    rcases hxj with hxj | hxj <;> rcases hxl with hxl | hxl
    · exfalso
      apply hjl
      exact longCycleOffset_injective hk hj hl (hxj.symm.trans hxl)
    · left
      exact ⟨longCycleOffset_injective hk hj hpl (hxj.symm.trans hxl), hxj⟩
    · right
      exact ⟨longCycleOffset_injective hk hpj hl (hxj.symm.trans hxl), hxj⟩
    · exfalso
      apply hjl
      have hpEq := longCycleOffset_injective hk hpj hpl (hxj.symm.trans hxl)
      calc
        j = longCycleNext k (longCyclePrev k j) :=
          (longCycleNext_prev hj).symm
        _ = longCycleNext k (longCyclePrev k l) := by rw [hpEq]
        _ = l := longCycleNext_prev hl
  rcases classify hrhoj hrhol with hrho | hrho <;>
    rcases classify hsigmaj hsigmal with hsigma | hsigma
  · exact hrho.2.trans hsigma.2.symm
  · exfalso
    have hnext : longCycleNext k j = l := by
      rw [hrho.1]
      exact longCycleNext_prev hl
    exact longCycleNext_ne_prev hk hj (hnext.trans hsigma.1.symm)
  · exfalso
    have hnext : longCycleNext k j = l := by
      rw [hsigma.1]
      exact longCycleNext_prev hl
    exact longCycleNext_ne_prev hk hj (hnext.trans hrho.1.symm)
  · exact hrho.2.trans hsigma.2.symm

#print axioms longCycleOffset_injective
#print axioms longCycleRowOffset_realizable
#print axioms longCycleRowOffsets_card
#print axioms longCycleRowsAtOffset_eq_pair
#print axioms longCycleRowsAtOffset_card
#print axioms longCycle_no_four_cycle

end Erdos686Variant
end Erdos686
