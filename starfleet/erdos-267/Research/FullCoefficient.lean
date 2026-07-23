import Research.CoefficientBlock

/-!
# The finite full Lambert coefficient at a fixed exponent
-/

namespace Research

open scoped BigOperators

/-- A nonzero contribution at exponent `m` can only come from an index at most
`m`. -/
theorem fibLambertCoeff_index_le_of_ne_zero
    (n m : ℕ) (_hn : 0 < n) (h : fibLambertCoeff n m ≠ 0) :
    n ≤ m := by
  unfold fibLambertCoeff at h
  split_ifs at h with he h₂ h₄ h₄' <;> try contradiction
  · have hm := Nat.mod_le m (2 * n)
    omega
  · have hm := Nat.mod_le m (4 * n)
    omega
  · have hm := Nat.mod_le m (4 * n)
    omega

/-- Positive strict index sequences dominate their position by at least one. -/
theorem position_add_one_le_index
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n) (k : ℕ) :
    k + 1 ≤ n k := by
  have h := hmono.add_le_nat k 0
  have h0 := hpos 0
  simp only [add_zero] at h
  omega

/-- Terms whose sequence position is at least the exponent contribute zero. -/
theorem fibLambertCoeff_eq_zero_of_exponent_le_position
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    {m k : ℕ} (hmk : m ≤ k) :
    fibLambertCoeff (n k) m = 0 := by
  by_contra hne
  have hidx := fibLambertCoeff_index_le_of_ne_zero (n k) m (hpos k) hne
  have hposition := position_add_one_le_index n hpos hmono k
  omega

/-- The full coefficient at exponent `m`; only the first `m` sequence
positions can contribute. -/
def selectedFibLambertCoeff (n : ℕ → ℕ) (m : ℕ) : ℤ :=
  ∑ k ∈ Finset.range m, fibLambertCoeff (n k) m

/-- Any larger finite cutoff computes the same full coefficient. -/
theorem prefixFibLambertCoeff_eq_selected
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    {m K : ℕ} (hmK : m ≤ K) :
    prefixFibLambertCoeff n K m = selectedFibLambertCoeff n m := by
  rw [prefixFibLambertCoeff, selectedFibLambertCoeff]
  rw [← Finset.sum_subset (Finset.range_mono hmK)]
  intro k hkK hkm
  have hmk : m ≤ k := by
    simpa only [Finset.mem_range, not_lt] using hkm
  exact fibLambertCoeff_eq_zero_of_exponent_le_position n hpos hmono hmk

/-- Linear absolute bound for the full coefficient. -/
theorem abs_selectedFibLambertCoeff_le
    (n : ℕ → ℕ) (m : ℕ) :
    |selectedFibLambertCoeff n m| ≤ (m : ℤ) := by
  simpa [selectedFibLambertCoeff, prefixFibLambertCoeff] using
    abs_prefixFibLambertCoeff_le n m m

/-- Under a common-period shift, the prefix contribution to the two full
coefficients agrees exactly; all discrepancy comes from later positions. -/
theorem selectedFibLambertCoeff_shift_prefix_cancel
    (n : ℕ → ℕ) (K X m : ℕ)
    (hperiod : ∀ k < K, 4 * n k ∣ X) :
    prefixFibLambertCoeff n K (m + X) = prefixFibLambertCoeff n K m :=
  prefixFibLambertCoeff_add_commonPeriod n K X hperiod m

end Research
