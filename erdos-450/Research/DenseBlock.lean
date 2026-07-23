import Research.Basic

namespace Erdos450

/-- A translate immediately to the right of `(2n)! + n` is completely filled
with integers having a divisor in `(n,2n)`, up to length `n`. -/
theorem dense_factorial_translate (n y : ℕ) (hy : y ≤ n) :
    localCount n (Nat.factorial (2 * n) + n) y = y - 1 := by
  classical
  unfold localCount badIntegers
  rw [Finset.card_filter_eq_iff.mpr]
  · rw [Nat.card_Ioo]
    omega
  · intro m hm
    rw [Finset.mem_Ioo] at hm
    let k := m - (Nat.factorial (2 * n) + n)
    have hkpos : 0 < k := Nat.sub_pos_of_lt hm.1
    have hklt : k < y := by
      dsimp [k]
      omega
    have hmk : Nat.factorial (2 * n) + n + k = m := by
      dsimp [k]
      omega
    refine ⟨n + k, by omega, by omega, ?_⟩
    have hd : n + k ∣ Nat.factorial (2 * n) :=
      Nat.dvd_factorial (by omega) (by omega)
    have hs : n + k ∣ Nat.factorial (2 * n) + (n + k) :=
      dvd_add hd (dvd_refl (n + k))
    rw [← hmk]
    simpa [Nat.add_assoc] using hs

/-- Consequently, any uniform estimate at a length `y ≤ n` must at least
accommodate the density `(y-1)/y` of this explicit translate. -/
theorem uniform_sparse_forces_dense_block_bound (ε : ℝ) (n y : ℕ)
    (hy : y ≤ n) (h : UniformlySparse ε n y) :
    (y - 1 : ℕ) ≤ ε * (y : ℝ) := by
  have hx := h (Nat.factorial (2 * n) + n)
  rw [dense_factorial_translate n y hy] at hx
  exact_mod_cast hx

/-- Negative-space form: if `εy < y-1` and `y ≤ n`, the requested uniform
bound is impossible. -/
theorem not_uniformlySparse_of_lt_dense_block (ε : ℝ) (n y : ℕ)
    (hy : y ≤ n) (hε : ε * (y : ℝ) < (y - 1 : ℕ)) :
    ¬ UniformlySparse ε n y := by
  intro h
  have hb := uniform_sparse_forces_dense_block_bound ε n y hy h
  exact (not_lt_of_ge hb) hε

end Erdos450
