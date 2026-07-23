import Research.Cover

/-!
# The nonlocal divisibility-cover example `n_k = 2^k + 1`
-/

namespace Research

open Filter Topology
open scoped BigOperators

/-- The geometric sum of powers of two in natural arithmetic. -/
theorem sum_range_two_pow (N : ℕ) :
    (∑ k ∈ Finset.range N, 2 ^ k) = 2 ^ N - 1 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      have hp := Nat.one_le_two_pow (n := N)
      omega

/-- The corresponding exact sum over a natural interval. -/
theorem sum_Ico_two_pow {a b : ℕ} (hab : a ≤ b) :
    (∑ k ∈ Finset.Ico a b, 2 ^ k) = 2 ^ b - 2 ^ a := by
  have h := Finset.sum_range_add_sum_Ico (fun k => 2 ^ k) hab
  rw [sum_range_two_pow, sum_range_two_pow] at h
  have ha := Nat.one_le_two_pow (n := a)
  have hb := Nat.one_le_two_pow (n := b)
  have hp := Nat.pow_le_pow_right (by omega : 0 < 2) hab
  omega

/-- A convenient bound for the sparse initial part of the cover. -/
theorem sum_three_mul_shifted_two_pow_le :
    ∀ m : ℕ, 2 ≤ m →
      (∑ k ∈ Finset.range m, (2 ^ (3 * k) + 1)) ≤ 2 ^ (3 * m - 1) := by
  intro m hm
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hm
  induction q with
  | zero => norm_num
  | succ q ih =>
      let m := 2 + q
      have hm1 : 1 ≤ 3 * m := by dsimp [m]; omega
      have hterm : 2 ^ (3 * m) = 2 * 2 ^ (3 * m - 1) := by
        conv_lhs => rw [show 3 * m = (3 * m - 1) + 1 by omega]
        rw [pow_succ]
        ring
      have hnext : 2 ^ (3 * (m + 1) - 1) = 8 * 2 ^ (3 * m - 1) := by
        rw [show 3 * (m + 1) - 1 = (3 * m - 1) + 3 by omega, pow_add]
        norm_num
        ring
      have hp := Nat.one_le_two_pow (n := 3 * m - 1)
      have ih' := ih (by omega)
      have ih_m :
          (∑ k ∈ Finset.range m, (2 ^ (3 * k) + 1)) ≤
            2 ^ (3 * m - 1) := by simpa [m] using ih'
      rw [show 2 + (q + 1) = m + 1 by dsimp [m]; omega,
        Finset.sum_range_succ]
      rw [hterm, hnext]
      omega

/-- The exponential margin in the cover dominates its linear bookkeeping. -/
theorem eight_mul_le_three_pow_margin :
    ∀ m : ℕ, 2 ≤ m → 8 * m ≤ 2 ^ (3 * m - 1) + 1 := by
  intro m hm
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hm
  induction q with
  | zero => norm_num
  | succ q ih =>
      let m := 2 + q
      have hnext : 2 ^ (3 * (m + 1) - 1) = 8 * 2 ^ (3 * m - 1) := by
        rw [show 3 * (m + 1) - 1 = (3 * m - 1) + 3 by omega, pow_add]
        norm_num
        ring
      have hp := Nat.one_le_two_pow (n := 3 * m - 1)
      have ih' := ih (by omega)
      have ih_m : 8 * m ≤ 2 ^ (3 * m - 1) + 1 := by simpa [m] using ih'
      simpa [m, Nat.add_assoc] using (show
        8 * (m + 1) ≤ 2 ^ (3 * (m + 1) - 1) + 1 by
          rw [hnext]
          omega)

/-- The positions used to cover the prefix ending at `9m`: sparse triple
positions below `3m`, together with the entire final interval. -/
def shiftedTwoPowCover (m : ℕ) : Finset ℕ :=
  (Finset.range m).image (fun k => 3 * k) ∪ Finset.Ico (3 * m) (9 * m)

/-- The two pieces of `shiftedTwoPowCover` are disjoint. -/
theorem shiftedTwoPowCover_disjoint (m : ℕ) :
    Disjoint ((Finset.range m).image (fun k => 3 * k))
      (Finset.Ico (3 * m) (9 * m)) := by
  rw [Finset.disjoint_left]
  intro j hj hIco
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
  have hklt := Finset.mem_range.mp hk
  have hjlo := (Finset.mem_Ico.mp hIco).1
  omega

/-- Exact cardinality of the cover. -/
theorem shiftedTwoPowCover_card (m : ℕ) :
    (shiftedTwoPowCover m).card = 7 * m := by
  rw [shiftedTwoPowCover, Finset.card_union_of_disjoint
    (shiftedTwoPowCover_disjoint m),
    Finset.card_image_of_injective _ (by intro a b h; dsimp at h; omega),
    Finset.card_range, Nat.card_Ico]
  omega

/-- Cubing the underlying power proves the required index divisibility. -/
theorem shifted_two_pow_dvd_triple (k : ℕ) :
    2 ^ k + 1 ∣ 2 ^ (3 * k) + 1 := by
  have h := (show Odd 3 by norm_num).nat_add_dvd_pow_add_pow (2 ^ k) 1
  simpa [Nat.pow_mul, mul_comm] using h

/-- Every position before `9m` is covered by `shiftedTwoPowCover m`. -/
theorem shiftedTwoPowCover_covers (m k : ℕ) (hk : k < 9 * m) :
    ∃ j ∈ shiftedTwoPowCover m, 2 ^ k + 1 ∣ 2 ^ j + 1 := by
  by_cases hlate : 3 * m ≤ k
  · refine ⟨k, ?_, dvd_refl _⟩
    exact Finset.mem_union_right _ (Finset.mem_Ico.mpr ⟨hlate, hk⟩)
  · refine ⟨3 * k, ?_, shifted_two_pow_dvd_triple k⟩
    by_cases hearly : k < m
    · exact Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hearly, rfl⟩)
    · exact Finset.mem_union_right _ (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)

/-- Weight bound required by the general divisibility-cover theorem. -/
theorem shiftedTwoPowCover_budget (m : ℕ) (hm : 2 ≤ m) :
    (∑ j ∈ shiftedTwoPowCover m, (2 ^ j + 1)) + 9 * m ≤
      (2 ^ (9 * m) + 1) + (shiftedTwoPowCover m).card := by
  have hd := shiftedTwoPowCover_disjoint m
  have himage :
      (∑ j ∈ (Finset.range m).image (fun k => 3 * k), (2 ^ j + 1)) =
        ∑ k ∈ Finset.range m, (2 ^ (3 * k) + 1) := by
    exact Finset.sum_image (by intro a ha b hb h; dsimp at h; omega)
  have hfirst := sum_three_mul_shifted_two_pow_le m hm
  have hpow := sum_Ico_two_pow (show 3 * m ≤ 9 * m by omega)
  have hcardIco : (Finset.Ico (3 * m) (9 * m)).card = 6 * m := by
    rw [Nat.card_Ico]
    omega
  have hsecond :
      (∑ j ∈ Finset.Ico (3 * m) (9 * m), (2 ^ j + 1)) =
        (2 ^ (9 * m) - 2 ^ (3 * m)) + 6 * m := by
    rw [Finset.sum_add_distrib, hpow]
    simp only [Finset.sum_const, smul_eq_mul, mul_one, hcardIco]
  have hmargin := eight_mul_le_three_pow_margin m hm
  have hcard :
      ((Finset.range m).image (fun k => 3 * k) ∪
        Finset.Ico (3 * m) (9 * m)).card = 7 * m := by
    simpa [shiftedTwoPowCover] using shiftedTwoPowCover_card m
  rw [shiftedTwoPowCover, Finset.sum_union hd, himage, hsecond, hcard]
  have hp : 2 ^ (3 * m) = 2 * 2 ^ (3 * m - 1) := by
    conv_lhs => rw [show 3 * m = (3 * m - 1) + 1 by omega]
    rw [pow_succ]
    ring
  have hle : 2 ^ (3 * m) ≤ 2 ^ (9 * m) :=
    Nat.pow_le_pow_right (by omega : 0 < 2) (by omega)
  omega

/-- The classical below-ratio-two example `n_k=2^k+1` has irrational
reciprocal-Fibonacci sum. -/
theorem irrational_reciprocal_fib_shifted_two_powers :
    Irrational (∑' k : ℕ, (Nat.fib (2 ^ k + 1) : ℝ)⁻¹) := by
  let n : ℕ → ℕ := fun k => 2 ^ k + 1
  let s : ℕ → ℕ := fun t => 9 * (t + 2)
  let J : ℕ → Finset ℕ := fun t => shiftedTwoPowCover (t + 2)
  apply irrational_reciprocal_fib_of_divisibility_covers n s J
  · intro k
    simp [n]
  · intro a b hab
    dsimp [n]
    have hp := Nat.pow_lt_pow_right (by omega : 1 < 2) hab
    omega
  · apply Filter.tendsto_atTop.mpr
    intro B
    filter_upwards [eventually_ge_atTop B] with t ht
    dsimp [s]
    omega
  · intro t k hk
    simpa [n, s, J] using shiftedTwoPowCover_covers (t + 2) k hk
  · intro t
    simpa [n, s, J] using shiftedTwoPowCover_budget (t + 2) (by omega)

end Research
