import Research.FourthModularLinearStage
import Mathlib.Tactic

open scoped BigOperators

namespace Erdos521

/-- Taking a fixed lag difference costs at most a factor four in modular residual energy. -/
lemma modular_lag_difference_energy (y : ℕ → ℝ) (m : ℕ → ℤ) (N L : ℕ)
    (hL : L ≤ N) :
    (∑ q ∈ Finset.range (N - L),
      ((y (q + L) - y q) - ((m (q + L) : ℝ) - (m q : ℝ)) * Real.pi) ^ 2) ≤
      4 * ∑ q ∈ Finset.range N, (y q - (m q : ℝ) * Real.pi) ^ 2 := by
  let r : ℕ → ℝ := fun q ↦ y q - (m q : ℝ) * Real.pi
  have hpoint (q : ℕ) :
      ((y (q + L) - y q) - ((m (q + L) : ℝ) - (m q : ℝ)) * Real.pi) ^ 2 ≤
        2 * (r q ^ 2 + r (q + L) ^ 2) := by
    have hid : (y (q + L) - y q) -
        ((m (q + L) : ℝ) - (m q : ℝ)) * Real.pi = r (q + L) - r q := by
      dsimp [r]
      ring
    rw [hid]
    exact first_difference_sq_le _ _
  calc
    _ ≤ ∑ q ∈ Finset.range (N - L), 2 * (r q ^ 2 + r (q + L) ^ 2) :=
      Finset.sum_le_sum fun q hq ↦ hpoint q
    _ = 2 * ((∑ q ∈ Finset.range (N - L), r q ^ 2) +
        ∑ q ∈ Finset.range (N - L), r (q + L) ^ 2) := by
      simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ 2 * ((∑ q ∈ Finset.range N, r q ^ 2) +
        ∑ q ∈ Finset.range N, r q ^ 2) := by
      have h0 : (∑ q ∈ Finset.range (N - L), r q ^ 2) ≤
          ∑ q ∈ Finset.range N, r q ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_mono (by omega : N - L ≤ N))
          (fun q hq hnot ↦ sq_nonneg _)
      have hshift : (∑ q ∈ Finset.range (N - L), r (q + L) ^ 2) ≤
          ∑ q ∈ Finset.range N, r q ^ 2 := by
        have h := sum_range_shift_le_sum_range_add (fun q ↦ r q ^ 2)
          (fun q ↦ sq_nonneg _) (N - L) L L le_rfl
        have hLN : L + (N - L) = N := by omega
        simpa [add_comm, hLN] using h
      nlinarith
    _ = 4 * ∑ q ∈ Finset.range N, (y q - (m q : ℝ) * Real.pi) ^ 2 := by
      dsimp [r]
      ring

/-- Reflecting a prefix about an endpoint also costs at most a factor four in modular energy. -/
lemma modular_reflection_difference_energy (y : ℕ → ℝ) (m : ℕ → ℤ) (K M : ℕ)
    (hM : M ≤ K + 1) :
    (∑ q ∈ Finset.range M,
      ((y (K - q) - y q) - ((m (K - q) : ℝ) - (m q : ℝ)) * Real.pi) ^ 2) ≤
      4 * ∑ q ∈ Finset.range (K + 1), (y q - (m q : ℝ) * Real.pi) ^ 2 := by
  let r : ℕ → ℝ := fun q ↦ y q - (m q : ℝ) * Real.pi
  have hqK {q : ℕ} (hq : q ∈ Finset.range M) : q ≤ K := by
    have := Finset.mem_range.mp hq
    omega
  have hpoint (q : ℕ) (hq : q ∈ Finset.range M) :
      ((y (K - q) - y q) - ((m (K - q) : ℝ) - (m q : ℝ)) * Real.pi) ^ 2 ≤
        2 * (r q ^ 2 + r (K - q) ^ 2) := by
    have hid : (y (K - q) - y q) -
        ((m (K - q) : ℝ) - (m q : ℝ)) * Real.pi = r (K - q) - r q := by
      dsimp [r]
      ring
    rw [hid]
    exact first_difference_sq_le _ _
  have hreflect : (∑ q ∈ Finset.range M, r (K - q) ^ 2) ≤
      ∑ q ∈ Finset.range (K + 1), r q ^ 2 := by
    let g : ℕ → ℕ := fun q ↦ K - q
    have hginj : Set.InjOn g (Finset.range M : Set ℕ) := by
      intro q1 hq1 q2 hq2 heq
      have h1 : q1 ≤ K := hqK hq1
      have h2 : q2 ≤ K := hqK hq2
      dsimp [g] at heq
      omega
    have himage : Finset.image g (Finset.range M) ⊆ Finset.range (K + 1) := by
      intro q hq
      rw [Finset.mem_image] at hq
      obtain ⟨p, hp, rfl⟩ := hq
      have hpK : p ≤ K := hqK hp
      apply Finset.mem_range.mpr
      dsimp [g]
      omega
    calc
      (∑ q ∈ Finset.range M, r (K - q) ^ 2) =
          ∑ q ∈ Finset.image g (Finset.range M), r q ^ 2 := by
        rw [Finset.sum_image hginj]
      _ ≤ ∑ q ∈ Finset.range (K + 1), r q ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg himage
          (fun q hq hnot ↦ sq_nonneg _)
  calc
    _ ≤ ∑ q ∈ Finset.range M, 2 * (r q ^ 2 + r (K - q) ^ 2) :=
      Finset.sum_le_sum fun q hq ↦ hpoint q hq
    _ = 2 * ((∑ q ∈ Finset.range M, r q ^ 2) +
        ∑ q ∈ Finset.range M, r (K - q) ^ 2) := by
      simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ 2 * ((∑ q ∈ Finset.range (K + 1), r q ^ 2) +
        ∑ q ∈ Finset.range (K + 1), r q ^ 2) := by
      have h0 : (∑ q ∈ Finset.range M, r q ^ 2) ≤
          ∑ q ∈ Finset.range (K + 1), r q ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_mono hM) (fun q hq hnot ↦ sq_nonneg _)
      nlinarith
    _ = 4 * ∑ q ∈ Finset.range (K + 1),
        (y q - (m q : ℝ) * Real.pi) ^ 2 := by
      dsimp [r]
      ring

end Erdos521
