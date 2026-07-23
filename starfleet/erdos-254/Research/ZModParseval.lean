import Mathlib.Analysis.Fourier.ZMod

namespace Erdos254.ZModParseval

open Finset AddChar
open scoped BigOperators ComplexConjugate
open ZMod

noncomputable section

variable {N : ℕ} [NeZero N]

private lemma character_sum (t : ZMod N) :
    ∑ k : ZMod N, stdAddChar (t * k) = if t = 0 then (N : ℂ) else 0 := by
  split_ifs with h
  · simp [h]
  · exact sum_eq_zero_of_ne_one (isPrimitive_stdAddChar N h)

/-- Parseval's identity for the unnormalized DFT on `ZMod N`. -/
theorem dft_energy (Φ : ZMod N → ℂ) :
    ∑ k : ZMod N, starRingEnd ℂ (𝓕 Φ k) * 𝓕 Φ k =
      (N : ℂ) * ∑ j : ZMod N, starRingEnd ℂ (Φ j) * Φ j := by
  simp only [dft_apply, map_sum, map_mul, smul_eq_mul]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hchar (x y i : ZMod N) :
      starRingEnd ℂ (stdAddChar (-(y * x))) * stdAddChar (-(i * x)) =
        stdAddChar ((y - i) * x) := by
    rw [← inv_apply_eq_conj, ← map_neg_eq_inv, ← map_add_eq_mul]
    congr 1
    ring
  have hinner (y i : ZMod N) :
      (∑ x : ZMod N,
        starRingEnd ℂ (stdAddChar (-(y * x))) * starRingEnd ℂ (Φ y) *
          (stdAddChar (-(i * x)) * Φ i)) =
        if y = i then (N : ℂ) * (starRingEnd ℂ (Φ y) * Φ i) else 0 := by
    calc
      _ = ∑ x : ZMod N, (starRingEnd ℂ (Φ y) * Φ i) *
          (starRingEnd ℂ (stdAddChar (-(y * x))) * stdAddChar (-(i * x))) := by
        apply Finset.sum_congr rfl
        intro x hx
        ring
      _ = (starRingEnd ℂ (Φ y) * Φ i) *
          ∑ x : ZMod N, stdAddChar ((y - i) * x) := by
        simp_rw [hchar]
        rw [Finset.mul_sum]
      _ = (starRingEnd ℂ (Φ y) * Φ i) *
          (if y - i = 0 then (N : ℂ) else 0) := by
        rw [character_sum]
      _ = if y = i then (N : ℂ) * (starRingEnd ℂ (Φ y) * Φ i) else 0 := by
        simp only [sub_eq_zero]
        by_cases h : y = i <;> simp [h] <;> ring
  have hswap (y : ZMod N) :
      (∑ x : ZMod N, ∑ i : ZMod N,
        starRingEnd ℂ (stdAddChar (-(y * x))) * starRingEnd ℂ (Φ y) *
          (stdAddChar (-(i * x)) * Φ i)) =
      ∑ i : ZMod N,
        if y = i then (N : ℂ) * (starRingEnd ℂ (Φ y) * Φ i) else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    exact hinner y i
  simp_rw [hswap]
  simp

/-- Fourier transform of the DFT energy is cyclic autocorrelation. -/
theorem dft_energy_character (Φ : ZMod N → ℂ) (n : ZMod N) :
    ∑ k : ZMod N,
      (starRingEnd ℂ (𝓕 Φ k) * 𝓕 Φ k) * stdAddChar (k * n) =
      (N : ℂ) * ∑ j : ZMod N, starRingEnd ℂ (Φ j) * Φ (j + n) := by
  simp only [dft_apply, map_sum, map_mul, smul_eq_mul]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_mul]
  have hchar (x y i : ZMod N) :
      (starRingEnd ℂ (stdAddChar (-(y * x))) * stdAddChar (-(i * x))) *
          stdAddChar (x * n) = stdAddChar ((y - i + n) * x) := by
    rw [← inv_apply_eq_conj, ← map_neg_eq_inv, ← map_add_eq_mul,
      ← map_add_eq_mul]
    congr 1
    ring
  have hinner (y i : ZMod N) :
      (∑ x : ZMod N,
        (starRingEnd ℂ (stdAddChar (-(y * x))) * starRingEnd ℂ (Φ y) *
          (stdAddChar (-(i * x)) * Φ i)) * stdAddChar (x * n)) =
        if i = y + n then (N : ℂ) * (starRingEnd ℂ (Φ y) * Φ i) else 0 := by
    calc
      _ = ∑ x : ZMod N, (starRingEnd ℂ (Φ y) * Φ i) *
          ((starRingEnd ℂ (stdAddChar (-(y * x))) * stdAddChar (-(i * x))) *
            stdAddChar (x * n)) := by
        apply Finset.sum_congr rfl
        intro x hx
        ring
      _ = (starRingEnd ℂ (Φ y) * Φ i) *
          ∑ x : ZMod N, stdAddChar ((y - i + n) * x) := by
        simp_rw [hchar]
        rw [Finset.mul_sum]
      _ = (starRingEnd ℂ (Φ y) * Φ i) *
          (if y - i + n = 0 then (N : ℂ) else 0) := by
        rw [character_sum]
      _ = if i = y + n then (N : ℂ) * (starRingEnd ℂ (Φ y) * Φ i) else 0 := by
        have heq : y - i + n = 0 ↔ i = y + n := by
          constructor <;> intro h
          · linear_combination -h
          · rw [h]
            abel
        simp only [heq]
        by_cases h : i = y + n <;> simp [h] <;> ring
  have hswap (y : ZMod N) :
      (∑ x : ZMod N, ∑ i : ZMod N,
        (starRingEnd ℂ (stdAddChar (-(y * x))) * starRingEnd ℂ (Φ y) *
          (stdAddChar (-(i * x)) * Φ i)) * stdAddChar (x * n)) =
      ∑ i : ZMod N,
        if i = y + n then (N : ℂ) * (starRingEnd ℂ (Φ y) * Φ i) else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    exact hinner y i
  simp_rw [hswap]
  simp

/-- Real norm-squared form of Parseval. -/
theorem sum_norm_sq_dft (Φ : ZMod N → ℂ) :
    ∑ k : ZMod N, ‖𝓕 Φ k‖ ^ 2 =
      (N : ℝ) * ∑ j : ZMod N, ‖Φ j‖ ^ 2 := by
  have h := congrArg Complex.re (dft_energy Φ)
  simp only [mul_comm, Complex.mul_conj,
    Complex.normSq_eq_norm_sq] at h
  norm_cast at h

end

end Erdos254.ZModParseval
