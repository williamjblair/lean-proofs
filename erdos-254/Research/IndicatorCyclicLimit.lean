import Mathlib
import Research.CyclicSpectralLimit

namespace Erdos254.IndicatorCyclicLimit

open Filter Topology MeasureTheory
open scoped BigOperators ComplexConjugate
open Erdos254.FiniteCyclicSpectral Erdos254.CyclicSpectralLimit

noncomputable section

local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩
local instance (j : ℕ) : NeZero (M j) := ⟨by simp [M]⟩

/-- Indicators of increasingly long finite cyclic models yield a limiting
spectral measure. Any short difference forced by two occupied cyclic sites is
then present in the limiting positivity set. -/
theorem exists_spectral_probability_of_cyclic_indicators
    (P : ∀ j : ℕ, Finset (ZMod (M j)))
    (D : Set ℕ) (δ : ℝ) (hδ : 0 < δ)
    (hP : ∀ j : ℕ, (P j).Nonempty)
    (hdensity : ∀ j : ℕ, δ ≤ (P j).card / (M j : ℝ))
    (hpair : ∀ j n : ℕ, n < j + 1 →
      ∀ k : ZMod (M j), k ∈ P j → k + (n : ZMod (M j)) ∈ P j → n ∈ D) :
    ∃ μ : ProbabilityMeasure Circle,
      δ ≤ (μ : Measure Circle).real {(1 : Circle)} ∧
      ∀ n : ℕ, 0 < (∫ z : Circle, (z : ℂ) ^ n ∂(μ : Measure Circle)).re → n ∈ D := by
  let Φ : ∀ j : ℕ, ZMod (M j) → ℂ := fun j k => if k ∈ P j then 1 else 0
  have henergy (j : ℕ) : energy (Φ j) = (P j).card := by
    unfold energy
    calc
      (∑ k : ZMod (M j), ‖Φ j k‖ ^ 2) =
          ∑ k : ZMod (M j), if k ∈ P j then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro k hk
        by_cases h : k ∈ P j <;> simp [Φ, h]
      _ = ∑ k ∈ P j, (1 : ℝ) := by
        rw [show (∑ k : ZMod (M j), if k ∈ P j then (1 : ℝ) else 0) =
          ∑ k ∈ Finset.univ, if k ∈ P j then (1 : ℝ) else 0 by rfl]
        rw [Finset.sum_ite_mem]
        simp
      _ = (P j).card := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hsum (j : ℕ) : ∑ k : ZMod (M j), Φ j k = ((P j).card : ℂ) := by
    calc
      (∑ k : ZMod (M j), Φ j k) =
          ∑ k : ZMod (M j), if k ∈ P j then (1 : ℂ) else 0 := by rfl
      _ = ∑ k ∈ P j, (1 : ℂ) := by
        rw [show (∑ k : ZMod (M j), if k ∈ P j then (1 : ℂ) else 0) =
          ∑ k ∈ Finset.univ, if k ∈ P j then (1 : ℂ) else 0 by rfl]
        rw [Finset.sum_ite_mem]
        simp
      _ = ((P j).card : ℂ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hE : ∀ j : ℕ, 0 < energy (Φ j) := by
    intro j
    rw [henergy]
    exact_mod_cast (P j).card_pos.mpr (hP j)
  have hatom : ∀ j : ℕ,
      δ ≤ ‖∑ k : ZMod (M j), Φ j k‖ ^ 2 / denom (Φ j) := by
    intro j
    rw [hsum]
    unfold denom
    rw [henergy]
    rw [Complex.norm_natCast]
    have hcard : (0 : ℝ) < (P j).card := by
      exact_mod_cast (P j).card_pos.mpr (hP j)
    calc
      δ ≤ (P j).card / (M j : ℝ) := hdensity j
      _ = ((P j).card : ℝ) ^ 2 /
          ((M j : ℝ) * (P j).card) := by field_simp
  have hcorr : ∀ j n : ℕ, 0 ≤ (correlation Φ j n).re := by
    intro j n
    unfold correlation
    rw [henergy]
    simp [Φ, Complex.real_smul]
    apply mul_nonneg (inv_nonneg.mpr (by positivity))
    apply Finset.sum_nonneg
    intro i hi
    split_ifs <;> norm_num
  have hdetect : ∀ j n : ℕ, n < j + 1 →
      0 < (correlation Φ j n).re → n ∈ D := by
    intro j n hn hpos
    have hne : (∑ k : ZMod (M j),
        starRingEnd ℂ (Φ j k) * Φ j (k + (n : ZMod (M j)))) ≠ 0 := by
      intro hz
      have : correlation Φ j n = 0 := by
        unfold correlation
        rw [hz, smul_zero]
      rw [this] at hpos
      simp at hpos
    obtain ⟨k, hk, hkne⟩ := Finset.exists_ne_zero_of_sum_ne_zero
      (s := Finset.univ) hne
    simp only [Finset.mem_univ] at hk
    have hkP : k ∈ P j := by
      by_contra h
      simp [Φ, h] at hkne
    have hknP : k + (n : ZMod (M j)) ∈ P j := by
      by_contra h
      simp [Φ, h] at hkne
    exact hpair j n hn k hkP hknP
  exact exists_limit_spectral_probability Φ D δ hδ hE hatom hcorr hdetect

/-- Shifted finite-embedding form for cyclic indicators. -/
theorem exists_spectral_probability_of_cyclic_indicators_finitely_embedded
    (P : ∀ j : ℕ, Finset (ZMod (M j)))
    (q : ℕ → ℕ) (S : Set ℕ) (δ : ℝ)
    (hP : ∀ j : ℕ, (P j).Nonempty)
    (hdensity : ∀ j : ℕ, δ ≤ (P j).card / (M j : ℝ))
    (hpair : ∀ j n : ℕ, n < j + 1 →
      ∀ k : ZMod (M j), k ∈ P j → k + (n : ZMod (M j)) ∈ P j →
        n + q j ∈ S) :
    ∃ μ : ProbabilityMeasure Circle,
      δ ≤ (μ : Measure Circle).real {(1 : Circle)} ∧
      ∀ F : Finset ℕ,
        (∀ n ∈ F, 0 < (∫ z : Circle, (z : ℂ) ^ n ∂(μ : Measure Circle)).re) →
        ∃ r : ℕ, ∀ n ∈ F, n + r ∈ S := by
  let Φ : ∀ j : ℕ, ZMod (M j) → ℂ := fun j k => if k ∈ P j then 1 else 0
  have henergy (j : ℕ) : energy (Φ j) = (P j).card := by
    unfold energy
    calc
      (∑ k : ZMod (M j), ‖Φ j k‖ ^ 2) =
          ∑ k : ZMod (M j), if k ∈ P j then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro k hk
        by_cases h : k ∈ P j <;> simp [Φ, h]
      _ = ∑ k ∈ P j, (1 : ℝ) := by
        rw [show (∑ k : ZMod (M j), if k ∈ P j then (1 : ℝ) else 0) =
          ∑ k ∈ Finset.univ, if k ∈ P j then (1 : ℝ) else 0 by rfl]
        rw [Finset.sum_ite_mem]
        simp
      _ = (P j).card := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hsum (j : ℕ) : ∑ k : ZMod (M j), Φ j k = ((P j).card : ℂ) := by
    calc
      (∑ k : ZMod (M j), Φ j k) =
          ∑ k : ZMod (M j), if k ∈ P j then (1 : ℂ) else 0 := by rfl
      _ = ∑ k ∈ P j, (1 : ℂ) := by
        rw [show (∑ k : ZMod (M j), if k ∈ P j then (1 : ℂ) else 0) =
          ∑ k ∈ Finset.univ, if k ∈ P j then (1 : ℂ) else 0 by rfl]
        rw [Finset.sum_ite_mem]
        simp
      _ = ((P j).card : ℂ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hE : ∀ j : ℕ, 0 < energy (Φ j) := by
    intro j
    rw [henergy]
    exact_mod_cast (P j).card_pos.mpr (hP j)
  have hatom : ∀ j : ℕ,
      δ ≤ ‖∑ k : ZMod (M j), Φ j k‖ ^ 2 / denom (Φ j) := by
    intro j
    rw [hsum]
    unfold denom
    rw [henergy, Complex.norm_natCast]
    have hcard : (0 : ℝ) < (P j).card := by
      exact_mod_cast (P j).card_pos.mpr (hP j)
    calc
      δ ≤ (P j).card / (M j : ℝ) := hdensity j
      _ = ((P j).card : ℝ) ^ 2 /
          ((M j : ℝ) * (P j).card) := by field_simp
  have hdetect : ∀ j n : ℕ, n < j + 1 →
      0 < (correlation Φ j n).re → n + q j ∈ S := by
    intro j n hn hpos
    have hne : (∑ k : ZMod (M j),
        starRingEnd ℂ (Φ j k) * Φ j (k + (n : ZMod (M j)))) ≠ 0 := by
      intro hz
      have : correlation Φ j n = 0 := by
        unfold correlation
        rw [hz, smul_zero]
      rw [this] at hpos
      simp at hpos
    obtain ⟨k, hk, hkne⟩ := Finset.exists_ne_zero_of_sum_ne_zero
      (s := Finset.univ) hne
    simp only [Finset.mem_univ] at hk
    have hkP : k ∈ P j := by
      by_contra h
      simp [Φ, h] at hkne
    have hknP : k + (n : ZMod (M j)) ∈ P j := by
      by_contra h
      simp [Φ, h] at hkne
    exact hpair j n hn k hkP hknP
  exact exists_limit_spectral_probability_finitely_embedded Φ q S δ hE hatom hdetect

end

end Erdos254.IndicatorCyclicLimit
