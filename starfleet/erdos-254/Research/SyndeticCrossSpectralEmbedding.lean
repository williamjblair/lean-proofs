import Mathlib
import Research.SyndeticDensityBlocks
import Research.CrossAlignment
import Research.DenseChunk
import Research.FiniteBlockSpectral

namespace Erdos254.SyndeticCrossSpectralEmbedding

open MeasureTheory
open scoped BigOperators
open Erdos254.SyndeticDensityBlocks Erdos254.CrossAlignment Erdos254.DenseChunk
open Erdos254.FiniteBlockSpectral Erdos254.CyclicSpectralLimit

noncomputable section

attribute [local instance] Classical.propDecidable
local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩

/-- Finite cyclic alignment of two syndetic sets, followed by spectral
compactness, produces a positive-trivial-atom spectral measure whose positivity
set is finitely embeddable in their sumset. -/
theorem exists_cross_spectral_finite_embedding
    (S₀ S₁ : Set ℕ)
    (h₀ : ∃ K : ℕ, ∀ n : ℕ, ∃ s : ℕ,
      s ∈ S₀ ∧ s ≤ n ∧ n ≤ s + K)
    (h₁ : ∃ K : ℕ, ∀ n : ℕ, ∃ s : ℕ,
      s ∈ S₁ ∧ s ≤ n ∧ n ≤ s + K) :
    ∃ μ : ProbabilityMeasure Circle,
      0 < (μ : Measure Circle).real {(1 : Circle)} ∧
      ∀ F : Finset ℕ,
        (∀ n ∈ F, 0 < (∫ z : Circle, (z : ℂ) ^ n ∂(μ : Measure Circle)).re) →
        ∃ r : ℕ, ∀ n ∈ F,
          n + r ∈ {x | ∃ s₀ ∈ S₀, ∃ s₁ ∈ S₁, s₀ + s₁ = x} := by
  obtain ⟨K₀, hS₀⟩ := h₀
  obtain ⟨K₁, hS₁⟩ := h₁
  let Q₀ := K₀ + 1
  let Q₁ := K₁ + 1
  let R := Q₀ * Q₁
  have hQ₀ : 0 < Q₀ := by dsimp [Q₀]; omega
  have hQ₁ : 0 < Q₁ := by dsimp [Q₁]; omega
  have hR : 0 < R := mul_pos hQ₀ hQ₁
  have hex : ∀ j : ℕ, ∃ q : ℕ, ∃ B : Finset ℕ,
      (∀ x ∈ B, x < j + 1) ∧ B.Nonempty ∧
      (j + 1 ≤ 2 * R * B.card) ∧
      ∀ x ∈ B, ∀ y ∈ B, ∀ n : ℕ, y = x + n →
        n + q ∈ {z | ∃ s₀ ∈ S₀, ∃ s₁ ∈ S₁, s₀ + s₁ = z} := by
    intro j
    let m := j + 1
    let L := m * R
    let A : Finset ℕ := (Finset.range L).filter (fun x => x ∈ S₀)
    let B₁ : Finset ℕ := (Finset.range L).filter (fun x => x ∈ S₁)
    have hAbound : ∀ x ∈ A, x < L := by
      intro x hx
      exact Finset.mem_range.mp (Finset.mem_filter.mp hx).1
    have hB₁bound : ∀ x ∈ B₁, x < L := by
      intro x hx
      exact Finset.mem_range.mp (Finset.mem_filter.mp hx).1
    have hAcard : m * Q₁ ≤ A.card := by
      have h := card_filter_range_mul_lower S₀ K₀ (m * Q₁) hS₀
      simpa [A, L, R, Q₀, Q₁, Nat.mul_assoc, Nat.mul_left_comm,
        Nat.mul_comm] using h
    have hB₁card : m * Q₀ ≤ B₁.card := by
      have h := card_filter_range_mul_lower S₁ K₁ (m * Q₀) hS₁
      simpa [B₁, L, R, Q₀, Q₁, Nat.mul_assoc, Nat.mul_left_comm,
        Nat.mul_comm] using h
    obtain ⟨q, hq, C, hCcard, hC⟩ :=
      exists_large_exact_sum_fiber A B₁ L (by dsimp [L, m]; positivity)
        hAbound hB₁bound
    have hCbound : ∀ x ∈ C, x < m * R := by
      intro x hx
      have := (hC x hx).1
      exact hAbound x this
    obtain ⟨c, hcR, B, hchunk, hB⟩ :=
      exists_dense_chunk C m R (by dsimp [m]; omega) hR hCbound
    have hmC : m ≤ 2 * C.card := by
      have hlower : (m * Q₁) * (m * Q₀) ≤ A.card * B₁.card :=
        Nat.mul_le_mul hAcard hB₁card
      have htotal : (m * Q₁) * (m * Q₀) ≤ (2 * L) * C.card :=
        hlower.trans hCcard
      have hfactor : 0 < m * R := mul_pos (by dsimp [m]; omega) hR
      apply Nat.le_of_mul_le_mul_left (c := m * R) _ hfactor
      calc
        (m * R) * m = (m * Q₁) * (m * Q₀) := by
          dsimp [R]
          ring
        _ ≤ (2 * L) * C.card := htotal
        _ = (m * R) * (2 * C.card) := by
          dsimp [L]
          ring
    have hmB : m ≤ 2 * R * B.card := by
      exact hmC.trans <| by nlinarith [hchunk]
    have hBnonempty : B.Nonempty := Finset.card_pos.mp (by
      by_contra hnot
      have hc : B.card = 0 := Nat.eq_zero_of_not_pos hnot
      rw [hc] at hmB
      simp at hmB)
    refine ⟨q, B, ?_, hBnonempty, ?_, ?_⟩
    · intro x hx
      exact (hB x hx).1
    · simpa [m] using hmB
    · intro x hx y hy n hyn
      have hxC := (hB x hx).2
      have hyC := (hB y hy).2
      have hxdata := hC (c * m + x) hxC
      have hydata := hC (c * m + y) hyC
      obtain ⟨hxA, b, hbB₁, hxsum⟩ := hxdata
      have hyA := hydata.1
      refine ⟨c * m + y, ?_, b, ?_, ?_⟩
      · exact (Finset.mem_filter.mp hyA).2
      · exact (Finset.mem_filter.mp hbB₁).2
      · omega
  choose q B hBbound hBnonempty hmB hdiff using hex
  let δ : ℝ := 1 / (6 * R)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hdensity : ∀ j : ℕ, δ ≤ (B j).card / (M j : ℝ) := by
    intro j
    have hm := hmB j
    dsimp [δ]
    simp only [M]
    push_cast
    have hm' : ((j + 1 : ℕ) : ℝ) ≤ 2 * R * (B j).card := by exact_mod_cast hm
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hscaled : 3 * ((j + 1 : ℕ) : ℝ) ≤
        6 * R * ((B j).card : ℝ) := by nlinarith [hm']
    simpa [mul_assoc, mul_left_comm, mul_comm] using hscaled
  obtain ⟨μ, hμatom, hembed⟩ :=
    exists_spectral_probability_of_dense_blocks_finitely_embedded
      B q {z | ∃ s₀ ∈ S₀, ∃ s₁ ∈ S₁, s₀ + s₁ = z} δ
      hBbound hBnonempty hdensity
      (fun j x y n hx hy hxy => hdiff j x hx y hy n hxy)
  exact ⟨μ, hδ.trans_le hμatom, hembed⟩

end

end Erdos254.SyndeticCrossSpectralEmbedding
