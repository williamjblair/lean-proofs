import Mathlib
import Research.SpectralWienerDecomposition

namespace Erdos254.AtomicBohrLower

open MeasureTheory
open scoped BigOperators Topology
open Erdos254.AtomicDecomposition Erdos254.SpectralWienerDecomposition

noncomputable section

local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩

/-- A positive atom at the trivial character gives a finite-dimensional Bohr
neighborhood on which the full atomic Fourier series stays uniformly positive. -/
theorem exists_finite_circle_bohr_atomic_lower
    (μ : Measure Circle) [IsFiniteMeasure μ]
    (δ : ℝ) (hδ : 0 < δ) (hδatom : δ ≤ μ.real {(1 : Circle)}) :
    ∃ d : ℕ, ∃ a : Fin d → Circle, ∃ U : Set (Fin d → Circle),
      IsOpen U ∧ (fun _ => (1 : Circle)) ∈ U ∧
      ∀ n : ℕ, (fun i => a i ^ n) ∈ U → δ / 2 < (atomicCoeff μ n).re := by
  obtain ⟨F, hF⟩ := exists_finite_atomic_approximation μ (δ / 8) (by positivity)
  let e : Fin F.card ≃ {z : atomSet μ // z ∈ F} := F.equivFin.symm
  let a : Fin F.card → Circle := fun i => ((e i : atomSet μ) : Circle)
  let mass : ℝ := ∑ z ∈ F, μ.real {(z : Circle)}
  let g : (Fin F.card → Circle) → ℝ := fun x =>
    (∑ i : Fin F.card,
      ((μ.real {((e i : atomSet μ) : Circle)} : ℝ) : ℂ) * (x i : ℂ)).re
  let U : Set (Fin F.card → Circle) := {x | mass - δ / 8 < g x}
  have hg : Continuous g := by
    dsimp [g]
    fun_prop
  have hUopen : IsOpen U := hg.isOpen_preimage _ isOpen_Ioi
  have hsum_e (q : atomSet μ → ℂ) :
      (∑ i : Fin F.card, q (e i)) = ∑ z ∈ F, q z := by
    calc
      (∑ i : Fin F.card, q (e i)) =
          ∑ z : {z : atomSet μ // z ∈ F}, q z :=
        e.sum_comp (fun z : {z : atomSet μ // z ∈ F} => q z)
      _ = ∑ z ∈ F, q z := Finset.sum_coe_sort F q
  have hg_one : g (fun _ => (1 : Circle)) = mass := by
    dsimp [g, mass]
    simp only [mul_one]
    have hs := hsum_e (fun z : atomSet μ =>
      ((μ.real {(z : Circle)} : ℝ) : ℂ))
    rw [hs]
    simp
  have hone : (fun _ => (1 : Circle)) ∈ U := by
    dsimp [U]
    rw [hg_one]
    linarith [hδ]
  refine ⟨F.card, a, U, hUopen, hone, ?_⟩
  intro n hnU
  have hfinite : g (fun i => a i ^ n) =
      (∑ z ∈ F, μ.real {(z : Circle)} • (((z : atomSet μ) : Circle) : ℂ) ^ n).re := by
    dsimp only [g]
    have hpow (i : Fin F.card) :
        ((a i ^ n : Circle) : ℂ) =
          ((((e i : {z : atomSet μ // z ∈ F}) : atomSet μ) : Circle) : ℂ) ^ n := by
      rw [Circle.coe_pow]
    simp_rw [hpow]
    have hs := hsum_e (fun z : atomSet μ =>
      ((μ.real {(z : Circle)} : ℝ) : ℂ) * (((z : Circle) : ℂ) ^ n))
    rw [hs]
    simp_rw [Complex.real_smul]
  have hclose_n := hF n
  have hclose_zero := hF 0
  have hatom0 : δ ≤ (atomicCoeff μ 0).re :=
    hδatom.trans (singleton_one_mass_le_atomicCoeff_zero μ)
  have hmass : δ - δ / 8 < mass := by
    have hre : |(atomicCoeff μ 0).re - mass| < δ / 8 := by
      have := Complex.abs_re_le_norm
        (atomicCoeff μ 0 - ∑ z ∈ F,
          μ.real {(z : Circle)} • (((z : atomSet μ) : Circle) : ℂ) ^ 0)
      have hsimp :
          (∑ z ∈ F, μ.real {(z : Circle)} •
            (((z : atomSet μ) : Circle) : ℂ) ^ 0).re = mass := by
        dsimp [mass]
        simp
      change |(atomicCoeff μ 0).re -
        (∑ z ∈ F, μ.real {(z : Circle)} •
          (((z : atomSet μ) : Circle) : ℂ) ^ 0).re| ≤ _ at this
      rw [hsimp] at this
      exact this.trans_lt hclose_zero
    nlinarith [hatom0, (abs_lt.mp hre).2]
  have hgLower : mass - δ / 8 < g (fun i => a i ^ n) := hnU
  rw [hfinite] at hgLower
  have hre_n : |(atomicCoeff μ n).re -
      (∑ z ∈ F, μ.real {(z : Circle)} •
        (((z : atomSet μ) : Circle) : ℂ) ^ n).re| < δ / 8 := by
    have hrele := Complex.abs_re_le_norm
      (atomicCoeff μ n - ∑ z ∈ F,
        μ.real {(z : Circle)} • (((z : atomSet μ) : Circle) : ℂ) ^ n)
    change |(atomicCoeff μ n).re -
      (∑ z ∈ F, μ.real {(z : Circle)} •
        (((z : atomSet μ) : Circle) : ℂ) ^ n).re| ≤ _ at hrele
    exact hrele.trans_lt hclose_n
  have hlowerRe := (abs_lt.mp hre_n).1
  linarith

end

end Erdos254.AtomicBohrLower
