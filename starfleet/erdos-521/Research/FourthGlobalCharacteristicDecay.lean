import Research.FourthGlobalModularCoercivity
import Mathlib.Tactic

open scoped BigOperators

namespace Erdos521

/-- Every real phase has an integer multiple of `π` within the centered half-period. -/
lemma exists_centered_pi_representative (x : ℝ) :
    ∃ m : ℤ, |x - (m : ℝ) * Real.pi| ≤ Real.pi / 2 := by
  let y : ℝ := x / Real.pi + 1 / 2
  let m : ℤ := ⌊y⌋
  refine ⟨m, ?_⟩
  have hlo : (m : ℝ) ≤ y := by
    dsimp [m]
    exact Int.floor_le y
  have hhi : y < (m : ℝ) + 1 := by
    dsimp [m]
    exact Int.lt_floor_add_one y
  have hpi0 : 0 ≤ Real.pi := Real.pi_pos.le
  have hloMul := mul_le_mul_of_nonneg_right hlo hpi0
  have hhiMul := mul_le_mul_of_nonneg_right hhi.le hpi0
  have hcancel : x / Real.pi * Real.pi = x := div_mul_cancel₀ x Real.pi_ne_zero
  rw [abs_le]
  constructor <;> dsimp [y] at hloMul hhiMul <;> nlinarith

noncomputable def centeredPiRepresentative (x : ℝ) : ℤ :=
  Classical.choose (exists_centered_pi_representative x)

lemma centeredPiRepresentative_spec (x : ℝ) :
    |x - (centeredPiRepresentative x : ℝ) * Real.pi| ≤ Real.pi / 2 :=
  Classical.choose_spec (exists_centered_pi_representative x)

/-- On the entire fundamental dual cell, the characteristic product has a uniform two-branch
majorant: either macroscopic exponential decay in `N`, or Gaussian decay in the exact covariance
quadratic form. -/
lemma fourthOriginalCharacteristicProduct_global_decay
    (N : ℕ) (hN : 20 ≤ N) (s t : ℝ)
    (hs : |s| ≤ Real.pi / 2) (ht : |t| ≤ Real.pi / 2) :
    |fourthOriginalCharacteristicProduct (N + 2) s t| ≤
      Real.exp (-(2 / Real.pi ^ 2) *
        min ((N : ℝ) / 100000000000000000000)
          ((∑ i : Option (Fin (N + 2 + 1)),
            fourthOriginalPhase (N + 2) s t i ^ 2) / 3000000000)) := by
  let mOld : ℕ → ℤ := fun q ↦ centeredPiRepresentative (fourthOldPolynomialPhase q s t)
  let mAll : Option (Fin (N + 2 + 1)) → ℤ
    | none => 0
    | some q => mOld q
  let E : ℝ := ∑ q ∈ Finset.range (N + 3),
    (fourthOldPolynomialPhase q s t - (mOld q : ℝ) * Real.pi) ^ 2
  let Q : ℝ := ∑ i : Option (Fin (N + 2 + 1)),
    fourthOriginalPhase (N + 2) s t i ^ 2
  have hres : ∀ i, |fourthOriginalPhase (N + 2) s t i -
      (mAll i : ℝ) * Real.pi| ≤ Real.pi / 2 := by
    intro i
    cases i with
    | none => simpa [mAll, fourthOriginalPhase] using ht
    | some q =>
        change |fourthOldPolynomialPhase q s t -
          (centeredPiRepresentative (fourthOldPolynomialPhase q s t) : ℝ) * Real.pi| ≤
            Real.pi / 2
        exact centeredPiRepresentative_spec _
  have hdich := fourth_old_modular_energy_dichotomy N s t mOld hN hs ht
  have hfull : (∑ i : Option (Fin (N + 2 + 1)),
      (fourthOriginalPhase (N + 2) s t i - (mAll i : ℝ) * Real.pi) ^ 2) =
      t ^ 2 + E := by
    rw [Fintype.sum_option]
    simp only [mAll, fourthOriginalPhase, Int.cast_zero, zero_mul, sub_zero]
    change t ^ 2 +
        (∑ q : Fin (N + 2 + 1),
          (fourthOldPolynomialPhase q s t - (mOld q : ℝ) * Real.pi) ^ 2) = _
    have hsumEq : (∑ q : Fin (N + 2 + 1),
        (fourthOldPolynomialPhase q s t - (mOld q : ℝ) * Real.pi) ^ 2) =
        ∑ q ∈ Finset.range (N + 2 + 1),
          (fourthOldPolynomialPhase q s t - (mOld q : ℝ) * Real.pi) ^ 2 :=
      Fin.sum_univ_eq_sum_range
        (fun q : ℕ ↦ (fourthOldPolynomialPhase q s t -
          (mOld q : ℝ) * Real.pi) ^ 2) (N + 2 + 1)
    rw [hsumEq]
  have hE0 : 0 ≤ E := Finset.sum_nonneg fun q hq ↦ sq_nonneg _
  have ht0 : 0 ≤ t ^ 2 := sq_nonneg _
  have henergy : min ((N : ℝ) / 100000000000000000000) (Q / 3000000000) ≤
      ∑ i : Option (Fin (N + 2 + 1)),
        (fourthOriginalPhase (N + 2) s t i - (mAll i : ℝ) * Real.pi) ^ 2 := by
    rw [hfull]
    rcases hdich with hlarge | hlocal
    · exact (min_le_left _ _).trans (hlarge.trans (by linarith))
    · have hQ : Q / 3000000000 ≤ E := by
        apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 3000000000)).2
        dsimp [Q, E] at hlocal ⊢
        nlinarith
      exact (min_le_right _ _).trans (hQ.trans (by linarith))
  exact fourthOriginalCharacteristicProduct_decay_of_modular_energy
    (N + 2) s t
    (min ((N : ℝ) / 100000000000000000000) (Q / 3000000000))
    mAll hres (by simpa [Q] using henergy)

end Erdos521
