import Mathlib
import Research.PiecewiseAssembly

namespace Erdos254.CirclePiecewiseToAddCircle

open scoped Topology
open Erdos254.PiecewiseAssembly

noncomputable section

private lemma toCircle_arg_div_two_pi (z : Circle) :
    AddCircle.toCircle ((((z : ℂ).arg / (2 * Real.pi) : ℝ) : UnitAddCircle)) = z := by
  rw [AddCircle.toCircle_apply_mk]
  rw [show 2 * Real.pi / (1 : ℝ) * ((z : ℂ).arg / (2 * Real.pi)) =
      (z : ℂ).arg by field_simp [Real.pi_ne_zero]]
  exact Circle.exp_arg z

/-- Translate a multiplicative finite-circle piecewise-Bohr witness into the
additive unit-torus coordinates used by the BFW interface. -/
theorem circle_piecewise_bohr_to_additive
    {d : ℕ} (a : Fin d → Circle) (U : Set (Fin d → Circle))
    (hU : IsOpen U) (hone : (fun _ => (1 : Circle)) ∈ U)
    (J S : Set ℕ) (hJ : IsThick J)
    (hinc : ∀ n : ℕ, (fun i => a i ^ n) ∈ U → n ∈ J → n ∈ S) :
    ∃ α : Fin d → ℝ, ∃ V : Set (UnitAddTorus (Fin d)),
      IsOpen V ∧ (0 : ℕ) • (fun i => (α i : UnitAddCircle)) ∈ V ∧
      IsThick J ∧
      ∀ n : ℕ, n • (fun i => (α i : UnitAddCircle)) ∈ V → n ∈ J → n ∈ S := by
  let α : Fin d → ℝ := fun i => (a i : ℂ).arg / (2 * Real.pi)
  let T : UnitAddTorus (Fin d) → (Fin d → Circle) := fun x i =>
    AddCircle.toCircle (x i)
  let V : Set (UnitAddTorus (Fin d)) := T ⁻¹' U
  have hT : Continuous T := by
    dsimp [T]
    fun_prop
  have hV : IsOpen V := hU.preimage hT
  have hzero : (0 : UnitAddTorus (Fin d)) ∈ V := by
    dsimp [V, T]
    simpa using hone
  refine ⟨α, V, hV, ?_, hJ, ?_⟩
  · simpa using hzero
  · intro n hnV hnJ
    apply hinc n _ hnJ
    have hmap : T (n • (fun i => (α i : UnitAddCircle))) =
        (fun i => a i ^ n) := by
      funext i
      dsimp [T]
      rw [AddCircle.toCircle_nsmul, toCircle_arg_div_two_pi]
    exact hmap ▸ hnV

end

end Erdos254.CirclePiecewiseToAddCircle
