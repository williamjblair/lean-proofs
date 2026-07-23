import Research.Circles
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# The four-circle inversion genericity lemma

A rational parametrization of a circle reduces the exceptional four-circle
identity to a product in `ℝ[X]`.  This file supplies the algebraic step needed
to show that the identity cannot hold for four distinct positive circles with
no coaxial triple.
-/

namespace Erdos130
namespace Circle
namespace QuadGeneric

open Polynomial

noncomputable section

/-- Coefficients of a generalized circle equation
`a(x²+y²)+b x+c y+d`. -/
structure GenCircle where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ

/-- Evaluation of a generalized circle equation. -/
def GenCircle.eval (G : GenCircle) (p : Point) : ℝ :=
  G.a * (p.1 ^ 2 + p.2 ^ 2) + G.b * p.1 + G.c * p.2 + G.d

/-- The generalized-circle equation of an actual circle. -/
def circleEquation (Z : Circle) : GenCircle where
  a := 1
  b := -2 * Z.center.1
  c := -2 * Z.center.2
  d := q Z

@[simp] theorem circleEquation_eval (Z : Circle) (O : Point) :
    (circleEquation Z).eval O = inversionDenom O Z := by
  simp only [GenCircle.eval, circleEquation, inversionDenom, sqDist, q]
  ring

/-- Denominator and coordinate numerators for the standard rational
parametrization of the circumference of `D`. -/
def denPoly : ℝ[X] := 1 + X ^ 2

def xNumPoly (D : Circle) : ℝ[X] :=
  C (D.center.1 + D.radius) + C (D.center.1 - D.radius) * X ^ 2

def yNumPoly (D : Circle) : ℝ[X] :=
  C D.center.2 * denPoly + C (2 * D.radius) * X

/-- Homogeneous pullback of a generalized circle equation along that rational
parametrization. -/
def pullbackPoly (G : GenCircle) (D : Circle) : ℝ[X] :=
  C G.a * (xNumPoly D ^ 2 + yNumPoly D ^ 2) +
    C G.b * xNumPoly D * denPoly + C G.c * yNumPoly D * denPoly +
    C G.d * denPoly ^ 2

/-- The corresponding parametrized point. -/
def circleParam (D : Circle) (t : ℝ) : Point :=
  let den := 1 + t ^ 2
  ((D.center.1 + D.radius + (D.center.1 - D.radius) * t ^ 2) / den,
   (D.center.2 * den + 2 * D.radius * t) / den)

private theorem den_ne_zero (t : ℝ) : 1 + t ^ 2 ≠ 0 := by positivity

/-- Evaluation of the polynomial pullback is the denominator-squared
geometric evaluation. -/
theorem eval_pullbackPoly (G : GenCircle) (D : Circle) (t : ℝ) :
    Polynomial.eval t (pullbackPoly G D) =
      (1 + t ^ 2) ^ 2 * G.eval (circleParam D t) := by
  simp only [pullbackPoly, xNumPoly, yNumPoly, denPoly, circleParam,
    GenCircle.eval, eval_add, eval_mul, eval_pow, eval_C, eval_X, eval_one]
  field_simp [den_ne_zero t]
  <;> ring

/-- The parametrized point lies on `D`. -/
theorem circleParam_on (D : Circle) (t : ℝ) :
    inversionDenom (circleParam D t) D = 0 := by
  simp only [circleParam, inversionDenom, sqDist]
  field_simp [den_ne_zero t]
  <;> ring

/-- A generalized circle whose pullback vanishes identically is proportional
to the equation of the parametrized positive-radius circle. -/
theorem proportional_of_pullback_eq_zero (G : GenCircle) (D : Circle)
    (hr : D.radius ≠ 0) (hpoly : pullbackPoly G D = 0) :
    ∃ μ : ℝ, G.a = μ ∧ G.b = -2 * μ * D.center.1 ∧
      G.c = -2 * μ * D.center.2 ∧ G.d = μ * q D := by
  have h0 : G.eval (circleParam D 0) = 0 := by
    have he := congrArg (Polynomial.eval 0) hpoly
    rw [eval_pullbackPoly] at he
    norm_num at he ⊢
    exact he
  have h1 : G.eval (circleParam D 1) = 0 := by
    have he := congrArg (Polynomial.eval 1) hpoly
    rw [eval_pullbackPoly] at he
    norm_num at he
    exact he
  have hm1 : G.eval (circleParam D (-1)) = 0 := by
    have he := congrArg (Polynomial.eval (-1)) hpoly
    rw [eval_pullbackPoly] at he
    norm_num at he
    exact he
  simp only [circleParam, GenCircle.eval] at h0 h1 hm1
  norm_num at h0 h1 hm1
  have hcprod : D.radius * (G.c + 2 * G.a * D.center.2) = 0 := by
    linear_combination (h1 - hm1) / 2
  have hc : G.c = -2 * G.a * D.center.2 := by
    have := (mul_eq_zero.mp hcprod).resolve_left hr
    linarith
  have hbprod : D.radius * (G.b + 2 * G.a * D.center.1) = 0 := by
    linear_combination h0 - (h1 + hm1) / 2
  have hb : G.b = -2 * G.a * D.center.1 := by
    have := (mul_eq_zero.mp hbprod).resolve_left hr
    linarith
  refine ⟨G.a, rfl, hb, hc, ?_⟩
  simp only [q]
  rw [hb, hc] at h0
  linear_combination h0

/-- Distinct positive-radius circles give nonzero pullback polynomials on each
other's rational parametrizations. -/
theorem pullback_circle_ne_zero (Z D : Circle) (hZ : 0 < Z.radius)
    (hD : 0 < D.radius) (hne : Z ≠ D) :
    pullbackPoly (circleEquation Z) D ≠ 0 := by
  intro hp
  obtain ⟨μ, ha, hb, hc, hd⟩ :=
    proportional_of_pullback_eq_zero (circleEquation Z) D (ne_of_gt hD) hp
  simp only [circleEquation] at ha hb hc hd
  have hμ : μ = 1 := by linarith
  subst μ
  have hx : Z.center.1 = D.center.1 := by linarith
  have hy : Z.center.2 = D.center.2 := by linarith
  have hr2 : Z.radius ^ 2 = D.radius ^ 2 := by
    simp only [q] at hd
    rw [hx, hy] at hd
    nlinarith
  have hr : Z.radius = D.radius := by nlinarith
  apply hne
  cases Z with
  | mk z rz =>
      cases D with
      | mk d rd =>
          simp only [Circle.mk.injEq]
          exact ⟨Prod.ext hx hy, hr⟩

/-- Generalized-circle coefficients of the inverse-center collinearity locus
of three circles. -/
def tripleEquation (A B C : Circle) : GenCircle where
  a := -detCols (fun _ => 1) (fun Z => Z.center.1)
    (fun Z => Z.center.2) A B C
  b := -detCols (fun _ => 1) (fun Z => Z.center.2) q A B C
  c := detCols (fun _ => 1) (fun Z => Z.center.1) q A B C
  d := detCols (fun Z => Z.center.1) (fun Z => Z.center.2) q A B C

@[simp] theorem tripleEquation_eval (A B C : Circle) (O : Point) :
    (tripleEquation A B C).eval O = clearedInverseCenterTriple O A B C := by
  rw [clearedInverseCenterTriple_eq]
  simp only [tripleEquation, GenCircle.eval]
  ring

/-- If the four-circle cleared determinant vanishes for every inversion center,
then the triple locus of any three is a scalar multiple of the fourth circle,
provided the fourth circle is distinct from them. -/
theorem triple_locus_of_universal_quad (A B C D : Circle)
    (hA : 0 < A.radius) (hB : 0 < B.radius) (hC : 0 < C.radius)
    (hD : 0 < D.radius) (hAD : A ≠ D) (hBD : B ≠ D) (hCD : C ≠ D)
    (hall : ∀ O : Point, clearedInverseCenterQuad O A B C D = 0) :
    ∃ μ : ℝ, ∀ O : Point,
      clearedInverseCenterTriple O A B C = μ * inversionDenom O D := by
  let PA := pullbackPoly (circleEquation A) D
  let PB := pullbackPoly (circleEquation B) D
  let PC := pullbackPoly (circleEquation C) D
  let PT := pullbackPoly (tripleEquation A B C) D
  have hgeom (t : ℝ) :
      inversionDenom (circleParam D t) A *
        inversionDenom (circleParam D t) B *
        inversionDenom (circleParam D t) C *
        clearedInverseCenterTriple (circleParam D t) A B C = 0 := by
    have hq := hall (circleParam D t)
    rw [clearedInverseCenterQuad_on_circle _ A B C D (circleParam_on D t)] at hq
    have hr2 : 0 < D.radius ^ 2 := sq_pos_of_pos hD
    nlinarith
  have hpoly : PA * PB * PC * PT = 0 := by
    apply Polynomial.funext
    intro t
    simp only [eval_mul, eval_zero]
    dsimp [PA, PB, PC, PT]
    rw [eval_pullbackPoly, eval_pullbackPoly, eval_pullbackPoly,
      eval_pullbackPoly]
    simp only [circleEquation_eval, tripleEquation_eval]
    linear_combination ((1 + t ^ 2) ^ 8) * hgeom t
  have hPA : PA ≠ 0 := by
    dsimp [PA]
    exact pullback_circle_ne_zero A D hA hD hAD
  have hPB : PB ≠ 0 := by
    dsimp [PB]
    exact pullback_circle_ne_zero B D hB hD hBD
  have hPC : PC ≠ 0 := by
    dsimp [PC]
    exact pullback_circle_ne_zero C D hC hD hCD
  have hPT : PT = 0 := by
    rcases mul_eq_zero.mp hpoly with hpabc | hpT
    · rcases mul_eq_zero.mp hpabc with hpab | hpC
      · rcases mul_eq_zero.mp hpab with hpA | hpB
        · exact False.elim (hPA hpA)
        · exact False.elim (hPB hpB)
      · exact False.elim (hPC hpC)
    · exact hpT
  obtain ⟨μ, ha, hb, hc, hd⟩ := proportional_of_pullback_eq_zero
    (tripleEquation A B C) D (ne_of_gt hD) hPT
  refine ⟨μ, fun O => ?_⟩
  rw [← tripleEquation_eval]
  simp only [GenCircle.eval]
  rw [ha, hb, hc, hd]
  rw [← circleEquation_eval D O]
  simp only [circleEquation, GenCircle.eval]
  ring

/-- Under the additional noncoaxiality hypothesis, the scalar in the preceding
locus identity is nonzero. -/
theorem nonzero_triple_locus_of_universal_quad (A B C D : Circle)
    (hA : 0 < A.radius) (hB : 0 < B.radius) (hC : 0 < C.radius)
    (hD : 0 < D.radius) (hAD : A ≠ D) (hBD : B ≠ D) (hCD : C ≠ D)
    (hnc : ¬ Coaxial3 A B C)
    (hall : ∀ O : Point, clearedInverseCenterQuad O A B C D = 0) :
    ∃ μ : ℝ, μ ≠ 0 ∧ ∀ O : Point,
      clearedInverseCenterTriple O A B C = μ * inversionDenom O D := by
  obtain ⟨μ, hμ⟩ := triple_locus_of_universal_quad A B C D
    hA hB hC hD hAD hBD hCD hall
  refine ⟨μ, ?_, hμ⟩
  intro hz
  subst μ
  apply hnc
  rw [coaxial3_iff_cleared_eq_zero]
  intro O
  simpa using hμ O

/-- Four distinct positive circles with no coaxial triple cannot have an
identically vanishing inverse-center cyclic determinant.  Three row orderings
are stated explicitly so the theorem can be applied without relying on hidden
permutation conventions. -/
theorem not_universal_inverse_cyclic_quad (A B C D : Circle)
    (hA : 0 < A.radius) (hB : 0 < B.radius)
    (hC : 0 < C.radius) (hD : 0 < D.radius)
    (hABne : A ≠ B) (hACne : A ≠ C) (hADne : A ≠ D)
    (hBCne : B ≠ C) (hBDne : B ≠ D) (hCDne : C ≠ D)
    (hncABC : ¬ Coaxial3 A B C) (hncBCD : ¬ Coaxial3 B C D)
    (hncACD : ¬ Coaxial3 A C D)
    (h₁ : ∀ O : Point, clearedInverseCenterQuad O A B C D = 0)
    (h₂ : ∀ O : Point, clearedInverseCenterQuad O B C D A = 0)
    (h₃ : ∀ O : Point, clearedInverseCenterQuad O A C D B = 0) : False := by
  obtain ⟨μ₁, hμ₁, hl₁⟩ := nonzero_triple_locus_of_universal_quad A B C D
    hA hB hC hD hADne hBDne hCDne hncABC h₁
  obtain ⟨hDA, hDB, hDC⟩ := orthogonal_of_triple_locus A B C D hμ₁ hl₁
  obtain ⟨μ₂, hμ₂, hl₂⟩ := nonzero_triple_locus_of_universal_quad B C D A
    hB hC hD hA hABne.symm hACne.symm hADne.symm hncBCD h₂
  obtain ⟨hAB, hAC, hAD⟩ := orthogonal_of_triple_locus B C D A hμ₂ hl₂
  obtain ⟨μ₃, hμ₃, hl₃⟩ := nonzero_triple_locus_of_universal_quad A C D B
    hA hC hD hB hABne hBCne.symm hBDne.symm hncACD h₃
  obtain ⟨hBA, hBC, hBD⟩ := orthogonal_of_triple_locus A C D B hμ₃ hl₃
  apply not_four_pairwise_inversiveOrthogonal A B C D hA hB hC hD
    hAB hAC hAD hBC hBD
  rw [inversiveInner_comm]
  exact hDC

/-- Clean nondegeneracy form: for four distinct positive circles with the three
relevant triples noncoaxial, the cleared cyclic determinant is nonzero for some
inversion center. -/
theorem exists_center_clearedInverseCenterQuad_ne_zero (A B C D : Circle)
    (hA : 0 < A.radius) (hB : 0 < B.radius)
    (hC : 0 < C.radius) (hD : 0 < D.radius)
    (hABne : A ≠ B) (hACne : A ≠ C) (hADne : A ≠ D)
    (hBCne : B ≠ C) (hBDne : B ≠ D) (hCDne : C ≠ D)
    (hncABC : ¬ Coaxial3 A B C) (hncBCD : ¬ Coaxial3 B C D)
    (hncACD : ¬ Coaxial3 A C D) :
    ∃ O : Point, clearedInverseCenterQuad O A B C D ≠ 0 := by
  by_contra hex
  push_neg at hex
  apply not_universal_inverse_cyclic_quad A B C D hA hB hC hD
    hABne hACne hADne hBCne hBDne hCDne hncABC hncBCD hncACD hex
  · intro O
    rw [clearedInverseCenterQuad_rotate]
    simp [hex O]
  · intro O
    rw [clearedInverseCenterQuad_cycle_last_three]
    exact hex O

end

end QuadGeneric
end Circle
end Erdos130
