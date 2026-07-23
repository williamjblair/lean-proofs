import Research.FiniteWitness

/-!
# Generic translation and infinite assembly

Finite witnesses are translated, one block at a time, along the polynomial
curve `(t,t^3)`.  Explicit exceptional polynomials enforce global determinant
general position without changing any within-block distance.
-/

namespace Erdos130
namespace InfiniteAssembly

open Circle
open FiniteWitness
open Polynomial

noncomputable section

/-- Translation of a point along the cubic parameter curve. -/
def curveTranslate (t : ℝ) (p : Point) : Point :=
  (p.1 + t, p.2 + t ^ 3)

/-- Constant and moving polynomial point coordinates. -/
def constX (p : Point) : ℝ[X] := C p.1
def constY (p : Point) : ℝ[X] := C p.2
def moveX (p : Point) : ℝ[X] := C p.1 + X
def moveY (p : Point) : ℝ[X] := C p.2 + X ^ 3

/-- Oriented-area determinant over polynomial coordinates. -/
def orientPoly (x₁ y₁ x₂ y₂ x₃ y₃ : ℝ[X]) : ℝ[X] :=
  x₁ * (y₂ - y₃) - y₁ * (x₂ - x₃) + (x₂ * y₃ - x₃ * y₂)

/-- Four-point cyclic determinant over polynomial coordinates. -/
def cyclicPoly (x₁ y₁ x₂ y₂ x₃ y₃ x₄ y₄ : ℝ[X]) : ℝ[X] :=
  let N₁ := x₁ ^ 2 + y₁ ^ 2
  let N₂ := x₂ ^ 2 + y₂ ^ 2
  let N₃ := x₃ ^ 2 + y₃ ^ 2
  let N₄ := x₄ ^ 2 + y₄ ^ 2
  N₁ * (x₂ * (y₃ - y₄) - y₂ * (x₃ - x₄) + (x₃ * y₄ - x₄ * y₃)) -
  x₁ * (N₂ * (y₃ - y₄) - y₂ * (N₃ - N₄) + (N₃ * y₄ - N₄ * y₃)) +
  y₁ * (N₂ * (x₃ - x₄) - x₂ * (N₃ - N₄) + (N₃ * x₄ - N₄ * x₃)) -
  (N₂ * (x₃ * y₄ - x₄ * y₃) - x₂ * (N₃ * y₄ - N₄ * y₃) +
    y₂ * (N₃ * x₄ - N₄ * x₃))

/-- Pair collision, mixed orientation, and mixed cyclicity polynomials in their
canonical orders. -/
def pairExceptional (A B : Point) : ℝ[X] :=
  (moveX A - constX B) ^ 2 + (moveY A - constY B) ^ 2

def oneOrientExceptional (A B Cc : Point) : ℝ[X] :=
  orientPoly (moveX A) (moveY A) (constX B) (constY B) (constX Cc) (constY Cc)

def twoOrientExceptional (A B Cc : Point) : ℝ[X] :=
  orientPoly (moveX A) (moveY A) (moveX B) (moveY B) (constX Cc) (constY Cc)

def oneCyclicExceptional (A B Cc D : Point) : ℝ[X] :=
  cyclicPoly (moveX A) (moveY A) (constX B) (constY B)
    (constX Cc) (constY Cc) (constX D) (constY D)

def twoCyclicExceptional (A B Cc D : Point) : ℝ[X] :=
  cyclicPoly (moveX A) (moveY A) (moveX B) (moveY B)
    (constX Cc) (constY Cc) (constX D) (constY D)

def threeCyclicExceptional (A B Cc D : Point) : ℝ[X] :=
  cyclicPoly (moveX A) (moveY A) (moveX B) (moveY B)
    (moveX Cc) (moveY Cc) (constX D) (constY D)

@[simp] theorem eval_pairExceptional (t : ℝ) (A B : Point) :
    Polynomial.eval t (pairExceptional A B) = sqDist (curveTranslate t A) B := by
  simp [pairExceptional, moveX, moveY, constX, constY, curveTranslate, sqDist]

@[simp] theorem eval_oneOrientExceptional (t : ℝ) (A B Cc : Point) :
    Polynomial.eval t (oneOrientExceptional A B Cc) =
      orient (curveTranslate t A) B Cc := by
  simp [oneOrientExceptional, orientPoly, moveX, moveY, constX, constY,
    curveTranslate, orient]

@[simp] theorem eval_twoOrientExceptional (t : ℝ) (A B Cc : Point) :
    Polynomial.eval t (twoOrientExceptional A B Cc) =
      orient (curveTranslate t A) (curveTranslate t B) Cc := by
  simp [twoOrientExceptional, orientPoly, moveX, moveY, constX, constY,
    curveTranslate, orient]

@[simp] theorem eval_oneCyclicExceptional (t : ℝ) (A B Cc D : Point) :
    Polynomial.eval t (oneCyclicExceptional A B Cc D) =
      cyclicDet (curveTranslate t A) B Cc D := by
  simp [oneCyclicExceptional, cyclicPoly, moveX, moveY, constX, constY,
    curveTranslate, cyclicDet]

@[simp] theorem eval_twoCyclicExceptional (t : ℝ) (A B Cc D : Point) :
    Polynomial.eval t (twoCyclicExceptional A B Cc D) =
      cyclicDet (curveTranslate t A) (curveTranslate t B) Cc D := by
  simp [twoCyclicExceptional, cyclicPoly, moveX, moveY, constX, constY,
    curveTranslate, cyclicDet]

@[simp] theorem eval_threeCyclicExceptional (t : ℝ) (A B Cc D : Point) :
    Polynomial.eval t (threeCyclicExceptional A B Cc D) =
      cyclicDet (curveTranslate t A) (curveTranslate t B)
        (curveTranslate t Cc) D := by
  simp [threeCyclicExceptional, cyclicPoly, moveX, moveY, constX, constY,
    curveTranslate, cyclicDet]

/-- The sixth even coefficient of any degree-six polynomial is isolated by
these seven symmetric sample values.  We use the identity only through exact
`linear_combination` calculations below. -/
private theorem pairExceptional_ne_zero (A B : Point) :
    pairExceptional A B ≠ 0 := by
  intro hp
  have h0 := congrArg (Polynomial.eval 0) hp
  have h1 := congrArg (Polynomial.eval 1) hp
  have hm1 := congrArg (Polynomial.eval (-1)) hp
  have h2 := congrArg (Polynomial.eval 2) hp
  have hm2 := congrArg (Polynomial.eval (-2)) hp
  have h3 := congrArg (Polynomial.eval 3) hp
  have hm3 := congrArg (Polynomial.eval (-3)) hp
  simp only [eval_pairExceptional, Polynomial.eval_zero] at h0 h1 hm1 h2 hm2 h3 hm3
  norm_num at h0 h1 hm1 h2 hm2 h3 hm3
  have hone : (1 : ℝ) = 0 := by
    simp only [curveTranslate, sqDist] at h0 h1 hm1 h2 hm2 h3 hm3
    linear_combination (h1 + hm1 - 2 * h0) / 48 -
      (h2 + hm2 - 2 * h0) / 120 + (h3 + hm3 - 2 * h0) / 720
  norm_num at hone

/-- One moving point and two distinct fixed points never give the zero
orientation polynomial. -/
theorem oneOrientExceptional_ne_zero (A : Point) {B Cc : Point} (hBC : B ≠ Cc) :
    oneOrientExceptional A B Cc ≠ 0 := by
  intro hp
  have h1 := congrArg (Polynomial.eval 1) hp
  have hm1 := congrArg (Polynomial.eval (-1)) hp
  have h2 := congrArg (Polynomial.eval 2) hp
  have hm2 := congrArg (Polynomial.eval (-2)) hp
  simp only [eval_oneOrientExceptional, Polynomial.eval_zero, curveTranslate, orient] at h1 hm1 h2 hm2
  norm_num at h1 hm1 h2 hm2
  have hx : Cc.1 - B.1 = 0 := by
    linear_combination (h2 - hm2) / 12 - (h1 - hm1) / 6
  have hy : B.2 - Cc.2 = 0 := by
    linear_combination (h1 - hm1) / 2 - hx
  apply hBC
  apply Prod.ext <;> linarith

/-- Two jointly moving distinct points and one fixed point never give the zero
orientation polynomial. -/
theorem twoOrientExceptional_ne_zero {A B : Point} (hAB : A ≠ B) (Cc : Point) :
    twoOrientExceptional A B Cc ≠ 0 := by
  intro hp
  have h1 := congrArg (Polynomial.eval 1) hp
  have hm1 := congrArg (Polynomial.eval (-1)) hp
  have h2 := congrArg (Polynomial.eval 2) hp
  have hm2 := congrArg (Polynomial.eval (-2)) hp
  simp only [eval_twoOrientExceptional, Polynomial.eval_zero, curveTranslate, orient] at h1 hm1 h2 hm2
  norm_num at h1 hm1 h2 hm2
  have hx : A.1 - B.1 = 0 := by
    linear_combination (h2 - hm2) / 12 - (h1 - hm1) / 6
  have hy : B.2 - A.2 = 0 := by
    linear_combination (h1 - hm1) / 2 - hx
  apply hAB
  apply Prod.ext <;> linarith

set_option maxHeartbeats 1000000 in
/-- One moving point and a fixed determinant-nondegenerate triple give a
nonzero cyclicity polynomial. -/
theorem oneCyclicExceptional_ne_zero (A : Point) {B Cc D : Point}
    (hBCD : orient B Cc D ≠ 0) : oneCyclicExceptional A B Cc D ≠ 0 := by
  intro hp
  have h0 := congrArg (Polynomial.eval 0) hp
  have h1 := congrArg (Polynomial.eval 1) hp
  have hm1 := congrArg (Polynomial.eval (-1)) hp
  have h2 := congrArg (Polynomial.eval 2) hp
  have hm2 := congrArg (Polynomial.eval (-2)) hp
  have h3 := congrArg (Polynomial.eval 3) hp
  have hm3 := congrArg (Polynomial.eval (-3)) hp
  simp only [eval_oneCyclicExceptional, Polynomial.eval_zero, curveTranslate,
    cyclicDet] at h0 h1 hm1 h2 hm2 h3 hm3
  norm_num at h0 h1 hm1 h2 hm2 h3 hm3
  apply hBCD
  simp only [orient]
  linear_combination (h1 + hm1 - 2 * h0) / 48 -
    (h2 + hm2 - 2 * h0) / 120 + (h3 + hm3 - 2 * h0) / 720

set_option maxHeartbeats 1000000 in
/-- Three jointly moving determinant-nondegenerate points and one fixed point
give a nonzero cyclicity polynomial. -/
theorem threeCyclicExceptional_ne_zero {A B Cc : Point}
    (hABC : orient A B Cc ≠ 0) (D : Point) :
    threeCyclicExceptional A B Cc D ≠ 0 := by
  intro hp
  have h0 := congrArg (Polynomial.eval 0) hp
  have h1 := congrArg (Polynomial.eval 1) hp
  have hm1 := congrArg (Polynomial.eval (-1)) hp
  have h2 := congrArg (Polynomial.eval 2) hp
  have hm2 := congrArg (Polynomial.eval (-2)) hp
  have h3 := congrArg (Polynomial.eval 3) hp
  have hm3 := congrArg (Polynomial.eval (-3)) hp
  simp only [eval_threeCyclicExceptional, Polynomial.eval_zero, curveTranslate,
    cyclicDet] at h0 h1 hm1 h2 hm2 h3 hm3
  norm_num at h0 h1 hm1 h2 hm2 h3 hm3
  apply hABC
  simp only [orient]
  linear_combination -((h1 + hm1 - 2 * h0) / 48 -
    (h2 + hm2 - 2 * h0) / 120 + (h3 + hm3 - 2 * h0) / 720)

/-- Degree-six and degree-four coefficients of the two-moving/two-fixed
cyclic determinant. -/
def twoCyclicK6 (A B Cc D : Point) : ℝ :=
  -(A.1 - B.1) * (Cc.2 - D.2) - (A.2 - B.2) * (Cc.1 - D.1)

def twoCyclicK4 (A B Cc D : Point) : ℝ :=
  -2 * ((A.1 - B.1) * (Cc.1 - D.1) -
    (A.2 - B.2) * (Cc.2 - D.2))

set_option maxHeartbeats 1000000 in
/-- Symmetrizing in `t` removes every odd term and exposes only the two
coefficients needed below. -/
theorem twoCyclic_even_identity (t : ℝ) (A B Cc D : Point) :
    cyclicDet (curveTranslate t A) (curveTranslate t B) Cc D +
      cyclicDet (curveTranslate (-t) A) (curveTranslate (-t) B) Cc D -
      2 * cyclicDet (curveTranslate 0 A) (curveTranslate 0 B) Cc D =
    2 * twoCyclicK6 A B Cc D * (t ^ 6 - t ^ 2) +
      2 * twoCyclicK4 A B Cc D * t ^ 4 := by
  simp only [cyclicDet, curveTranslate, twoCyclicK6, twoCyclicK4]
  ring

/-- Two distinct jointly moving points and two distinct fixed points give a
nonzero cyclicity polynomial.  Its degree-six and degree-four coefficients are
the real and imaginary parts of the product of the two nonzero displacement
vectors. -/
theorem twoCyclicExceptional_ne_zero {A B Cc D : Point}
    (hAB : A ≠ B) (hCD : Cc ≠ D) : twoCyclicExceptional A B Cc D ≠ 0 := by
  intro hp
  have h0 := congrArg (Polynomial.eval 0) hp
  have h1 := congrArg (Polynomial.eval 1) hp
  have hm1 := congrArg (Polynomial.eval (-1)) hp
  have h2 := congrArg (Polynomial.eval 2) hp
  have hm2 := congrArg (Polynomial.eval (-2)) hp
  simp only [eval_twoCyclicExceptional, Polynomial.eval_zero] at h0 h1 hm1 h2 hm2
  have he1 := twoCyclic_even_identity 1 A B Cc D
  have he2 := twoCyclic_even_identity 2 A B Cc D
  rw [h1, hm1, h0] at he1
  rw [h2, hm2, h0] at he2
  norm_num at he1 he2
  have h4 : twoCyclicK4 A B Cc D = 0 := by linarith
  have h6 : twoCyclicK6 A B Cc D = 0 := by linarith
  have hsum : (A.1 - B.1) * (Cc.2 - D.2) +
      (A.2 - B.2) * (Cc.1 - D.1) = 0 := by
    simp only [twoCyclicK6] at h6
    linarith
  have hdiff : (A.1 - B.1) * (Cc.1 - D.1) -
      (A.2 - B.2) * (Cc.2 - D.2) = 0 := by
    simp only [twoCyclicK4] at h4
    linarith
  have hprod :
      ((A.1 - B.1) ^ 2 + (A.2 - B.2) ^ 2) *
        ((Cc.1 - D.1) ^ 2 + (Cc.2 - D.2) ^ 2) = 0 := by
    calc
      _ = ((A.1 - B.1) * (Cc.2 - D.2) +
            (A.2 - B.2) * (Cc.1 - D.1)) ^ 2 +
          ((A.1 - B.1) * (Cc.1 - D.1) -
            (A.2 - B.2) * (Cc.2 - D.2)) ^ 2 := by ring
      _ = 0 := by rw [hsum, hdiff]; norm_num
  rcases mul_eq_zero.mp hprod with hnorm | hnorm
  · have hpairs := (add_eq_zero_iff_of_nonneg (sq_nonneg (A.1 - B.1))
        (sq_nonneg (A.2 - B.2))).mp hnorm
    apply hAB
    apply Prod.ext
    · linarith [sq_eq_zero_iff.mp hpairs.1]
    · linarith [sq_eq_zero_iff.mp hpairs.2]
  · have hpairs := (add_eq_zero_iff_of_nonneg (sq_nonneg (Cc.1 - D.1))
        (sq_nonneg (Cc.2 - D.2))).mp hnorm
    apply hCD
    apply Prod.ext
    · linarith [sq_eq_zero_iff.mp hpairs.1]
    · linarith [sq_eq_zero_iff.mp hpairs.2]

/-! ## One generic adjoining step -/

/-- Old points stay fixed and new points follow the cubic translation. -/
def adjoinPoint {α β : Type*} (P : β → Point) (Q : α → Point) (t : ℝ) :
    Sum β α → Point
  | .inl b => P b
  | .inr a => curveTranslate t (Q a)

/-- Polynomial coordinates of a prospective joined point. -/
def joinedXPoly {α β : Type*} (P : β → Point) (Q : α → Point) :
    Sum β α → ℝ[X]
  | .inl b => constX (P b)
  | .inr a => moveX (Q a)

def joinedYPoly {α β : Type*} (P : β → Point) (Q : α → Point) :
    Sum β α → ℝ[X]
  | .inl b => constY (P b)
  | .inr a => moveY (Q a)

def joinedOrientPoly {α β : Type*} (P : β → Point) (Q : α → Point)
    (v : Fin 3 → Sum β α) : ℝ[X] :=
  orientPoly (joinedXPoly P Q (v 0)) (joinedYPoly P Q (v 0))
    (joinedXPoly P Q (v 1)) (joinedYPoly P Q (v 1))
    (joinedXPoly P Q (v 2)) (joinedYPoly P Q (v 2))

def joinedCyclicPoly {α β : Type*} (P : β → Point) (Q : α → Point)
    (v : Fin 4 → Sum β α) : ℝ[X] :=
  cyclicPoly (joinedXPoly P Q (v 0)) (joinedYPoly P Q (v 0))
    (joinedXPoly P Q (v 1)) (joinedYPoly P Q (v 1))
    (joinedXPoly P Q (v 2)) (joinedYPoly P Q (v 2))
    (joinedXPoly P Q (v 3)) (joinedYPoly P Q (v 3))

@[simp] theorem eval_joinedXPoly {α β : Type*} (P : β → Point) (Q : α → Point)
    (t : ℝ) (x : Sum β α) :
    Polynomial.eval t (joinedXPoly P Q x) = (adjoinPoint P Q t x).1 := by
  cases x <;> simp [joinedXPoly, adjoinPoint, constX, moveX, curveTranslate]

@[simp] theorem eval_joinedYPoly {α β : Type*} (P : β → Point) (Q : α → Point)
    (t : ℝ) (x : Sum β α) :
    Polynomial.eval t (joinedYPoly P Q x) = (adjoinPoint P Q t x).2 := by
  cases x <;> simp [joinedYPoly, adjoinPoint, constY, moveY, curveTranslate]

@[simp] theorem eval_joinedOrientPoly {α β : Type*} (P : β → Point)
    (Q : α → Point) (t : ℝ) (v : Fin 3 → Sum β α) :
    Polynomial.eval t (joinedOrientPoly P Q v) =
      orient (adjoinPoint P Q t (v 0)) (adjoinPoint P Q t (v 1))
        (adjoinPoint P Q t (v 2)) := by
  simp [joinedOrientPoly, orientPoly, orient]

@[simp] theorem eval_joinedCyclicPoly {α β : Type*} (P : β → Point)
    (Q : α → Point) (t : ℝ) (v : Fin 4 → Sum β α) :
    Polynomial.eval t (joinedCyclicPoly P Q v) =
      cyclicDet (adjoinPoint P Q t (v 0)) (adjoinPoint P Q t (v 1))
        (adjoinPoint P Q t (v 2)) (adjoinPoint P Q t (v 3)) := by
  simp [joinedCyclicPoly, cyclicPoly, cyclicDet]

private theorem vec3_ne {σ : Type*} {v : Fin 3 → σ} (hvi : Function.Injective v) :
    v 0 ≠ v 1 ∧ v 0 ≠ v 2 ∧ v 1 ≠ v 2 := by
  exact ⟨fun h => (by decide : (0 : Fin 3) ≠ 1) (hvi h),
    fun h => (by decide : (0 : Fin 3) ≠ 2) (hvi h),
    fun h => (by decide : (1 : Fin 3) ≠ 2) (hvi h)⟩

set_option maxHeartbeats 1000000 in
/-- Every injective joined triple has a genuine orientation polynomial. -/
theorem joinedOrientPoly_ne_zero {α β : Type*} (P : β → Point) (Q : α → Point)
    (hP : StrongIndexedGeneralPosition P) (hQ : StrongIndexedGeneralPosition Q)
    (v : Fin 3 → Sum β α) (hvi : Function.Injective v) :
    joinedOrientPoly P Q v ≠ 0 := by
  obtain ⟨h01, h02, h12⟩ := vec3_ne hvi
  cases h0 : v 0 with
  | inl b0 =>
    cases h1 : v 1 with
    | inl b1 =>
      cases h2 : v 2 with
      | inl b2 =>
        intro hp
        have he := congrArg (Polynomial.eval 0) hp
        simp only [eval_joinedOrientPoly, Polynomial.eval_zero] at he
        let w : Fin 3 → β := ![b0, b1, b2]
        have hb01 : b0 ≠ b1 := by intro h; apply h01; rw [h0, h1, h]
        have hb02 : b0 ≠ b2 := by intro h; apply h02; rw [h0, h2, h]
        have hb12 : b1 ≠ b2 := by intro h; apply h12; rw [h1, h2, h]
        have hwi : Function.Injective w := by
          intro i j hij
          fin_cases i <;> fin_cases j <;> simp_all [w]
        apply hP.2.1 w hwi
        simpa [adjoinPoint, h0, h1, h2, w, curveTranslate] using he
      | inr a2 =>
        have hb01 : P b0 ≠ P b1 := fun h => h01 (by
          rw [h0, h1, hP.1 h])
        intro hp
        apply oneOrientExceptional_ne_zero (Q a2) hb01
        calc
          oneOrientExceptional (Q a2) (P b0) (P b1) =
              joinedOrientPoly P Q v := by
                simp [oneOrientExceptional, joinedOrientPoly, joinedXPoly,
                  joinedYPoly, h0, h1, h2, orientPoly]
                ring
          _ = 0 := by assumption
    | inr a1 =>
      cases h2 : v 2 with
      | inl b2 =>
        have hb02 : P b0 ≠ P b2 := fun h => h02 (by
          rw [h0, h2, hP.1 h])
        intro hp
        apply oneOrientExceptional_ne_zero (Q a1) hb02
        calc
          oneOrientExceptional (Q a1) (P b0) (P b2) =
              -joinedOrientPoly P Q v := by
                simp [oneOrientExceptional, joinedOrientPoly, joinedXPoly,
                  joinedYPoly, h0, h1, h2, orientPoly]
                ring
          _ = 0 := by rw [show joinedOrientPoly P Q v = 0 by assumption]; simp
      | inr a2 =>
        have ha12 : Q a1 ≠ Q a2 := fun h => h12 (by
          rw [h1, h2, hQ.1 h])
        intro hp
        apply twoOrientExceptional_ne_zero ha12 (P b0)
        calc
          twoOrientExceptional (Q a1) (Q a2) (P b0) =
              joinedOrientPoly P Q v := by
                simp [twoOrientExceptional, joinedOrientPoly, joinedXPoly,
                  joinedYPoly, h0, h1, h2, orientPoly]
                ring
          _ = 0 := by assumption
  | inr a0 =>
    cases h1 : v 1 with
    | inl b1 =>
      cases h2 : v 2 with
      | inl b2 =>
        have hb12 : P b1 ≠ P b2 := fun h => h12 (by
          rw [h1, h2, hP.1 h])
        intro hp
        apply oneOrientExceptional_ne_zero (Q a0) hb12
        calc
          oneOrientExceptional (Q a0) (P b1) (P b2) =
              joinedOrientPoly P Q v := by
                simp [oneOrientExceptional, joinedOrientPoly, joinedXPoly,
                  joinedYPoly, h0, h1, h2, orientPoly]
          _ = 0 := hp
      | inr a2 =>
        have ha02 : Q a0 ≠ Q a2 := fun h => h02 (by
          rw [h0, h2, hQ.1 h])
        intro hp
        apply twoOrientExceptional_ne_zero ha02 (P b1)
        calc
          twoOrientExceptional (Q a0) (Q a2) (P b1) =
              -joinedOrientPoly P Q v := by
                simp [twoOrientExceptional, joinedOrientPoly, joinedXPoly,
                  joinedYPoly, h0, h1, h2, orientPoly]
                ring
          _ = 0 := by rw [show joinedOrientPoly P Q v = 0 by assumption]; simp
    | inr a1 =>
      cases h2 : v 2 with
      | inl b2 =>
        have ha01 : Q a0 ≠ Q a1 := fun h => h01 (by
          rw [h0, h1, hQ.1 h])
        intro hp
        apply twoOrientExceptional_ne_zero ha01 (P b2)
        calc
          twoOrientExceptional (Q a0) (Q a1) (P b2) =
              joinedOrientPoly P Q v := by
                simp [twoOrientExceptional, joinedOrientPoly, joinedXPoly,
                  joinedYPoly, h0, h1, h2, orientPoly]
          _ = 0 := hp
      | inr a2 =>
        intro hp
        have he := congrArg (Polynomial.eval 0) hp
        simp only [eval_joinedOrientPoly, Polynomial.eval_zero] at he
        let w : Fin 3 → α := ![a0, a1, a2]
        have ha01 : a0 ≠ a1 := by intro h; apply h01; rw [h0, h1, h]
        have ha02 : a0 ≠ a2 := by intro h; apply h02; rw [h0, h2, h]
        have ha12 : a1 ≠ a2 := by intro h; apply h12; rw [h1, h2, h]
        have hwi : Function.Injective w := by
          intro i j hij
          fin_cases i <;> fin_cases j <;> simp_all [w]
        apply hQ.2.1 w hwi
        simpa [adjoinPoint, h0, h1, h2, w, curveTranslate] using he

private theorem vec4_injective {σ : Type*} {a b c d : σ}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    Function.Injective (![a, b, c, d] : Fin 4 → σ) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

private theorem strong_orient3 {σ : Type*} {P : σ → Point}
    (hP : StrongIndexedGeneralPosition P) {a b c : σ}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    orient (P a) (P b) (P c) ≠ 0 := by
  let w : Fin 3 → σ := ![a, b, c]
  have hwi : Function.Injective w := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [w]
  simpa [w] using hP.2.1 w hwi

set_option maxHeartbeats 3000000 in
/-- Every injective joined quadruple has a genuine cyclic-determinant
polynomial. -/
theorem joinedCyclicPoly_ne_zero {α β : Type*} (P : β → Point) (Q : α → Point)
    (hP : StrongIndexedGeneralPosition P) (hQ : StrongIndexedGeneralPosition Q)
    (v : Fin 4 → Sum β α) (hvi : Function.Injective v) :
    joinedCyclicPoly P Q v ≠ 0 := by
  have h01 : v 0 ≠ v 1 := fun h => (by decide : (0 : Fin 4) ≠ 1) (hvi h)
  have h02 : v 0 ≠ v 2 := fun h => (by decide : (0 : Fin 4) ≠ 2) (hvi h)
  have h03 : v 0 ≠ v 3 := fun h => (by decide : (0 : Fin 4) ≠ 3) (hvi h)
  have h12 : v 1 ≠ v 2 := fun h => (by decide : (1 : Fin 4) ≠ 2) (hvi h)
  have h13 : v 1 ≠ v 3 := fun h => (by decide : (1 : Fin 4) ≠ 3) (hvi h)
  have h23 : v 2 ≠ v 3 := fun h => (by decide : (2 : Fin 4) ≠ 3) (hvi h)
  cases h0 : v 0 with
  | inl b0 =>
    cases h1 : v 1 with
    | inl b1 =>
      cases h2 : v 2 with
      | inl b2 =>
        cases h3 : v 3 with
        | inl b3 =>
          intro hp
          have he := congrArg (Polynomial.eval 0) hp
          simp only [eval_joinedCyclicPoly, Polynomial.eval_zero] at he
          have hb01 : b0 ≠ b1 := by intro h; apply h01; rw [h0, h1, h]
          have hb02 : b0 ≠ b2 := by intro h; apply h02; rw [h0, h2, h]
          have hb03 : b0 ≠ b3 := by intro h; apply h03; rw [h0, h3, h]
          have hb12 : b1 ≠ b2 := by intro h; apply h12; rw [h1, h2, h]
          have hb13 : b1 ≠ b3 := by intro h; apply h13; rw [h1, h3, h]
          have hb23 : b2 ≠ b3 := by intro h; apply h23; rw [h2, h3, h]
          let w : Fin 4 → β := ![b0, b1, b2, b3]
          apply hP.2.2 w (vec4_injective hb01 hb02 hb03 hb12 hb13 hb23)
          simpa [adjoinPoint, h0, h1, h2, h3, w, curveTranslate] using he
        | inr a3 =>
          have hb01 : b0 ≠ b1 := by intro h; apply h01; rw [h0, h1, h]
          have hb02 : b0 ≠ b2 := by intro h; apply h02; rw [h0, h2, h]
          have hb12 : b1 ≠ b2 := by intro h; apply h12; rw [h1, h2, h]
          intro hp
          apply oneCyclicExceptional_ne_zero (Q a3)
            (strong_orient3 hP hb01 hb02 hb12)
          calc
            oneCyclicExceptional (Q a3) (P b0) (P b1) (P b2) =
                -joinedCyclicPoly P Q v := by
              simp [oneCyclicExceptional, joinedCyclicPoly, joinedXPoly,
                joinedYPoly, h0, h1, h2, h3, cyclicPoly]
              ring
            _ = 0 := by rw [hp]; simp
      | inr a2 =>
        cases h3 : v 3 with
        | inl b3 =>
          have hb01 : b0 ≠ b1 := by intro h; apply h01; rw [h0, h1, h]
          have hb03 : b0 ≠ b3 := by intro h; apply h03; rw [h0, h3, h]
          have hb13 : b1 ≠ b3 := by intro h; apply h13; rw [h1, h3, h]
          intro hp
          apply oneCyclicExceptional_ne_zero (Q a2)
            (strong_orient3 hP hb01 hb03 hb13)
          calc
            oneCyclicExceptional (Q a2) (P b0) (P b1) (P b3) =
                joinedCyclicPoly P Q v := by
              simp [oneCyclicExceptional, joinedCyclicPoly, joinedXPoly,
                joinedYPoly, h0, h1, h2, h3, cyclicPoly]
              ring
            _ = 0 := hp
        | inr a3 =>
          have ha23 : Q a2 ≠ Q a3 := fun h => h23 (by rw [h2, h3, hQ.1 h])
          have hb01 : P b0 ≠ P b1 := fun h => h01 (by rw [h0, h1, hP.1 h])
          intro hp
          apply twoCyclicExceptional_ne_zero ha23 hb01
          calc
            twoCyclicExceptional (Q a2) (Q a3) (P b0) (P b1) =
                joinedCyclicPoly P Q v := by
              simp [twoCyclicExceptional, joinedCyclicPoly, joinedXPoly,
                joinedYPoly, h0, h1, h2, h3, cyclicPoly]
              ring
            _ = 0 := hp
    | inr a1 =>
      cases h2 : v 2 with
      | inl b2 =>
        cases h3 : v 3 with
        | inl b3 =>
          have hb02 : b0 ≠ b2 := by intro h; apply h02; rw [h0, h2, h]
          have hb03 : b0 ≠ b3 := by intro h; apply h03; rw [h0, h3, h]
          have hb23 : b2 ≠ b3 := by intro h; apply h23; rw [h2, h3, h]
          intro hp
          apply oneCyclicExceptional_ne_zero (Q a1)
            (strong_orient3 hP hb02 hb03 hb23)
          calc
            oneCyclicExceptional (Q a1) (P b0) (P b2) (P b3) =
                -joinedCyclicPoly P Q v := by
              simp [oneCyclicExceptional, joinedCyclicPoly, joinedXPoly,
                joinedYPoly, h0, h1, h2, h3, cyclicPoly]
              ring
            _ = 0 := by rw [hp]; simp
        | inr a3 =>
          have ha13 : Q a1 ≠ Q a3 := fun h => h13 (by rw [h1, h3, hQ.1 h])
          have hb02 : P b0 ≠ P b2 := fun h => h02 (by rw [h0, h2, hP.1 h])
          intro hp
          apply twoCyclicExceptional_ne_zero ha13 hb02
          calc
            twoCyclicExceptional (Q a1) (Q a3) (P b0) (P b2) =
                -joinedCyclicPoly P Q v := by
              simp [twoCyclicExceptional, joinedCyclicPoly, joinedXPoly,
                joinedYPoly, h0, h1, h2, h3, cyclicPoly]
              ring
            _ = 0 := by rw [hp]; simp
      | inr a2 =>
        cases h3 : v 3 with
        | inl b3 =>
          have ha12 : Q a1 ≠ Q a2 := fun h => h12 (by rw [h1, h2, hQ.1 h])
          have hb03 : P b0 ≠ P b3 := fun h => h03 (by rw [h0, h3, hP.1 h])
          intro hp
          apply twoCyclicExceptional_ne_zero ha12 hb03
          calc
            twoCyclicExceptional (Q a1) (Q a2) (P b0) (P b3) =
                joinedCyclicPoly P Q v := by
              simp [twoCyclicExceptional, joinedCyclicPoly, joinedXPoly,
                joinedYPoly, h0, h1, h2, h3, cyclicPoly]
              ring
            _ = 0 := hp
        | inr a3 =>
          have ha12 : a1 ≠ a2 := by intro h; apply h12; rw [h1, h2, h]
          have ha13 : a1 ≠ a3 := by intro h; apply h13; rw [h1, h3, h]
          have ha23 : a2 ≠ a3 := by intro h; apply h23; rw [h2, h3, h]
          intro hp
          apply threeCyclicExceptional_ne_zero
            (strong_orient3 hQ ha12 ha13 ha23) (P b0)
          calc
            threeCyclicExceptional (Q a1) (Q a2) (Q a3) (P b0) =
                -joinedCyclicPoly P Q v := by
              simp [threeCyclicExceptional, joinedCyclicPoly, joinedXPoly,
                joinedYPoly, h0, h1, h2, h3, cyclicPoly]
              ring
            _ = 0 := by rw [hp]; simp
  | inr a0 =>
    cases h1 : v 1 with
    | inl b1 =>
      cases h2 : v 2 with
      | inl b2 =>
        cases h3 : v 3 with
        | inl b3 =>
          have hb12 : b1 ≠ b2 := by intro h; apply h12; rw [h1, h2, h]
          have hb13 : b1 ≠ b3 := by intro h; apply h13; rw [h1, h3, h]
          have hb23 : b2 ≠ b3 := by intro h; apply h23; rw [h2, h3, h]
          intro hp
          apply oneCyclicExceptional_ne_zero (Q a0)
            (strong_orient3 hP hb12 hb13 hb23)
          calc
            oneCyclicExceptional (Q a0) (P b1) (P b2) (P b3) =
                joinedCyclicPoly P Q v := by
              simp [oneCyclicExceptional, joinedCyclicPoly, joinedXPoly,
                joinedYPoly, h0, h1, h2, h3, cyclicPoly]
            _ = 0 := hp
        | inr a3 =>
          have ha03 : Q a0 ≠ Q a3 := fun h => h03 (by rw [h0, h3, hQ.1 h])
          have hb12 : P b1 ≠ P b2 := fun h => h12 (by rw [h1, h2, hP.1 h])
          intro hp
          apply twoCyclicExceptional_ne_zero ha03 hb12
          calc
            twoCyclicExceptional (Q a0) (Q a3) (P b1) (P b2) =
                joinedCyclicPoly P Q v := by
              simp [twoCyclicExceptional, joinedCyclicPoly, joinedXPoly,
                joinedYPoly, h0, h1, h2, h3, cyclicPoly]
              ring
            _ = 0 := hp
      | inr a2 =>
        cases h3 : v 3 with
        | inl b3 =>
          have ha02 : Q a0 ≠ Q a2 := fun h => h02 (by rw [h0, h2, hQ.1 h])
          have hb13 : P b1 ≠ P b3 := fun h => h13 (by rw [h1, h3, hP.1 h])
          intro hp
          apply twoCyclicExceptional_ne_zero ha02 hb13
          calc
            twoCyclicExceptional (Q a0) (Q a2) (P b1) (P b3) =
                -joinedCyclicPoly P Q v := by
              simp [twoCyclicExceptional, joinedCyclicPoly, joinedXPoly,
                joinedYPoly, h0, h1, h2, h3, cyclicPoly]
              ring
            _ = 0 := by rw [hp]; simp
        | inr a3 =>
          have ha02 : a0 ≠ a2 := by intro h; apply h02; rw [h0, h2, h]
          have ha03 : a0 ≠ a3 := by intro h; apply h03; rw [h0, h3, h]
          have ha23 : a2 ≠ a3 := by intro h; apply h23; rw [h2, h3, h]
          intro hp
          apply threeCyclicExceptional_ne_zero
            (strong_orient3 hQ ha02 ha03 ha23) (P b1)
          calc
            threeCyclicExceptional (Q a0) (Q a2) (Q a3) (P b1) =
                joinedCyclicPoly P Q v := by
              simp [threeCyclicExceptional, joinedCyclicPoly, joinedXPoly,
                joinedYPoly, h0, h1, h2, h3, cyclicPoly]
              ring
            _ = 0 := hp
    | inr a1 =>
      cases h2 : v 2 with
      | inl b2 =>
        cases h3 : v 3 with
        | inl b3 =>
          have ha01 : Q a0 ≠ Q a1 := fun h => h01 (by rw [h0, h1, hQ.1 h])
          have hb23 : P b2 ≠ P b3 := fun h => h23 (by rw [h2, h3, hP.1 h])
          intro hp
          apply twoCyclicExceptional_ne_zero ha01 hb23
          calc
            twoCyclicExceptional (Q a0) (Q a1) (P b2) (P b3) =
                joinedCyclicPoly P Q v := by
              simp [twoCyclicExceptional, joinedCyclicPoly, joinedXPoly,
                joinedYPoly, h0, h1, h2, h3, cyclicPoly]
            _ = 0 := hp
        | inr a3 =>
          have ha01 : a0 ≠ a1 := by intro h; apply h01; rw [h0, h1, h]
          have ha03 : a0 ≠ a3 := by intro h; apply h03; rw [h0, h3, h]
          have ha13 : a1 ≠ a3 := by intro h; apply h13; rw [h1, h3, h]
          intro hp
          apply threeCyclicExceptional_ne_zero
            (strong_orient3 hQ ha01 ha03 ha13) (P b2)
          calc
            threeCyclicExceptional (Q a0) (Q a1) (Q a3) (P b2) =
                -joinedCyclicPoly P Q v := by
              simp [threeCyclicExceptional, joinedCyclicPoly, joinedXPoly,
                joinedYPoly, h0, h1, h2, h3, cyclicPoly]
              ring
            _ = 0 := by rw [hp]; simp
      | inr a2 =>
        cases h3 : v 3 with
        | inl b3 =>
          have ha01 : a0 ≠ a1 := by intro h; apply h01; rw [h0, h1, h]
          have ha02 : a0 ≠ a2 := by intro h; apply h02; rw [h0, h2, h]
          have ha12 : a1 ≠ a2 := by intro h; apply h12; rw [h1, h2, h]
          intro hp
          apply threeCyclicExceptional_ne_zero
            (strong_orient3 hQ ha01 ha02 ha12) (P b3)
          calc
            threeCyclicExceptional (Q a0) (Q a1) (Q a2) (P b3) =
                joinedCyclicPoly P Q v := by
              simp [threeCyclicExceptional, joinedCyclicPoly, joinedXPoly,
                joinedYPoly, h0, h1, h2, h3, cyclicPoly]
            _ = 0 := hp
        | inr a3 =>
          intro hp
          have he := congrArg (Polynomial.eval 0) hp
          simp only [eval_joinedCyclicPoly, Polynomial.eval_zero] at he
          have ha01 : a0 ≠ a1 := by intro h; apply h01; rw [h0, h1, h]
          have ha02 : a0 ≠ a2 := by intro h; apply h02; rw [h0, h2, h]
          have ha03 : a0 ≠ a3 := by intro h; apply h03; rw [h0, h3, h]
          have ha12 : a1 ≠ a2 := by intro h; apply h12; rw [h1, h2, h]
          have ha13 : a1 ≠ a3 := by intro h; apply h13; rw [h1, h3, h]
          have ha23 : a2 ≠ a3 := by intro h; apply h23; rw [h2, h3, h]
          let w : Fin 4 → α := ![a0, a1, a2, a3]
          apply hQ.2.2 w (vec4_injective ha01 ha02 ha03 ha12 ha13 ha23)
          simpa [adjoinPoint, h0, h1, h2, h3, w, curveTranslate] using he

variable {α β : Type*} [Fintype α] [Fintype β]

noncomputable def joinedPairProduct (P : β → Point) (Q : α → Point) : ℝ[X] :=
  ∏ a : α, ∏ b : β, pairExceptional (Q a) (P b)

noncomputable def joinedTripleFactor (P : β → Point) (Q : α → Point)
    (v : Fin 3 → Sum β α) : ℝ[X] := by
  classical
  exact if Function.Injective v then joinedOrientPoly P Q v else 1

noncomputable def joinedTripleProduct (P : β → Point) (Q : α → Point) : ℝ[X] :=
  ∏ v : Fin 3 → Sum β α, joinedTripleFactor P Q v

noncomputable def joinedQuadFactor (P : β → Point) (Q : α → Point)
    (v : Fin 4 → Sum β α) : ℝ[X] := by
  classical
  exact if Function.Injective v then joinedCyclicPoly P Q v else 1

noncomputable def joinedQuadProduct (P : β → Point) (Q : α → Point) : ℝ[X] :=
  ∏ v : Fin 4 → Sum β α, joinedQuadFactor P Q v

noncomputable def joinedExceptionalProduct (P : β → Point) (Q : α → Point) : ℝ[X] :=
  joinedPairProduct P Q * joinedTripleProduct P Q * joinedQuadProduct P Q

/-- The complete finite product of mixed point-incidence constraints is
nonzero. -/
theorem joinedExceptionalProduct_ne_zero (P : β → Point) (Q : α → Point)
    (hP : StrongIndexedGeneralPosition P) (hQ : StrongIndexedGeneralPosition Q) :
    joinedExceptionalProduct P Q ≠ 0 := by
  classical
  apply mul_ne_zero
  · apply mul_ne_zero
    · apply Finset.prod_ne_zero_iff.mpr
      intro a ha
      apply Finset.prod_ne_zero_iff.mpr
      intro b hb
      exact pairExceptional_ne_zero (Q a) (P b)
    · apply Finset.prod_ne_zero_iff.mpr
      intro v hv
      simp only [joinedTripleFactor]
      split_ifs with hvi
      · exact joinedOrientPoly_ne_zero P Q hP hQ v hvi
      · exact one_ne_zero
  · apply Finset.prod_ne_zero_iff.mpr
    intro v hv
    simp only [joinedQuadFactor]
    split_ifs with hvi
    · exact joinedCyclicPoly_ne_zero P Q hP hQ v hvi
    · exact one_ne_zero

/-- A rational cubic-translation parameter simultaneously avoids every mixed
collision, collinearity and cyclicity constraint. -/
theorem exists_rational_good_translation_parameter (P : β → Point) (Q : α → Point)
    (hP : StrongIndexedGeneralPosition P) (hQ : StrongIndexedGeneralPosition Q) :
    ∃ q : ℚ,
      Polynomial.eval (q : ℝ) (joinedPairProduct P Q) ≠ 0 ∧
      Polynomial.eval (q : ℝ) (joinedTripleProduct P Q) ≠ 0 ∧
      Polynomial.eval (q : ℝ) (joinedQuadProduct P Q) ≠ 0 := by
  obtain ⟨q, hq⟩ := Circle.GenericBooster.exists_rational_polynomial_eval_ne_zero
    (joinedExceptionalProduct P Q) (joinedExceptionalProduct_ne_zero P Q hP hQ)
  simp only [joinedExceptionalProduct, Polynomial.eval_mul, mul_ne_zero_iff] at hq
  exact ⟨q, hq.1.1, hq.1.2, hq.2⟩

/-- One rational translation adjoins a finite strong-GP block to a finite
strong-GP family. -/
theorem exists_rational_strongGP_adjoin (P : β → Point) (Q : α → Point)
    (hP : StrongIndexedGeneralPosition P) (hQ : StrongIndexedGeneralPosition Q) :
    ∃ q : ℚ, StrongIndexedGeneralPosition (adjoinPoint P Q (q : ℝ)) := by
  classical
  obtain ⟨q, hpairs, htriples, hquads⟩ :=
    exists_rational_good_translation_parameter P Q hP hQ
  have hpair (a : α) (b : β) :
      sqDist (curveTranslate (q : ℝ) (Q a)) (P b) ≠ 0 := by
    simp only [joinedPairProduct, Polynomial.eval_prod] at hpairs
    have ha := (Finset.prod_ne_zero_iff.mp hpairs) a (Finset.mem_univ a)
    have hb := (Finset.prod_ne_zero_iff.mp ha) b (Finset.mem_univ b)
    simpa using hb
  have htriple (v : Fin 3 → Sum β α) (hvi : Function.Injective v) :
      orient (adjoinPoint P Q (q : ℝ) (v 0))
        (adjoinPoint P Q (q : ℝ) (v 1))
        (adjoinPoint P Q (q : ℝ) (v 2)) ≠ 0 := by
    simp only [joinedTripleProduct, Polynomial.eval_prod] at htriples
    have hv := (Finset.prod_ne_zero_iff.mp htriples) v (Finset.mem_univ v)
    simp only [joinedTripleFactor, if_pos hvi] at hv
    simpa using hv
  have hquad (v : Fin 4 → Sum β α) (hvi : Function.Injective v) :
      cyclicDet (adjoinPoint P Q (q : ℝ) (v 0))
        (adjoinPoint P Q (q : ℝ) (v 1))
        (adjoinPoint P Q (q : ℝ) (v 2))
        (adjoinPoint P Q (q : ℝ) (v 3)) ≠ 0 := by
    simp only [joinedQuadProduct, Polynomial.eval_prod] at hquads
    have hv := (Finset.prod_ne_zero_iff.mp hquads) v (Finset.mem_univ v)
    simp only [joinedQuadFactor, if_pos hvi] at hv
    simpa using hv
  refine ⟨q, ?_, htriple, hquad⟩
  intro x y hxy
  cases x with
  | inl b =>
    cases y with
    | inl c => exact congrArg Sum.inl (hP.1 hxy)
    | inr a =>
      exfalso
      apply hpair a b
      simp only [adjoinPoint] at hxy
      rw [← hxy]
      simp [sqDist]
  | inr a =>
    cases y with
    | inl b =>
      exfalso
      apply hpair a b
      simp only [adjoinPoint] at hxy
      rw [hxy]
      simp [sqDist]
    | inr c =>
      apply congrArg Sum.inr
      apply hQ.1
      have hx := congrArg Prod.fst hxy
      have hy := congrArg Prod.snd hxy
      simp only [adjoinPoint, curveTranslate] at hx hy
      apply Prod.ext <;> linarith

/-! ## Countably many recursively translated finite witnesses -/

/-- One finite witness block, packaged with its finite/nonempty index type. -/
structure BlockData (k : ℕ) where
  Carrier : Type
  fintypeCarrier : Fintype Carrier
  nonemptyCarrier : Nonempty Carrier
  point : Carrier → Point
  strong : StrongIndexedGeneralPosition point
  noColor : NoKPointColoring point k

private theorem exists_blockData (k : ℕ) : Nonempty (BlockData k) := by
  obtain ⟨α, αfin, αne, P, hstrong, hindexed, hrat, hno⟩ :=
    exists_finite_rational_generalPosition_noKPointColoring k
  exact ⟨⟨α, αfin, αne, P, hstrong, hno⟩⟩

/-- A fixed finite witness for each color count. -/
noncomputable def blockData (k : ℕ) : BlockData k :=
  Classical.choice (exists_blockData k)

noncomputable instance blockFintype (k : ℕ) : Fintype (blockData k).Carrier :=
  (blockData k).fintypeCarrier

noncomputable instance blockNonempty (k : ℕ) : Nonempty (blockData k).Carrier :=
  (blockData k).nonemptyCarrier

abbrev BlockCarrier (k : ℕ) := (blockData k).Carrier

/-- Indices of the first `n` heterogeneous blocks. -/
abbrev PrefixIndex (n : ℕ) := Σ i : Fin n, BlockCarrier i.val

/-- Adding the last sigma fiber is equivalent to adjoining one new block. -/
noncomputable def prefixSuccEquiv (n : ℕ) :
    Sum (PrefixIndex n) (BlockCarrier n) ≃ PrefixIndex (n + 1) where
  toFun
    | .inl ⟨i, a⟩ => ⟨i.castSucc, a⟩
    | .inr a => ⟨Fin.last n, a⟩
  invFun z := Fin.lastCases
    (motive := fun i => BlockCarrier i.val → Sum (PrefixIndex n) (BlockCarrier n))
    (fun a => Sum.inr a) (fun i a => Sum.inl ⟨i, a⟩) z.1 z.2
  left_inv x := by
    cases x with
    | inl z => rcases z with ⟨i, a⟩; simp
    | inr a => simp
  right_inv z := by
    rcases z with ⟨i, a⟩
    revert a
    refine Fin.lastCases ?_ (fun j => ?_) i
    · intro a; simp only [Fin.lastCases_last]
    · intro a; simp only [Fin.lastCases_castSucc]

/-- Determinant general position is invariant under an equivalence of indices. -/
theorem strong_reindex {γ δ : Type*} (e : γ ≃ δ) {P : γ → Point}
    (hP : StrongIndexedGeneralPosition P) :
    StrongIndexedGeneralPosition (fun d => P (e.symm d)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact hP.1.comp e.symm.injective
  · intro v hvi
    let w : Fin 3 → γ := fun i => e.symm (v i)
    exact hP.2.1 w (e.symm.injective.comp hvi)
  · intro v hvi
    let w : Fin 4 → γ := fun i => e.symm (v i)
    exact hP.2.2 w (e.symm.injective.comp hvi)

/-- One rational parameter per block in a finite prefix. -/
abbrev PrefixParams (n : ℕ) := Fin n → ℚ

/-- Point family represented by a finite parameter prefix. -/
def prefixPoint (n : ℕ) (ps : PrefixParams n) : PrefixIndex n → Point
  | ⟨i, a⟩ => curveTranslate (ps i : ℝ) ((blockData i.val).point a)

/-- Extend a parameter prefix by one final parameter. -/
def extendParams {n : ℕ} (ps : PrefixParams n) (q : ℚ) : PrefixParams (n + 1) :=
  Fin.lastCases q ps

@[simp] theorem prefixPoint_succ_old {n : ℕ} (ps : PrefixParams n) (q : ℚ)
    (z : PrefixIndex n) :
    prefixPoint (n + 1) (extendParams ps q) (prefixSuccEquiv n (Sum.inl z)) =
      prefixPoint n ps z := by
  rcases z with ⟨i, a⟩
  simp [prefixPoint, extendParams, prefixSuccEquiv]

@[simp] theorem prefixPoint_succ_new {n : ℕ} (ps : PrefixParams n) (q : ℚ)
    (a : BlockCarrier n) :
    prefixPoint (n + 1) (extendParams ps q) (prefixSuccEquiv n (Sum.inr a)) =
      curveTranslate (q : ℝ) ((blockData n).point a) := by
  simp [prefixPoint, extendParams, prefixSuccEquiv]

/-- A prefix state stores both its translation parameters and their verified
strong-GP invariant. -/
structure PrefixState (n : ℕ) where
  params : PrefixParams n
  strong : StrongIndexedGeneralPosition (prefixPoint n params)

noncomputable def initialState : PrefixState 0 where
  params := Fin.elim0
  strong := by
    refine ⟨?_, ?_, ?_⟩
    · intro x
      exact Fin.elim0 x.1
    · intro v
      exact Fin.elim0 (v 0).1
    · intro v
      exact Fin.elim0 (v 0).1

/-- Extend a verified prefix by the next finite witness, using the generic
adjoining theorem. -/
noncomputable def nextState {n : ℕ} (s : PrefixState n) : PrefixState (n + 1) := by
  let hex := exists_rational_strongGP_adjoin
    (prefixPoint n s.params) (blockData n).point s.strong (blockData n).strong
  let q : ℚ := Classical.choose hex
  have hjoined := Classical.choose_spec hex
  refine ⟨extendParams s.params q, ?_⟩
  have hre := strong_reindex (prefixSuccEquiv n) hjoined
  have heq : (fun d => adjoinPoint (prefixPoint n s.params) (blockData n).point
      (q : ℝ) ((prefixSuccEquiv n).symm d)) =
      prefixPoint (n + 1) (extendParams s.params q) := by
    funext d
    let x := (prefixSuccEquiv n).symm d
    calc
      adjoinPoint (prefixPoint n s.params) (blockData n).point (q : ℝ)
          ((prefixSuccEquiv n).symm d) =
          adjoinPoint (prefixPoint n s.params) (blockData n).point (q : ℝ) x := rfl
      _ = prefixPoint (n + 1) (extendParams s.params q) (prefixSuccEquiv n x) := by
        cases x with
        | inl z => exact (prefixPoint_succ_old s.params q z).symm
        | inr a => exact (prefixPoint_succ_new s.params q a).symm
      _ = prefixPoint (n + 1) (extendParams s.params q) d := by
        rw [(prefixSuccEquiv n).apply_symm_apply]
  rw [← heq]
  exact hre

/-- The compatible recursively chosen prefix states. -/
noncomputable def chosenState : (n : ℕ) → PrefixState n
  | 0 => initialState
  | n + 1 => nextState (chosenState n)

@[simp] theorem chosenState_succ_castSucc (n : ℕ) (i : Fin n) :
    (chosenState (n + 1)).params i.castSucc = (chosenState n).params i := by
  simp [chosenState, nextState, extendParams]

/-- Parameters already chosen in a prefix remain unchanged in every later
prefix. -/
theorem chosenState_params_stable {m n : ℕ} (h : m ≤ n) (i : Fin m) :
    (chosenState n).params (Fin.castLE h i) = (chosenState m).params i := by
  induction n, h using Nat.le_induction with
  | base => rfl
  | @succ n h ih =>
      have hfin : Fin.castLE (Nat.le.step h) i = (Fin.castLE h i).castSucc := by
        apply Fin.ext
        rfl
      rw [hfin, chosenState_succ_castSucc, ih]

/-- Index type and point family of the countable union. -/
abbrev InfiniteIndex := Σ n : ℕ, BlockCarrier n

/-- Translation parameter permanently assigned to block `n`. -/
noncomputable def blockParam (n : ℕ) : ℚ :=
  (chosenState (n + 1)).params (Fin.last n)

/-- The final countable point family. -/
noncomputable def infinitePoint : InfiniteIndex → Point
  | ⟨n, a⟩ => curveTranslate (blockParam n : ℝ) ((blockData n).point a)

/-- Forget the bound on a prefix index. -/
def prefixForget {n : ℕ} : PrefixIndex n → InfiniteIndex
  | ⟨i, a⟩ => ⟨i.val, a⟩

/-- A point from block `i<n` has the same coordinates in prefix `n` and in the
final family. -/
theorem prefixPoint_eq_infinitePoint {n i : ℕ} (hi : i < n)
    (a : BlockCarrier i) :
    prefixPoint n (chosenState n).params ⟨⟨i, hi⟩, a⟩ =
      infinitePoint ⟨i, a⟩ := by
  have hle : i + 1 ≤ n := Nat.succ_le_iff.mpr hi
  have hs := chosenState_params_stable hle (Fin.last i)
  have hfin : Fin.castLE hle (Fin.last i) = (⟨i, hi⟩ : Fin n) := by
    apply Fin.ext
    rfl
  rw [hfin] at hs
  simp only [prefixPoint, infinitePoint, blockParam]
  rw [hs]

/-- Any finite tuple of final indices is represented, injectively when the
original tuple is, in one verified prefix. -/
theorem exists_prefix_representation {κ : Type*} [Fintype κ] [Nonempty κ]
    (v : κ → InfiniteIndex) :
    ∃ (n : ℕ) (w : κ → PrefixIndex n),
      (Function.Injective v → Function.Injective w) ∧
      (∀ j, prefixForget (w j) = v j) ∧
      ∀ j, prefixPoint n (chosenState n).params (w j) = infinitePoint (v j) := by
  classical
  let total : ℕ := ∑ j : κ, (v j).1
  let n : ℕ := total + 1
  have hlt (j : κ) : (v j).1 < n := by
    apply Nat.lt_succ_of_le
    exact Finset.single_le_sum (s := Finset.univ) (f := fun x : κ => (v x).1)
      (fun x hx => Nat.zero_le _) (Finset.mem_univ j)
  let w : κ → PrefixIndex n := fun j => ⟨⟨(v j).1, hlt j⟩, (v j).2⟩
  refine ⟨n, w, ?_, ?_, ?_⟩
  · intro hvi x y hxy
    apply hvi
    have hf := congrArg prefixForget hxy
    simpa [w, prefixForget] using hf
  · intro j
    simp [w, prefixForget]
  · intro j
    simpa [w] using prefixPoint_eq_infinitePoint (hlt j) (v j).2

/-- The countable assembled family satisfies the determinant form of global
general position. -/
theorem infinitePoint_strongGP : StrongIndexedGeneralPosition infinitePoint := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy
    let v : Fin 2 → InfiniteIndex := ![x, y]
    obtain ⟨n, w, hwi, hforget, hw⟩ := exists_prefix_representation v
    have hp : prefixPoint n (chosenState n).params (w 0) =
        prefixPoint n (chosenState n).params (w 1) := by
      rw [hw 0, hw 1]
      simpa [v] using hxy
    have hi := (chosenState n).strong.1 hp
    calc
      x = v 0 := by simp [v]
      _ = prefixForget (w 0) := (hforget 0).symm
      _ = prefixForget (w 1) := congrArg prefixForget hi
      _ = v 1 := hforget 1
      _ = y := by simp [v]
  · intro v hvi
    obtain ⟨n, w, hwi, hforget, hw⟩ := exists_prefix_representation v
    have hn := (chosenState n).strong.2.1 w (hwi hvi)
    simpa only [hw] using hn
  · intro v hvi
    obtain ⟨n, w, hwi, hforget, hw⟩ := exists_prefix_representation v
    have hn := (chosenState n).strong.2.2 w (hwi hvi)
    simpa only [hw] using hn

@[simp] theorem sqDist_curveTranslate (t : ℝ) (p q : Point) :
    sqDist (curveTranslate t p) (curveTranslate t q) = sqDist p q := by
  simp only [sqDist, curveTranslate]
  ring

/-- Common translation preserves the exact positive-integer adjacency
predicate. -/
theorem adjacent_curveTranslate (t : ℝ) {p q : Point} (h : Adjacent p q) :
    Adjacent (curveTranslate t p) (curveTranslate t q) := by
  rcases h with ⟨hpq, n, hn, hd⟩
  refine ⟨?_, n, hn, ?_⟩
  · intro he
    apply hpq
    have hx := congrArg Prod.fst he
    have hy := congrArg Prod.snd he
    simp only [curveTranslate] at hx hy
    apply Prod.ext <;> linarith
  · rw [sqDist_curveTranslate, hd]

/-- Every finite number of colors fails already on its corresponding translated
block of the final indexed family. -/
theorem infinitePoint_noKColoring (k : ℕ) :
    NoKPointColoring infinitePoint k := by
  intro color
  let blockColor : BlockCarrier k → Fin k := fun a => color ⟨k, a⟩
  obtain ⟨a, b, hab, hadj, hc⟩ := (blockData k).noColor blockColor
  refine ⟨⟨k, a⟩, ⟨k, b⟩, ?_, ?_, hc⟩
  · intro h
    apply hab
    cases h
    rfl
  · exact adjacent_curveTranslate (blockParam k : ℝ) hadj

/-- A canonical index in every nonempty block. -/
noncomputable def natBlockIndex (n : ℕ) : InfiniteIndex :=
  ⟨n, Classical.choice (blockNonempty n)⟩

private theorem natBlockIndex_injective : Function.Injective natBlockIndex := by
  intro m n h
  exact congrArg Sigma.fst h

noncomputable instance infiniteIndexInfinite : Infinite InfiniteIndex :=
  Infinite.of_injective natBlockIndex natBlockIndex_injective

/-- Indexed general position passes to the range set. -/
theorem generalPosition_range_of_indexed {σ : Type*} {P : σ → Point}
    (hP : IndexedGeneralPosition P) : GeneralPosition (Set.range P) := by
  constructor
  · rintro p q r ⟨a, rfl⟩ ⟨b, rfl⟩ ⟨c, rfl⟩ hab hac hbc
    let v : Fin 3 → σ := ![a, b, c]
    have hab' : a ≠ b := fun h => hab (congrArg P h)
    have hac' : a ≠ c := fun h => hac (congrArg P h)
    have hbc' : b ≠ c := fun h => hbc (congrArg P h)
    have hvi : Function.Injective v := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [v]
    simpa [v] using hP.2.1 v hvi
  · rintro p q r s ⟨a, rfl⟩ ⟨b, rfl⟩ ⟨c, rfl⟩ ⟨d, rfl⟩
      hab hac had hbc hbd hcd
    let v : Fin 4 → σ := ![a, b, c, d]
    have hab' : a ≠ b := fun h => hab (congrArg P h)
    have hac' : a ≠ c := fun h => hac (congrArg P h)
    have had' : a ≠ d := fun h => had (congrArg P h)
    have hbc' : b ≠ c := fun h => hbc (congrArg P h)
    have hbd' : b ≠ d := fun h => hbd (congrArg P h)
    have hcd' : c ≠ d := fun h => hcd (congrArg P h)
    have hvi : Function.Injective v :=
      vec4_injective hab' hac' had' hbc' hbd' hcd'
    simpa [v] using hP.2.2 v hvi

/-- The final range has no proper coloring by any finite color type. -/
theorem infinitePoint_range_no_finite_coloring (k : ℕ) :
    ¬ HasKColoring (Set.range infinitePoint) k := by
  rintro ⟨color, hproper⟩
  let indexColor : InfiniteIndex → Fin k := fun i =>
    color ⟨infinitePoint i, ⟨i, rfl⟩⟩
  obtain ⟨i, j, hij, hadj, hc⟩ := infinitePoint_noKColoring k indexColor
  have hne := hproper ⟨infinitePoint i, ⟨i, rfl⟩⟩
    ⟨infinitePoint j, ⟨j, rfl⟩⟩ hadj
  exact hne hc

/-- Complete solution theorem in the exact language of the pinned verifier. -/
theorem erdos130_infinite_chromatic_solution :
    ∃ A : Set Point,
      A.Infinite ∧ GeneralPosition A ∧ ∀ k : ℕ, ¬ HasKColoring A k := by
  let A : Set Point := Set.range infinitePoint
  refine ⟨A, ?_, ?_, ?_⟩
  · exact Set.infinite_range_of_injective infinitePoint_strongGP.1
  · exact generalPosition_range_of_indexed infinitePoint_strongGP.indexed
  · exact infinitePoint_range_no_finite_coloring

end
end InfiniteAssembly
end Erdos130
