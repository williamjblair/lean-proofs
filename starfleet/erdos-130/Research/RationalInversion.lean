import Research.QuadGeneric
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Simultaneous rational choice of an inversion center

The exceptional denominator, collinearity, and concyclicity conditions are
represented as bivariate polynomials.  A nonzero finite product cannot vanish
on every rational point, by multivariate polynomial extensionality on the
infinite rational grid.
-/

namespace Erdos130
namespace Circle
namespace RationalInversion

open MvPolynomial

noncomputable section

abbrev Var := Fin 2

/-- Coordinate variables for an inversion center. -/
def U : MvPolynomial Var ℝ := X 0
def V : MvPolynomial Var ℝ := X 1

/-- Relative coordinate and power polynomials. -/
def xPoly (Z : Circle) : MvPolynomial Var ℝ := C Z.center.1 - U
def yPoly (Z : Circle) : MvPolynomial Var ℝ := C Z.center.2 - V
def denomPoly (Z : Circle) : MvPolynomial Var ℝ :=
  xPoly Z ^ 2 + yPoly Z ^ 2 - C (Z.radius ^ 2)

/-- Three-by-three determinant over an arbitrary commutative ring. -/
def det3R {R : Type*} [CommRing R] (f g h : Circle → R)
    (A B Cc : Circle) : R :=
  f A * (g B * h Cc - g Cc * h B) -
  g A * (f B * h Cc - f Cc * h B) +
  h A * (f B * g Cc - f Cc * g B)

/-- Four-by-four determinant over an arbitrary commutative ring. -/
def det4R {R : Type*} [CommRing R] (f g h j : Circle → R)
    (A B Cc D : Circle) : R :=
  f A * det3R g h j B Cc D - g A * det3R f h j B Cc D +
    h A * det3R f g j B Cc D - j A * det3R f g h B Cc D

/-- Polynomial for inverse-center collinearity of a triple. -/
def triplePoly (A B Cc : Circle) : MvPolynomial Var ℝ :=
  det3R xPoly yPoly denomPoly A B Cc

/-- Polynomial for inverse-center generalized concyclicity of a quadruple. -/
def quadPoly (A B Cc D : Circle) : MvPolynomial Var ℝ :=
  det4R (fun Z => xPoly Z ^ 2 + yPoly Z ^ 2)
    (fun Z => xPoly Z * denomPoly Z)
    (fun Z => yPoly Z * denomPoly Z)
    (fun Z => denomPoly Z ^ 2) A B Cc D

/-- Evaluating the denominator polynomial recovers circle power. -/
@[simp] theorem eval_denomPoly (O : Var → ℝ) (Z : Circle) :
    MvPolynomial.eval O (denomPoly Z) = inversionDenom (O 0, O 1) Z := by
  simp only [denomPoly, xPoly, yPoly, U, V, map_sub, map_add, map_pow,
    eval_C, eval_X, inversionDenom, sqDist]

/-- Evaluating the triple polynomial recovers the cleared triple determinant. -/
@[simp] theorem eval_triplePoly (O : Var → ℝ) (A B Cc : Circle) :
    MvPolynomial.eval O (triplePoly A B Cc) =
      clearedInverseCenterTriple (O 0, O 1) A B Cc := by
  simp only [triplePoly, det3R, xPoly, yPoly, denomPoly, U, V,
    map_sub, map_add, map_mul, map_pow, eval_C, eval_X,
    clearedInverseCenterTriple, detCols, inversionDenom, sqDist]

/-- Evaluating the quadruple polynomial recovers the cleared cyclic determinant. -/
@[simp] theorem eval_quadPoly (O : Var → ℝ) (A B Cc D : Circle) :
    MvPolynomial.eval O (quadPoly A B Cc D) =
      clearedInverseCenterQuad (O 0, O 1) A B Cc D := by
  simp only [quadPoly, det4R, det3R, xPoly, yPoly, denomPoly, U, V,
    map_sub, map_add, map_mul, map_pow, eval_C, eval_X,
    clearedInverseCenterQuad, det4Cols, detCols, inversionDenom, sqDist]

/-- Positive-radius denominator polynomials are nonzero. -/
theorem denomPoly_ne_zero (Z : Circle) (hr : 0 < Z.radius) :
    denomPoly Z ≠ 0 := by
  intro hp
  -- Use the center itself, with its two coordinates assigned separately.
  let o : Var → ℝ := fun i => if i = 0 then Z.center.1 else Z.center.2
  have he := congrArg (MvPolynomial.eval o) hp
  rw [eval_denomPoly] at he
  norm_num [o, inversionDenom, sqDist] at he
  nlinarith

/-- A noncoaxial triple has a genuinely nonzero exceptional polynomial. -/
theorem triplePoly_ne_zero (A B Cc : Circle) (hnc : ¬ Coaxial3 A B Cc) :
    triplePoly A B Cc ≠ 0 := by
  intro hp
  apply hnc
  rw [coaxial3_iff_cleared_eq_zero]
  intro O
  let x : Var → ℝ := fun i => if i = 0 then O.1 else O.2
  have he := congrArg (MvPolynomial.eval x) hp
  rw [eval_triplePoly] at he
  simpa [x] using he

/-- F-013 implies that every eligible quadruple polynomial is nonzero. -/
theorem quadPoly_ne_zero (A B Cc D : Circle)
    (hA : 0 < A.radius) (hB : 0 < B.radius)
    (hC : 0 < Cc.radius) (hD : 0 < D.radius)
    (hABne : A ≠ B) (hACne : A ≠ Cc) (hADne : A ≠ D)
    (hBCne : B ≠ Cc) (hBDne : B ≠ D) (hCDne : Cc ≠ D)
    (hncABC : ¬ Coaxial3 A B Cc) (hncBCD : ¬ Coaxial3 B Cc D)
    (hncACD : ¬ Coaxial3 A Cc D) :
    quadPoly A B Cc D ≠ 0 := by
  obtain ⟨O, hO⟩ := QuadGeneric.exists_center_clearedInverseCenterQuad_ne_zero
    A B Cc D hA hB hC hD hABne hACne hADne hBCne hBDne hCDne
    hncABC hncBCD hncACD
  intro hp
  let x : Var → ℝ := fun i => if i = 0 then O.1 else O.2
  have he := congrArg (MvPolynomial.eval x) hp
  rw [eval_quadPoly] at he
  exact hO (by simpa [x] using he)

variable {α : Type*} [Fintype α]

/-- Product of all denominator constraints for a finite family. -/
def denomProduct (F : α → Circle) : MvPolynomial Var ℝ :=
  ∏ i : α, denomPoly (F i)

/-- A triple contributes its exceptional polynomial only when its index map is
injective; repeated-index tuples contribute `1`. -/
noncomputable def tripleFactor (F : α → Circle) (v : Fin 3 → α) : MvPolynomial Var ℝ := by
  classical
  exact if Function.Injective v then triplePoly (F (v 0)) (F (v 1)) (F (v 2)) else 1

def tripleProduct (F : α → Circle) : MvPolynomial Var ℝ :=
  ∏ v : Fin 3 → α, tripleFactor F v

/-- Analogous factor and product over ordered quadruples. -/
noncomputable def quadFactor (F : α → Circle) (v : Fin 4 → α) : MvPolynomial Var ℝ := by
  classical
  exact if Function.Injective v then
    quadPoly (F (v 0)) (F (v 1)) (F (v 2)) (F (v 3)) else 1

def quadProduct (F : α → Circle) : MvPolynomial Var ℝ :=
  ∏ v : Fin 4 → α, quadFactor F v

def exceptionalProduct (F : α → Circle) : MvPolynomial Var ℝ :=
  denomProduct F * tripleProduct F * quadProduct F

/-- The finite exceptional product is nonzero for a positive injective family
with no coaxial triple. -/
theorem exceptionalProduct_ne_zero (F : α → Circle)
    (hpos : ∀ i, 0 < (F i).radius) (hinj : Function.Injective F)
    (hnc : ∀ v : Fin 3 → α, Function.Injective v →
      ¬ Coaxial3 (F (v 0)) (F (v 1)) (F (v 2))) :
    exceptionalProduct F ≠ 0 := by
  classical
  apply mul_ne_zero
  · apply mul_ne_zero
    · apply Finset.prod_ne_zero_iff.mpr
      intro i hi
      exact denomPoly_ne_zero (F i) (hpos i)
    · apply Finset.prod_ne_zero_iff.mpr
      intro v hv
      simp only [tripleFactor]
      split_ifs with hvi
      · exact triplePoly_ne_zero _ _ _ (hnc v hvi)
      · exact one_ne_zero
  · apply Finset.prod_ne_zero_iff.mpr
    intro v hv
    simp only [quadFactor]
    split_ifs with hvi
    · have h01 : v 0 ≠ v 1 := fun h =>
        (show (0 : Fin 4) ≠ 1 by decide) (hvi h)
      have h02 : v 0 ≠ v 2 := fun h =>
        (show (0 : Fin 4) ≠ 2 by decide) (hvi h)
      have h03 : v 0 ≠ v 3 := fun h =>
        (show (0 : Fin 4) ≠ 3 by decide) (hvi h)
      have h12 : v 1 ≠ v 2 := fun h =>
        (show (1 : Fin 4) ≠ 2 by decide) (hvi h)
      have h13 : v 1 ≠ v 3 := fun h =>
        (show (1 : Fin 4) ≠ 3 by decide) (hvi h)
      have h23 : v 2 ≠ v 3 := fun h =>
        (show (2 : Fin 4) ≠ 3 by decide) (hvi h)
      let t012 : Fin 3 → α := ![v 0, v 1, v 2]
      let t123 : Fin 3 → α := ![v 1, v 2, v 3]
      let t023 : Fin 3 → α := ![v 0, v 2, v 3]
      have hi012 : Function.Injective t012 := by
        intro x y hxy
        fin_cases x <;> fin_cases y <;> simp_all [t012]
      have hi123 : Function.Injective t123 := by
        intro x y hxy
        fin_cases x <;> fin_cases y <;> simp_all [t123]
      have hi023 : Function.Injective t023 := by
        intro x y hxy
        fin_cases x <;> fin_cases y <;> simp_all [t023]
      apply quadPoly_ne_zero
      · exact hpos (v 0)
      · exact hpos (v 1)
      · exact hpos (v 2)
      · exact hpos (v 3)
      · exact fun h => h01 (hinj h)
      · exact fun h => h02 (hinj h)
      · exact fun h => h03 (hinj h)
      · exact fun h => h12 (hinj h)
      · exact fun h => h13 (hinj h)
      · exact fun h => h23 (hinj h)
      · simpa [t012] using hnc t012 hi012
      · simpa [t123] using hnc t123 hi123
      · simpa [t023] using hnc t023 hi023
    · exact one_ne_zero

/-- The real casts of rational numbers form an infinite coordinate set. -/
def ratRange : Set ℝ := Set.range (fun q : ℚ => (q : ℝ))

private theorem ratRange_infinite : ratRange.Infinite :=
  Set.infinite_range_of_injective Rat.cast_injective

/-- A nonzero bivariate real polynomial is nonzero at some rational point. -/
theorem exists_rational_eval_ne_zero (P : MvPolynomial Var ℝ) (hP : P ≠ 0) :
    ∃ (o : ℚ × ℚ),
      MvPolynomial.eval (fun i => if i = 0 then (o.1 : ℝ) else (o.2 : ℝ)) P ≠ 0 := by
  have hex : ∃ x : Var → ℝ,
      x ∈ Set.pi Set.univ (fun _ => ratRange) ∧ MvPolynomial.eval x P ≠ 0 := by
    by_contra hn
    have hall : ∀ x : Var → ℝ, x ∈ Set.pi Set.univ (fun _ => ratRange) →
        MvPolynomial.eval x P = 0 := by
      intro x hx
      by_contra hne
      exact hn ⟨x, hx, hne⟩
    apply hP
    apply MvPolynomial.funext_set (fun _ : Var => ratRange)
      (fun _ => ratRange_infinite)
    intro x hx
    simpa using hall x hx
  obtain ⟨x, hx, heval⟩ := hex
  obtain ⟨u, hu⟩ := hx 0 (Set.mem_univ 0)
  obtain ⟨v, hv⟩ := hx 1 (Set.mem_univ 1)
  refine ⟨(u, v), ?_⟩
  have hfun : x = fun i => if i = 0 then (u : ℝ) else (v : ℝ) := by
    funext i
    fin_cases i
    · simpa using hu.symm
    · simpa using hv.symm
  simpa [hfun] using heval

/-- Simultaneous rational avoidance of every denominator, triple, and quadruple
exception for a finite good circle family. -/
theorem exists_rational_good_inversion_center (F : α → Circle)
    (hpos : ∀ i, 0 < (F i).radius) (hinj : Function.Injective F)
    (hnc : ∀ v : Fin 3 → α, Function.Injective v →
      ¬ Coaxial3 (F (v 0)) (F (v 1)) (F (v 2))) :
    ∃ (o : ℚ × ℚ),
      (∀ i, inversionDenom ((o.1 : ℝ), (o.2 : ℝ)) (F i) ≠ 0) ∧
      (∀ v : Fin 3 → α, Function.Injective v →
        clearedInverseCenterTriple ((o.1 : ℝ), (o.2 : ℝ))
          (F (v 0)) (F (v 1)) (F (v 2)) ≠ 0) ∧
      (∀ v : Fin 4 → α, Function.Injective v →
        clearedInverseCenterQuad ((o.1 : ℝ), (o.2 : ℝ))
          (F (v 0)) (F (v 1)) (F (v 2)) (F (v 3)) ≠ 0) := by
  classical
  obtain ⟨o, ho⟩ := exists_rational_eval_ne_zero (exceptionalProduct F)
    (exceptionalProduct_ne_zero F hpos hinj hnc)
  let x : Var → ℝ := fun i => if i = 0 then (o.1 : ℝ) else (o.2 : ℝ)
  have hdenProd : MvPolynomial.eval x (denomProduct F) ≠ 0 := by
    intro hz
    apply ho
    simp [exceptionalProduct, x, hz]
  have htriProd : MvPolynomial.eval x (tripleProduct F) ≠ 0 := by
    intro hz
    apply ho
    simp [exceptionalProduct, x, hz]
  have hquadProd : MvPolynomial.eval x (quadProduct F) ≠ 0 := by
    intro hz
    apply ho
    simp [exceptionalProduct, x, hz]
  have hdenFactors : ∀ i, MvPolynomial.eval x (denomPoly (F i)) ≠ 0 := by
    rw [denomProduct, map_prod] at hdenProd
    exact fun i => (Finset.prod_ne_zero_iff.mp hdenProd) i (Finset.mem_univ i)
  have htriFactors : ∀ v, MvPolynomial.eval x (tripleFactor F v) ≠ 0 := by
    rw [tripleProduct, map_prod] at htriProd
    exact fun v => (Finset.prod_ne_zero_iff.mp htriProd) v (Finset.mem_univ v)
  have hquadFactors : ∀ v, MvPolynomial.eval x (quadFactor F v) ≠ 0 := by
    rw [quadProduct, map_prod] at hquadProd
    exact fun v => (Finset.prod_ne_zero_iff.mp hquadProd) v (Finset.mem_univ v)
  refine ⟨o, ?_, ?_, ?_⟩
  · intro i
    simpa [x] using hdenFactors i
  · intro v hvi
    have hv := htriFactors v
    simp only [tripleFactor, if_pos hvi] at hv
    simpa [x] using hv
  · intro v hvi
    have hv := hquadFactors v
    simp only [quadFactor, if_pos hvi] at hv
    simpa [x] using hv

/-- Geometric corollary: at the selected rational center, all distinct inverse
centers avoid collinear triples and concyclic quadruples. -/
theorem exists_rational_inverse_centers_general_position (F : α → Circle)
    (hpos : ∀ i, 0 < (F i).radius) (hinj : Function.Injective F)
    (hnc : ∀ v : Fin 3 → α, Function.Injective v →
      ¬ Coaxial3 (F (v 0)) (F (v 1)) (F (v 2))) :
    ∃ (o : ℚ × ℚ),
      let O : Point := ((o.1 : ℝ), (o.2 : ℝ));
      (∀ i, inversionDenom O (F i) ≠ 0) ∧
      (∀ v : Fin 3 → α, Function.Injective v →
        ¬ Collinear (inverseRelativeCenter O (F (v 0)))
          (inverseRelativeCenter O (F (v 1)))
          (inverseRelativeCenter O (F (v 2)))) ∧
      (∀ v : Fin 4 → α, Function.Injective v →
        ¬ Concyclic4 (inverseRelativeCenter O (F (v 0)))
          (inverseRelativeCenter O (F (v 1)))
          (inverseRelativeCenter O (F (v 2)))
          (inverseRelativeCenter O (F (v 3)))) := by
  obtain ⟨o, hden, htri, hquad⟩ :=
    exists_rational_good_inversion_center F hpos hinj hnc
  refine ⟨o, hden, ?_, ?_⟩
  · intro v hvi hcol
    have horient : orient (inverseRelativeCenter ((o.1 : ℝ), (o.2 : ℝ)) (F (v 0)))
        (inverseRelativeCenter ((o.1 : ℝ), (o.2 : ℝ)) (F (v 1)))
        (inverseRelativeCenter ((o.1 : ℝ), (o.2 : ℝ)) (F (v 2))) = 0 :=
      (collinear_iff_orient_eq_zero _ _ _).mp hcol
    apply htri v hvi
    rw [clearedInverseCenterTriple_eq_denom_mul_orient _ _ _ _
      (hden (v 0)) (hden (v 1)) (hden (v 2)), horient, mul_zero]
  · intro v hvi hcyc
    have hdet := cyclicDet_eq_zero_of_concyclic4 hcyc
    apply hquad v hvi
    rw [clearedInverseCenterQuad_eq_denom_mul_cyclicDet _ _ _ _ _
      (hden (v 0)) (hden (v 1)) (hden (v 2)) (hden (v 3)), hdet, mul_zero]

end

end RationalInversion
end Circle
end Erdos130
