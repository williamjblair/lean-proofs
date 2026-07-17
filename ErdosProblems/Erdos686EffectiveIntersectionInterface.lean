/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686OsculationFixedDivisor
import Mathlib.Algebra.Polynomial.Roots

/-!
# Erdős 686: effective zero-dimensional intersection interface

This module does not claim a global closure theorem.  It specifies the exact
certificate needed to turn a coprime residual pair into a finite integral
search:

1. choose the integer shear `T = X + lambda Y`;
2. provide a nonzero Sylvester resultant `R_lambda(T)` together with its
   polynomial identity;
3. enumerate all integral roots of the resultant;
4. at every root, compute and certify the univariate gcd in `Y`;
5. enumerate every integral root of that gcd;
6. reconstruct `(X,Y)` and verify the original consecutive-product curve.

The coefficient and integer-root bounds are explicit fields of the certificate
and therefore remain support-dependent.  No comparison with the surviving
Diophantine scale is made here.
-/

namespace Erdos686
namespace Erdos686Variant

open scoped BigOperators
open Polynomial

/-- Integral affine shear coordinate `T = X + lambda Y`. -/
def shearCoordinate (lambda : ℤ) (p : ℤ × ℤ) : ℤ :=
  p.1 + lambda * p.2

/-- Recover `X` from `T` and `Y`. -/
def unshearPoint (lambda t y : ℤ) : ℤ × ℤ :=
  (t - lambda * y, y)

@[simp]
theorem unshear_shear (lambda : ℤ) (p : ℤ × ℤ) :
    unshearPoint lambda (shearCoordinate lambda p) p.2 = p := by
  apply Prod.ext
  · simp [unshearPoint, shearCoordinate]
  · simp [unshearPoint]

/-- Evaluation at an integral pair. -/
noncomputable def evalIntPair
    (F : BivariateIntPolynomial) (p : ℤ × ℤ) : ℤ :=
  evalIntAt ![p.1, p.2] F

/-- A divisibility characterization of a univariate gcd, unique up to a unit. -/
structure UnivariateGCDCertificate
    (A B G : Polynomial ℤ) : Prop where
  divides_left : G ∣ A
  divides_right : G ∣ B
  greatest : ∀ D : Polynomial ℤ, D ∣ A → D ∣ B → D ∣ G

/-- Any common integral root of two polynomials is a root of a certified gcd. -/
theorem UnivariateGCDCertificate.eval_eq_zero_of_common_root
    {A B G : Polynomial ℤ}
    (hG : UnivariateGCDCertificate A B G)
    (y : ℤ) (hA : A.eval y = 0) (hB : B.eval y = 0) :
    G.eval y = 0 := by
  have hdA : X - C y ∣ A :=
    (Polynomial.dvd_iff_isRoot).2 hA
  have hdB : X - C y ∣ B :=
    (Polynomial.dvd_iff_isRoot).2 hB
  have hdG : X - C y ∣ G := hG.greatest (X - C y) hdA hdB
  exact (Polynomial.dvd_iff_isRoot).1 hdG

/-- Explicit support-dependent coefficient and integral-root bounds for the
computed Sylvester resultant. -/
structure SylvesterRootBoundCertificate
    (R : Polynomial ℤ) : Prop where
  coefficientBound : ℕ
  rootBound : ℕ
  coefficient_bound : ∀ i : ℕ, (R.coeff i).natAbs ≤ coefficientBound
  integral_root_bound : ∀ t : ℤ, R.eval t = 0 → t.natAbs ≤ rootBound

/-- Complete effective certificate for one sheared residual intersection. -/
structure EffectiveIntersectionCertificate
    (P Q : BivariateIntPolynomial) where
  lambda : ℤ

  /- Sheared specializations in `Y`, obtained by setting `X = T-lambda Y`. -/
  fiberP : ℤ → Polynomial ℤ
  fiberQ : ℤ → Polynomial ℤ
  fiberP_eval : ∀ t y : ℤ,
    (fiberP t).eval y = evalIntPair P (unshearPoint lambda t y)
  fiberQ_eval : ∀ t y : ℤ,
    (fiberQ t).eval y = evalIntPair Q (unshearPoint lambda t y)

  /- Nonzero resultant and a Sylvester/adjugate identity. -/
  resultant : Polynomial ℤ
  resultant_nonzero : resultant ≠ 0
  bezoutLeft : ℤ → Polynomial ℤ
  bezoutRight : ℤ → Polynomial ℤ
  resultant_identity : ∀ t : ℤ,
    C (resultant.eval t) =
      bezoutLeft t * fiberP t + bezoutRight t * fiberQ t
  sylvesterBound : SylvesterRootBoundCertificate resultant

  /- Finite enumeration of all integral resultant roots. -/
  resultantRoots : Finset ℤ
  resultantRoots_complete : ∀ t : ℤ,
    resultant.eval t = 0 → t ∈ resultantRoots
  resultantRoots_sound : ∀ t : ℤ,
    t ∈ resultantRoots → resultant.eval t = 0

  /- Certified gcd and integral `Y`-root enumeration in every fiber. -/
  fiberGCD : ℤ → Polynomial ℤ
  fiberGCD_certificate : ∀ t : ℤ,
    UnivariateGCDCertificate (fiberP t) (fiberQ t) (fiberGCD t)
  fiberYRoots : ℤ → Finset ℤ
  fiberYRoots_complete : ∀ t y : ℤ,
    t ∈ resultantRoots → (fiberGCD t).eval y = 0 →
      y ∈ fiberYRoots t
  fiberYRoots_sound : ∀ t y : ℤ,
    t ∈ resultantRoots → y ∈ fiberYRoots t →
      (fiberGCD t).eval y = 0

/-- Every integral intersection produces an integral root of the nonzero
sheared resultant. -/
theorem integral_intersection_gives_resultant_root
    {P Q : BivariateIntPolynomial}
    (C : EffectiveIntersectionCertificate P Q)
    (p : ℤ × ℤ)
    (hP : evalIntPair P p = 0)
    (hQ : evalIntPair Q p = 0) :
    C.resultant.eval (shearCoordinate C.lambda p) = 0 := by
  let t := shearCoordinate C.lambda p
  have hPt : (C.fiberP t).eval p.2 = 0 := by
    rw [C.fiberP_eval]
    simpa [t] using hP
  have hQt : (C.fiberQ t).eval p.2 = 0 := by
    rw [C.fiberQ_eval]
    simpa [t] using hQ
  have hid := congrArg (Polynomial.eval p.2) (C.resultant_identity t)
  simpa [hPt, hQt] using hid

/-- The fiber gcd vanishes at the `Y` coordinate of every integral
intersection. -/
theorem integral_intersection_gives_fiber_gcd_root
    {P Q : BivariateIntPolynomial}
    (C : EffectiveIntersectionCertificate P Q)
    (p : ℤ × ℤ)
    (hP : evalIntPair P p = 0)
    (hQ : evalIntPair Q p = 0) :
    (C.fiberGCD (shearCoordinate C.lambda p)).eval p.2 = 0 := by
  let t := shearCoordinate C.lambda p
  have hPt : (C.fiberP t).eval p.2 = 0 := by
    rw [C.fiberP_eval]
    simpa [t] using hP
  have hQt : (C.fiberQ t).eval p.2 = 0 := by
    rw [C.fiberQ_eval]
    simpa [t] using hQ
  exact (C.fiberGCD_certificate t).eval_eq_zero_of_common_root p.2 hPt hQt

/-- The finite raw candidate set obtained from resultant roots and fiber-gcd
roots. -/
noncomputable def EffectiveIntersectionCertificate.rawCandidates
    {P Q : BivariateIntPolynomial}
    (C : EffectiveIntersectionCertificate P Q) : Finset (ℤ × ℤ) :=
  C.resultantRoots.biUnion fun t =>
    (C.fiberYRoots t).image fun y => unshearPoint C.lambda t y

/-- Completeness of the resultant/gcd enumeration for integral intersections. -/
theorem integral_intersection_mem_rawCandidates
    {P Q : BivariateIntPolynomial}
    (C : EffectiveIntersectionCertificate P Q)
    (p : ℤ × ℤ)
    (hP : evalIntPair P p = 0)
    (hQ : evalIntPair Q p = 0) :
    p ∈ C.rawCandidates := by
  let t := shearCoordinate C.lambda p
  have hresultant : C.resultant.eval t = 0 := by
    exact integral_intersection_gives_resultant_root C p hP hQ
  have ht : t ∈ C.resultantRoots :=
    C.resultantRoots_complete t hresultant
  have hgcd : (C.fiberGCD t).eval p.2 = 0 := by
    exact integral_intersection_gives_fiber_gcd_root C p hP hQ
  have hy : p.2 ∈ C.fiberYRoots t :=
    C.fiberYRoots_complete t p.2 ht hgcd
  rw [EffectiveIntersectionCertificate.rawCandidates, Finset.mem_biUnion]
  refine ⟨t, ht, ?_⟩
  rw [Finset.mem_image]
  exact ⟨p.2, hy, by simpa [t] using (unshear_shear C.lambda p)⟩

/-- Verify the original consecutive-product curve only after finite
intersection enumeration. -/
noncomputable def EffectiveIntersectionCertificate.verifiedCurveCandidates
    {P Q : BivariateIntPolynomial}
    (C : EffectiveIntersectionCertificate P Q)
    (curve : BivariateIntPolynomial) : Finset (ℤ × ℤ) :=
  C.rawCandidates.filter fun p => evalIntPair curve p = 0

/-- Every returned verified candidate satisfies the original curve. -/
theorem verifiedCurveCandidates_sound
    {P Q curve : BivariateIntPolynomial}
    (C : EffectiveIntersectionCertificate P Q)
    {p : ℤ × ℤ}
    (hp : p ∈ C.verifiedCurveCandidates curve) :
    evalIntPair curve p = 0 := by
  exact (Finset.mem_filter.mp hp).2

/-- Every integral residual intersection that also lies on the original curve
appears in the verified finite list. -/
theorem verifiedCurveCandidates_complete
    {P Q curve : BivariateIntPolynomial}
    (C : EffectiveIntersectionCertificate P Q)
    (p : ℤ × ℤ)
    (hP : evalIntPair P p = 0)
    (hQ : evalIntPair Q p = 0)
    (hcurve : evalIntPair curve p = 0) :
    p ∈ C.verifiedCurveCandidates curve := by
  rw [EffectiveIntersectionCertificate.verifiedCurveCandidates,
    Finset.mem_filter]
  exact ⟨integral_intersection_mem_rawCandidates C p hP hQ, hcurve⟩

/-- The explicit root bound applies to every integral intersection shear
coordinate.  Its numerical size remains support-dependent. -/
theorem integral_intersection_shear_natAbs_le
    {P Q : BivariateIntPolynomial}
    (C : EffectiveIntersectionCertificate P Q)
    (p : ℤ × ℤ)
    (hP : evalIntPair P p = 0)
    (hQ : evalIntPair Q p = 0) :
    (shearCoordinate C.lambda p).natAbs ≤ C.sylvesterBound.rootBound := by
  apply C.sylvesterBound.integral_root_bound
  exact integral_intersection_gives_resultant_root C p hP hQ

#print axioms UnivariateGCDCertificate.eval_eq_zero_of_common_root
#print axioms integral_intersection_gives_resultant_root
#print axioms integral_intersection_gives_fiber_gcd_root
#print axioms integral_intersection_mem_rawCandidates
#print axioms verifiedCurveCandidates_sound
#print axioms verifiedCurveCandidates_complete
#print axioms integral_intersection_shear_natAbs_le

end Erdos686Variant
end Erdos686
