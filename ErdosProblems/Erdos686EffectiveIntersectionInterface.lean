/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686OsculationDichotomy
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Erdős 686: effective integral-intersection certificate interface

This module does not assert that a small resultant exists uniformly.  It
records the exact data a support-specific certificate must provide: a shear,
a nonzero univariate resultant, its complete integral root list, complete
fiber-gcd root lists, and verification on the original curve.
-/

namespace Erdos686
namespace Erdos686Variant

open Polynomial

/-- The integral point with sheared coordinate `t = x + lambda*y`. -/
def unshearPoint (lambda t y : ℤ) : Fin 2 → ℤ
  | 0 => t - lambda * y
  | 1 => y

@[simp]
theorem unshearPoint_sheared_coordinate (lambda t y : ℤ) :
    unshearPoint lambda t y 0 + lambda * unshearPoint lambda t y 1 = t := by
  simp [unshearPoint]

/-- All exact, support-dependent data needed to turn a coprime bivariate
intersection into a finite integral enumeration. -/
structure EffectiveIntersectionCertificate
    (P Q : BivariateIntPolynomial)
    (originalCurve : (Fin 2 → ℤ) → Prop) where
  lambda : ℤ
  resultant : Polynomial ℤ
  resultant_ne_zero : resultant ≠ 0
  rootBound : ℕ
  integralTRoots : Finset ℤ
  fiberGCD : ℤ → Polynomial ℤ
  integralYRoots : ℤ → Finset ℤ
  resultant_of_common_zero :
    ∀ p : Fin 2 → ℤ,
      evalIntAt p P = 0 →
      evalIntAt p Q = 0 →
      resultant.eval (p 0 + lambda * p 1) = 0
  resultant_root_bound :
    ∀ t : ℤ, resultant.eval t = 0 → t.natAbs ≤ rootBound
  tRoots_complete :
    ∀ t : ℤ, resultant.eval t = 0 → t ∈ integralTRoots
  fiberGCD_of_common_zero :
    ∀ p : Fin 2 → ℤ,
      evalIntAt p P = 0 →
      evalIntAt p Q = 0 →
      (fiberGCD (p 0 + lambda * p 1)).eval (p 1) = 0
  yRoots_complete :
    ∀ t y : ℤ,
      t ∈ integralTRoots →
      (fiberGCD t).eval y = 0 →
      y ∈ integralYRoots t
  candidates_verified :
    ∀ t y : ℤ,
      t ∈ integralTRoots →
      y ∈ integralYRoots t →
      evalIntAt (unshearPoint lambda t y) P = 0 →
      evalIntAt (unshearPoint lambda t y) Q = 0 →
      originalCurve (unshearPoint lambda t y)

/-- Every common integral zero is captured by the exact sheared resultant
and fiber-gcd lists and is verified on the original curve. -/
theorem EffectiveIntersectionCertificate.common_zero_enumerated
    {P Q : BivariateIntPolynomial}
    {originalCurve : (Fin 2 → ℤ) → Prop}
    (C : EffectiveIntersectionCertificate P Q originalCurve)
    (p : Fin 2 → ℤ)
    (hP : evalIntAt p P = 0)
    (hQ : evalIntAt p Q = 0) :
    let t := p 0 + C.lambda * p 1
    t ∈ C.integralTRoots ∧
      p 1 ∈ C.integralYRoots t ∧
      t.natAbs ≤ C.rootBound ∧
      originalCurve p := by
  let t := p 0 + C.lambda * p 1
  have hR : C.resultant.eval t = 0 :=
    C.resultant_of_common_zero p hP hQ
  have ht : t ∈ C.integralTRoots := C.tRoots_complete t hR
  have hG : (C.fiberGCD t).eval (p 1) = 0 :=
    C.fiberGCD_of_common_zero p hP hQ
  have hy : p 1 ∈ C.integralYRoots t :=
    C.yRoots_complete t (p 1) ht hG
  have hpEq : unshearPoint C.lambda t (p 1) = p := by
    funext i
    fin_cases i
    · simp [unshearPoint, t]
    · simp [unshearPoint]
  refine ⟨ht, hy, C.resultant_root_bound t hR, ?_⟩
  rw [← hpEq]
  exact C.candidates_verified t (p 1) ht hy
    (by simpa [hpEq] using hP) (by simpa [hpEq] using hQ)

/-- The interface exposes the finite candidate rectangle without claiming
that its support-dependent size is small enough for the arithmetic tail. -/
def EffectiveIntersectionCertificate.candidatePairs
    {P Q : BivariateIntPolynomial}
    {originalCurve : (Fin 2 → ℤ) → Prop}
    (C : EffectiveIntersectionCertificate P Q originalCurve) :
    Finset (ℤ × ℤ) :=
  C.integralTRoots.biUnion fun t =>
    (C.integralYRoots t).image fun y => (t, y)

#print axioms unshearPoint_sheared_coordinate
#print axioms EffectiveIntersectionCertificate.common_zero_enumerated

end Erdos686Variant
end Erdos686
