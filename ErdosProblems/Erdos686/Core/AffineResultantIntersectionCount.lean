/- leanprover/lean4:v4.29.1 mathlib v4.29.1 -/
import ErdosProblems.Erdos686.Core.EffectiveIntersectionInterface
import ErdosProblems.Erdos686.Core.OsculationResidualPair
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Roots

/-!
# Erdős 686: affine intersection counts from a resultant-fiber certificate

Mathlib's polynomial library supplies the exact bound saying that a nonzero
univariate polynomial has at most its natural degree many distinct roots.  A
general projective Bézout theorem for two bivariate curves, with intersection
multiplicities, is not currently used by this repository.  This file records
the strongest direct replacement needed by the osculation campaign.

A certificate provides a nonzero sheared resultant `R(T)` and, above every
root `t` of `R`, a nonzero fiber polynomial `G_t(Y)`.  Every affine common
zero maps injectively to a pair `(t,y)` with `R(t)=G_t(y)=0`.  Consequently
the number of affine common zeros is at most

`natDegree R * maxFiberDegree`.

In particular, if both degree bounds are at most `r-e`, the exact requested
affine bound `(r-e)^2` follows.  No effective root enumeration and no claim
about projective points at infinity or intersection multiplicities is made.
-/

namespace Erdos686
namespace Erdos686Variant

open Polynomial

/-- Rational sheared coordinates `(t,y)=(x+lambda*y,y)`. -/
def rationalShearedPair (lambda : ℚ) (p : Fin 2 → ℚ) : ℚ × ℚ :=
  (p 0 + lambda * p 1, p 1)

/-- The shear is injective: `x=t-lambda*y` recovers the original point. -/
theorem rationalShearedPair_injective (lambda : ℚ) :
    Function.Injective (rationalShearedPair lambda) := by
  intro p q hpq
  have ht := congrArg Prod.fst hpq
  have hy := congrArg Prod.snd hpq
  apply _root_.funext
  intro i
  fin_cases i
  · dsimp [rationalShearedPair] at ht hy ⊢
    rw [hy] at ht
    linarith
  · simpa [rationalShearedPair] using hy

/-- Exact zero-dimensional affine certificate.  The two nonvanishing fields
exclude vertical components: the resultant is globally nonzero, and every
fiber used above a resultant root is nonzero. -/
structure AffineResultantFiberCertificate
    (P Q : BivariateRatPolynomial) where
  lambda : ℚ
  resultant : Polynomial ℚ
  fiber : ℚ → Polynomial ℚ
  resultant_ne_zero : resultant ≠ 0
  fiber_ne_zero_of_resultant_root :
    ∀ t : ℚ, resultant.eval t = 0 → fiber t ≠ 0
  resultant_of_common_zero :
    ∀ p : Fin 2 → ℚ,
      evalRatAt p P = 0 →
      evalRatAt p Q = 0 →
      resultant.eval (p 0 + lambda * p 1) = 0
  fiber_of_common_zero :
    ∀ p : Fin 2 → ℚ,
      evalRatAt p P = 0 →
      evalRatAt p Q = 0 →
      (fiber (p 0 + lambda * p 1)).eval (p 1) = 0

/-- The finite set of root pairs exposed by a resultant-fiber certificate. -/
noncomputable def AffineResultantFiberCertificate.candidatePairs
    {P Q : BivariateRatPolynomial}
    (C : AffineResultantFiberCertificate P Q) : Finset (ℚ × ℚ) :=
  C.resultant.roots.toFinset.biUnion fun t ↦
    (C.fiber t).roots.toFinset.image fun y ↦ (t, y)

/-- Every affine common zero maps to the finite candidate-pair set. -/
theorem AffineResultantFiberCertificate.shearedPair_mem_candidatePairs
    {P Q : BivariateRatPolynomial}
    (C : AffineResultantFiberCertificate P Q)
    (p : Fin 2 → ℚ)
    (hP : evalRatAt p P = 0)
    (hQ : evalRatAt p Q = 0) :
    rationalShearedPair C.lambda p ∈ C.candidatePairs := by
  classical
  let t := p 0 + C.lambda * p 1
  have hR : C.resultant.eval t = 0 :=
    C.resultant_of_common_zero p hP hQ
  have htRoots : t ∈ C.resultant.roots :=
    (C.resultant.mem_roots C.resultant_ne_zero).mpr hR
  have hfiberNe : C.fiber t ≠ 0 :=
    C.fiber_ne_zero_of_resultant_root t hR
  have hfiber : (C.fiber t).eval (p 1) = 0 :=
    C.fiber_of_common_zero p hP hQ
  have hyRoots : p 1 ∈ (C.fiber t).roots :=
    ((C.fiber t).mem_roots hfiberNe).mpr hfiber
  apply Finset.mem_biUnion.mpr
  refine ⟨t, Multiset.mem_toFinset.mpr htRoots, ?_⟩
  apply Finset.mem_image.mpr
  exact ⟨p 1, Multiset.mem_toFinset.mpr hyRoots, rfl⟩

/-- Candidate-pair count from the exact univariate root bounds. -/
theorem AffineResultantFiberCertificate.candidatePairs_card_le
    {P Q : BivariateRatPolynomial}
    (C : AffineResultantFiberCertificate P Q)
    (fiberDegreeBound : ℕ)
    (hdegree : ∀ t : ℚ,
      C.resultant.eval t = 0 →
      (C.fiber t).natDegree ≤ fiberDegreeBound) :
    C.candidatePairs.card ≤
      C.resultant.natDegree * fiberDegreeBound := by
  classical
  let T := C.resultant.roots.toFinset
  let Y : ℚ → Finset (ℚ × ℚ) := fun t ↦
    (C.fiber t).roots.toFinset.image fun y ↦ (t, y)
  have hT : T.card ≤ C.resultant.natDegree := by
    calc
      T.card ≤ C.resultant.roots.card := Multiset.toFinset_card_le _
      _ ≤ C.resultant.natDegree := Polynomial.card_roots' _
  have hY : ∀ t ∈ T, (Y t).card ≤ fiberDegreeBound := by
    intro t ht
    have htRoots : t ∈ C.resultant.roots :=
      Multiset.mem_toFinset.mp ht
    have hR : C.resultant.eval t = 0 :=
      (C.resultant.mem_roots C.resultant_ne_zero).mp htRoots
    calc
      (Y t).card ≤ (C.fiber t).roots.toFinset.card :=
        Finset.card_image_le
      _ ≤ (C.fiber t).roots.card := Multiset.toFinset_card_le _
      _ ≤ (C.fiber t).natDegree := Polynomial.card_roots' _
      _ ≤ fiberDegreeBound := hdegree t hR
  change (T.biUnion Y).card ≤
    C.resultant.natDegree * fiberDegreeBound
  exact (Finset.card_biUnion_le_card_mul T Y fiberDegreeBound hY).trans
    (Nat.mul_le_mul_right fiberDegreeBound hT)

/-- The affine rational common-zero set of two bivariate polynomials. -/
def rationalCommonZeroSet (P Q : BivariateRatPolynomial) :
    Set (Fin 2 → ℚ) :=
  {p | evalRatAt p P = 0 ∧ evalRatAt p Q = 0}

/-- A resultant-fiber certificate makes the full affine common-zero set
finite, without enumerating it. -/
theorem AffineResultantFiberCertificate.commonZeroSet_finite
    {P Q : BivariateRatPolynomial}
    (C : AffineResultantFiberCertificate P Q) :
    (rationalCommonZeroSet P Q).Finite := by
  classical
  let f := rationalShearedPair C.lambda
  have hmaps : Set.MapsTo f (rationalCommonZeroSet P Q)
      (C.candidatePairs : Set (ℚ × ℚ)) := by
    intro p hp
    exact C.shearedPair_mem_candidatePairs p hp.1 hp.2
  have himage : (f '' rationalCommonZeroSet P Q).Finite :=
    C.candidatePairs.finite_toSet.subset (Set.image_subset_iff.mpr hmaps)
  exact Set.Finite.of_finite_image himage
    (rationalShearedPair_injective C.lambda).injOn

/-- Exact affine intersection count from a nonzero resultant and uniformly
bounded nonzero fibers. -/
theorem AffineResultantFiberCertificate.commonZeroSet_ncard_le
    {P Q : BivariateRatPolynomial}
    (C : AffineResultantFiberCertificate P Q)
    (fiberDegreeBound : ℕ)
    (hdegree : ∀ t : ℚ,
      C.resultant.eval t = 0 →
      (C.fiber t).natDegree ≤ fiberDegreeBound) :
    (rationalCommonZeroSet P Q).ncard ≤
      C.resultant.natDegree * fiberDegreeBound := by
  classical
  let f := rationalShearedPair C.lambda
  have hmaps : Set.MapsTo f (rationalCommonZeroSet P Q)
      (C.candidatePairs : Set (ℚ × ℚ)) := by
    intro p hp
    exact C.shearedPair_mem_candidatePairs p hp.1 hp.2
  have hcard : (rationalCommonZeroSet P Q).ncard ≤
      (C.candidatePairs : Set (ℚ × ℚ)).ncard :=
    Set.ncard_le_ncard_of_injOn f hmaps
      (rationalShearedPair_injective C.lambda).injOn
      C.candidatePairs.finite_toSet
  have hcand : (C.candidatePairs : Set (ℚ × ℚ)).ncard =
      C.candidatePairs.card := Set.ncard_coe_finset _
  rw [hcand] at hcard
  exact hcard.trans (C.candidatePairs_card_le fiberDegreeBound hdegree)

/-- The requested `(r-e)^2` affine bound under explicit, independently
checkable resultant and fiber degree hypotheses. -/
theorem AffineResultantFiberCertificate.commonZeroSet_ncard_le_degree_sq
    {P Q : BivariateRatPolynomial}
    (C : AffineResultantFiberCertificate P Q)
    (degreeBound : ℕ)
    (hresultantDegree : C.resultant.natDegree ≤ degreeBound)
    (hfiberDegree : ∀ t : ℚ,
      C.resultant.eval t = 0 →
      (C.fiber t).natDegree ≤ degreeBound) :
    (rationalCommonZeroSet P Q).ncard ≤ degreeBound ^ 2 := by
  calc
    (rationalCommonZeroSet P Q).ncard ≤
        C.resultant.natDegree * degreeBound :=
      C.commonZeroSet_ncard_le degreeBound hfiberDegree
    _ ≤ degreeBound * degreeBound :=
      Nat.mul_le_mul_right degreeBound hresultantDegree
    _ = degreeBound ^ 2 := by ring

/-- Osculation spelling of the preceding square bound. -/
theorem AffineResultantFiberCertificate.commonZeroSet_ncard_le_r_sub_e_sq
    {P Q : BivariateRatPolynomial}
    (C : AffineResultantFiberCertificate P Q)
    {r e : ℕ}
    (hresultantDegree : C.resultant.natDegree ≤ r - e)
    (hfiberDegree : ∀ t : ℚ,
      C.resultant.eval t = 0 →
      (C.fiber t).natDegree ≤ r - e) :
    (rationalCommonZeroSet P Q).ncard ≤ (r - e) ^ 2 :=
  C.commonZeroSet_ncard_le_degree_sq (r - e)
    hresultantDegree hfiberDegree

/-- The exact residual-branch interface: a selected factor-coprime residual
pair together with a separately certified zero-dimensional affine resultant
and fiber system.  Factor-coprimality alone does not construct the latter. -/
structure CertifiedCoprimeResidualIntersection
    {V : Submodule ℚ BivariateRatPolynomial}
    (h : FixedDivisorPresentation V) where
  first : V
  second : V
  coprime : FactorCoprime (h.quotient first) (h.quotient second)
  affineCertificate : AffineResultantFiberCertificate
    (h.quotient first) (h.quotient second)

/-- The corrected residual branch has at most `(r-e)^2` affine rational
points once its explicit resultant and fiber degree certificate is supplied.
This is not an effective enumeration theorem. -/
theorem CertifiedCoprimeResidualIntersection.commonZeroSet_ncard_le_r_sub_e_sq
    {V : Submodule ℚ BivariateRatPolynomial}
    {h : FixedDivisorPresentation V}
    (C : CertifiedCoprimeResidualIntersection h)
    {r e : ℕ}
    (hresultantDegree :
      C.affineCertificate.resultant.natDegree ≤ r - e)
    (hfiberDegree : ∀ t : ℚ,
      C.affineCertificate.resultant.eval t = 0 →
      (C.affineCertificate.fiber t).natDegree ≤ r - e) :
    (rationalCommonZeroSet
      (h.quotient C.first) (h.quotient C.second)).ncard ≤
        (r - e) ^ 2 :=
  C.affineCertificate.commonZeroSet_ncard_le_r_sub_e_sq
    hresultantDegree hfiberDegree

#print axioms rationalShearedPair_injective
#print axioms AffineResultantFiberCertificate.shearedPair_mem_candidatePairs
#print axioms AffineResultantFiberCertificate.candidatePairs_card_le
#print axioms AffineResultantFiberCertificate.commonZeroSet_finite
#print axioms AffineResultantFiberCertificate.commonZeroSet_ncard_le
#print axioms AffineResultantFiberCertificate.commonZeroSet_ncard_le_r_sub_e_sq
#print axioms CertifiedCoprimeResidualIntersection.commonZeroSet_ncard_le_r_sub_e_sq

end Erdos686Variant
end Erdos686
