/- leanprover/lean4:v4.29.1 mathlib v4.29.1 -/
import ErdosProblems.Erdos686BoundedOsculationSpace
import ErdosProblems.Erdos686OsculationDichotomy

/-!
# Erdős 686: basis-free fixed-divisor interface

Mathlib does not presently provide the multivariate primitive gcd required
by the osculation campaign.  This module therefore records the exact
universal property of such a fixed divisor and proves everything which
follows from that property.  Existence or effective computation is not
asserted.

In particular, quotient polynomials below do not inherit the support jets.
The only specialization conclusion used here comes from evaluating the
displayed product identity.
-/

namespace Erdos686
namespace Erdos686Variant

open scoped BigOperators

/-- Convert total-degree coefficient vectors to rational bivariate
polynomials. -/
noncomputable def osculationCoeffToRatPolynomial (r : ℕ) :
    (OsculationMonomial r → ℚ) →ₗ[ℚ] BivariateRatPolynomial where
  toFun c := ∑ u,
    MvPolynomial.C (c u) *
      MvPolynomial.X 0 ^ u.xExponent *
      MvPolynomial.X 1 ^ u.yExponent
  map_add' c d := by
    simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
  map_smul' a c := by
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    simp [Algebra.smul_def, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    ring

/-- Polynomial realization of the canonical bounded coefficient space. -/
noncomputable def boundedOsculationPolynomialSpace
    {r q : ℕ} (A : Matrix (Fin q) (OsculationMonomial r) ℤ) (B : ℕ) :
    Submodule ℚ BivariateRatPolynomial :=
  (boundedOsculationSpace A B).map (osculationCoeffToRatPolynomial r)

/-- Universal-property definition of a fixed divisor of a polynomial
subspace.  It is independent of any basis or generating family by
construction. -/
structure IsFixedDivisor
    (V : Submodule ℚ BivariateRatPolynomial)
    (D : BivariateRatPolynomial) : Prop where
  ne_zero : D ≠ 0
  divides_all : ∀ F, F ∈ V → D ∣ F
  greatest : ∀ E : BivariateRatPolynomial,
    (∀ F, F ∈ V → E ∣ F) → E ∣ D

/-- Two fixed divisors of the same space differ only by a unit. -/
theorem IsFixedDivisor.associated
    {V : Submodule ℚ BivariateRatPolynomial}
    {D E : BivariateRatPolynomial}
    (hD : IsFixedDivisor V D) (hE : IsFixedDivisor V E) :
    Associated D E := by
  exact associated_of_dvd_dvd
    (hE.greatest D hD.divides_all)
    (hD.greatest E hE.divides_all)

/-- Replacing a fixed divisor by an associate is only scalar normalization. -/
theorem IsFixedDivisor.of_associated
    {V : Submodule ℚ BivariateRatPolynomial}
    {D E : BivariateRatPolynomial}
    (hD : IsFixedDivisor V D) (hDE : Associated D E) :
    IsFixedDivisor V E := by
  refine ⟨?_, ?_, ?_⟩
  · exact fun hE0 => hD.ne_zero (hDE.eq_zero_iff.mpr hE0)
  · intro F hFV
    exact hDE.dvd_iff_dvd_left.mp (hD.divides_all F hFV)
  · intro C hC
    exact hDE.dvd_iff_dvd_right.mp (hD.greatest C hC)

/-- Fixed-divisor status depends only on the subspace, so changing a basis or
any spanning family leaves it unchanged. -/
theorem isFixedDivisor_congr_space
    {V W : Submodule ℚ BivariateRatPolynomial}
    {D : BivariateRatPolynomial} (hVW : V = W) :
    IsFixedDivisor V D ↔ IsFixedDivisor W D := by
  subst W
  rfl

/-- Explicit generating-set version of basis independence. -/
theorem isFixedDivisor_span_congr
    {S T : Set BivariateRatPolynomial}
    {D : BivariateRatPolynomial}
    (hspan : Submodule.span ℚ S = Submodule.span ℚ T) :
    IsFixedDivisor (Submodule.span ℚ S) D ↔
      IsFixedDivisor (Submodule.span ℚ T) D :=
  isFixedDivisor_congr_space hspan

/-- A presentation of division of an entire polynomial space by its fixed
divisor.  The quotient is recorded pointwise; no false jet inheritance is
included. -/
structure FixedDivisorPresentation
    (V : Submodule ℚ BivariateRatPolynomial) where
  D : BivariateRatPolynomial
  fixed : IsFixedDivisor V D
  quotient : V → BivariateRatPolynomial
  factor : ∀ F : V, F.1 = D * quotient F

/-- The whole residual family has no nonunit common divisor.  This is a
family statement; it does not assert that an arbitrary selected pair is
coprime. -/
theorem FixedDivisorPresentation.residual_has_no_common_nonunit
    {V : Submodule ℚ BivariateRatPolynomial}
    (h : FixedDivisorPresentation V)
    (E : BivariateRatPolynomial)
    (hE : ∀ F : V, E ∣ h.quotient F) :
    IsUnit E := by
  have hDE : h.D * E ∣ h.D := by
    apply h.fixed.greatest
    intro F hFV
    let F' : V := ⟨F, hFV⟩
    obtain ⟨Q, hQ⟩ := hE F'
    refine ⟨Q, ?_⟩
    calc
      F = h.D * h.quotient F' := h.factor F'
      _ = (h.D * E) * Q := by rw [hQ]; ring
  apply isUnit_of_dvd_one
  exact (mul_dvd_mul_iff_left h.fixed.ne_zero).mp (by simpa using hDE)

/-- Specialization of one member of a fixed-divisor presentation.  This is
the valid product split and makes no derivative claim about the quotient. -/
theorem FixedDivisorPresentation.specialization_split
    {V : Submodule ℚ BivariateRatPolynomial}
    (h : FixedDivisorPresentation V)
    (F : V) (p : Fin 2 → ℚ)
    (hzero : evalRatAt p F.1 = 0) :
    evalRatAt p h.D = 0 ∨ evalRatAt p (h.quotient F) = 0 := by
  have hprod :
      evalRatAt p F.1 =
        evalRatAt p h.D * evalRatAt p (h.quotient F) := by
    simpa only [map_mul] using congrArg (evalRatAt p) (h.factor F)
  exact mul_eq_zero.mp (hprod ▸ hzero)

/-- Two residual specializations give the corrected fixed-divisor/residual
pair dichotomy.  Finiteness or effective enumeration of the residual pair
requires a separate resultant certificate. -/
theorem FixedDivisorPresentation.two_specialization_split
    {V : Submodule ℚ BivariateRatPolynomial}
    (h : FixedDivisorPresentation V)
    (F G : V) (p : Fin 2 → ℚ)
    (hF : evalRatAt p F.1 = 0)
    (hG : evalRatAt p G.1 = 0) :
    evalRatAt p h.D = 0 ∨
      (evalRatAt p (h.quotient F) = 0 ∧
        evalRatAt p (h.quotient G) = 0) := by
  rcases h.specialization_split F p hF with hD | hQF
  · exact Or.inl hD
  · rcases h.specialization_split G p hG with hD | hQG
    · exact Or.inl hD
    · exact Or.inr ⟨hQF, hQG⟩

/-- Interface for the extra certificate needed to select a coprime residual
pair.  Its existence is deliberately not inferred merely from the global
family gcd statement. -/
structure CoprimeResidualPairCertificate
    {V : Submodule ℚ BivariateRatPolynomial}
    (h : FixedDivisorPresentation V) where
  first : V
  second : V
  coprime : FactorCoprime (h.quotient first) (h.quotient second)

#print axioms IsFixedDivisor.associated
#print axioms IsFixedDivisor.of_associated
#print axioms FixedDivisorPresentation.residual_has_no_common_nonunit
#print axioms FixedDivisorPresentation.two_specialization_split

end Erdos686Variant
end Erdos686
