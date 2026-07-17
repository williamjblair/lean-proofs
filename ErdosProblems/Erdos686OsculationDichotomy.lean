/- leanprover/lean4:v4.29.1 mathlib v4.29.1 -/
import ErdosProblems.Erdos686SparseJetCertificate

/-!
# Erdős 686: fixed-factor specialization after bivariate osculation

This file records only the value-level factor-specialization statement valid
without an effective multivariate Bézout theorem.  If two integral bivariate
polynomials have a displayed fixed factor, then at a common integral zero
either that fixed factor vanishes or both displayed residual quotients vanish.

This split says nothing about allocation of a support derivative jet.  In
particular, it does not say that the fixed factor inherits the value and
directional-derivative conditions.  The exact three-case product-rule theorem
is provided by `Erdos686LocalJetFactorAllocation`.

The factorization interface below also says exactly what is meant by a
"primitive rational gcd presentation": the integral fixed factor is
primitive, and its two quotients have no common nonunit factor after mapping
their coefficients to `ℚ`.  We do not identify the residual branch with an
effectively enumerated finite intersection here.  That requires a separate
resultant certificate.
-/

namespace Erdos686
namespace Erdos686Variant

abbrev BivariateRatPolynomial := MvPolynomial (Fin 2) ℚ

/-- Coefficient extension from integral to rational bivariate polynomials. -/
noncomputable def rationalize :
    BivariateIntPolynomial →+* BivariateRatPolynomial :=
  MvPolynomial.map (algebraMap ℤ ℚ)

/-- Evaluation of an integral bivariate polynomial at an integral point. -/
noncomputable def evalIntAt (p : Fin 2 → ℤ) :
    BivariateIntPolynomial →+* ℤ :=
  MvPolynomial.eval₂Hom (RingHom.id ℤ) p

/-- Evaluation of a rational bivariate polynomial at a rational point. -/
noncomputable def evalRatAt (p : Fin 2 → ℚ) :
    BivariateRatPolynomial →+* ℚ :=
  MvPolynomial.eval₂Hom (RingHom.id ℚ) p

/-- An integral multivariate polynomial is primitive when every integer
dividing all of its coefficients is a unit.  Quantifying over every exponent,
rather than just the finite support, makes the zero coefficients harmless. -/
def IsPrimitiveInt (P : BivariateIntPolynomial) : Prop :=
  ∀ d : ℤ, (∀ e : Fin 2 →₀ ℕ, d ∣ P.coeff e) → IsUnit d

/-- Factor-coprimality is the correct multivariate replacement for a gcd
equation.  `IsCoprime` would be too strong here: in `ℚ[X,Y]`, the polynomials
`X` and `Y` have no common irreducible factor but do not generate the unit
ideal. -/
def FactorCoprime {R : Type*} [CommRing R] (P Q : R) : Prop :=
  ∀ D : R, D ∣ P → D ∣ Q → IsUnit D

/-- A precise integral presentation of a rational fixed gcd, up to rational
units.  The factor equations are integral; primitiveness fixes the scalar
content of `G`; factor-coprimality of the rationalized quotients says no
further nonunit polynomial factor remains common over `ℚ`.

No claim about Bézout coefficients or inherited support jets is bundled into
this structure. -/
structure PrimitiveRationalGCDPresentation
    (F₁ F₂ : BivariateIntPolynomial) where
  G : BivariateIntPolynomial
  Q₁ : BivariateIntPolynomial
  Q₂ : BivariateIntPolynomial
  factor_first : F₁ = G * Q₁
  factor_second : F₂ = G * Q₂
  primitive_G : IsPrimitiveInt G
  coprime_rational_quotients :
    FactorCoprime (rationalize Q₁) (rationalize Q₂)

/-- Rationalization commutes with specialization at an integral point. -/
theorem rationalize_specialize (p : Fin 2 → ℤ)
    (F : BivariateIntPolynomial) :
    evalRatAt (fun i => (p i : ℚ)) (rationalize F) =
      (evalIntAt p F : ℚ) := by
  change MvPolynomial.eval₂ (RingHom.id ℚ) (fun i => (p i : ℚ))
      (MvPolynomial.map (algebraMap ℤ ℚ) F) =
    algebraMap ℤ ℚ (MvPolynomial.eval₂ (RingHom.id ℤ) p F)
  rw [MvPolynomial.eval₂_map]
  simpa using
    (MvPolynomial.eval₂_comp_right
      (algebraMap ℤ ℚ) (RingHom.id ℤ) p F).symm

/-- A displayed integral fixed factor remains a common factor over `ℚ`. -/
theorem PrimitiveRationalGCDPresentation.rational_common_factor
    {F₁ F₂ : BivariateIntPolynomial}
    (h : PrimitiveRationalGCDPresentation F₁ F₂) :
    rationalize h.G ∣ rationalize F₁ ∧
      rationalize h.G ∣ rationalize F₂ := by
  constructor
  · refine ⟨rationalize h.Q₁, ?_⟩
    simpa only [map_mul] using
      congrArg rationalize h.factor_first
  · refine ⟨rationalize h.Q₂, ?_⟩
    simpa only [map_mul] using
      congrArg rationalize h.factor_second

/-- The fixed-divisor branch at an integral specialization. -/
def PrimitiveRationalGCDPresentation.FixedFactorAt
    {F₁ F₂ : BivariateIntPolynomial}
    (h : PrimitiveRationalGCDPresentation F₁ F₂)
    (p : Fin 2 → ℤ) : Prop :=
  evalIntAt p h.G = 0

/-- The residual-pair branch at an integral specialization.  This name does
not assert zero-dimensionality or effective elimination. -/
def PrimitiveRationalGCDPresentation.ResidualPairAt
    {F₁ F₂ : BivariateIntPolynomial}
    (h : PrimitiveRationalGCDPresentation F₁ F₂)
    (p : Fin 2 → ℤ) : Prop :=
  evalIntAt p h.Q₁ = 0 ∧ evalIntAt p h.Q₂ = 0

/-- Evaluation of two product identities in an integral domain gives the
exact fixed-factor/residual-pair split. -/
theorem evaluated_product_split
    {R : Type*} [CommRing R] [IsDomain R]
    {F₁ F₂ G Q₁ Q₂ : R}
    (h₁ : F₁ = G * Q₁) (h₂ : F₂ = G * Q₂)
    (hz₁ : F₁ = 0) (hz₂ : F₂ = 0) :
    G = 0 ∨ (Q₁ = 0 ∧ Q₂ = 0) := by
  by_cases hG : G = 0
  · exact Or.inl hG
  · right
    constructor
    · exact (mul_eq_zero.mp (h₁ ▸ hz₁)).resolve_left hG
    · exact (mul_eq_zero.mp (h₂ ▸ hz₂)).resolve_left hG

/-- Direct polynomial specialization form of `evaluated_product_split`.  It
requires only the displayed factorizations and makes no gcd or jet claim. -/
theorem bivariate_specialization_split
    {F₁ F₂ G Q₁ Q₂ : BivariateIntPolynomial}
    (h₁ : F₁ = G * Q₁) (h₂ : F₂ = G * Q₂)
    (p : Fin 2 → ℤ)
    (hz₁ : evalIntAt p F₁ = 0)
    (hz₂ : evalIntAt p F₂ = 0) :
    evalIntAt p G = 0 ∨
      (evalIntAt p Q₁ = 0 ∧ evalIntAt p Q₂ = 0) := by
  apply evaluated_product_split
      (R := ℤ)
      (F₁ := evalIntAt p F₁) (F₂ := evalIntAt p F₂)
      (G := evalIntAt p G)
      (Q₁ := evalIntAt p Q₁) (Q₂ := evalIntAt p Q₂)
  · simpa only [map_mul] using congrArg (evalIntAt p) h₁
  · simpa only [map_mul] using congrArg (evalIntAt p) h₂
  · exact hz₁
  · exact hz₂

/-- Unit fixed factors contribute no zero locus, including after integral
specialization. -/
theorem bivariate_quotients_vanish_of_isUnit_common_factor
    {F₁ F₂ G Q₁ Q₂ : BivariateIntPolynomial}
    (h₁ : F₁ = G * Q₁) (h₂ : F₂ = G * Q₂)
    (hunit : IsUnit G)
    (p : Fin 2 → ℤ)
    (hz₁ : evalIntAt p F₁ = 0)
    (hz₂ : evalIntAt p F₂ = 0) :
    evalIntAt p Q₁ = 0 ∧ evalIntAt p Q₂ = 0 := by
  rcases bivariate_specialization_split h₁ h₂ p hz₁ hz₂ with hzero | hquot
  · exact False.elim ((hunit.map (evalIntAt p)).ne_zero hzero)
  · exact hquot

/-- Specializing a primitive rational gcd presentation at a common integral
zero produces the exact value-level dichotomy used by the osculation campaign. -/
theorem PrimitiveRationalGCDPresentation.specialization_split
    {F₁ F₂ : BivariateIntPolynomial}
    (h : PrimitiveRationalGCDPresentation F₁ F₂)
    (p : Fin 2 → ℤ)
    (hz₁ : evalIntAt p F₁ = 0)
    (hz₂ : evalIntAt p F₂ = 0) :
    h.FixedFactorAt p ∨ h.ResidualPairAt p := by
  exact bivariate_specialization_split
    h.factor_first h.factor_second p hz₁ hz₂

/-- If the displayed fixed factor is a unit polynomial, its specialization
cannot vanish, so every common zero lies in the residual-pair branch. -/
theorem PrimitiveRationalGCDPresentation.residualPairAt_of_isUnit_G
    {F₁ F₂ : BivariateIntPolynomial}
    (h : PrimitiveRationalGCDPresentation F₁ F₂)
    (p : Fin 2 → ℤ)
    (hunit : IsUnit h.G)
    (hz₁ : evalIntAt p F₁ = 0)
    (hz₂ : evalIntAt p F₂ = 0) :
    h.ResidualPairAt p := by
  rcases h.specialization_split p hz₁ hz₂ with hzero | hquot
  · exact False.elim ((hunit.map (evalIntAt p)).ne_zero hzero)
  · exact hquot

/-- Public interface for rational factor-coprimality of the residual
quotients.  This is weaker than a Bézout identity and is stable under the
intended multivariate interpretation. -/
theorem PrimitiveRationalGCDPresentation.coprime_quotient_interface
    {F₁ F₂ : BivariateIntPolynomial}
    (h : PrimitiveRationalGCDPresentation F₁ F₂)
    (D : BivariateRatPolynomial)
    (hd₁ : D ∣ rationalize h.Q₁)
    (hd₂ : D ∣ rationalize h.Q₂) :
    IsUnit D :=
  h.coprime_rational_quotients D hd₁ hd₂

#print axioms rationalize_specialize
#print axioms evaluated_product_split
#print axioms bivariate_specialization_split
#print axioms bivariate_quotients_vanish_of_isUnit_common_factor
#print axioms PrimitiveRationalGCDPresentation.specialization_split
#print axioms PrimitiveRationalGCDPresentation.residualPairAt_of_isUnit_G
#print axioms PrimitiveRationalGCDPresentation.coprime_quotient_interface

end Erdos686Variant
end Erdos686
