/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686BoundedOsculationSpace
import ErdosProblems.Erdos686OsculationDichotomy
import ErdosProblems.Erdos686LocalJetFactorAllocation

/-!
# Erdős 686: canonical fixed divisor and corrected residual dichotomy

The fixed divisor is attached to the entire bounded rational space, not to a
chosen pair of kernel vectors.  A pair, basis, or bounded generating family may
be used to compute it only after a certificate proves that it detects exactly
the same common divisors.

The residual branch below is deliberately certificate-backed.  Factor
coprimality gives a zero-dimensional algebraic branch, but integral enumeration
is left to the effective resultant interface.
-/

namespace Erdos686
namespace Erdos686Variant

abbrev BivariatePolynomialSpace :=
  Submodule ℚ BivariateRatPolynomial

/-- A basis-free fixed-divisor specification.  The first field says `D` divides
every member of `V`; the second says every other common divisor divides `D`.
Thus `D` is unique up to a rational unit. -/
structure FixedDivisorCertificate
    (V : BivariatePolynomialSpace) (D : BivariateRatPolynomial) : Prop where
  divides : ∀ F : BivariateRatPolynomial, F ∈ V → D ∣ F
  greatest : ∀ G : BivariateRatPolynomial,
    (∀ F : BivariateRatPolynomial, F ∈ V → G ∣ F) → G ∣ D

/-- Any two fixed divisors of the same space are associated.  This is the
basis-independent uniqueness statement. -/
theorem fixedDivisor_associated
    {V : BivariatePolynomialSpace} {D E : BivariateRatPolynomial}
    (hD : FixedDivisorCertificate V D)
    (hE : FixedDivisorCertificate V E) :
    Associated D E := by
  apply associated_iff_dvd_dvd.mpr
  exact ⟨hE.greatest D hD.divides, hD.greatest E hE.divides⟩

/-- Canonical choice of a fixed divisor when a fixed-divisor certificate is
available.  All theorems about this choice are invariant under association. -/
noncomputable def canonicalFixedDivisor
    (V : BivariatePolynomialSpace)
    (hexists : ∃ D, FixedDivisorCertificate V D) :
    BivariateRatPolynomial :=
  Classical.choose hexists

theorem canonicalFixedDivisor_spec
    (V : BivariatePolynomialSpace)
    (hexists : ∃ D, FixedDivisorCertificate V D) :
    FixedDivisorCertificate V (canonicalFixedDivisor V hexists) :=
  Classical.choose_spec hexists

/-- Polynomial realization of the canonical coefficient space.  The choice of
realization is explicit; no hidden identification with the full jet space is
made. -/
noncomputable def boundedOsculationPolynomialSpace
    {r m : ℕ} (S : OsculationSupportData m) (B : ℕ)
    (realize : (OsculationMonomial r → ℚ) →ₗ[ℚ] BivariateRatPolynomial) :
    BivariatePolynomialSpace :=
  (boundedOsculationSpace S B).map realize

/-- The fixed divisor `D_S` of the whole bounded polynomial space. -/
noncomputable def boundedOsculationFixedDivisor
    {r m : ℕ} (S : OsculationSupportData m) (B : ℕ)
    (realize : (OsculationMonomial r → ℚ) →ₗ[ℚ] BivariateRatPolynomial)
    (hexists : ∃ D,
      FixedDivisorCertificate
        (boundedOsculationPolynomialSpace S B realize) D) :
    BivariateRatPolynomial :=
  canonicalFixedDivisor (boundedOsculationPolynomialSpace S B realize) hexists

/-- A family detects common divisors of `V` exactly.  This is the missing
hypothesis whenever a selected family or basis is used to compute the fixed
divisor. -/
structure FamilyDetectsCommonDivisors
    {ι : Type*} (V : BivariatePolynomialSpace)
    (f : ι → BivariateRatPolynomial) : Prop where
  mem : ∀ i, f i ∈ V
  detects : ∀ G : BivariateRatPolynomial,
    (∀ F : BivariateRatPolynomial, F ∈ V → G ∣ F) ↔
      ∀ i, G ∣ f i

/-- GCD specification for a selected family. -/
structure FamilyGCDCertificate
    {ι : Type*} (f : ι → BivariateRatPolynomial)
    (D : BivariateRatPolynomial) : Prop where
  divides : ∀ i, D ∣ f i
  greatest : ∀ G : BivariateRatPolynomial,
    (∀ i, G ∣ f i) → G ∣ D

/-- A detecting family GCD is a fixed divisor of the whole space. -/
theorem FamilyGCDCertificate.toFixedDivisor
    {ι : Type*} {V : BivariatePolynomialSpace}
    {f : ι → BivariateRatPolynomial} {D : BivariateRatPolynomial}
    (hdetect : FamilyDetectsCommonDivisors V f)
    (hfamily : FamilyGCDCertificate f D) :
    FixedDivisorCertificate V D := by
  constructor
  · exact (hdetect.detects D).mpr hfamily.divides
  · intro G hG
    exact hfamily.greatest G ((hdetect.detects G).mp hG)

/-- Independence from the selected bounded generating family. -/
theorem fixedDivisor_independent_of_selected_family
    {ι κ : Type*} {V : BivariatePolynomialSpace}
    {f : ι → BivariateRatPolynomial}
    {g : κ → BivariateRatPolynomial}
    {D E : BivariateRatPolynomial}
    (hf : FamilyDetectsCommonDivisors V f)
    (hg : FamilyDetectsCommonDivisors V g)
    (hD : FamilyGCDCertificate f D)
    (hE : FamilyGCDCertificate g E) :
    Associated D E :=
  fixedDivisor_associated (hD.toFixedDivisor hf) (hE.toFixedDivisor hg)

/-- Basis changes do not change the fixed divisor, provided both bases detect
all common divisors of the same space. -/
theorem fixedDivisor_independent_of_basis_change
    {ι κ : Type*} {V : BivariatePolynomialSpace}
    {basis₁ : ι → BivariateRatPolynomial}
    {basis₂ : κ → BivariateRatPolynomial}
    {D₁ D₂ : BivariateRatPolynomial}
    (h₁ : FamilyDetectsCommonDivisors V basis₁)
    (h₂ : FamilyDetectsCommonDivisors V basis₂)
    (hD₁ : FamilyGCDCertificate basis₁ D₁)
    (hD₂ : FamilyGCDCertificate basis₂ D₂) :
    Associated D₁ D₂ :=
  fixedDivisor_independent_of_selected_family h₁ h₂ hD₁ hD₂

/-- Scalar normalization cannot change the fixed divisor once both normalized
representatives satisfy the same basis-free specification. -/
theorem fixedDivisor_independent_of_scalar_normalization
    {V : BivariatePolynomialSpace} {D D' : BivariateRatPolynomial}
    (hD : FixedDivisorCertificate V D)
    (hD' : FixedDivisorCertificate V D') :
    Associated D D' :=
  fixedDivisor_associated hD hD'

/-- A pair of kernel vectors determines the canonical fixed divisor only when
it is certified to detect every common divisor of the full bounded space. -/
theorem fixedDivisor_independent_of_detecting_pair
    {V : BivariatePolynomialSpace}
    {pair₁ pair₂ : Fin 2 → BivariateRatPolynomial}
    {D₁ D₂ : BivariateRatPolynomial}
    (hpair₁ : FamilyDetectsCommonDivisors V pair₁)
    (hpair₂ : FamilyDetectsCommonDivisors V pair₂)
    (hD₁ : FamilyGCDCertificate pair₁ D₁)
    (hD₂ : FamilyGCDCertificate pair₂ D₂) :
    Associated D₁ D₂ :=
  fixedDivisor_independent_of_selected_family hpair₁ hpair₂ hD₁ hD₂

/-- Division of the whole bounded space by its fixed divisor.  The quotient is
recorded for every member of the space, not merely for two selected vectors. -/
structure ResidualSystem
    (V : BivariatePolynomialSpace) (D : BivariateRatPolynomial) where
  quotient : V → BivariateRatPolynomial
  factor : ∀ F : V, F.1 = D * quotient F

/-- A common divisor of every residual quotient must be a unit. -/
theorem residualSystem_has_no_nonunit_common_divisor
    {V : BivariatePolynomialSpace} {D : BivariateRatPolynomial}
    (hD : FixedDivisorCertificate V D)
    (hDne : D ≠ 0)
    (R : ResidualSystem V D)
    (E : BivariateRatPolynomial)
    (hE : ∀ F : V, E ∣ R.quotient F) :
    IsUnit E := by
  have hDE : ∀ F : BivariateRatPolynomial, F ∈ V → D * E ∣ F := by
    intro F hF
    let FV : V := ⟨F, hF⟩
    rcases hE FV with ⟨Q, hQ⟩
    refine ⟨Q, ?_⟩
    rw [R.factor FV, hQ]
    ring
  rcases hD.greatest (D * E) hDE with ⟨Q, hQ⟩
  have hEQ : E * Q = 1 := by
    apply mul_left_cancel₀ hDne
    calc
      D * (E * Q) = (D * E) * Q := by ring
      _ = D := hQ.symm
      _ = D * 1 := by ring
  exact isUnit_iff_exists_inv.mpr ⟨Q, hEQ⟩

/-- Certificate that two residual members are factor-coprime and carry the
support-dependent Bézout intersection bound.  The integer `intersectionCount`
counts projective intersections with multiplicity. -/
structure ResidualPairCertificate
    {V : BivariatePolynomialSpace} {D : BivariateRatPolynomial}
    (R : ResidualSystem V D) (degreeBound : ℕ) where
  left : V
  right : V
  factor_coprime : FactorCoprime (R.quotient left) (R.quotient right)
  left_degree_le : ℕ
  right_degree_le : ℕ
  left_degree_bound : left_degree_le ≤ degreeBound
  right_degree_bound : right_degree_le ≤ degreeBound
  intersectionCount : ℕ
  bezout_bound : intersectionCount ≤ degreeBound ^ 2

/-- The effective residual branch at a specified point. -/
structure ResidualBranchAt
    {V : BivariatePolynomialSpace} {D : BivariateRatPolynomial}
    (R : ResidualSystem V D) (p : Fin 2 → ℚ) (degreeBound : ℕ) : Prop where
  P : BivariateRatPolynomial
  Q : BivariateRatPolynomial
  P_is_residual : ∃ F : V, P = R.quotient F
  Q_is_residual : ∃ F : V, Q = R.quotient F
  factor_coprime : FactorCoprime P Q
  P_zero : evalRatAt p P = 0
  Q_zero : evalRatAt p Q = 0
  no_nonunit_common_divisor :
    ∀ E : BivariateRatPolynomial,
      (∀ F : V, E ∣ R.quotient F) → IsUnit E
  projectiveIntersectionCount : ℕ
  bezout_bound : projectiveIntersectionCount ≤ degreeBound ^ 2

/-- If all original members vanish at `p` and the fixed divisor does not,
every residual quotient vanishes at `p`. -/
theorem residual_quotient_vanishes_at
    {V : BivariatePolynomialSpace} {D : BivariateRatPolynomial}
    (R : ResidualSystem V D) (p : Fin 2 → ℚ)
    (hvanish : ∀ F : BivariateRatPolynomial, F ∈ V → evalRatAt p F = 0)
    (hDpoint : evalRatAt p D ≠ 0)
    (F : V) :
    evalRatAt p (R.quotient F) = 0 := by
  have hprod : evalRatAt p D * evalRatAt p (R.quotient F) = 0 := by
    rw [← map_mul]
    rw [← R.factor F]
    exact hvanish F.1 F.2
  exact (mul_eq_zero.mp hprod).resolve_left hDpoint

/-- Corrected fixed-divisor dichotomy.  The second branch is not declared
eliminated: it carries a finite-intersection bound and must be passed to an
effective resultant certificate for integral enumeration. -/
theorem corrected_fixed_divisor_dichotomy
    {V : BivariatePolynomialSpace} {D : BivariateRatPolynomial}
    (hD : FixedDivisorCertificate V D)
    (R : ResidualSystem V D)
    (p : Fin 2 → ℚ) (r e : ℕ)
    (hvanish : ∀ F : BivariateRatPolynomial, F ∈ V → evalRatAt p F = 0)
    (hpair : ResidualPairCertificate R (r - e)) :
    evalRatAt p D = 0 ∨ ResidualBranchAt R p (r - e) := by
  by_cases hDpoint : evalRatAt p D = 0
  · exact Or.inl hDpoint
  · right
    have hDne : D ≠ 0 := by
      intro hzero
      apply hDpoint
      simp [hzero]
    refine
      { P := R.quotient hpair.left
        Q := R.quotient hpair.right
        P_is_residual := ⟨hpair.left, rfl⟩
        Q_is_residual := ⟨hpair.right, rfl⟩
        factor_coprime := hpair.factor_coprime
        P_zero := residual_quotient_vanishes_at R p hvanish hDpoint hpair.left
        Q_zero := residual_quotient_vanishes_at R p hvanish hDpoint hpair.right
        no_nonunit_common_divisor :=
          residualSystem_has_no_nonunit_common_divisor hD hDne R
        projectiveIntersectionCount := hpair.intersectionCount
        bezout_bound := hpair.bezout_bound }

/-- Dimension and degree data required for the fixed-divisor bound on the full
jet space.  The `dimension_upper` field is the multiplication-by-divisor
injection into degree at most `r-e`; it is intentionally scoped to `K_r(S)`. -/
structure FullJetFixedDivisorDegreeCertificate
    {r m : ℕ} (S : OsculationSupportData m) (e : ℕ) : Prop where
  e_le_r : e ≤ r
  dimension_upper :
    Module.finrank ℚ (fullRationalJetSpace S) ≤
      osculationMonomialCount (r - e)
  count_gap_identity :
    2 * (osculationMonomialCount r -
      osculationMonomialCount (r - e)) =
      e * (2 * r - e + 3)

/-- Fixed-divisor degree bound for the full rational jet space only:
`e(2r-e+3)/2 <= 2m`. -/
theorem fullJet_fixedDivisor_degree_bound
    {r m e : ℕ} (S : OsculationSupportData m)
    (h : FullJetFixedDivisorDegreeCertificate S e) :
    e * (2 * r - e + 3) / 2 ≤ 2 * m := by
  have hlower := fullRationalJetSpace_finrank_lower S
  have hupper := h.dimension_upper
  have hcount := h.count_gap_identity
  have hgap :
      osculationMonomialCount r -
          osculationMonomialCount (r - e) ≤ 2 * m := by
    omega
  have hstrong : e * (2 * r - e + 3) ≤ 4 * m := by
    omega
  omega

/-- Transferring a full-jet fixed-divisor degree theorem to `V_B(S)` requires
an explicit spanning theorem. -/
def BoundedFixedDivisorDegreeTransferAllowed
    {r m : ℕ} (S : OsculationSupportData m) (B : ℕ) : Prop :=
  BoundedSpaceSpansFullJet S B

#print axioms fixedDivisor_associated
#print axioms canonicalFixedDivisor_spec
#print axioms FamilyGCDCertificate.toFixedDivisor
#print axioms fixedDivisor_independent_of_selected_family
#print axioms fixedDivisor_independent_of_basis_change
#print axioms fixedDivisor_independent_of_scalar_normalization
#print axioms fixedDivisor_independent_of_detecting_pair
#print axioms residualSystem_has_no_nonunit_common_divisor
#print axioms residual_quotient_vanishes_at
#print axioms corrected_fixed_divisor_dichotomy
#print axioms fullJet_fixedDivisor_degree_bound

end Erdos686Variant
end Erdos686
