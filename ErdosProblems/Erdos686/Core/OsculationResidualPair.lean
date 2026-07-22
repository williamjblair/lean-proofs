/- leanprover/lean4:v4.29.1 mathlib v4.29.1 -/
import ErdosProblems.Erdos686.Core.OsculationFixedDivisor
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors

/-!
# Erdős 686: extracting a coprime residual pair

The fixed-divisor presentation already proves that its entire residual
family has no common nonunit divisor.  Over the infinite field `ℚ`, this
family statement can be strengthened to the existence of two residual
elements with no common nonunit factor.

The proof fixes one nonzero residual polynomial.  Its normalized irreducible
factors are finite.  For each such factor, residual elements divisible by it
form a proper rational subspace.  A finite union of proper subspaces cannot
cover a vector space over `ℚ`, so a second residual avoids all of them.

This is only the coprime-pair extraction required by the corrected
fixed-divisor dichotomy.  It does not assert a Bezout identity or an effective
enumeration of the pair's integral common zeros.
-/

namespace Erdos686
namespace Erdos686Variant

open UniqueFactorizationMonoid

noncomputable local instance : NormalizationMonoid BivariateRatPolynomial :=
  UniqueFactorizationMonoid.normalizationMonoid

/-- Divisibility by a fixed polynomial pulls back along the residual linear
map to a rational subspace of the original polynomial space. -/
noncomputable def FixedDivisorPresentation.residualDivisibilitySubspace
    {V : Submodule ℚ BivariateRatPolynomial}
    (h : FixedDivisorPresentation V) (P : BivariateRatPolynomial) :
    Submodule ℚ V :=
  (divisiblePolynomialSubspace P).comap h.residualLinearMap

theorem FixedDivisorPresentation.mem_residualDivisibilitySubspace_iff
    {V : Submodule ℚ BivariateRatPolynomial}
    (h : FixedDivisorPresentation V) (P : BivariateRatPolynomial) (F : V) :
    F ∈ h.residualDivisibilitySubspace P ↔ P ∣ h.quotient F := by
  rfl

/-- Every irreducible residual divisor cuts out a proper subspace.  Otherwise
that irreducible would divide the whole residual family, contradicting the
universal property of the fixed divisor. -/
theorem FixedDivisorPresentation.residualDivisibilitySubspace_ne_top
    {V : Submodule ℚ BivariateRatPolynomial}
    (h : FixedDivisorPresentation V) {P : BivariateRatPolynomial}
    (hP : Irreducible P) :
    h.residualDivisibilitySubspace P ≠ ⊤ := by
  intro htop
  have hall : ∀ F : V, P ∣ h.quotient F := by
    intro F
    have hmem : F ∈ h.residualDivisibilitySubspace P := by
      rw [htop]
      exact Submodule.mem_top
    exact (h.mem_residualDivisibilitySubspace_iff P F).mp hmem
  exact hP.not_isUnit (h.residual_has_no_common_nonunit P hall)

/-- A nonzero element of the presented space has a nonzero residual
quotient. -/
theorem FixedDivisorPresentation.quotient_ne_zero_of_ne_zero
    {V : Submodule ℚ BivariateRatPolynomial}
    (h : FixedDivisorPresentation V) {F : V} (hF : F ≠ 0) :
    h.quotient F ≠ 0 := by
  intro hQ
  apply hF
  apply Subtype.ext
  calc
    F.1 = h.D * h.quotient F := h.factor F
    _ = 0 := by rw [hQ, mul_zero]
    _ = (0 : V).1 := rfl

/-- The corrected residual-family statement really does yield a pair of
factor-coprime residual elements.  The use of a finite-union theorem is
essential: unit gcd of a whole finite family does not imply that an arbitrary
selected pair is coprime. -/
theorem FixedDivisorPresentation.exists_factorCoprime_residual_pair
    {V : Submodule ℚ BivariateRatPolynomial}
    (h : FixedDivisorPresentation V) (hV : V ≠ ⊥) :
    ∃ F G : V, FactorCoprime (h.quotient F) (h.quotient G) := by
  classical
  haveI : Nontrivial V := Submodule.nontrivial_iff_ne_bot.mpr hV
  obtain ⟨F, hF⟩ : ∃ F : V, F ≠ 0 := exists_ne 0
  have hQF : h.quotient F ≠ 0 := h.quotient_ne_zero_of_ne_zero hF
  let factors : Type :=
    {P // P ∈ (normalizedFactors (h.quotient F)).toFinset}
  let factorSubspace : factors → Submodule ℚ V :=
    fun P ↦ h.residualDivisibilitySubspace P.1
  have hproper : ∀ P : factors, factorSubspace P ≠ ⊤ := by
    intro P
    apply h.residualDivisibilitySubspace_ne_top
    exact irreducible_of_normalized_factor P.1
      (Multiset.mem_toFinset.mp P.2)
  obtain ⟨G, hG⟩ :=
    Submodule.exists_forall_notMem_of_forall_ne_top factorSubspace hproper
  refine ⟨F, G, ?_⟩
  have hrel : IsRelPrime (h.quotient F) (h.quotient G) := by
    apply WfDvdMonoid.isRelPrime_of_no_irreducible_factors
    · exact fun hzero ↦ hQF hzero.1
    · intro P hPirred hPF hPG
      obtain ⟨Q, hQmem, hPQ⟩ :=
        exists_mem_normalizedFactors_of_dvd hQF hPirred hPF
      let Qidx : factors := ⟨Q, by simpa [factors] using hQmem⟩
      apply hG Qidx
      change Q ∣ h.quotient G
      exact hPQ.dvd_iff_dvd_left.mp hPG
  exact hrel

/-- The previously abstract pair-certificate interface is inhabited for every
nonzero presented residual space over `ℚ`. -/
theorem FixedDivisorPresentation.exists_coprimeResidualPairCertificate
    {V : Submodule ℚ BivariateRatPolynomial}
    (h : FixedDivisorPresentation V) (hV : V ≠ ⊥) :
    Nonempty (CoprimeResidualPairCertificate h) := by
  obtain ⟨F, G, hcop⟩ := h.exists_factorCoprime_residual_pair hV
  exact ⟨⟨F, G, hcop⟩⟩

/-- Under the exact bounded-kernel entry envelope, the canonical bounded
osculation polynomial space has both a fixed-divisor presentation and an
inhabited coprime residual-pair certificate. -/
theorem exists_boundedOsculationPresentation_with_coprimeResidualPair
    {m r k : ℕ}
    (A : Matrix (Fin (2 * m)) (OsculationMonomial r) ℤ)
    (hentry : ∀ i u,
      (A i u).natAbs ≤ 3 * r * 2 ^ k * k ^ (r - 1))
    (hm : 0 < m)
    (hcolumns : 4 * m + 1 ≤ osculationMonomialCount r)
    (hr : 0 < r) (hk : 0 < k) :
    ∃ h : FixedDivisorPresentation
        (boundedOsculationPolynomialSpace A
          (12 * osculationMonomialCount r * r *
            2 ^ k * k ^ (r - 1))),
      Nonempty (CoprimeResidualPairCertificate h) := by
  let V := boundedOsculationPolynomialSpace A
    (12 * osculationMonomialCount r * r * 2 ^ k * k ^ (r - 1))
  have hV : V ≠ ⊥ :=
    boundedOsculationPolynomialSpace_ne_bot_of_entry_bound
      A hentry hm hcolumns hr hk
  obtain ⟨h⟩ :=
    exists_fixedDivisorPresentation_boundedOsculation_of_entry_bound
      A hentry hm hcolumns hr hk
  exact ⟨h, h.exists_coprimeResidualPairCertificate hV⟩

/-- Direct corrected dichotomy for a whole vanishing space: either the fixed
divisor vanishes at the target, or a factor-coprime residual pair vanishes
there.  This stops before any claim of effective intersection enumeration. -/
theorem FixedDivisorPresentation.exists_factorCoprime_specialization_split
    {V : Submodule ℚ BivariateRatPolynomial}
    (h : FixedDivisorPresentation V) (hV : V ≠ ⊥)
    (p : Fin 2 → ℚ)
    (hzero : ∀ F : V, evalRatAt p F.1 = 0) :
    ∃ F G : V,
      FactorCoprime (h.quotient F) (h.quotient G) ∧
        (evalRatAt p h.D = 0 ∨
          (evalRatAt p (h.quotient F) = 0 ∧
            evalRatAt p (h.quotient G) = 0)) := by
  obtain ⟨F, G, hcop⟩ := h.exists_factorCoprime_residual_pair hV
  exact ⟨F, G, hcop, h.two_specialization_split F G p (hzero F) (hzero G)⟩

#print axioms FixedDivisorPresentation.residualDivisibilitySubspace_ne_top
#print axioms FixedDivisorPresentation.quotient_ne_zero_of_ne_zero
#print axioms FixedDivisorPresentation.exists_factorCoprime_residual_pair
#print axioms FixedDivisorPresentation.exists_coprimeResidualPairCertificate
#print axioms exists_boundedOsculationPresentation_with_coprimeResidualPair
#print axioms FixedDivisorPresentation.exists_factorCoprime_specialization_split

end Erdos686Variant
end Erdos686
