/- leanprover/lean4:v4.29.1 mathlib v4.29.1 -/
import ErdosProblems.Erdos686BoundedOsculationSpace
import ErdosProblems.Erdos686OsculationDichotomy
import ErdosProblems.Erdos686OsculationKernel
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid

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

noncomputable local instance : NormalizationMonoid BivariateRatPolynomial :=
  UniqueFactorizationMonoid.normalizationMonoid

noncomputable local instance : NormalizedGCDMonoid BivariateRatPolynomial :=
  UniqueFactorizationMonoid.toNormalizedGCDMonoid BivariateRatPolynomial

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

theorem osculationMonomial_exponents_injective {r : ℕ}
    {u v : OsculationMonomial r}
    (h : u.xExponent = v.xExponent ∧
      u.yExponent = v.yExponent) :
    u = v := by
  rcases h with ⟨hx, hy⟩
  rcases u with ⟨ua, ub⟩
  rcases v with ⟨va, vb⟩
  dsimp [OsculationMonomial.xExponent,
    OsculationMonomial.yExponent] at hx hy ⊢
  have huv : ua = va := Fin.ext hx
  subst va
  congr
  exact Fin.ext hy

theorem osculationRatMonomial_eq_monomial
    {r : ℕ} (c : ℚ) (u : OsculationMonomial r) :
    MvPolynomial.C c * MvPolynomial.X 0 ^ u.xExponent *
        MvPolynomial.X 1 ^ u.yExponent =
      MvPolynomial.monomial
        (bivariateExponent u.xExponent u.yExponent) c := by
  rw [MvPolynomial.C_mul_X_pow_eq_monomial]
  rw [← MvPolynomial.monomial_add_single]
  rfl

/-- Reading the coefficient at a basis exponent recovers the corresponding
coefficient-vector entry. -/
theorem osculationCoeffToRatPolynomial_coeff
    {r : ℕ} (c : OsculationMonomial r → ℚ)
    (u : OsculationMonomial r) :
    (osculationCoeffToRatPolynomial r c).coeff
        (bivariateExponent u.xExponent u.yExponent) = c u := by
  simp only [osculationCoeffToRatPolynomial, LinearMap.coe_mk,
    AddHom.coe_mk, MvPolynomial.coeff_sum,
    osculationRatMonomial_eq_monomial,
    MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single u]
  · simp
  · intro v _ hv
    simp only [ite_eq_right_iff]
    intro hexp
    exfalso
    apply hv
    apply osculationMonomial_exponents_injective
    exact bivariateExponent_eq_iff.mp hexp
  · simp

/-- Distinct total-degree coefficient vectors define distinct rational
bivariate polynomials. -/
theorem osculationCoeffToRatPolynomial_injective (r : ℕ) :
    Function.Injective (osculationCoeffToRatPolynomial r) := by
  intro c d hcd
  funext u
  have hcoeff := congrArg
    (fun P : BivariateRatPolynomial =>
      P.coeff (bivariateExponent u.xExponent u.yExponent)) hcd
  simpa only [osculationCoeffToRatPolynomial_coeff] using hcoeff

/-- Polynomial realization of the canonical bounded coefficient space. -/
noncomputable def boundedOsculationPolynomialSpace
    {r q : ℕ} (A : Matrix (Fin q) (OsculationMonomial r) ℤ) (B : ℕ) :
    Submodule ℚ BivariateRatPolynomial :=
  (boundedOsculationSpace A B).map (osculationCoeffToRatPolynomial r)

/-- One nonzero bounded integral kernel vector already makes the canonical
bounded polynomial space nonzero. -/
theorem boundedOsculationPolynomialSpace_ne_bot_of_kernel_vector
    {r q : ℕ} (A : Matrix (Fin q) (OsculationMonomial r) ℤ)
    (B : ℕ) (z : OsculationMonomial r → ℤ)
    (hzker : A.mulVec z = 0)
    (hzbound : ∀ u, (z u).natAbs ≤ B)
    (hzne : z ≠ 0) :
    boundedOsculationPolynomialSpace A B ≠ ⊥ := by
  have hzlat : z ∈ integralOsculationLattice A :=
    (mem_integralOsculationLattice_iff A z).mpr hzker
  have hzcoeff : integralCoeffCast z ∈ boundedOsculationSpace A B :=
    Submodule.subset_span ⟨z, hzlat, hzbound, rfl⟩
  have hzcast_ne : integralCoeffCast z ≠ 0 := by
    intro hzero
    apply hzne
    funext u
    have hu := congrFun hzero u
    change (z u : ℚ) = 0 at hu
    exact_mod_cast hu
  have hpoly_ne :
      osculationCoeffToRatPolynomial r (integralCoeffCast z) ≠ 0 := by
    intro hzero
    apply hzcast_ne
    apply osculationCoeffToRatPolynomial_injective r
    simpa using hzero
  have hmem :
      osculationCoeffToRatPolynomial r (integralCoeffCast z) ∈
        boundedOsculationPolynomialSpace A B := by
    exact ⟨integralCoeffCast z, hzcoeff, rfl⟩
  intro hbot
  rw [hbot] at hmem
  exact hpoly_ne (by simpa using hmem)

/-- Exact numerical route from the banked bounded independent kernel family
to nontriviality of the canonical bounded polynomial space. -/
theorem boundedOsculationPolynomialSpace_ne_bot_of_entry_bound
    {m r k : ℕ}
    (A : Matrix (Fin (2 * m)) (OsculationMonomial r) ℤ)
    (hentry : ∀ i u,
      (A i u).natAbs ≤ 3 * r * 2 ^ k * k ^ (r - 1))
    (hm : 0 < m)
    (hcolumns : 4 * m + 1 ≤ osculationMonomialCount r)
    (hr : 0 < r) (hk : 0 < k) :
    boundedOsculationPolynomialSpace A
      (12 * osculationMonomialCount r * r * 2 ^ k * k ^ (r - 1)) ≠ ⊥ := by
  let N := Fintype.card (OsculationMonomial r)
  let e : Fin N ≃ OsculationMonomial r :=
    (Fintype.equivFin (OsculationMonomial r)).symm
  let A' : Matrix (Fin (2 * m)) (Fin N) ℤ := A.submatrix id e
  have hentry' : ∀ i j,
      (A' i j).natAbs ≤ 3 * r * 2 ^ k * k ^ (r - 1) := by
    intro i j
    exact hentry i (e j)
  have hcolumns' : 4 * m + 1 ≤ N := by
    change 4 * m + 1 ≤ Fintype.card (OsculationMonomial r)
    rw [osculationMonomialBasis_card]
    exact hcolumns
  obtain ⟨z, hli, hker, hbound⟩ :=
    exists_bounded_independent_osculation_kernel_family_advertised
      A' hentry' hm hcolumns' hr hk
  have hindex : 0 < N - 4 * m + 1 := by omega
  let i0 : Fin (N - 4 * m + 1) := ⟨0, hindex⟩
  let z0 : Fin N → ℤ := z i0
  have hz0ne : z0 ≠ 0 := by
    intro hz0
    apply hli.ne_zero i0
    funext j
    simp [z0, hz0]
  let z' : OsculationMonomial r → ℤ := fun u => z0 (e.symm u)
  have hz'ne : z' ≠ 0 := by
    intro hz'
    apply hz0ne
    funext j
    have hj := congrFun hz' (e j)
    simpa [z'] using hj
  have hz'ker : A.mulVec z' = 0 := by
    have hz0ker := hker i0
    rw [show A' = A.submatrix id e by rfl,
      Matrix.submatrix_mulVec_equiv] at hz0ker
    simpa [z', z0] using hz0ker
  have hz'bound : ∀ u,
      (z' u).natAbs ≤
        12 * osculationMonomialCount r * r * 2 ^ k * k ^ (r - 1) := by
    intro u
    have hu := hbound i0 (e.symm u)
    change (z' u).natAbs ≤
      12 * Fintype.card (OsculationMonomial r) * r *
        2 ^ k * k ^ (r - 1) at hu
    rw [osculationMonomialBasis_card] at hu
    exact hu
  exact boundedOsculationPolynomialSpace_ne_bot_of_kernel_vector
    A _ z' hz'ker hz'bound hz'ne

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

/-- The rational subspace consisting of all multiples of `D`. -/
def divisiblePolynomialSubspace (D : BivariateRatPolynomial) :
    Submodule ℚ BivariateRatPolynomial where
  carrier := {F | D ∣ F}
  zero_mem' := dvd_zero D
  add_mem' hF hG := dvd_add hF hG
  smul_mem' a F hF := dvd_smul_of_dvd a hF

/-- The gcd of a finite family, using the GCD monoid obtained from the
unique-factorization theorem for multivariate polynomials. -/
noncomputable def finitePolynomialFamilyGCD
    {ι : Type*} [Fintype ι]
    (f : ι → BivariateRatPolynomial) : BivariateRatPolynomial :=
  Finset.univ.gcd f

theorem finitePolynomialFamilyGCD_dvd
    {ι : Type*} [Fintype ι]
    (f : ι → BivariateRatPolynomial) (i : ι) :
    finitePolynomialFamilyGCD f ∣ f i := by
  exact Finset.gcd_dvd (Finset.mem_univ i)

/-- A common divisor of a finite family divides its chosen gcd. -/
theorem dvd_finitePolynomialFamilyGCD
    {ι : Type*} [Fintype ι]
    (f : ι → BivariateRatPolynomial) (E : BivariateRatPolynomial)
    (hE : ∀ i, E ∣ f i) :
    E ∣ finitePolynomialFamilyGCD f := by
  apply Finset.dvd_gcd
  intro i _
  exact hE i

/-- The finite-family gcd is nonzero as soon as one family member is
nonzero. -/
theorem finitePolynomialFamilyGCD_ne_zero
    {ι : Type*} [Fintype ι]
    (f : ι → BivariateRatPolynomial)
    (hne : ∃ i, f i ≠ 0) :
    finitePolynomialFamilyGCD f ≠ 0 := by
  rw [finitePolynomialFamilyGCD, Finset.gcd_ne_zero_iff]
  simpa using hne

/-- The finite-family gcd has the fixed-divisor universal property on the
rational span of the family. -/
theorem finitePolynomialFamilyGCD_isFixedDivisor_span
    {ι : Type*} [Fintype ι]
    (f : ι → BivariateRatPolynomial)
    (hne : ∃ i, f i ≠ 0) :
    IsFixedDivisor (Submodule.span ℚ (Set.range f))
      (finitePolynomialFamilyGCD f) := by
  let D := finitePolynomialFamilyGCD f
  refine ⟨finitePolynomialFamilyGCD_ne_zero f hne, ?_, ?_⟩
  · intro F hF
    have hspan :
        Submodule.span ℚ (Set.range f) ≤ divisiblePolynomialSubspace D := by
      rw [Submodule.span_le]
      rintro G ⟨i, rfl⟩
      exact finitePolynomialFamilyGCD_dvd f i
    exact hspan hF
  · intro E hE
    apply dvd_finitePolynomialFamilyGCD f E
    intro i
    exact hE (f i) (Submodule.subset_span ⟨i, rfl⟩)

/-- Every nonzero finite-dimensional rational polynomial subspace has a
fixed divisor satisfying the universal property.  The construction is the
gcd of an arbitrary finite basis; uniqueness up to associates below makes
the result basis-independent. -/
theorem exists_isFixedDivisor_of_finiteDimensional
    (V : Submodule ℚ BivariateRatPolynomial)
    [FiniteDimensional ℚ V] (hV : V ≠ ⊥) :
    ∃ D : BivariateRatPolynomial, IsFixedDivisor V D := by
  let b := Module.finBasis ℚ V
  let f : Fin (Module.finrank ℚ V) → BivariateRatPolynomial :=
    fun i => (b i).1
  haveI : Nontrivial V := Submodule.nontrivial_iff_ne_bot.mpr hV
  have hdim : 0 < Module.finrank ℚ V := Module.finrank_pos
  have hne : ∃ i, f i ≠ 0 := by
    let i : Fin (Module.finrank ℚ V) := ⟨0, hdim⟩
    refine ⟨i, ?_⟩
    intro hi
    apply b.ne_zero i
    apply Subtype.ext
    exact hi
  have hspan : Submodule.span ℚ (Set.range f) = V := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro F ⟨i, rfl⟩
      exact (b i).property
    · intro F hFV
      let F' : V := ⟨F, hFV⟩
      have hmem :
          (∑ i, (b.repr F' i) • (b i).1) ∈
            Submodule.span ℚ (Set.range f) := by
        apply Submodule.sum_mem
        intro i _
        apply Submodule.smul_mem
        exact Submodule.subset_span ⟨i, rfl⟩
      have heq : (∑ i, (b.repr F' i) • (b i).1) = F := by
        have heq' := congrArg Subtype.val (b.sum_repr F')
        simpa only [Submodule.coe_sum, Submodule.coe_smul] using heq'
      rwa [heq] at hmem
  let D := finitePolynomialFamilyGCD f
  have hfix := finitePolynomialFamilyGCD_isFixedDivisor_span f hne
  refine ⟨D, hfix.ne_zero, ?_, ?_⟩
  · intro F hFV
    apply hfix.divides_all F
    rw [hspan]
    exact hFV
  · intro E hE
    apply hfix.greatest E
    intro F hF
    apply hE F
    rw [← hspan]
    exact hF

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

/-- The canonical bounded polynomial space has a fixed divisor whenever it
is nonzero.  Finite dimensionality comes from its realization as the range
of a linear map whose domain is a subspace of the finite coefficient space. -/
theorem exists_isFixedDivisor_boundedOsculationPolynomialSpace
    {r q : ℕ} (A : Matrix (Fin q) (OsculationMonomial r) ℤ) (B : ℕ)
    (hne : boundedOsculationPolynomialSpace A B ≠ ⊥) :
    ∃ D : BivariateRatPolynomial,
      IsFixedDivisor (boundedOsculationPolynomialSpace A B) D := by
  let φ := (osculationCoeffToRatPolynomial r).domRestrict
    (boundedOsculationSpace A B)
  have hrange : LinearMap.range φ =
      boundedOsculationPolynomialSpace A B := by
    simp [φ, boundedOsculationPolynomialSpace]
  haveI : FiniteDimensional ℚ (LinearMap.range φ) :=
    LinearMap.finiteDimensional_range φ
  have hrange_ne : LinearMap.range φ ≠ ⊥ := by
    rw [hrange]
    exact hne
  obtain ⟨D, hD⟩ :=
    exists_isFixedDivisor_of_finiteDimensional (LinearMap.range φ) hrange_ne
  exact ⟨D, (isFixedDivisor_congr_space hrange).mp hD⟩

/-- Under the exact entry envelope and column-count hypotheses of the
bounded-kernel theorem, the canonical bounded polynomial space admits a
basis-independent fixed divisor without a separate nonzero assumption. -/
theorem exists_isFixedDivisor_boundedOsculationPolynomialSpace_of_entry_bound
    {m r k : ℕ}
    (A : Matrix (Fin (2 * m)) (OsculationMonomial r) ℤ)
    (hentry : ∀ i u,
      (A i u).natAbs ≤ 3 * r * 2 ^ k * k ^ (r - 1))
    (hm : 0 < m)
    (hcolumns : 4 * m + 1 ≤ osculationMonomialCount r)
    (hr : 0 < r) (hk : 0 < k) :
    ∃ D : BivariateRatPolynomial,
      IsFixedDivisor
        (boundedOsculationPolynomialSpace A
          (12 * osculationMonomialCount r * r *
            2 ^ k * k ^ (r - 1))) D := by
  apply exists_isFixedDivisor_boundedOsculationPolynomialSpace
  exact boundedOsculationPolynomialSpace_ne_bot_of_entry_bound
    A hentry hm hcolumns hr hk

/-- A presentation of division of an entire polynomial space by its fixed
divisor.  The quotient is recorded pointwise; no false jet inheritance is
included. -/
structure FixedDivisorPresentation
    (V : Submodule ℚ BivariateRatPolynomial) where
  D : BivariateRatPolynomial
  fixed : IsFixedDivisor V D
  quotient : V → BivariateRatPolynomial
  factor : ∀ F : V, F.1 = D * quotient F

/-- A fixed divisor supplies a pointwise quotient presentation by choice.
No derivative or jet data is transferred to these quotients. -/
noncomputable def IsFixedDivisor.toPresentation
    {V : Submodule ℚ BivariateRatPolynomial}
    {D : BivariateRatPolynomial} (h : IsFixedDivisor V D) :
    FixedDivisorPresentation V where
  D := D
  fixed := h
  quotient F := Classical.choose (h.divides_all F.1 F.2)
  factor F := Classical.choose_spec (h.divides_all F.1 F.2)

theorem FixedDivisorPresentation.quotient_zero
    {V : Submodule ℚ BivariateRatPolynomial}
    (h : FixedDivisorPresentation V) :
    h.quotient 0 = 0 := by
  apply mul_left_cancel₀ h.fixed.ne_zero
  calc
    h.D * h.quotient 0 = (0 : V).1 := (h.factor 0).symm
    _ = h.D * 0 := by simp

theorem FixedDivisorPresentation.quotient_add
    {V : Submodule ℚ BivariateRatPolynomial}
    (h : FixedDivisorPresentation V) (F G : V) :
    h.quotient (F + G) = h.quotient F + h.quotient G := by
  apply mul_left_cancel₀ h.fixed.ne_zero
  calc
    h.D * h.quotient (F + G) = (F + G).1 := (h.factor (F + G)).symm
    _ = F.1 + G.1 := rfl
    _ = h.D * h.quotient F + h.D * h.quotient G := by
      rw [← h.factor F, ← h.factor G]
    _ = h.D * (h.quotient F + h.quotient G) := by ring

theorem FixedDivisorPresentation.quotient_smul
    {V : Submodule ℚ BivariateRatPolynomial}
    (h : FixedDivisorPresentation V) (a : ℚ) (F : V) :
    h.quotient (a • F) = a • h.quotient F := by
  apply mul_left_cancel₀ h.fixed.ne_zero
  calc
    h.D * h.quotient (a • F) = (a • F).1 := (h.factor (a • F)).symm
    _ = a • F.1 := rfl
    _ = a • (h.D * h.quotient F) := by rw [← h.factor F]
    _ = h.D * (a • h.quotient F) := by
      simp [Algebra.smul_def]
      ring

/-- Division by the nonzero fixed divisor is a linear operation on the
presented space. -/
noncomputable def FixedDivisorPresentation.residualLinearMap
    {V : Submodule ℚ BivariateRatPolynomial}
    (h : FixedDivisorPresentation V) :
    V →ₗ[ℚ] BivariateRatPolynomial where
  toFun := h.quotient
  map_add' := h.quotient_add
  map_smul' := h.quotient_smul

/-- Nonzero finite-dimensional spaces possess a full fixed-divisor
presentation. -/
theorem exists_fixedDivisorPresentation_of_finiteDimensional
    (V : Submodule ℚ BivariateRatPolynomial)
    [FiniteDimensional ℚ V] (hV : V ≠ ⊥) :
    Nonempty (FixedDivisorPresentation V) := by
  obtain ⟨D, hD⟩ := exists_isFixedDivisor_of_finiteDimensional V hV
  exact ⟨hD.toPresentation⟩

/-- Exact bounded-osculation hypotheses also supply a full quotient
presentation, with no additional nontriviality assumption. -/
theorem exists_fixedDivisorPresentation_boundedOsculation_of_entry_bound
    {m r k : ℕ}
    (A : Matrix (Fin (2 * m)) (OsculationMonomial r) ℤ)
    (hentry : ∀ i u,
      (A i u).natAbs ≤ 3 * r * 2 ^ k * k ^ (r - 1))
    (hm : 0 < m)
    (hcolumns : 4 * m + 1 ≤ osculationMonomialCount r)
    (hr : 0 < r) (hk : 0 < k) :
    Nonempty (FixedDivisorPresentation
      (boundedOsculationPolynomialSpace A
        (12 * osculationMonomialCount r * r *
          2 ^ k * k ^ (r - 1)))) := by
  obtain ⟨D, hD⟩ :=
    exists_isFixedDivisor_boundedOsculationPolynomialSpace_of_entry_bound
      A hentry hm hcolumns hr hk
  exact ⟨hD.toPresentation⟩

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

/-- Quotients of a finite basis form an exact finite residual certificate:
their gcd is a unit.  This does not imply that any pair in that basis is
coprime. -/
theorem FixedDivisorPresentation.isUnit_gcd_basis_quotients
    {V : Submodule ℚ BivariateRatPolynomial}
    [FiniteDimensional ℚ V]
    (h : FixedDivisorPresentation V) :
    IsUnit (finitePolynomialFamilyGCD
      (fun i : Fin (Module.finrank ℚ V) =>
        h.quotient (Module.finBasis ℚ V i))) := by
  let b := Module.finBasis ℚ V
  let g := finitePolynomialFamilyGCD
    (fun i : Fin (Module.finrank ℚ V) => h.quotient (b i))
  apply h.residual_has_no_common_nonunit g
  intro F
  have hsum :
      g ∣ ∑ i, (b.repr F i) • h.quotient (b i) := by
    apply Finset.dvd_sum
    intro i _
    exact dvd_smul_of_dvd (b.repr F i)
      (finitePolynomialFamilyGCD_dvd
        (fun j : Fin (Module.finrank ℚ V) => h.quotient (b j)) i)
  have heq :
      (∑ i, (b.repr F i) • h.quotient (b i)) = h.quotient F := by
    calc
      (∑ i, (b.repr F i) • h.quotient (b i)) =
          h.residualLinearMap (∑ i, (b.repr F i) • b i) := by
        rw [map_sum]
        simp only [map_smul]
        rfl
      _ = h.residualLinearMap F :=
        congrArg h.residualLinearMap (b.sum_repr F)
      _ = h.quotient F := rfl
  rwa [heq] at hsum

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
#print axioms finitePolynomialFamilyGCD_isFixedDivisor_span
#print axioms exists_isFixedDivisor_of_finiteDimensional
#print axioms exists_isFixedDivisor_boundedOsculationPolynomialSpace
#print axioms osculationCoeffToRatPolynomial_injective
#print axioms boundedOsculationPolynomialSpace_ne_bot_of_entry_bound
#print axioms exists_isFixedDivisor_boundedOsculationPolynomialSpace_of_entry_bound
#print axioms exists_fixedDivisorPresentation_of_finiteDimensional
#print axioms exists_fixedDivisorPresentation_boundedOsculation_of_entry_bound
#print axioms FixedDivisorPresentation.residual_has_no_common_nonunit
#print axioms FixedDivisorPresentation.isUnit_gcd_basis_quotients
#print axioms FixedDivisorPresentation.two_specialization_split

end Erdos686Variant
end Erdos686
