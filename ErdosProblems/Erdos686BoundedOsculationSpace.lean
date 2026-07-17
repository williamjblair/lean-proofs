/- leanprover/lean4:v4.29.1 mathlib v4.29.1 -/
import ErdosProblems.Erdos686LowDegreeOsculation
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Erdős 686: canonical bounded osculation spaces

This file separates three objects which must not be conflated:

* `integralOsculationLattice A`, the full integral kernel of the constraint
  matrix;
* `boundedOsculationSpace A B`, the rational span of *all* lattice vectors
  whose coefficient sup norm is at most `B`;
* `rationalOsculationKernel A`, the full rational kernel.

The middle object is canonical by definition, but need not equal the last
one without a separate spanning theorem.
-/

namespace Erdos686
namespace Erdos686Variant

open scoped BigOperators

/-- The full integral osculation lattice. -/
def integralOsculationLattice
    {q N : Type*} [Fintype N]
    (A : Matrix q N ℤ) : Submodule ℤ (N → ℤ) :=
  LinearMap.ker A.mulVecLin

/-- Coordinatewise extension of an integral coefficient vector to `ℚ`. -/
def integralCoeffCast {N : Type*} (z : N → ℤ) : N → ℚ :=
  fun i => (z i : ℚ)

/-- The bounded part of the integral lattice, before taking a rational span. -/
def boundedIntegralOscillationSet
    {q N : Type*} [Fintype N]
    (A : Matrix q N ℤ) (B : ℕ) : Set (N → ℚ) :=
  {v | ∃ z : N → ℤ,
    z ∈ integralOsculationLattice A ∧
    (∀ i, (z i).natAbs ≤ B) ∧
    v = integralCoeffCast z}

/-- The canonical rational bounded vanishing space.  It is the span of all
bounded integral lattice points, rather than the span of an arbitrarily
selected bounded family. -/
def boundedOsculationSpace
    {q N : Type*} [Fintype N]
    (A : Matrix q N ℤ) (B : ℕ) : Submodule ℚ (N → ℚ) :=
  Submodule.span ℚ (boundedIntegralOscillationSet A B)

/-- The full rational jet kernel associated to an integral matrix. -/
def rationalOsculationKernel
    {q N : Type*} [Fintype N]
    (A : Matrix q N ℤ) : Submodule ℚ (N → ℚ) :=
  LinearMap.ker (A.map (algebraMap ℤ ℚ)).mulVecLin

theorem mem_integralOsculationLattice_iff
    {q N : Type*} [Fintype N]
  (A : Matrix q N ℤ) (z : N → ℤ) :
    z ∈ integralOsculationLattice A ↔ A.mulVec z = 0 := by
  simp [integralOsculationLattice]

theorem boundedIntegralOscillationSet_mono
    {q N : Type*} [Fintype N]
    (A : Matrix q N ℤ) {B C : ℕ} (hBC : B ≤ C) :
    boundedIntegralOscillationSet A B ⊆
      boundedIntegralOscillationSet A C := by
  rintro v ⟨z, hz, hB, rfl⟩
  exact ⟨z, hz, fun i => (hB i).trans hBC, rfl⟩

theorem boundedOsculationSpace_mono
    {q N : Type*} [Fintype N]
    (A : Matrix q N ℤ) {B C : ℕ} (hBC : B ≤ C) :
    boundedOsculationSpace A B ≤ boundedOsculationSpace A C := by
  exact Submodule.span_mono (boundedIntegralOscillationSet_mono A hBC)

/-- Every cast integral lattice point lies in the full rational jet kernel. -/
theorem integralCoeffCast_mem_rationalOsculationKernel
    {q N : Type*} [Fintype q] [Fintype N]
    (A : Matrix q N ℤ) (z : N → ℤ)
    (hz : z ∈ integralOsculationLattice A) :
    integralCoeffCast z ∈ rationalOsculationKernel A := by
  rw [mem_integralOsculationLattice_iff] at hz
  rw [rationalOsculationKernel, LinearMap.mem_ker,
    Matrix.mulVecLin_apply]
  funext i
  have hi := congrFun hz i
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at hi ⊢
  simpa [Matrix.map_apply, integralCoeffCast] using
    congrArg (fun t : ℤ => (t : ℚ)) hi

/-- `V_B` is contained in the full rational jet kernel.  No reverse
inclusion is asserted. -/
theorem boundedOsculationSpace_le_rationalOsculationKernel
    {q N : Type*} [Fintype q] [Fintype N]
    (A : Matrix q N ℤ) (B : ℕ) :
    boundedOsculationSpace A B ≤ rationalOsculationKernel A := by
  rw [boundedOsculationSpace, Submodule.span_le]
  rintro v ⟨z, hz, -, rfl⟩
  exact integralCoeffCast_mem_rationalOsculationKernel A z hz

/-- A linear specialization which vanishes on every bounded lattice point
vanishes on the canonical bounded span.  This is the basis-free form of the
cancellation step. -/
theorem linear_specialization_vanishes_on_boundedOsculationSpace
    {q N : Type*} [Fintype N]
    (A : Matrix q N ℤ) (B : ℕ)
    (ev : (N → ℚ) →ₗ[ℚ] ℚ)
    (hev : ∀ z : N → ℤ,
      z ∈ integralOsculationLattice A →
      (∀ i, (z i).natAbs ≤ B) →
      ev (integralCoeffCast z) = 0) :
    boundedOsculationSpace A B ≤ LinearMap.ker ev := by
  rw [boundedOsculationSpace, Submodule.span_le]
  rintro v ⟨z, hz, hB, rfl⟩
  exact LinearMap.mem_ker.mpr (hev z hz hB)

/-- The full rational jet kernel of a `2m × N` matrix has dimension at
least `N-2m`. -/
theorem rationalOsculationKernel_finrank_lower
    {N : Type*} [Fintype N] {m : ℕ}
    (A : Matrix (Fin (2 * m)) N ℤ) :
    Fintype.card N - 2 * m ≤
      Module.finrank ℚ (rationalOsculationKernel A) := by
  let f : (N → ℚ) →ₗ[ℚ] (Fin (2 * m) → ℚ) :=
    (A.map (algebraMap ℤ ℚ)).mulVecLin
  have hrange : Module.finrank ℚ (LinearMap.range f) ≤ 2 * m := by
    calc
      Module.finrank ℚ (LinearMap.range f) ≤
          Module.finrank ℚ (Fin (2 * m) → ℚ) :=
        Submodule.finrank_le _
      _ = 2 * m := by simp
  have hranknull := LinearMap.finrank_range_add_finrank_ker f
  have hdomain : Module.finrank ℚ (N → ℚ) = Fintype.card N := by
    simp
  change Fintype.card N - 2 * m ≤
    Module.finrank ℚ (LinearMap.ker f)
  omega

/-- Osculation-basis form of the same lower bound. -/
theorem rationalOsculationKernel_finrank_lower_basis
    {r m : ℕ}
    (A : Matrix (Fin (2 * m)) (OsculationMonomial r) ℤ) :
    osculationMonomialCount r - 2 * m ≤
      Module.finrank ℚ (rationalOsculationKernel A) := by
  have h := rationalOsculationKernel_finrank_lower
    A
  rw [osculationMonomialBasis_card] at h
  exact h

/-!
The next lemma isolates the exact arithmetic used in a full-space fixed
divisor degree argument.  The hypothesis `hdimUpper` is precisely the
quotient-space dimension estimate which must be proved from divisibility;
it is not available for `V_B` merely from bounded kernel extraction.
-/

/-- Exact binomial-dimension calculation behind the full-space fixed-divisor
degree inequality. -/
theorem fixedDivisor_degree_inequality_of_dimension_bounds
    {r e m d : ℕ}
    (he : e ≤ r)
    (hlower : osculationMonomialCount r - 2 * m ≤ d)
    (hupper : d ≤ osculationMonomialCount (r - e)) :
    e * (2 * r - e + 3) ≤ 4 * m := by
  have hlowerNat : osculationMonomialCount r ≤ d + 2 * m :=
    Nat.sub_le_iff_le_add.mp hlower
  have hlowerQ :
      (osculationMonomialCount r : ℚ) ≤ d + 2 * m := by
    exact_mod_cast hlowerNat
  have hupperQ :
      (d : ℚ) ≤ osculationMonomialCount (r - e) := by
    exact_mod_cast hupper
  have hcount (t : ℕ) :
      (osculationMonomialCount t : ℚ) =
        ((t : ℚ) + 2) * ((t : ℚ) + 1) / 2 := by
    unfold osculationMonomialCount
    rw [Nat.cast_choose_two]
    push_cast [show 1 ≤ t + 2 by omega]
    ring
  rw [hcount r] at hlowerQ
  rw [hcount (r - e)] at hupperQ
  have hsubQ : ((r - e : ℕ) : ℚ) = (r : ℚ) - e := by
    rw [Nat.cast_sub he]
  rw [hsubQ] at hupperQ
  have htargetQ :
      (e : ℚ) * (2 * r - e + 3) ≤ 4 * m := by
    nlinarith
  have htwor : e ≤ 2 * r := he.trans (by omega)
  exact_mod_cast htargetQ

#print axioms boundedOsculationSpace_le_rationalOsculationKernel
#print axioms linear_specialization_vanishes_on_boundedOsculationSpace
#print axioms rationalOsculationKernel_finrank_lower_basis
#print axioms fixedDivisor_degree_inequality_of_dimension_bounds

end Erdos686Variant
end Erdos686
