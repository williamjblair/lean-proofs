/- leanprover/lean4:v4.29.1 mathlib v4.29.1 -/
import ErdosProblems.Erdos686.Core.RowDiagonalSixCycle

/-!
# Erdős 686: cyclic secant invariant at arbitrary component length

For a cyclic permutation `σ`, write the row and signed-diagonal terms as

`x i = a i * b i * r i`,
`y i = b i * a (σ i) * q i`.

Every adjacent secant factors by `b i * b (σ i)`.  Multiplying around the
cycle therefore exposes the square of the complete alternating `b`-mass.
If the cyclic product vanishes, one local five-owner defect vanishes and the
same coprimality kernel as in the six-cycle forces owner-square crowding into
two neighbouring diagonal cofactors.
-/

namespace Erdos686
namespace Erdos686Variant

open scoped BigOperators

/-- The cyclic product of adjacent row/diagonal secants. -/
def cyclicSecantProduct
    {ι : Type*} [Fintype ι] (σ : Equiv.Perm ι)
    (x y : ι → ℤ) : ℤ :=
  ∏ i, (x i * y (σ i) - x (σ i) * y i)

/-- The local square-weighted cofactor defect at one cyclic index. -/
def cyclicLocalQuotient
    {ι : Type*} (σ : Equiv.Perm ι)
    (a r q : ι → ℤ) (i : ι) : ℤ :=
  a i * a (σ (σ i)) * r i * q (σ i) -
    a (σ i) ^ 2 * r (σ i) * q i

/-- One adjacent cyclic secant has the same exact five-owner factorization
at every component length. -/
theorem cyclic_adjacent_secant_factorization
    {ι : Type*} (σ : Equiv.Perm ι)
    (a b r q x y : ι → ℤ)
    (hx : ∀ i, x i = a i * b i * r i)
    (hy : ∀ i, y i = b i * a (σ i) * q i)
    (i : ι) :
    x i * y (σ i) - x (σ i) * y i =
      b i * b (σ i) * cyclicLocalQuotient σ a r q i := by
  simpa [cyclicLocalQuotient] using
    (sixCycle_adjacent_secant_factorization
      (hx i) (hx (σ i)) (hy i) (hy (σ i)))

/-- Exact arbitrary-length factorization.  Reindexing by the cyclic
permutation makes the product of the two adjacent `b`-factors the square of
the complete alternating mass. -/
theorem cyclicSecantProduct_factorization
    {ι : Type*} [Fintype ι] (σ : Equiv.Perm ι)
    (a b r q x y : ι → ℤ)
    (hx : ∀ i, x i = a i * b i * r i)
    (hy : ∀ i, y i = b i * a (σ i) * q i) :
    cyclicSecantProduct σ x y =
      (∏ i, b i) ^ 2 * ∏ i, cyclicLocalQuotient σ a r q i := by
  unfold cyclicSecantProduct
  simp_rw [cyclic_adjacent_secant_factorization σ a b r q x y hx hy]
  simp_rw [Finset.prod_mul_distrib]
  rw [Equiv.prod_comp σ b]
  ring

/-- Nonzero branch at arbitrary component length. -/
theorem cyclic_alternatingMass_sq_le_secantProduct_natAbs
    {ι : Type*} [Fintype ι] (σ : Equiv.Perm ι)
    (a b r q : ι → ℕ) (x y : ι → ℤ)
    (hx : ∀ i, x i = (a i : ℤ) * b i * r i)
    (hy : ∀ i, y i = (b i : ℤ) * a (σ i) * q i)
    (hnonzero : cyclicSecantProduct σ x y ≠ 0) :
    (∏ i, b i) ^ 2 ≤ (cyclicSecantProduct σ x y).natAbs := by
  apply Nat.le_of_dvd (Int.natAbs_pos.mpr hnonzero)
  have hfactor := cyclicSecantProduct_factorization σ
    (fun i => (a i : ℤ)) (fun i => (b i : ℤ))
    (fun i => (r i : ℤ)) (fun i => (q i : ℤ)) x y hx hy
  have hdvdZ : (((∏ i, b i) ^ 2 : ℕ) : ℤ) ∣
      cyclicSecantProduct σ x y := by
    rw [hfactor]
    refine ⟨∏ i, cyclicLocalQuotient σ
      (fun i => (a i : ℤ)) (fun i => (r i : ℤ))
        (fun i => (q i : ℤ)) i, ?_⟩
    push_cast
    ring
  convert Int.natAbs_dvd_natAbs.mpr hdvdZ using 1

/-- Arbitrary-length secant-or-crowding dichotomy.  The zero branch names
the precise cyclic position at which the local owner-square crowding occurs. -/
theorem cyclic_secant_or_ownerSquare_crowding
    {ι : Type*} [Fintype ι] (σ : Equiv.Perm ι)
    (a b r q : ι → ℕ) (x y : ι → ℤ)
    (hb : ∀ i, 0 < b i)
    (hmid : ∀ i, (a (σ i) ^ 2).Coprime
      (a i * a (σ (σ i)) * r i))
    (hneighbours : ∀ i, (a i * a (σ (σ i))).Coprime
      (a (σ i) ^ 2 * r (σ i)))
    (hx : ∀ i, x i = (a i : ℤ) * b i * r i)
    (hy : ∀ i, y i = (b i : ℤ) * a (σ i) * q i) :
    (∏ i, b i) ^ 2 ≤ (cyclicSecantProduct σ x y).natAbs ∨
      ∃ i, (a i * a (σ (σ i))) * a (σ i) ^ 2 ∣
        q i * q (σ i) := by
  by_cases hsec : cyclicSecantProduct σ x y = 0
  · right
    unfold cyclicSecantProduct at hsec
    obtain ⟨i, _hi, hisec⟩ := Finset.prod_eq_zero_iff.mp hsec
    refine ⟨i, ?_⟩
    have hfactor := cyclic_adjacent_secant_factorization σ
      (fun i => (a i : ℤ)) (fun i => (b i : ℤ))
      (fun i => (r i : ℤ)) (fun i => (q i : ℤ)) x y hx hy i
    rw [hisec] at hfactor
    have hlocal : cyclicLocalQuotient σ
        (fun i => (a i : ℤ)) (fun i => (r i : ℤ))
          (fun i => (q i : ℤ)) i = 0 := by
      apply (mul_eq_zero.mp hfactor.symm).resolve_left
      exact mul_ne_zero
        (Int.ofNat_ne_zero.mpr (Nat.ne_of_gt (hb i)))
        (Int.ofNat_ne_zero.mpr (Nat.ne_of_gt (hb (σ i))))
    unfold cyclicLocalQuotient at hlocal
    change (a i : ℤ) * a (σ (σ i)) * r i * q (σ i) -
      (a (σ i) : ℤ) ^ 2 * r (σ i) * q i = 0 at hlocal
    have hzero : a i * a (σ (σ i)) * r i * q (σ i) =
        a (σ i) ^ 2 * r (σ i) * q i := by
      exact_mod_cast (sub_eq_zero.mp hlocal)
    exact sixCycle_zero_localQuotient_forces_crowding
      (hmid i) (hneighbours i) hzero
  · left
    exact cyclic_alternatingMass_sq_le_secantProduct_natAbs
      σ a b r q x y hx hy hsec

#print axioms cyclic_adjacent_secant_factorization
#print axioms cyclicSecantProduct_factorization
#print axioms cyclic_alternatingMass_sq_le_secantProduct_natAbs
#print axioms cyclic_secant_or_ownerSquare_crowding

end Erdos686Variant
end Erdos686
