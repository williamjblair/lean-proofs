/- leanprover/lean4:v4.29.1 mathlib v4.29.1 -/
import ErdosProblems.Erdos686.Core.BarycentricMomentLadder
import ErdosProblems.Erdos686.Core.OsculationFixedDivisor

/-!
# Erdős 686: matching / bounded-osculation bridge

This module instantiates the abstract bounded fixed-divisor package with the
actual normalized `2m × N_r` osculation matrix.  Independently, it packages
the moment-ladder conclusion for the actual barycentric polynomials `U`, `V`,
and `matchingPhi`: in the zero-leading-coefficient branch the matching
polynomial is not identically zero, and any quotient after removal of the
canonical `W²` factor is nonzero with its exact degree.

The second statement assumes the displayed `W²` factorization.  It does not
assert that a matching resultant is nonzero, nor does it divide by `V(-n)`.
-/

namespace Erdos686
namespace Erdos686Variant

open scoped BigOperators
open Polynomial

/-- The actual normalized osculation constraint matrix satisfies the exact
entry envelope used by the bounded kernel and fixed-divisor construction. -/
theorem osculationConstraintMatrix_entry_bound
    {m r k : ℕ} (j rho b A : Fin m → ℤ)
    (hr : 0 < r) (hk : 0 < k)
    (hj : ∀ e, (j e).natAbs ≤ k)
    (hrho : ∀ e, (rho e).natAbs ≤ k)
    (hb : ∀ e, (b e).natAbs ≤ 2 ^ (k - 1))
    (hA : ∀ e, (A e).natAbs ≤ 5 * 2 ^ (k - 1)) :
    ∀ row u,
      (osculationConstraintMatrix r m j rho b A row u).natAbs ≤
        3 * r * 2 ^ k * k ^ (r - 1) := by
  intro row u
  rw [osculationConstraintMatrix]
  split_ifs with hrow
  · exact osculationValueEntry_natAbs_le hr hk u
      (j ⟨row.val, hrow⟩) (rho ⟨row.val, hrow⟩)
      (hj ⟨row.val, hrow⟩) (hrho ⟨row.val, hrow⟩)
  · let e : Fin m := ⟨row.val - m, by omega⟩
    exact osculationDirectionEntry_natAbs_le hr hk u
      (b e) (A e) (j e) (rho e)
      (hj e) (hrho e) (hb e) (hA e)

/-- The exact normalized support data instantiate the canonical bounded
fixed-divisor presentation for the actual osculation matrix. -/
theorem exists_fixedDivisorPresentation_normalizedOsculation
    {m r k : ℕ} (j rho b A : Fin m → ℤ)
    (hm : 0 < m)
    (hcolumns : 4 * m + 1 ≤ osculationMonomialCount r)
    (hr : 0 < r) (hk : 0 < k)
    (hj : ∀ e, (j e).natAbs ≤ k)
    (hrho : ∀ e, (rho e).natAbs ≤ k)
    (hb : ∀ e, (b e).natAbs ≤ 2 ^ (k - 1))
    (hA : ∀ e, (A e).natAbs ≤ 5 * 2 ^ (k - 1)) :
    Nonempty (FixedDivisorPresentation
      (boundedOsculationPolynomialSpace
        (osculationConstraintMatrix r m j rho b A)
        (12 * osculationMonomialCount r * r *
          2 ^ k * k ^ (r - 1)))) := by
  apply exists_fixedDivisorPresentation_boundedOsculation_of_entry_bound
  · exact osculationConstraintMatrix_entry_bound
      j rho b A hr hk hj hrho hb hA
  · exact hm
  · exact hcolumns
  · exact hr
  · exact hk

/-- The two natural-number presentations of the exact quotient degree agree.
This is kept separate so downstream statements can use the audited
`m(k-2)-qk` form directly. -/
theorem matching_quotient_degree_arithmetic
    {m q k : ℕ} :
    k * (m - q) - 2 * m = m * (k - 2) - q * k := by
  rw [Nat.mul_sub_left_distrib]
  rw [Nat.mul_sub_left_distrib]
  simp only [Nat.sub_sub, Nat.mul_comm]
  rw [add_comm]

/-- Distinct double interpolation nodes combine into the canonical `W²`
factor.  This is the exact square-Hermite algebra needed downstream: both
the value and the ordinary derivative of the polynomial must vanish at every
node. -/
theorem W_sq_dvd_of_value_derivative_vanish
    {m : ℕ} {j : Fin m → ℤ} {Phi : Polynomial ℤ}
    (hj : Function.Injective j)
    (hPhi : Phi ≠ 0)
    (hvalue : ∀ e, Phi.eval (j e) = 0)
    (hderivative : ∀ e, Phi.derivative.eval (j e) = 0) :
    (W Finset.univ j) ^ 2 ∣ Phi := by
  classical
  have hlocal : ∀ e : Fin m, (factor j e) ^ 2 ∣ Phi := by
    intro e
    have hmult : 1 < Phi.rootMultiplicity (j e) :=
      (one_lt_rootMultiplicity_iff_isRoot hPhi).mpr
        ⟨hvalue e, hderivative e⟩
    exact (le_rootMultiplicity_iff hPhi).mp hmult
  let f : ℤ →+* ℚ := algebraMap ℤ ℚ
  have hjQ : Function.Injective (fun e : Fin m => (j e : ℚ)) := by
    intro e l hel
    apply hj
    exact Int.cast_injective hel
  have hpair :
      ((Finset.univ : Finset (Fin m)) : Set (Fin m)).Pairwise
        (Function.onFun IsCoprime
          (fun e => ((factor j e) ^ 2).map f)) := by
    intro e _ f _ hef
    simpa only [factor, Polynomial.map_pow, Polynomial.map_sub,
      Polynomial.map_X, Polynomial.map_C, RingHom.id_apply] using
      (pairwise_coprime_X_sub_C hjQ hef).pow
  have hprodQ :
      (∏ e ∈ (Finset.univ : Finset (Fin m)),
        ((factor j e) ^ 2).map f) ∣ Phi.map f :=
    Finset.prod_dvd_of_coprime hpair
      (fun e _ => Polynomial.map_dvd f (hlocal e))
  have hmapDvd : ((W Finset.univ j) ^ 2).map f ∣ Phi.map f := by
    simpa only [W, Polynomial.map_pow, Polynomial.map_prod,
      Finset.prod_pow] using hprodQ
  exact (Polynomial.map_dvd_map f Int.cast_injective
    ((W_monic Finset.univ j).pow 2)).mp hmapDvd

/-- Exact finite-support zero-branch theorem for the actual barycentric
matching construction.  Distinct nodes, nonzero weights, zero total weight,
and `k ≥ 3` rule out `Phi ≡ 0`.  If `Phi = W² Q`, then `Q` is also
nonzero and has the exact audited degree `m(k-2)-qk`. -/
theorem fin_matchingPhi_zero_branch_nonzero_and_quotient_exact_degree
    {m k : ℕ} {j rho w : Fin m → ℤ}
    (hj : Function.Injective j)
    (hw : w ≠ 0)
    (hmu0 : mu Finset.univ j w 0 = 0)
    (hk : 3 ≤ k)
    (Q : Polynomial ℤ)
    (hfactor :
      matchingPhi k (U Finset.univ j rho w 0) (V Finset.univ j w) =
        (W Finset.univ j) ^ 2 * Q) :
    ∃ q, 1 ≤ q ∧ q ≤ m ∧
      (∀ p < q, mu Finset.univ j w p = 0) ∧
      (∀ p < q - 1, nu Finset.univ j rho w p = 0) ∧
      momentDelta k (mu Finset.univ j w q)
        (nu Finset.univ j rho w (q - 1)) ≠ 0 ∧
      matchingPhi k (U Finset.univ j rho w 0)
        (V Finset.univ j w) ≠ 0 ∧
      Q ≠ 0 ∧
      (matchingPhi k (U Finset.univ j rho w 0)
        (V Finset.univ j w)).natDegree = k * (m - q) ∧
      Q.natDegree = m * (k - 2) - q * k := by
  obtain ⟨q, hq, hqm, hmu, hnu, hdelta, hPhi, hPhiDeg⟩ :=
    fin_matchingPhi_exists_first_nonzero_block_and_exact_degree
      hj hw hmu0 hk
  have hm : 1 ≤ m := hq.trans hqm
  have hS : (Finset.univ : Finset (Fin m)).Nonempty := by
    exact ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  have hqcard : q ≤ (Finset.univ : Finset (Fin m)).card := by
    simpa using hqm
  have hQdeg : Q.natDegree = k * (m - q) - 2 * m := by
    have h := matchingPhi_quotient_natDegree_eq_first_nonzero_moment_block
      hS hq hqcard hmu hnu hdelta Q hfactor
    simpa using h
  have hQ : Q ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hfactor
    exact hPhi hfactor
  refine ⟨q, hq, hqm, hmu, hnu, hdelta, hPhi, hQ, hPhiDeg, ?_⟩
  rw [hQdeg, matching_quotient_degree_arithmetic]

/-- Fully factored zero-branch interface.  Explicit value and derivative
vanishing for the actual `matchingPhi(U,V)` construction produce `W² ∣ Phi`;
the moment ladder then proves that the quotient exists, is nonzero, and has
the exact finite-bound degree. -/
theorem fin_matchingPhi_zero_branch_exists_nonzero_quotient_exact_degree
    {m k : ℕ} {j rho w : Fin m → ℤ}
    (hj : Function.Injective j)
    (hw : w ≠ 0)
    (hmu0 : mu Finset.univ j w 0 = 0)
    (hk : 3 ≤ k)
    (hvalue : ∀ e,
      (matchingPhi k (U Finset.univ j rho w 0)
        (V Finset.univ j w)).eval (j e) = 0)
    (hderivative : ∀ e,
      (matchingPhi k (U Finset.univ j rho w 0)
        (V Finset.univ j w)).derivative.eval (j e) = 0) :
    ∃ Q : Polynomial ℤ, ∃ q, 1 ≤ q ∧ q ≤ m ∧
      (∀ p < q, mu Finset.univ j w p = 0) ∧
      (∀ p < q - 1, nu Finset.univ j rho w p = 0) ∧
      momentDelta k (mu Finset.univ j w q)
        (nu Finset.univ j rho w (q - 1)) ≠ 0 ∧
      matchingPhi k (U Finset.univ j rho w 0)
        (V Finset.univ j w) = (W Finset.univ j) ^ 2 * Q ∧
      matchingPhi k (U Finset.univ j rho w 0)
        (V Finset.univ j w) ≠ 0 ∧
      Q ≠ 0 ∧
      (matchingPhi k (U Finset.univ j rho w 0)
        (V Finset.univ j w)).natDegree = k * (m - q) ∧
      Q.natDegree = m * (k - 2) - q * k := by
  let Phi := matchingPhi k (U Finset.univ j rho w 0)
    (V Finset.univ j w)
  have hPhi : Phi ≠ 0 := by
    exact fin_matchingPhi_ne_zero_of_injective_nonzero_weights
      hj hw hmu0 hk
  have hWdvd : (W Finset.univ j) ^ 2 ∣ Phi := by
    apply W_sq_dvd_of_value_derivative_vanish hj hPhi
    · exact hvalue
    · exact hderivative
  obtain ⟨Q, hfactor⟩ := hWdvd
  have hfactor' :
      matchingPhi k (U Finset.univ j rho w 0) (V Finset.univ j w) =
        (W Finset.univ j) ^ 2 * Q := by
    exact hfactor
  obtain ⟨q, hq, hqm, hmu, hnu, hdelta,
      hPhi', hQ, hPhiDeg, hQDeg⟩ :=
    fin_matchingPhi_zero_branch_nonzero_and_quotient_exact_degree
      hj hw hmu0 hk Q hfactor'
  exact ⟨Q, q, hq, hqm, hmu, hnu, hdelta, hfactor',
    hPhi', hQ, hPhiDeg, hQDeg⟩

/-- Joint support-level package: the same normalized node and offset data
simultaneously produce the canonical bounded fixed-divisor presentation and
the exact nonzero barycentric quotient branch.  No implication between the
two conclusions beyond their shared input data is hidden in the statement. -/
theorem normalizedOsculation_and_matchingPhi_zero_branch
    {m r k : ℕ} (j rho b A w : Fin m → ℤ)
    (hm : 0 < m)
    (hcolumns : 4 * m + 1 ≤ osculationMonomialCount r)
    (hr : 0 < r) (hkpos : 0 < k)
    (hjbound : ∀ e, (j e).natAbs ≤ k)
    (hrhobound : ∀ e, (rho e).natAbs ≤ k)
    (hb : ∀ e, (b e).natAbs ≤ 2 ^ (k - 1))
    (hA : ∀ e, (A e).natAbs ≤ 5 * 2 ^ (k - 1))
    (hjinj : Function.Injective j)
    (hw : w ≠ 0)
    (hmu0 : mu Finset.univ j w 0 = 0)
    (hk : 3 ≤ k)
    (Q : Polynomial ℤ)
    (hfactor :
      matchingPhi k (U Finset.univ j rho w 0) (V Finset.univ j w) =
        (W Finset.univ j) ^ 2 * Q) :
    Nonempty (FixedDivisorPresentation
      (boundedOsculationPolynomialSpace
        (osculationConstraintMatrix r m j rho b A)
        (12 * osculationMonomialCount r * r *
          2 ^ k * k ^ (r - 1)))) ∧
      ∃ q, 1 ≤ q ∧ q ≤ m ∧
        matchingPhi k (U Finset.univ j rho w 0)
          (V Finset.univ j w) ≠ 0 ∧
        Q ≠ 0 ∧
        (matchingPhi k (U Finset.univ j rho w 0)
          (V Finset.univ j w)).natDegree = k * (m - q) ∧
        Q.natDegree = m * (k - 2) - q * k := by
  constructor
  · exact exists_fixedDivisorPresentation_normalizedOsculation
      j rho b A hm hcolumns hr hkpos hjbound hrhobound hb hA
  · obtain ⟨q, hq, hqm, _hmu, _hnu, _hdelta,
        hPhi, hQ, hPhiDeg, hQDeg⟩ :=
      fin_matchingPhi_zero_branch_nonzero_and_quotient_exact_degree
        hjinj hw hmu0 hk Q hfactor
    exact ⟨q, hq, hqm, hPhi, hQ, hPhiDeg, hQDeg⟩

#print axioms osculationConstraintMatrix_entry_bound
#print axioms exists_fixedDivisorPresentation_normalizedOsculation
#print axioms matching_quotient_degree_arithmetic
#print axioms W_sq_dvd_of_value_derivative_vanish
#print axioms fin_matchingPhi_zero_branch_nonzero_and_quotient_exact_degree
#print axioms fin_matchingPhi_zero_branch_exists_nonzero_quotient_exact_degree
#print axioms normalizedOsculation_and_matchingPhi_zero_branch

end Erdos686Variant
end Erdos686
