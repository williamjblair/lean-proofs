/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686OsculationFixedDivisor

/-!
# Erdős 686: the bounded-space fixed-divisor degree budget

The cube/fiber theorem produces `N_r - 4m + 1` linearly independent bounded
integral kernel vectors.  Because the canonical bounded space is the span of
*all* bounded integral kernel vectors, this is a genuine lower bound for the
dimension of `V_B` itself.  Combining that lower bound with the usual
quotient-space upper bound gives

`e(2r-e+3) ≤ 8m-2`.

This is deliberately separate from the sharper `4m` bound for the full
rational jet kernel.  No spanning equality `V_B = K_r` is asserted.
-/

namespace Erdos686
namespace Erdos686Variant

/-- Any bounded independent integral kernel family gives an honest dimension
lower bound for the canonical bounded space. -/
theorem boundedOsculationSpace_finrank_lower_of_independent_family
    {ι q N : Type*} [Fintype ι] [Fintype N]
    (A : Matrix q N ℤ) (B : ℕ) (z : ι → N → ℤ)
    (hli : LinearIndependent ℚ (fun i j => (z i j : ℚ)))
    (hker : ∀ i, A.mulVec (z i) = 0)
    (hbound : ∀ i j, (z i j).natAbs ≤ B) :
    Fintype.card ι ≤ Module.finrank ℚ (boundedOsculationSpace A B) := by
  let v : ι → N → ℚ := fun i => integralCoeffCast (z i)
  have hvEq : v = fun i j => (z i j : ℚ) := by
    rfl
  have hvli : LinearIndependent ℚ v := by
    simpa only [hvEq] using hli
  have hmem : ∀ i, v i ∈ boundedOsculationSpace A B := by
    intro i
    apply Submodule.subset_span
    refine ⟨z i, ?_, hbound i, rfl⟩
    exact (mem_integralOsculationLattice_iff A (z i)).mpr (hker i)
  have hspan : Submodule.span ℚ (Set.range v) ≤
      boundedOsculationSpace A B := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hmem i
  calc
    Fintype.card ι =
        Module.finrank ℚ (Submodule.span ℚ (Set.range v)) :=
      (finrank_span_eq_card hvli).symm
    _ ≤ Module.finrank ℚ (boundedOsculationSpace A B) :=
      Submodule.finrank_mono hspan

/-- Polynomial realization of the preceding lower bound.  Injectivity of the
coefficient-to-polynomial map preserves the entire independent family. -/
theorem boundedOsculationPolynomialSpace_finrank_lower_of_independent_family
    {ι : Type*} [Fintype ι] {q r : ℕ}
    (A : Matrix (Fin q) (OsculationMonomial r) ℤ) (B : ℕ)
    (z : ι → OsculationMonomial r → ℤ)
    (hli : LinearIndependent ℚ (fun i u => (z i u : ℚ)))
    (hker : ∀ i, A.mulVec (z i) = 0)
    (hbound : ∀ i u, (z i u).natAbs ≤ B) :
    Fintype.card ι ≤
      Module.finrank ℚ (boundedOsculationPolynomialSpace A B) := by
  let c : ι → OsculationMonomial r → ℚ :=
    fun i => integralCoeffCast (z i)
  let f : ι → BivariateRatPolynomial :=
    fun i => osculationCoeffToRatPolynomial r (c i)
  have hcli : LinearIndependent ℚ c := by
    simpa [c, integralCoeffCast] using hli
  have hmapKer : (osculationCoeffToRatPolynomial r).ker = ⊥ :=
    LinearMap.ker_eq_bot_of_injective
      (osculationCoeffToRatPolynomial_injective r)
  have hfli : LinearIndependent ℚ f := by
    simpa [f, Function.comp_def] using
      hcli.map' (osculationCoeffToRatPolynomial r) hmapKer
  have hfmem : ∀ i, f i ∈ boundedOsculationPolynomialSpace A B := by
    intro i
    refine ⟨c i, ?_, rfl⟩
    apply Submodule.subset_span
    refine ⟨z i, ?_, hbound i, rfl⟩
    exact (mem_integralOsculationLattice_iff A (z i)).mpr (hker i)
  let φ := (osculationCoeffToRatPolynomial r).domRestrict
    (boundedOsculationSpace A B)
  have hrange : LinearMap.range φ =
      boundedOsculationPolynomialSpace A B := by
    simp [φ, boundedOsculationPolynomialSpace]
  haveI : FiniteDimensional ℚ (LinearMap.range φ) :=
    LinearMap.finiteDimensional_range φ
  have hspan : Submodule.span ℚ (Set.range f) ≤
      boundedOsculationPolynomialSpace A B := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hfmem i
  calc
    Fintype.card ι =
        Module.finrank ℚ (Submodule.span ℚ (Set.range f)) :=
      (finrank_span_eq_card hfli).symm
    _ ≤ Module.finrank ℚ (LinearMap.range φ) :=
      Submodule.finrank_mono (by simpa [hrange] using hspan)
    _ = Module.finrank ℚ (boundedOsculationPolynomialSpace A B) := by
      rw [hrange]

/-- The advertised entry envelope gives the exact
`N_r - 4m + 1` lower bound for the canonical bounded polynomial space. -/
theorem boundedOsculationPolynomialSpace_finrank_lower_of_entry_bound
    {m r k : ℕ}
    (A : Matrix (Fin (2 * m)) (OsculationMonomial r) ℤ)
    (hentry : ∀ i u,
      (A i u).natAbs ≤ 3 * r * 2 ^ k * k ^ (r - 1))
    (hm : 0 < m)
    (hcolumns : 4 * m + 1 ≤ osculationMonomialCount r)
    (hr : 0 < r) (hk : 0 < k) :
    osculationMonomialCount r - 4 * m + 1 ≤
      Module.finrank ℚ
        (boundedOsculationPolynomialSpace A
          (12 * osculationMonomialCount r * r *
            2 ^ k * k ^ (r - 1))) := by
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
  let reindex : (Fin N → ℚ) ≃ₗ[ℚ]
      (OsculationMonomial r → ℚ) :=
    LinearEquiv.piCongrLeft ℚ (fun _ : OsculationMonomial r => ℚ) e
  let z' : Fin (N - 4 * m + 1) → OsculationMonomial r → ℤ :=
    fun i u => z i (e.symm u)
  have hzli : LinearIndependent ℚ (fun i u => (z' i u : ℚ)) := by
    have hreindexKer : reindex.toLinearMap.ker = ⊥ :=
      LinearMap.ker_eq_bot_of_injective reindex.injective
    have hmap := hli.map' reindex.toLinearMap hreindexKer
    have hreindexApply (v : Fin N → ℚ) (u : OsculationMonomial r) :
        reindex v u = v (e.symm u) := by
      simp [reindex, LinearEquiv.piCongrLeft]
    change LinearIndependent ℚ
      (fun i u => reindex (fun j => (z i j : ℚ)) u) at hmap
    simpa only [hreindexApply, z'] using hmap
  have hzker : ∀ i, A.mulVec (z' i) = 0 := by
    intro i
    have hi := hker i
    rw [show A' = A.submatrix id e by rfl,
      Matrix.submatrix_mulVec_equiv] at hi
    simpa [z'] using hi
  have hzbound : ∀ i u,
      (z' i u).natAbs ≤
        12 * osculationMonomialCount r * r *
          2 ^ k * k ^ (r - 1) := by
    intro i u
    have hu := hbound i (e.symm u)
    change (z' i u).natAbs ≤
      12 * Fintype.card (OsculationMonomial r) * r *
        2 ^ k * k ^ (r - 1) at hu
    rw [osculationMonomialBasis_card] at hu
    exact hu
  have hlower :=
    boundedOsculationPolynomialSpace_finrank_lower_of_independent_family
      A _ z' hzli hzker hzbound
  simp only [Fintype.card_fin] at hlower
  have hN : N = osculationMonomialCount r := by
    dsimp [N]
    exact osculationMonomialBasis_card r
  rw [hN] at hlower
  exact hlower

/-- Exact numerical consequence of the bounded-space dimension lower bound
and a degree-`e` quotient-space upper bound.  This is the correct fixed-
divisor budget for `V_B`, not the sharper full-kernel budget. -/
theorem boundedFixedDivisor_degree_inequality_of_dimension_bounds
    {r e m d : ℕ}
    (he : e ≤ r)
    (hcolumns : 4 * m + 1 ≤ osculationMonomialCount r)
    (hlower : osculationMonomialCount r - 4 * m + 1 ≤ d)
    (hupper : d ≤ osculationMonomialCount (r - e)) :
    e * (2 * r - e + 3) ≤ 8 * m - 2 := by
  have hcountLe : 4 * m ≤ osculationMonomialCount r := by omega
  have hlowerNat : osculationMonomialCount r + 1 ≤ d + 4 * m := by
    omega
  have hlowerQ :
      (osculationMonomialCount r : ℚ) + 1 ≤ d + 4 * m := by
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
      (e : ℚ) * (2 * r - e + 3) + 2 ≤ 8 * m := by
    nlinarith
  have htwor : e ≤ 2 * r := he.trans (by omega)
  have hfactorCast :
      ((2 * r - e + 3 : ℕ) : ℚ) =
        2 * (r : ℚ) - e + 3 := by
    rw [Nat.cast_add, Nat.cast_sub htwor]
    push_cast
    ring
  have htargetQ' :
      (e : ℚ) * ((2 * r - e + 3 : ℕ) : ℚ) + 2 ≤
        ((8 * m : ℕ) : ℚ) := by
    rw [hfactorCast]
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    exact htargetQ
  have htargetNat : e * (2 * r - e + 3) + 2 ≤ 8 * m := by
    exact_mod_cast htargetQ'
  omega

/-- Direct `V_B` interface: the cube/fiber lower bound and a separately
proved quotient-degree upper bound imply the corrected fixed-divisor degree
budget. -/
theorem boundedOsculationPolynomialSpace_fixedDivisor_degree_budget
    {m r k e : ℕ}
    (A : Matrix (Fin (2 * m)) (OsculationMonomial r) ℤ)
    (hentry : ∀ i u,
      (A i u).natAbs ≤ 3 * r * 2 ^ k * k ^ (r - 1))
    (hm : 0 < m)
    (hcolumns : 4 * m + 1 ≤ osculationMonomialCount r)
    (hr : 0 < r) (hk : 0 < k)
    (he : e ≤ r)
    (hquotientDegree :
      Module.finrank ℚ
          (boundedOsculationPolynomialSpace A
            (12 * osculationMonomialCount r * r *
              2 ^ k * k ^ (r - 1))) ≤
        osculationMonomialCount (r - e)) :
    e * (2 * r - e + 3) ≤ 8 * m - 2 := by
  apply boundedFixedDivisor_degree_inequality_of_dimension_bounds
    he hcolumns
  · exact boundedOsculationPolynomialSpace_finrank_lower_of_entry_bound
      A hentry hm hcolumns hr hk
  · exact hquotientDegree

#print axioms boundedOsculationSpace_finrank_lower_of_independent_family
#print axioms boundedOsculationPolynomialSpace_finrank_lower_of_independent_family
#print axioms boundedOsculationPolynomialSpace_finrank_lower_of_entry_bound
#print axioms boundedFixedDivisor_degree_inequality_of_dimension_bounds
#print axioms boundedOsculationPolynomialSpace_fixedDivisor_degree_budget

end Erdos686Variant
end Erdos686
