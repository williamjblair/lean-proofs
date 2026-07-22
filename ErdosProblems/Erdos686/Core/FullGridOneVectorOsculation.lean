/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.Core.MatchingOsculationBridge

/-!
# Erdős 686: one-vector osculation on the complete owner grid

The bounded independent-family construction uses the square-radius estimate
and therefore needs `4m < N_r` for `m` support nodes.  For the global
divisibility argument, however, one nonzero bounded polynomial is already a
useful object.  Allowing a larger, still completely explicit coefficient
radius reduces the exact column condition to `2m < N_r`.

For the complete `k × k` owner grid this condition already holds in total
degree `2k-1`, since

`N_(2k-1) = 2k^2+k > 2k^2`.

Thus full-grid square osculation admits nonzero integral polynomials one
degree below the `2k` size barrier.  This removes the previous support-count
obstruction only for kernel extraction.  It does **not** produce a useful
arithmetic specialization by itself: the guaranteed family can lie entirely
in the space of multiples of the degree-`k` equation polynomial, all of which
vanish at the target solution.  The sparse-support threshold for escaping
that common component is formalized below.
-/

namespace Erdos686
namespace Erdos686Variant

/-- A large explicit radius makes the finite-cube collision work under the
sharp dimension condition `q < N`.  The radius depends only on the matrix
row-mass bound, not on the eventual arithmetic variable `n`. -/
theorem largeRadius_cube_cardinality_inequality
    {q N L : ℕ} (hcolumns : q < N) :
    ((((L + 1) ^ q) * L + 1) ^ q) <
      (((L + 1) ^ q + 1) ^ N) := by
  let D := (L + 1) ^ q
  have hD : 1 ≤ D := by
    dsimp [D]
    exact one_le_pow₀ (by omega)
  have hbase : D * L + 1 ≤ D * (L + 1) := by
    nlinarith
  have hpow : (D * L + 1) ^ q ≤ (D * (L + 1)) ^ q :=
    Nat.pow_le_pow_left hbase q
  have hrewrite : (D * (L + 1)) ^ q = D ^ (q + 1) := by
    calc
      (D * (L + 1)) ^ q = D ^ q * (L + 1) ^ q := by rw [mul_pow]
      _ = D ^ q * D := by rw [show (L + 1) ^ q = D by rfl]
      _ = D ^ (q + 1) := (pow_succ D q).symm
  have hstrict : D ^ (q + 1) < (D + 1) ^ (q + 1) := by
    exact Nat.pow_lt_pow_left (by omega) (by omega)
  have hexponent : (D + 1) ^ (q + 1) ≤ (D + 1) ^ N := by
    apply pow_le_pow_right'
    · omega
    · omega
  dsimp [D] at hpow hrewrite hstrict hexponent ⊢
  rw [hrewrite] at hpow
  exact hpow.trans_lt (hstrict.trans_le hexponent)

/-- One bounded nonzero integer kernel vector under the sharp rank-counting
condition `q < N`.  The coefficient price is the explicit large radius
`(L+1)^q`, replacing the linear radius of the independent-family theorem. -/
theorem exists_nonzero_bounded_integer_kernel_vector_largeRadius
    {q N : ℕ} (A : Matrix (Fin q) (Fin N) ℤ) (L : ℕ)
    (hrow : ∀ i, ∑ j, (A i j).natAbs ≤ L)
    (hcolumns : q < N) :
    ∃ z : Fin N → ℤ,
      z ≠ 0 ∧
      A.mulVec z = 0 ∧
      ∀ j, (z j).natAbs ≤ (L + 1) ^ q := by
  apply exists_nonzero_bounded_integer_kernel_vector_of_card_lt
    A ((L + 1) ^ q) L hrow
  exact largeRadius_cube_cardinality_inequality hcolumns

private theorem exists_largeRadius_fiber_card_gt
    {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (C : ℕ)
    (hcard : Fintype.card β * C < Fintype.card α) :
    ∃ y, (Finset.univ.filter (fun x => f x = y)).card > C := by
  by_contra hn
  push Not at hn
  have hsigma :
      (∑ y : β, Fintype.card {x : α // f x = y}) = Fintype.card α := by
    rw [← Fintype.card_sigma]
    exact Fintype.card_congr (Equiv.sigmaFiberEquiv f)
  have hle : (∑ y : β, Fintype.card {x : α // f x = y}) ≤
      Fintype.card β * C := by
    calc
      _ ≤ ∑ _y : β, C := Finset.sum_le_sum (fun y _ => by
        simpa only [Fintype.card_subtype] using hn y)
      _ = Fintype.card β * C := by simp
  omega

/-- Sharp guaranteed-dimension version of the large-radius construction.
An integer `q × N` matrix with `q < N` has `N-q` linearly independent
integer kernel vectors, all with coordinatewise size at most `(L+1)^q`.
Unlike the earlier linear-radius family, this loses no extra factor of two
in the dimension count. -/
theorem exists_bounded_independent_integer_kernel_family_largeRadius
    {q N : ℕ} (A : Matrix (Fin q) (Fin N) ℤ) (L : ℕ)
    (hrow : ∀ i, ∑ j, (A i j).natAbs ≤ L)
    (hcolumns : q < N) :
    ∃ z : Fin (N - q) → Fin N → ℤ,
      LinearIndependent ℚ (fun i j => (z i j : ℚ)) ∧
      (∀ i, A.mulVec (z i) = 0) ∧
      ∀ i j, (z i j).natAbs ≤ (L + 1) ^ q := by
  let D := (L + 1) ^ q
  let cube := Fin N → Fin (D + 1)
  let code := Fin q → Fin (D * L + 1)
  let f : cube → code := cubeImageCode A D L hrow
  have hqpow : (D * L + 1) ^ q < (D + 1) ^ (q + 1) := by
    exact largeRadius_cube_cardinality_inequality (L := L) (Nat.lt_succ_self q)
  have htailPos : 0 < (D + 1) ^ (N - (q + 1)) :=
    Nat.pow_pos (by omega)
  have hfiberCard :
      Fintype.card code * (D + 1) ^ (N - (q + 1)) <
        Fintype.card cube := by
    simp only [cube, code, Fintype.card_fun, Fintype.card_fin]
    calc
      (D * L + 1) ^ q * (D + 1) ^ (N - (q + 1)) <
          (D + 1) ^ (q + 1) * (D + 1) ^ (N - (q + 1)) :=
        Nat.mul_lt_mul_of_pos_right hqpow htailPos
      _ = (D + 1) ^ N := by
        rw [← pow_add]
        congr 1
        omega
  obtain ⟨c, hc⟩ := exists_largeRadius_fiber_card_gt f
    ((D + 1) ^ (N - (q + 1))) hfiberCard
  let E : Finset cube := Finset.univ.filter (fun x => f x = c)
  let diffQ (x y : cube) : Fin N → ℚ :=
    fun j => (x j : ℚ) - (y j : ℚ)
  let G : Set (Fin N → ℚ) :=
    {v | ∃ x ∈ E, ∃ y ∈ E, v = diffQ x y}
  let W : Submodule ℚ (Fin N → ℚ) := Submodule.span ℚ G
  have hdiff : ∀ x ∈ E, ∀ y ∈ E, diffQ x y ∈ W := by
    intro x hx y hy
    exact Submodule.subset_span ⟨x, hx, y, hy, rfl⟩
  have hEcard : (D + 1) ^ (N - (q + 1)) < E.card := by
    simpa [E] using hc
  have hdim : N - (q + 1) < Module.finrank ℚ W := by
    by_contra hnot
    have hleDim : Module.finrank ℚ W ≤ N - (q + 1) := by omega
    have hcube := affine_cube_subset_card_le_finrank
      (N := N) D E W hdiff
    have hp : (D + 1) ^ Module.finrank ℚ W ≤
        (D + 1) ^ (N - (q + 1)) :=
      pow_le_pow_right' (by omega) hleDim
    omega
  have hs : N - q ≤ Module.finrank ℚ W := by omega
  obtain ⟨basis, hbmem, -, hbLI⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℚ G
  let e : Fin (N - q) → Fin (Module.finrank ℚ W) := Fin.castLE hs
  have heinj : Function.Injective e := Fin.castLE_injective hs
  have hchoose : ∀ i : Fin (N - q),
      ∃ x ∈ E, ∃ y ∈ E, basis (e i) = diffQ x y := by
    intro i
    simpa [G] using hbmem (e i)
  choose x hx y hy hxy using hchoose
  let z : Fin (N - q) → Fin N → ℤ :=
    fun i j => (x i j : ℤ) - (y i j : ℤ)
  refine ⟨z, ?_, ?_, ?_⟩
  · have hcomp : (fun i j => (z i j : ℚ)) = basis ∘ e := by
      funext i j
      have hij := congrFun (hxy i) j
      simpa [z, diffQ] using hij.symm
    rw [hcomp]
    exact hbLI.comp e heinj
  · intro i
    have hfx : f (x i) = c := (Finset.mem_filter.mp (hx i)).2
    have hfy : f (y i) = c := (Finset.mem_filter.mp (hy i)).2
    have himage := (cubeImageCode_eq_iff_mulVec_eq
      A D L hrow (x i) (y i)).mp (hfx.trans hfy.symm)
    funext row
    have hi := congrFun himage row
    simp only [z, Matrix.mulVec, dotProduct, Pi.zero_apply]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr hi
  · intro i j
    exact Int.natAbs_coe_sub_coe_le_of_le
      (Nat.le_of_lt_succ (x i j).isLt)
      (Nat.le_of_lt_succ (y i j).isLt)

/-- Entrywise-envelope form of the sharp one-vector theorem. -/
theorem exists_nonzero_bounded_integer_kernel_vector_largeRadius_of_entry_bound
    {q N : ℕ} (A : Matrix (Fin q) (Fin N) ℤ) (H : ℕ)
    (hentry : ∀ i j, (A i j).natAbs ≤ H)
    (hcolumns : q < N) :
    ∃ z : Fin N → ℤ,
      z ≠ 0 ∧
      A.mulVec z = 0 ∧
      ∀ j, (z j).natAbs ≤ (N * H + 1) ^ q := by
  have hrow : ∀ i, ∑ j, (A i j).natAbs ≤ N * H := by
    intro i
    calc
      ∑ j, (A i j).natAbs ≤ ∑ _j : Fin N, H :=
        Finset.sum_le_sum fun j _ => hentry i j
      _ = N * H := by simp
  exact exists_nonzero_bounded_integer_kernel_vector_largeRadius
    A (N * H) hrow hcolumns

/-- Entrywise-envelope form of the sharp `N-q` independent family. -/
theorem exists_bounded_independent_integer_kernel_family_largeRadius_of_entry_bound
    {q N : ℕ} (A : Matrix (Fin q) (Fin N) ℤ) (H : ℕ)
    (hentry : ∀ i j, (A i j).natAbs ≤ H)
    (hcolumns : q < N) :
    ∃ z : Fin (N - q) → Fin N → ℤ,
      LinearIndependent ℚ (fun i j => (z i j : ℚ)) ∧
      (∀ i, A.mulVec (z i) = 0) ∧
      ∀ i j, (z i j).natAbs ≤ (N * H + 1) ^ q := by
  have hrow : ∀ i, ∑ j, (A i j).natAbs ≤ N * H := by
    intro i
    calc
      ∑ j, (A i j).natAbs ≤ ∑ _j : Fin N, H :=
        Finset.sum_le_sum fun j _ => hentry i j
      _ = N * H := by simp
  exact exists_bounded_independent_integer_kernel_family_largeRadius
    A (N * H) hrow hcolumns

/-- Reindex the sharp one-vector theorem onto the canonical total-degree
monomial basis.  This needs only `2m < N_r`, half the column threshold of the
bounded independent-family construction. -/
theorem exists_nonzero_bounded_osculation_kernel_vector_largeRadius
    {m r : ℕ}
    (A : Matrix (Fin (2 * m)) (OsculationMonomial r) ℤ) (H : ℕ)
    (hentry : ∀ i u, (A i u).natAbs ≤ H)
    (hcolumns : 2 * m < osculationMonomialCount r) :
    ∃ z : OsculationMonomial r → ℤ,
      z ≠ 0 ∧
      A.mulVec z = 0 ∧
      ∀ u, (z u).natAbs ≤
        (osculationMonomialCount r * H + 1) ^ (2 * m) := by
  let N := Fintype.card (OsculationMonomial r)
  let e : Fin N ≃ OsculationMonomial r :=
    (Fintype.equivFin (OsculationMonomial r)).symm
  let A' : Matrix (Fin (2 * m)) (Fin N) ℤ := A.submatrix id e
  have hentry' : ∀ i j, (A' i j).natAbs ≤ H := by
    intro i j
    exact hentry i (e j)
  have hcolumns' : 2 * m < N := by
    change 2 * m < Fintype.card (OsculationMonomial r)
    rw [osculationMonomialBasis_card]
    exact hcolumns
  obtain ⟨z, hzne, hzker, hzbound⟩ :=
    exists_nonzero_bounded_integer_kernel_vector_largeRadius_of_entry_bound
      A' H hentry' hcolumns'
  let z' : OsculationMonomial r → ℤ := fun u => z (e.symm u)
  refine ⟨z', ?_, ?_, ?_⟩
  · intro hz'
    apply hzne
    funext j
    have hj := congrFun hz' (e j)
    simpa [z'] using hj
  · have hzker' := hzker
    rw [show A' = A.submatrix id e by rfl,
      Matrix.submatrix_mulVec_equiv] at hzker'
    simpa [z'] using hzker'
  · intro u
    have hu := hzbound (e.symm u)
    change (z' u).natAbs ≤
      (Fintype.card (OsculationMonomial r) * H + 1) ^ (2 * m) at hu
    rw [osculationMonomialBasis_card] at hu
    exact hu

/-- Reindexed sharp guaranteed-dimension family on the canonical monomial
basis.  This is the large-radius replacement for the old
`N_r-4m+1` family: it supplies exactly `N_r-2m` independent vectors. -/
theorem exists_bounded_independent_osculation_kernel_family_largeRadius
    {m r : ℕ}
    (A : Matrix (Fin (2 * m)) (OsculationMonomial r) ℤ) (H : ℕ)
    (hentry : ∀ i u, (A i u).natAbs ≤ H)
    (hcolumns : 2 * m < osculationMonomialCount r) :
    ∃ z : Fin (osculationMonomialCount r - 2 * m) →
        OsculationMonomial r → ℤ,
      LinearIndependent ℚ (fun i u => (z i u : ℚ)) ∧
      (∀ i, A.mulVec (z i) = 0) ∧
      ∀ i u, (z i u).natAbs ≤
        (osculationMonomialCount r * H + 1) ^ (2 * m) := by
  let N := Fintype.card (OsculationMonomial r)
  let e : Fin N ≃ OsculationMonomial r :=
    (Fintype.equivFin (OsculationMonomial r)).symm
  let A' : Matrix (Fin (2 * m)) (Fin N) ℤ := A.submatrix id e
  have hentry' : ∀ i j, (A' i j).natAbs ≤ H := by
    intro i j
    exact hentry i (e j)
  have hcolumns' : 2 * m < N := by
    change 2 * m < Fintype.card (OsculationMonomial r)
    rw [osculationMonomialBasis_card]
    exact hcolumns
  obtain ⟨z, hli, hker, hbound⟩ :=
    exists_bounded_independent_integer_kernel_family_largeRadius_of_entry_bound
      A' H hentry' hcolumns'
  have hN : N = osculationMonomialCount r := by
    dsimp [N]
    exact osculationMonomialBasis_card r
  let reindex : (Fin N → ℚ) ≃ₗ[ℚ]
      (OsculationMonomial r → ℚ) :=
    LinearEquiv.piCongrLeft ℚ (fun _ : OsculationMonomial r => ℚ) e
  let z' : Fin (N - 2 * m) → OsculationMonomial r → ℤ :=
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
  have hzbound : ∀ i u, (z' i u).natAbs ≤
      (N * H + 1) ^ (2 * m) := by
    intro i u
    have hu := hbound i (e.symm u)
    exact hu
  rw [← hN]
  exact ⟨z', hzli, hzker, hzbound⟩

/-- Exact full-grid column count: degree `2k-1`, not `2k`, already has more
monomials than the `2k²` value-and-tangent constraints. -/
theorem fullGrid_lowDegree_column_count
    {k : ℕ} (hk : 0 < k) :
    2 * (k * k) < osculationMonomialCount (2 * k - 1) := by
  unfold osculationMonomialCount
  rw [Nat.choose_two_right]
  have hfirst : 2 * k - 1 + 2 = 2 * k + 1 := by omega
  have hsecond : 2 * k + 1 - 1 = 2 * k := by omega
  rw [hfirst, hsecond]
  rw [show (2 * k + 1) * (2 * k) = ((2 * k + 1) * k) * 2 by ring]
  rw [Nat.mul_div_cancel _ (by norm_num : 0 < 2)]
  have halg : (2 * k + 1) * k = 2 * (k * k) + k := by ring
  rw [halg]
  omega

/-- The sharp family has exactly `k` guaranteed independent coefficient
vectors on the complete grid at degree `2k-1`. -/
theorem fullGrid_lowDegree_kernel_count
    {k : ℕ} (hk : 0 < k) :
    osculationMonomialCount (2 * k - 1) - 2 * (k * k) = k := by
  unfold osculationMonomialCount
  rw [Nat.choose_two_right]
  have hfirst : 2 * k - 1 + 2 = 2 * k + 1 := by omega
  have hsecond : 2 * k + 1 - 1 = 2 * k := by omega
  rw [hfirst, hsecond]
  rw [show (2 * k + 1) * (2 * k) = ((2 * k + 1) * k) * 2 by ring]
  rw [Nat.mul_div_cancel _ (by norm_num : 0 < 2)]
  have halg : (2 * k + 1) * k = 2 * (k * k) + k := by ring
  rw [halg]
  omega

/-- Exact evaluation-height bound for a bounded total-degree coefficient
vector.  In the full-grid specialization below the exponent is `2k-1`, so
any nonzero arithmetic specialization has one full power of the large
variable less than the owner-square modulus. -/
theorem osculationEvaluate_natAbs_le_of_coeff_bound
    {r B T : ℕ} (coeff : OsculationMonomial r → ℤ) (x y : ℤ)
    (hT : 1 ≤ T)
    (hcoeff : ∀ u, (coeff u).natAbs ≤ B)
    (hx : x.natAbs ≤ T) (hy : y.natAbs ≤ T) :
    (osculationEvaluate coeff x y).natAbs ≤
      osculationMonomialCount r * B * T ^ r := by
  rw [osculationEvaluate]
  calc
    (∑ u, coeff u * osculationMonomialValue u x y).natAbs ≤
        ∑ u, (coeff u * osculationMonomialValue u x y).natAbs :=
      Int.natAbs_sum_le Finset.univ _
    _ ≤ ∑ _u : OsculationMonomial r, B * T ^ r := by
      apply Finset.sum_le_sum
      intro u _
      rw [Int.natAbs_mul]
      exact Nat.mul_le_mul (hcoeff u)
        (osculationMonomialValue_natAbs_le hT u x y hx hy)
    _ = Fintype.card (OsculationMonomial r) * (B * T ^ r) := by simp
    _ = osculationMonomialCount r * B * T ^ r := by
      rw [osculationMonomialBasis_card]
      ring

/-- A matrix-kernel certificate gives the value and directional-derivative
equations required by the owner-square Taylor theorem, at every support
node simultaneously. -/
theorem osculation_constraints_of_mulVec_eq_zero
    {r m : ℕ} (j rho b A : Fin m → ℤ)
    (coeff : OsculationMonomial r → ℤ)
    (hker : (osculationConstraintMatrix r m j rho b A).mulVec coeff = 0) :
    ∀ e,
      osculationEvaluate coeff (j e) (rho e) = 0 ∧
      b e * osculationEvaluateDX coeff (j e) (rho e) +
        A e * osculationEvaluateDY coeff (j e) (rho e) = 0 := by
  intro e
  constructor
  · have he := congrFun hker (⟨e.val, by omega⟩ : Fin (2 * m))
    change dotProduct
        (osculationConstraintMatrix r m j rho b A
          ⟨e.val, by omega⟩) coeff = 0 at he
    rwa [osculation_value_row_dotProduct] at he
  · have he := congrFun hker (⟨m + e.val, by omega⟩ : Fin (2 * m))
    change dotProduct
        (osculationConstraintMatrix r m j rho b A
          ⟨m + e.val, by omega⟩) coeff = 0 at he
    rwa [osculation_direction_row_dotProduct] at he

/-- Complete-grid normalized osculation at degree `2k-1`.  The conclusion is
an actual nonzero integral coefficient vector satisfying every value and
directional constraint, with an exact coefficient bound independent of
`n` and `d`. -/
theorem exists_fullGrid_lowDegree_normalizedOsculation_kernel
    {k : ℕ} (hk : 0 < k)
    (j rho b A : Fin (k * k) → ℤ)
    (hj : ∀ e, (j e).natAbs ≤ k)
    (hrho : ∀ e, (rho e).natAbs ≤ k)
    (hb : ∀ e, (b e).natAbs ≤ 2 ^ (k - 1))
    (hA : ∀ e, (A e).natAbs ≤ 5 * 2 ^ (k - 1)) :
    ∃ z : OsculationMonomial (2 * k - 1) → ℤ,
      z ≠ 0 ∧
      (osculationConstraintMatrix (2 * k - 1) (k * k)
        j rho b A).mulVec z = 0 ∧
      ∀ u, (z u).natAbs ≤
        (osculationMonomialCount (2 * k - 1) *
            (3 * (2 * k - 1) * 2 ^ k * k ^ ((2 * k - 1) - 1)) + 1) ^
          (2 * (k * k)) := by
  apply exists_nonzero_bounded_osculation_kernel_vector_largeRadius
  · exact osculationConstraintMatrix_entry_bound
      j rho b A (by omega) hk hj hrho hb hA
  · exact fullGrid_lowDegree_column_count hk

/-- Strong full-grid form: degree `2k-1` supplies `k` linearly independent
bounded integral osculation polynomials, not merely one. -/
theorem exists_fullGrid_lowDegree_normalizedOsculation_kernel_family
    {k : ℕ} (hk : 0 < k)
    (j rho b A : Fin (k * k) → ℤ)
    (hj : ∀ e, (j e).natAbs ≤ k)
    (hrho : ∀ e, (rho e).natAbs ≤ k)
    (hb : ∀ e, (b e).natAbs ≤ 2 ^ (k - 1))
    (hA : ∀ e, (A e).natAbs ≤ 5 * 2 ^ (k - 1)) :
    ∃ z : Fin k → OsculationMonomial (2 * k - 1) → ℤ,
      LinearIndependent ℚ (fun i u => (z i u : ℚ)) ∧
      (∀ i, (osculationConstraintMatrix (2 * k - 1) (k * k)
        j rho b A).mulVec (z i) = 0) ∧
      ∀ i u, (z i u).natAbs ≤
        (osculationMonomialCount (2 * k - 1) *
            (3 * (2 * k - 1) * 2 ^ k * k ^ ((2 * k - 1) - 1)) + 1) ^
          (2 * (k * k)) := by
  obtain ⟨z, hli, hker, hbound⟩ :=
    exists_bounded_independent_osculation_kernel_family_largeRadius
      (osculationConstraintMatrix (2 * k - 1) (k * k) j rho b A)
      (3 * (2 * k - 1) * 2 ^ k * k ^ ((2 * k - 1) - 1))
      (osculationConstraintMatrix_entry_bound
        j rho b A (by omega) hk hj hrho hb hA)
      (fullGrid_lowDegree_column_count hk)
  have hcount := fullGrid_lowDegree_kernel_count hk
  let e : Fin k →
      Fin (osculationMonomialCount (2 * k - 1) - 2 * (k * k)) :=
    fun i => Fin.cast hcount.symm i
  have heinj : Function.Injective e := by
    intro i i' hii
    apply Fin.ext
    have hval : (e i).val = (e i').val :=
      congrArg (fun t => t.val) hii
    simpa [e] using hval
  let z' : Fin k → OsculationMonomial (2 * k - 1) → ℤ :=
    fun i => z (e i)
  refine ⟨z', ?_, ?_, ?_⟩
  · exact hli.comp e heinj
  · intro i
    exact hker (e i)
  · intro i u
    exact hbound (e i) u

/-! ## Common-component dimension obstruction

At degree `2k-1`, multiples of the degree-`k` equation polynomial by all
polynomials of degree at most `k-1` form a space of dimension
`N_(k-1)=k(k+1)/2`.  Hence the guaranteed kernel family only forces a
nonmultiple when

`N_(k-1) < N_(2k-1)-2m`, equivalently `4m < 3k^2+k`.

The theorem below is deliberately parameterized by the candidate
equation-multiple subspace and its dimension bound.  Identifying that
subspace with actual multiples of the equation polynomial is a separate
algebraic theorem; no divisibility claim is hidden in the interface.
-/

/-- A linearly independent family larger than a finite-dimensional subspace
has a member outside that subspace. -/
theorem exists_linearIndependent_member_not_mem_of_finrank_lt
    {ι V : Type*} [Fintype ι]
    [AddCommGroup V] [Module ℚ V]
    (f : ι → V) (hli : LinearIndependent ℚ f)
    (W : Submodule ℚ V) [Module.Finite ℚ W]
    (hsmall : Module.finrank ℚ W < Fintype.card ι) :
    ∃ i, f i ∉ W := by
  by_contra hall
  push Not at hall
  have hspan : Submodule.span ℚ (Set.range f) ≤ W := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hall i
  have hdim := Submodule.finrank_mono hspan
  rw [finrank_span_eq_card hli] at hdim
  omega

/-- Exact sparse-support threshold for escaping a degree-`k` common
component at ambient degree `2k-1`. -/
theorem sparseSupport_commonComponent_dimension_gap
    {k m : ℕ} (hk : 0 < k)
    (hsparse : 4 * m < 3 * k * k + k) :
    osculationMonomialCount (k - 1) <
      osculationMonomialCount (2 * k - 1) - 2 * m := by
  have hcount (t : ℕ) :
      (osculationMonomialCount t : ℚ) =
        ((t : ℚ) + 2) * ((t : ℚ) + 1) / 2 := by
    unfold osculationMonomialCount
    rw [Nat.cast_choose_two]
    push_cast [show 1 ≤ t + 2 by omega]
    ring
  have hkcast : ((k - 1 : ℕ) : ℚ) = (k : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k)]
    norm_num
  have htwokcast : ((2 * k - 1 : ℕ) : ℚ) = 2 * (k : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * k)]
    push_cast
    ring
  have hsparseQ : (4 * m : ℕ) < 3 * k * k + k := hsparse
  have hsparseQ' : ((4 * m : ℕ) : ℚ) < ((3 * k * k + k : ℕ) : ℚ) := by
    exact_mod_cast hsparseQ
  have hgapQ :
      (osculationMonomialCount (k - 1) : ℚ) + 2 * m <
        osculationMonomialCount (2 * k - 1) := by
    rw [hcount, hcount, hkcast, htwokcast]
    push_cast at hsparseQ' ⊢
    nlinarith
  have hgap :
      osculationMonomialCount (k - 1) + 2 * m <
        osculationMonomialCount (2 * k - 1) := by
    exact_mod_cast hgapQ
  exact Nat.lt_sub_of_add_lt hgap

/-- Correct sparse-support nonmultiple interface.  If the proposed
degree-`k` equation-multiple space has the expected dimension at most
`N_(k-1)`, then `4m < 3k²+k` forces a bounded degree-`2k-1` osculation
kernel polynomial outside it. -/
theorem exists_sparseSupport_lowDegree_kernel_not_mem_commonComponent
    {k m : ℕ} (hk : 0 < k)
    (hsparse : 4 * m < 3 * k * k + k)
    (j rho b A : Fin m → ℤ)
    (hj : ∀ e, (j e).natAbs ≤ k)
    (hrho : ∀ e, (rho e).natAbs ≤ k)
    (hb : ∀ e, (b e).natAbs ≤ 2 ^ (k - 1))
    (hA : ∀ e, (A e).natAbs ≤ 5 * 2 ^ (k - 1))
    (commonComponent : Submodule ℚ BivariateRatPolynomial)
    [Module.Finite ℚ commonComponent]
    (hcomponentDim : Module.finrank ℚ commonComponent ≤
      osculationMonomialCount (k - 1)) :
    ∃ z : OsculationMonomial (2 * k - 1) → ℤ,
      z ≠ 0 ∧
      (osculationConstraintMatrix (2 * k - 1) m j rho b A).mulVec z = 0 ∧
      (∀ u, (z u).natAbs ≤
        (osculationMonomialCount (2 * k - 1) *
            (3 * (2 * k - 1) * 2 ^ k * k ^ ((2 * k - 1) - 1)) + 1) ^
          (2 * m)) ∧
      osculationCoeffToRatPolynomial (2 * k - 1)
        (integralCoeffCast z) ∉ commonComponent := by
  let r := 2 * k - 1
  let H := 3 * r * 2 ^ k * k ^ (r - 1)
  have hgap := sparseSupport_commonComponent_dimension_gap hk hsparse
  have hcolumns : 2 * m < osculationMonomialCount r := by
    dsimp [r]
    omega
  obtain ⟨z, hli, hker, hbound⟩ :=
    exists_bounded_independent_osculation_kernel_family_largeRadius
      (osculationConstraintMatrix r m j rho b A) H
      (osculationConstraintMatrix_entry_bound
        j rho b A (by dsimp [r]; omega) hk hj hrho hb hA)
      hcolumns
  let f : Fin (osculationMonomialCount r - 2 * m) →
      BivariateRatPolynomial := fun i =>
    osculationCoeffToRatPolynomial r (integralCoeffCast (z i))
  have hfli : LinearIndependent ℚ f := by
    have hmapKer : (osculationCoeffToRatPolynomial r).ker = ⊥ :=
      LinearMap.ker_eq_bot_of_injective
        (osculationCoeffToRatPolynomial_injective r)
    have hmap := hli.map' (osculationCoeffToRatPolynomial r) hmapKer
    simpa [f, integralCoeffCast] using hmap
  have hsmall : Module.finrank ℚ commonComponent <
      Fintype.card (Fin (osculationMonomialCount r - 2 * m)) := by
    simp only [Fintype.card_fin]
    exact hcomponentDim.trans_lt (by simpa [r] using hgap)
  obtain ⟨i, hi⟩ :=
    exists_linearIndependent_member_not_mem_of_finrank_lt
      f hfli commonComponent hsmall
  refine ⟨z i, ?_, hker i, ?_, ?_⟩
  · intro hzero
    apply hli.ne_zero i
    funext u
    simp [hzero]
  · intro u
    simpa [r, H] using hbound i u
  · simpa [f, r] using hi

/-- The complete grid is in the dense branch for every `k≥2`; therefore the
`k`-element family proved above can be entirely contained in the equation-
multiple space. -/
theorem fullGrid_not_in_sparse_commonComponent_regime
    {k : ℕ} (hk : 2 ≤ k) :
    ¬ 4 * (k * k) < 3 * k * k + k := by
  nlinarith

/-- Multiplication by a fixed candidate equation polynomial, with the
cofactor restricted to total degree at most `k-1`. -/
noncomputable def degreeBoundedEquationMultiplication
    (k : ℕ) (E : BivariateRatPolynomial) :
    (OsculationMonomial (k - 1) → ℚ) →ₗ[ℚ] BivariateRatPolynomial :=
  (LinearMap.mulLeft ℚ E).comp
    (osculationCoeffToRatPolynomial (k - 1))

/-- The concrete degree-bounded equation-multiple subspace. -/
noncomputable def degreeBoundedEquationMultipleSpace
    (k : ℕ) (E : BivariateRatPolynomial) :
    Submodule ℚ BivariateRatPolynomial :=
  LinearMap.range (degreeBoundedEquationMultiplication k E)

noncomputable instance degreeBoundedEquationMultipleSpace_moduleFinite
    (k : ℕ) (E : BivariateRatPolynomial) :
    Module.Finite ℚ (degreeBoundedEquationMultipleSpace k E) := by
  unfold degreeBoundedEquationMultipleSpace
  exact LinearMap.finiteDimensional_range
    (degreeBoundedEquationMultiplication k E)

theorem mem_degreeBoundedEquationMultipleSpace_iff
    {k : ℕ} {E F : BivariateRatPolynomial} :
    F ∈ degreeBoundedEquationMultipleSpace k E ↔
      ∃ c : OsculationMonomial (k - 1) → ℚ,
        E * osculationCoeffToRatPolynomial (k - 1) c = F := by
  simp [degreeBoundedEquationMultipleSpace,
    degreeBoundedEquationMultiplication]

/-- The equation-multiple space has dimension at most `N_(k-1)`, without
assuming multiplication by `E` is injective. -/
theorem degreeBoundedEquationMultipleSpace_finrank_le
    (k : ℕ) (E : BivariateRatPolynomial) :
    Module.finrank ℚ (degreeBoundedEquationMultipleSpace k E) ≤
      osculationMonomialCount (k - 1) := by
  have h := LinearMap.finrank_range_le
    (degreeBoundedEquationMultiplication k E)
  change Module.finrank ℚ (degreeBoundedEquationMultipleSpace k E) ≤
    Module.finrank ℚ (OsculationMonomial (k - 1) → ℚ) at h
  have hdomain : Module.finrank ℚ (OsculationMonomial (k - 1) → ℚ) =
      Fintype.card (OsculationMonomial (k - 1)) := by simp
  rw [hdomain, osculationMonomialBasis_card] at h
  simpa using h

/-- Every equation multiple vanishes at every zero of the equation
polynomial.  This is the exact base-locus obstruction to using an arbitrary
kernel vector in the global divisibility estimate. -/
theorem degreeBoundedEquationMultipleSpace_specialization_vanishes
    {k : ℕ} {E F : BivariateRatPolynomial} {p : Fin 2 → ℚ}
    (hF : F ∈ degreeBoundedEquationMultipleSpace k E)
    (hE : evalRatAt p E = 0) :
    evalRatAt p F = 0 := by
  rw [mem_degreeBoundedEquationMultipleSpace_iff] at hF
  obtain ⟨c, rfl⟩ := hF
  simp [map_mul, hE]

/-- Unconditional version of the sparse-support interface for the concrete
degree-bounded multiples of an arbitrary candidate equation polynomial. -/
theorem exists_sparseSupport_lowDegree_kernel_outside_degreeBoundedEquationMultiples
    {k m : ℕ} (hk : 0 < k)
    (hsparse : 4 * m < 3 * k * k + k)
    (j rho b A : Fin m → ℤ)
    (hj : ∀ e, (j e).natAbs ≤ k)
    (hrho : ∀ e, (rho e).natAbs ≤ k)
    (hb : ∀ e, (b e).natAbs ≤ 2 ^ (k - 1))
    (hA : ∀ e, (A e).natAbs ≤ 5 * 2 ^ (k - 1))
    (E : BivariateRatPolynomial) :
    ∃ z : OsculationMonomial (2 * k - 1) → ℤ,
      z ≠ 0 ∧
      (osculationConstraintMatrix (2 * k - 1) m j rho b A).mulVec z = 0 ∧
      (∀ u, (z u).natAbs ≤
        (osculationMonomialCount (2 * k - 1) *
            (3 * (2 * k - 1) * 2 ^ k * k ^ ((2 * k - 1) - 1)) + 1) ^
          (2 * m)) ∧
      osculationCoeffToRatPolynomial (2 * k - 1)
        (integralCoeffCast z) ∉ degreeBoundedEquationMultipleSpace k E := by
  exact exists_sparseSupport_lowDegree_kernel_not_mem_commonComponent
    hk hsparse j rho b A hj hrho hb hA
    (degreeBoundedEquationMultipleSpace k E)
    (degreeBoundedEquationMultipleSpace_finrank_le k E)

/-! ## Reflection audit

Binomial reflection preserves the reduced coefficients, but it does not
duplicate osculation nodes.  For odd `k`, reflecting only the upper index
preserves the sign and directional coefficients while moving the `rho`
coordinate by `k+1-2i`.  For even `k`, the sign flips as well.  Reflecting
both indices sends `(j,rho)` to `(k+1-j,-rho)`, an affine symmetry rather
than a duplicate row.
-/

/-- Reflection of a one-based block index. -/
def matchingReflect (k h : ℕ) : ℕ := k + 1 - h

theorem matchingReflect_mem_Icc
    {k h : ℕ} (hh : h ∈ Finset.Icc 1 k) :
    matchingReflect k h ∈ Finset.Icc 1 k := by
  simp only [Finset.mem_Icc] at hh ⊢
  unfold matchingReflect
  omega

/-- Exact binomial symmetry `C_(k+1-h)=C_h`. -/
theorem matchingBinomial_reflect
    {k h : ℕ} (hh : h ∈ Finset.Icc 1 k) :
    matchingBinomial k (matchingReflect k h) = matchingBinomial k h := by
  have hh1 : 1 ≤ h := (Finset.mem_Icc.mp hh).1
  have hhk : h ≤ k := (Finset.mem_Icc.mp hh).2
  have hle : h - 1 ≤ k - 1 := by omega
  unfold matchingBinomial matchingReflect
  have href : k + 1 - h - 1 = (k - 1) - (h - 1) := by omega
  rw [href, Nat.choose_symm hle]

theorem reducedMatchingLeft_reflect_left
    {k i j : ℕ} (hi : i ∈ Finset.Icc 1 k) :
    reducedMatchingLeft k (matchingReflect k i) j =
      reducedMatchingLeft k i j := by
  simp only [reducedMatchingLeft, matchingBinomial_reflect hi]

theorem reducedMatchingRight_reflect_left
    {k i j : ℕ} (hi : i ∈ Finset.Icc 1 k) :
    reducedMatchingRight k (matchingReflect k i) j =
      reducedMatchingRight k i j := by
  simp only [reducedMatchingRight, matchingBinomial_reflect hi]

theorem reducedMatchingLeft_reflect_right
    {k i j : ℕ} (hj : j ∈ Finset.Icc 1 k) :
    reducedMatchingLeft k i (matchingReflect k j) =
      reducedMatchingLeft k i j := by
  simp only [reducedMatchingLeft, matchingBinomial_reflect hj]

theorem reducedMatchingRight_reflect_right
    {k i j : ℕ} (hj : j ∈ Finset.Icc 1 k) :
    reducedMatchingRight k i (matchingReflect k j) =
      reducedMatchingRight k i j := by
  simp only [reducedMatchingRight, matchingBinomial_reflect hj]

theorem neg_one_pow_reflect_left_of_odd
    {k i j : ℕ} (hi : i ∈ Finset.Icc 1 k) (hk : Odd k) :
    (-1 : ℤ) ^ (matchingReflect k i + j) = (-1 : ℤ) ^ (i + j) := by
  have hkmod : k % 2 = 1 := Nat.odd_iff.mp hk
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hik : i ≤ k := (Finset.mem_Icc.mp hi).2
  have hexp : matchingReflect k i + j + 2 * i =
      (k + 1) + (i + j) := by
    unfold matchingReflect
    omega
  have hmod : (matchingReflect k i + j) % 2 = (i + j) % 2 := by
    omega
  calc
    (-1 : ℤ) ^ (matchingReflect k i + j) =
        (-1 : ℤ) ^ ((matchingReflect k i + j) % 2) :=
      neg_one_pow_eq_pow_mod_two _
    _ = (-1 : ℤ) ^ ((i + j) % 2) := by rw [hmod]
    _ = (-1 : ℤ) ^ (i + j) := (neg_one_pow_eq_pow_mod_two _).symm

theorem neg_one_pow_reflect_left_of_even
    {k i j : ℕ} (hi : i ∈ Finset.Icc 1 k) (hk : Even k) :
    (-1 : ℤ) ^ (matchingReflect k i + j) =
      -((-1 : ℤ) ^ (i + j)) := by
  have hkmod : k % 2 = 0 := Nat.even_iff.mp hk
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hik : i ≤ k := (Finset.mem_Icc.mp hi).2
  have hexp : matchingReflect k i + j + 2 * i =
      (k + 1) + (i + j) := by
    unfold matchingReflect
    omega
  have hrefmod : (matchingReflect k i + j) % 2 =
      1 - (i + j) % 2 := by omega
  have hijmod : (i + j) % 2 = 0 ∨ (i + j) % 2 = 1 := by omega
  rcases hijmod with hzero | hone
  · have href : (matchingReflect k i + j) % 2 = 1 := by omega
    rw [Odd.neg_one_pow (Nat.odd_iff.mpr href),
      Even.neg_one_pow (Nat.even_iff.mpr hzero)]
  · have href : (matchingReflect k i + j) % 2 = 0 := by omega
    rw [Even.neg_one_pow (Nat.even_iff.mpr href),
      Odd.neg_one_pow (Nat.odd_iff.mpr hone)]
    norm_num

theorem neg_one_pow_reflect_both
    {k i j : ℕ}
    (hi : i ∈ Finset.Icc 1 k) (hj : j ∈ Finset.Icc 1 k) :
    (-1 : ℤ) ^ (matchingReflect k i + matchingReflect k j) =
      (-1 : ℤ) ^ (i + j) := by
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hik : i ≤ k := (Finset.mem_Icc.mp hi).2
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hjk : j ≤ k := (Finset.mem_Icc.mp hj).2
  have hexp : matchingReflect k i + matchingReflect k j + 2 * (i + j) =
      2 * (k + 1) + (i + j) := by
    unfold matchingReflect
    omega
  have hmod :
      (matchingReflect k i + matchingReflect k j) % 2 =
        (i + j) % 2 := by omega
  calc
    (-1 : ℤ) ^ (matchingReflect k i + matchingReflect k j) =
        (-1 : ℤ) ^
          ((matchingReflect k i + matchingReflect k j) % 2) :=
      neg_one_pow_eq_pow_mod_two _
    _ = (-1 : ℤ) ^ ((i + j) % 2) := by rw [hmod]
    _ = (-1 : ℤ) ^ (i + j) := (neg_one_pow_eq_pow_mod_two _).symm

/-- The normalized directional coefficient `4 sign a-b`. -/
def normalizedDirectionCoefficient (k i j : ℕ) : ℤ :=
  4 * (-1 : ℤ) ^ (i + j) * (reducedMatchingLeft k i j : ℤ) -
    (reducedMatchingRight k i j : ℤ)

theorem normalizedDirectionCoefficient_reflect_left_of_odd
    {k i j : ℕ} (hi : i ∈ Finset.Icc 1 k) (hk : Odd k) :
    normalizedDirectionCoefficient k (matchingReflect k i) j =
      normalizedDirectionCoefficient k i j := by
  unfold normalizedDirectionCoefficient
  rw [reducedMatchingLeft_reflect_left hi,
    reducedMatchingRight_reflect_left hi,
    neg_one_pow_reflect_left_of_odd hi hk]

/-- For even `k`, one-index reflection does not preserve the directional
coefficient: it sends `A` to `-A-2b`. -/
theorem normalizedDirectionCoefficient_reflect_left_of_even
    {k i j : ℕ} (hi : i ∈ Finset.Icc 1 k) (hk : Even k) :
    normalizedDirectionCoefficient k (matchingReflect k i) j =
      -normalizedDirectionCoefficient k i j -
        2 * (reducedMatchingRight k i j : ℤ) := by
  unfold normalizedDirectionCoefficient
  rw [reducedMatchingLeft_reflect_left hi,
    reducedMatchingRight_reflect_left hi,
    neg_one_pow_reflect_left_of_even hi hk]
  ring

/-- Row reflection moves the diagonal coordinate by `k+1-2i`; it is equal
only in the central row. -/
theorem reflected_left_rho_sub_rho
    {k i j : ℕ} (hi : i ∈ Finset.Icc 1 k) :
    ((matchingReflect k i : ℕ) : ℤ) - j - ((i : ℤ) - j) =
      (k + 1 : ℕ) - 2 * (i : ℤ) := by
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hik : i ≤ k := (Finset.mem_Icc.mp hi).2
  unfold matchingReflect
  push_cast
  omega

/-- Simultaneous reflection is the exact affine node symmetry
`(j,rho) ↦ (k+1-j,-rho)`. -/
theorem reflected_both_node
    {k i j : ℕ}
    (hi : i ∈ Finset.Icc 1 k) (hj : j ∈ Finset.Icc 1 k) :
    (((matchingReflect k j : ℕ) : ℤ),
      ((matchingReflect k i : ℕ) : ℤ) - matchingReflect k j) =
    (((k + 1 - j : ℕ) : ℤ), -((i : ℤ) - j)) := by
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hik : i ≤ k := (Finset.mem_Icc.mp hi).2
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hjk : j ≤ k := (Finset.mem_Icc.mp hj).2
  unfold matchingReflect
  ext <;> push_cast <;> omega

/-- The degree-one monomial `Y`. -/
def osculationYMonomial : OsculationMonomial 1 :=
  ⟨(⟨0, by omega⟩ : Fin 2), (⟨1, by omega⟩ : Fin (1 - 0 + 1))⟩

/-- Exact falsifier to duplicate-row compression.  At odd `k=3`, cells
`(i,j)=(1,1)` and `(3,1)` have identical reduced binomial data and sign, but
their nodes are `(1,0)` and `(1,2)`.  The value row already differs on the
degree-one monomial `Y`. -/
theorem odd_reflected_rows_not_duplicate_counterexample :
    reducedMatchingLeft 3 1 1 = reducedMatchingLeft 3 3 1 ∧
    reducedMatchingRight 3 1 1 = reducedMatchingRight 3 3 1 ∧
    (-1 : ℤ) ^ (1 + 1) = (-1 : ℤ) ^ (3 + 1) ∧
    osculationValueEntry 1 0 osculationYMonomial ≠
      osculationValueEntry 1 2 osculationYMonomial := by
  norm_num [reducedMatchingLeft, reducedMatchingRight, matchingBinomial,
    osculationValueEntry, osculationMonomialValue,
    OsculationMonomial.xExponent, OsculationMonomial.yExponent,
    osculationYMonomial]
  change (0 : ℤ) ≠ 2
  norm_num

#print axioms largeRadius_cube_cardinality_inequality
#print axioms exists_nonzero_bounded_integer_kernel_vector_largeRadius
#print axioms exists_bounded_independent_integer_kernel_family_largeRadius
#print axioms exists_nonzero_bounded_integer_kernel_vector_largeRadius_of_entry_bound
#print axioms exists_bounded_independent_integer_kernel_family_largeRadius_of_entry_bound
#print axioms exists_nonzero_bounded_osculation_kernel_vector_largeRadius
#print axioms exists_bounded_independent_osculation_kernel_family_largeRadius
#print axioms fullGrid_lowDegree_column_count
#print axioms fullGrid_lowDegree_kernel_count
#print axioms osculationEvaluate_natAbs_le_of_coeff_bound
#print axioms osculation_constraints_of_mulVec_eq_zero
#print axioms exists_fullGrid_lowDegree_normalizedOsculation_kernel
#print axioms exists_fullGrid_lowDegree_normalizedOsculation_kernel_family
#print axioms exists_linearIndependent_member_not_mem_of_finrank_lt
#print axioms sparseSupport_commonComponent_dimension_gap
#print axioms exists_sparseSupport_lowDegree_kernel_not_mem_commonComponent
#print axioms fullGrid_not_in_sparse_commonComponent_regime
#print axioms mem_degreeBoundedEquationMultipleSpace_iff
#print axioms degreeBoundedEquationMultipleSpace_finrank_le
#print axioms degreeBoundedEquationMultipleSpace_specialization_vanishes
#print axioms exists_sparseSupport_lowDegree_kernel_outside_degreeBoundedEquationMultiples
#print axioms matchingBinomial_reflect
#print axioms reducedMatchingLeft_reflect_left
#print axioms reducedMatchingRight_reflect_left
#print axioms neg_one_pow_reflect_left_of_odd
#print axioms neg_one_pow_reflect_left_of_even
#print axioms neg_one_pow_reflect_both
#print axioms normalizedDirectionCoefficient_reflect_left_of_odd
#print axioms normalizedDirectionCoefficient_reflect_left_of_even
#print axioms reflected_left_rho_sub_rho
#print axioms reflected_both_node
#print axioms odd_reflected_rows_not_duplicate_counterexample

end Erdos686Variant
end Erdos686
