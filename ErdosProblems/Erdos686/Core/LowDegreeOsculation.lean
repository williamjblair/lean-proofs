/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.Core.NormalizedMatching
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Erdős 686: low-degree bivariate osculation

This module begins the audited low-degree replacement for the older
square-Hermite interface.  It defines the exact total-degree monomial basis
and the value/directional-derivative constraint matrix.  The bounded
independent integer-kernel family is deliberately kept separate until its
finite-cube argument is fully formalized.
-/

namespace Erdos686
namespace Erdos686Variant

open scoped BigOperators

/-- Number of bivariate monomials of total degree at most `r`. -/
def osculationMonomialCount (r : ℕ) : ℕ :=
  (r + 2).choose 2

/-- A concrete monomial basis of total degree at most `r`.  The first
exponent is `a.val`; the second ranges from zero through `r-a.val`. -/
abbrev OsculationMonomial (r : ℕ) :=
  (a : Fin (r + 1)) × Fin (r - a.val + 1)

/-- Exponent of `X` in a basis monomial. -/
def OsculationMonomial.xExponent {r : ℕ}
    (u : OsculationMonomial r) : ℕ :=
  u.1.val

/-- Exponent of `Y` in a basis monomial. -/
def OsculationMonomial.yExponent {r : ℕ}
    (u : OsculationMonomial r) : ℕ :=
  u.2.val

theorem OsculationMonomial.totalDegree_le
    {r : ℕ} (u : OsculationMonomial r) :
    u.xExponent + u.yExponent ≤ r := by
  have hu := u.2.isLt
  dsimp [OsculationMonomial.xExponent, OsculationMonomial.yExponent]
  omega

/-- Exact cardinality of the total-degree basis. -/
theorem osculationMonomialBasis_card (r : ℕ) :
    Fintype.card (OsculationMonomial r) =
      osculationMonomialCount r := by
  simp only [OsculationMonomial, Fintype.card_sigma, Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range
    (fun i : ℕ => r - i + 1)]
  unfold osculationMonomialCount
  calc
    ∑ i ∈ Finset.range (r + 1), (r - i + 1) =
        ∑ i ∈ Finset.range (r + 1), (i + 1) := by
      simpa using
        (Finset.sum_range_reflect (fun i : ℕ => i + 1) (r + 1))
    _ = (r + 2).choose 2 := by
      simpa using (Nat.sum_range_add_choose r 1)

private theorem exists_osculation_degree (m : ℕ) :
    ∃ r, 4 * m + 1 ≤ osculationMonomialCount r := by
  refine ⟨4 * m + 1, ?_⟩
  unfold osculationMonomialCount
  rw [Nat.choose_two_right]
  apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mpr
  have hsub : 4 * m + 1 + 2 - 1 = 4 * m + 2 := by omega
  rw [hsub]
  nlinarith

/-- Least total degree whose monomial count is at least `4m+1`. -/
noncomputable def osculationDegree (m : ℕ) : ℕ :=
  Nat.find (exists_osculation_degree m)

theorem osculationDegree_spec (m : ℕ) :
    4 * m + 1 ≤
      osculationMonomialCount (osculationDegree m) :=
  Nat.find_spec (exists_osculation_degree m)

theorem osculationDegree_minimal
    {m r : ℕ}
    (hr : 4 * m + 1 ≤ osculationMonomialCount r) :
    osculationDegree m ≤ r :=
  Nat.find_min' (exists_osculation_degree m) hr

/-- Evaluation of one total-degree monomial. -/
def osculationMonomialValue
    {r : ℕ} (u : OsculationMonomial r) (x y : ℤ) : ℤ :=
  x ^ u.xExponent * y ^ u.yExponent

/-- Formal `X` derivative of one total-degree monomial, evaluated at
`(x,y)`. -/
def osculationMonomialDX
    {r : ℕ} (u : OsculationMonomial r) (x y : ℤ) : ℤ :=
  (u.xExponent : ℤ) *
    x ^ (u.xExponent - 1) * y ^ u.yExponent

/-- Formal `Y` derivative of one total-degree monomial, evaluated at
`(x,y)`. -/
def osculationMonomialDY
    {r : ℕ} (u : OsculationMonomial r) (x y : ℤ) : ℤ :=
  (u.yExponent : ℤ) *
    x ^ u.xExponent * y ^ (u.yExponent - 1)

/-- A formal `X` derivative monomial has the expected total-degree bound on
the integer box `|x|,|y| <= k`. -/
theorem osculationMonomialDX_natAbs_le
    {r k : ℕ} (hr : 1 ≤ r) (hk : 1 ≤ k)
    (u : OsculationMonomial r) (x y : ℤ)
    (hx : x.natAbs ≤ k) (hy : y.natAbs ≤ k) :
    (osculationMonomialDX u x y).natAbs ≤
      r * k ^ (r - 1) := by
  have hdeg := u.totalDegree_le
  by_cases ha : u.xExponent = 0
  · simp [osculationMonomialDX, ha]
  · have haPos : 1 ≤ u.xExponent := Nat.one_le_iff_ne_zero.mpr ha
    have hexp :
        (u.xExponent - 1) + u.yExponent ≤ r - 1 := by
      omega
    simp only [osculationMonomialDX, Int.natAbs_mul,
      Int.natAbs_natCast, Int.natAbs_pow]
    calc
      u.xExponent * x.natAbs ^ (u.xExponent - 1) *
          y.natAbs ^ u.yExponent ≤
          r * k ^ (u.xExponent - 1) * k ^ u.yExponent := by
        gcongr
        omega
      _ = r * k ^ ((u.xExponent - 1) + u.yExponent) := by
        rw [pow_add]
        ring
      _ ≤ r * k ^ (r - 1) := by
        exact Nat.mul_le_mul_left r
          (Nat.pow_le_pow_right hk hexp)

/-- Symmetric total-degree bound for a formal `Y` derivative monomial. -/
theorem osculationMonomialDY_natAbs_le
    {r k : ℕ} (hr : 1 ≤ r) (hk : 1 ≤ k)
    (u : OsculationMonomial r) (x y : ℤ)
    (hx : x.natAbs ≤ k) (hy : y.natAbs ≤ k) :
    (osculationMonomialDY u x y).natAbs ≤
      r * k ^ (r - 1) := by
  have hdeg := u.totalDegree_le
  by_cases hb : u.yExponent = 0
  · simp [osculationMonomialDY, hb]
  · have hbPos : 1 ≤ u.yExponent := Nat.one_le_iff_ne_zero.mpr hb
    have hexp :
        u.xExponent + (u.yExponent - 1) ≤ r - 1 := by
      omega
    simp only [osculationMonomialDY, Int.natAbs_mul,
      Int.natAbs_natCast, Int.natAbs_pow]
    calc
      u.yExponent * x.natAbs ^ u.xExponent *
          y.natAbs ^ (u.yExponent - 1) ≤
          r * k ^ u.xExponent * k ^ (u.yExponent - 1) := by
        gcongr
        omega
      _ = r * k ^ (u.xExponent + (u.yExponent - 1)) := by
        rw [pow_add]
        ring
      _ ≤ r * k ^ (r - 1) := by
        exact Nat.mul_le_mul_left r
          (Nat.pow_le_pow_right hk hexp)

/-- One value constraint entry. -/
def osculationValueEntry
    {r : ℕ} (j rho : ℤ) (u : OsculationMonomial r) : ℤ :=
  osculationMonomialValue u j rho

/-- One normalized directional-derivative constraint entry
`b*d/dX + A*d/dY`. -/
def osculationDirectionEntry
    {r : ℕ} (b A j rho : ℤ) (u : OsculationMonomial r) : ℤ :=
  b * osculationMonomialDX u j rho +
    A * osculationMonomialDY u j rho

/-- A total-degree monomial is bounded by `k^r` on the integer box
`|x|,|y| <= k`. -/
theorem osculationMonomialValue_natAbs_le
    {r k : ℕ} (hk : 1 ≤ k)
    (u : OsculationMonomial r) (x y : ℤ)
    (hx : x.natAbs ≤ k) (hy : y.natAbs ≤ k) :
    (osculationMonomialValue u x y).natAbs ≤ k ^ r := by
  have hdeg := u.totalDegree_le
  simp only [osculationMonomialValue, Int.natAbs_mul, Int.natAbs_pow]
  calc
    x.natAbs ^ u.xExponent * y.natAbs ^ u.yExponent ≤
        k ^ u.xExponent * k ^ u.yExponent := by
      gcongr
    _ = k ^ (u.xExponent + u.yExponent) := by rw [pow_add]
    _ ≤ k ^ r := Nat.pow_le_pow_right hk hdeg

/-- Exact arithmetic bound for a normalized directional entry.  The
reduced-binomial inputs enter only through the two displayed coefficient
bounds. -/
theorem osculationDirectionEntry_natAbs_le
    {r k : ℕ} (hr : 1 ≤ r) (hk : 1 ≤ k)
    (u : OsculationMonomial r) (b A j rho : ℤ)
    (hj : j.natAbs ≤ k) (hrho : rho.natAbs ≤ k)
    (hb : b.natAbs ≤ 2 ^ (k - 1))
    (hA : A.natAbs ≤ 5 * 2 ^ (k - 1)) :
    (osculationDirectionEntry b A j rho u).natAbs ≤
      3 * r * 2 ^ k * k ^ (r - 1) := by
  have hdx :=
    osculationMonomialDX_natAbs_le hr hk u j rho hj hrho
  have hdy :=
    osculationMonomialDY_natAbs_le hr hk u j rho hj hrho
  calc
    (osculationDirectionEntry b A j rho u).natAbs ≤
        (b * osculationMonomialDX u j rho).natAbs +
          (A * osculationMonomialDY u j rho).natAbs :=
      Int.natAbs_add_le _ _
    _ = b.natAbs * (osculationMonomialDX u j rho).natAbs +
          A.natAbs * (osculationMonomialDY u j rho).natAbs := by
      simp only [Int.natAbs_mul]
    _ ≤ 2 ^ (k - 1) * (r * k ^ (r - 1)) +
          (5 * 2 ^ (k - 1)) * (r * k ^ (r - 1)) := by
      exact Nat.add_le_add (Nat.mul_le_mul hb hdx)
        (Nat.mul_le_mul hA hdy)
    _ = 3 * r * 2 ^ k * k ^ (r - 1) := by
      obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      simp only [Nat.succ_sub_one, pow_succ]
      ring

/-- Value rows satisfy the same advertised entry envelope. -/
theorem osculationValueEntry_natAbs_le
    {r k : ℕ} (hr : 1 ≤ r) (hk : 1 ≤ k)
    (u : OsculationMonomial r) (j rho : ℤ)
    (hj : j.natAbs ≤ k) (hrho : rho.natAbs ≤ k) :
    (osculationValueEntry j rho u).natAbs ≤
      3 * r * 2 ^ k * k ^ (r - 1) := by
  have hvalue :=
    osculationMonomialValue_natAbs_le hk u j rho hj hrho
  calc
    (osculationValueEntry j rho u).natAbs ≤ k ^ r := hvalue
    _ = k * k ^ (r - 1) := by
      obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
      simp [pow_succ, mul_comm]
    _ ≤ 3 * r * 2 ^ k * k ^ (r - 1) := by
      gcongr
      have : k ≤ 2 ^ k := Nat.le_of_lt Nat.lt_two_pow_self
      nlinarith

/-- Exact `2m × N_r` osculation matrix: the first `m` rows are value
constraints and the second `m` rows are directional derivatives.  The source
package's references to a `4m × N_r` matrix are not used. -/
def osculationConstraintMatrix
    (r m : ℕ) (j rho b A : Fin m → ℤ) :
    Matrix (Fin (2 * m)) (OsculationMonomial r) ℤ :=
  fun row u =>
    if h : row.val < m then
      osculationValueEntry (j ⟨row.val, h⟩) (rho ⟨row.val, h⟩) u
    else
      let e : Fin m := ⟨row.val - m, by omega⟩
      osculationDirectionEntry (b e) (A e) (j e) (rho e) u

/-- Coefficient vector evaluation of the represented bivariate polynomial. -/
def osculationEvaluate
    {r : ℕ} (coeff : OsculationMonomial r → ℤ) (x y : ℤ) : ℤ :=
  ∑ u, coeff u * osculationMonomialValue u x y

/-- Evaluation of the represented formal `X` derivative. -/
def osculationEvaluateDX
    {r : ℕ} (coeff : OsculationMonomial r → ℤ) (x y : ℤ) : ℤ :=
  ∑ u, coeff u * osculationMonomialDX u x y

/-- Evaluation of the represented formal `Y` derivative. -/
def osculationEvaluateDY
    {r : ℕ} (coeff : OsculationMonomial r → ℤ) (x y : ℤ) : ℤ :=
  ∑ u, coeff u * osculationMonomialDY u x y

/-- The value row of the matrix is exactly polynomial evaluation. -/
theorem osculation_value_row_dotProduct
    {r m : ℕ} (j rho b A : Fin m → ℤ)
    (e : Fin m) (coeff : OsculationMonomial r → ℤ) :
    dotProduct
        (osculationConstraintMatrix r m j rho b A
          ⟨e.val, by omega⟩)
        coeff =
      osculationEvaluate coeff (j e) (rho e) := by
  simp [dotProduct, osculationConstraintMatrix,
    osculationValueEntry, osculationEvaluate, mul_comm]

/-- The directional row is exactly
`b * dF/dX + A * dF/dY`. -/
theorem osculation_direction_row_dotProduct
    {r m : ℕ} (j rho b A : Fin m → ℤ)
    (e : Fin m) (coeff : OsculationMonomial r → ℤ) :
    dotProduct
        (osculationConstraintMatrix r m j rho b A
          ⟨m + e.val, by omega⟩)
        coeff =
      b e * osculationEvaluateDX coeff (j e) (rho e) +
        A e * osculationEvaluateDY coeff (j e) (rho e) := by
  simp [dotProduct, osculationConstraintMatrix,
    osculationDirectionEntry, osculationEvaluateDX,
    osculationEvaluateDY, Finset.mul_sum, mul_add,
    mul_comm, mul_left_comm, Finset.sum_add_distrib]

#print axioms OsculationMonomial.totalDegree_le
#print axioms osculationMonomialBasis_card
#print axioms osculationDegree_spec
#print axioms osculationDegree_minimal
#print axioms osculation_value_row_dotProduct
#print axioms osculation_direction_row_dotProduct

end Erdos686Variant
end Erdos686
