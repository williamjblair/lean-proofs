/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686FullGridOneVectorOsculation
import ErdosProblems.Erdos686FullMassNormalization

/-!
# Erdős 686: dense common-component no-go theorem

This file instantiates the actual normalized equation component

`E(X,Y) = 4 R(X) - C(X+Y)`,

where both root products run from `1` through `k`.  At every owner-grid cell
`(X,Y)=(j,i-j)`, its value and normalized directional derivative vanish.
Consequently every product `E*P` satisfies the same first-order osculation
conditions, for completely arbitrary value and first derivatives of `P`.

At the arithmetic target `(-n,-d)`, the original block equation makes
`E(-n,-d)=0`.  Taking the cofactor `P=1` therefore gives an exact
countermodel to any attempt to deduce a nontrivial divisor of `P(-n,-d)`
from the same value/tangent owner-square Taylor constraints.  A successful
dense-branch argument must add an independent equation or control a
higher/normal jet not implied by those constraints.
-/

namespace Erdos686
namespace Erdos686Variant

open scoped BigOperators

private theorem pderiv_finset_prod
    {ι : Type*} [DecidableEq ι]
    (v : Fin 2) (s : Finset ι) (f : ι → BivariateRatPolynomial) :
    MvPolynomial.pderiv v (∏ i ∈ s, f i) =
      ∑ i ∈ s,
        MvPolynomial.pderiv v (f i) * ∏ j ∈ s.erase i, f j := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, MvPolynomial.pderiv_mul, ih,
        Finset.sum_insert ha, Finset.erase_insert ha]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.erase_insert_of_ne (by aesop), Finset.prod_insert]
      · ac_rfl
      · simp [ha]

/-- The integer root product with roots `1,...,k`. -/
def gridRootProduct (k : ℕ) (x : ℤ) : ℤ :=
  ∏ h ∈ Finset.Icc 1 k, (x - (h : ℤ))

/-- Integer evaluation of the actual normalized equation component. -/
def normalizedEquationValue (k : ℕ) (x y : ℤ) : ℤ :=
  4 * gridRootProduct k x - gridRootProduct k (x + y)

theorem gridRootProduct_at_root
    {k h : ℕ} (hh : h ∈ Finset.Icc 1 k) :
    gridRootProduct k (h : ℤ) = 0 := by
  unfold gridRootProduct
  apply Finset.prod_eq_zero hh
  simp

/-- Both root products vanish at every complete-grid node. -/
theorem normalizedEquationValue_at_cell
    {k i j : ℕ}
    (hi : i ∈ Finset.Icc 1 k) (hj : j ∈ Finset.Icc 1 k) :
    normalizedEquationValue k (j : ℤ) ((i : ℤ) - j) = 0 := by
  unfold normalizedEquationValue
  rw [gridRootProduct_at_root hj]
  have hsum : (j : ℤ) + ((i : ℤ) - j) = i := by ring
  rw [hsum, gridRootProduct_at_root hi]
  ring

/-- `X` derivative of `E` at the cell `(j,i-j)`. -/
def normalizedEquationDXAtCell (k i j : ℕ) : ℤ :=
  (-1 : ℤ) ^ (k - 1) *
    (4 * localBlockCoefficient k j - localBlockCoefficient k i)

/-- `Y` derivative of `E` at the cell `(j,i-j)`. -/
def normalizedEquationDYAtCell (k i : ℕ) : ℤ :=
  (-1 : ℤ) ^ (k - 1) * (-localBlockCoefficient k i)

private theorem neg_one_pow_cell_sign
    {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j) :
    (-1 : ℤ) ^ (i + j) * (-1 : ℤ) ^ (i - 1) =
      (-1 : ℤ) ^ (j - 1) := by
  rw [← pow_add]
  have hmod : ((i + j) + (i - 1)) % 2 = (j - 1) % 2 := by omega
  calc
    (-1 : ℤ) ^ ((i + j) + (i - 1)) =
        (-1 : ℤ) ^ (((i + j) + (i - 1)) % 2) :=
      neg_one_pow_eq_pow_mod_two _
    _ = (-1 : ℤ) ^ ((j - 1) % 2) := by rw [hmod]
    _ = (-1 : ℤ) ^ (j - 1) := (neg_one_pow_eq_pow_mod_two _).symm

/-- The actual equation component has zero normalized directional derivative
at every owner-grid cell.  This is the equation-facing common-component
identity, with the reduced binomial coefficients and parity sign explicit. -/
theorem normalizedEquation_directional_at_cell
    {k i j : ℕ}
    (hi : i ∈ Finset.Icc 1 k) (hj : j ∈ Finset.Icc 1 k) :
    (reducedMatchingRight k i j : ℤ) *
          normalizedEquationDXAtCell k i j +
        normalizedDirectionCoefficient k i j *
          normalizedEquationDYAtCell k i = 0 := by
  obtain ⟨q, -, hFi, hFj⟩ := exists_matchingCommonPrefactor hi hj
  have hFiZ : (localBlockCoefficientNat k i : ℤ) =
      (q : ℤ) * (reducedMatchingRight k i j : ℤ) := by
    exact_mod_cast hFi
  have hFjZ : (localBlockCoefficientNat k j : ℤ) =
      (q : ℤ) * (reducedMatchingLeft k i j : ℤ) := by
    exact_mod_cast hFj
  have hsign := neg_one_pow_cell_sign
    (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hj).1
  unfold normalizedEquationDXAtCell normalizedEquationDYAtCell
  unfold normalizedDirectionCoefficient
  rw [localBlockCoefficient_eq_sign_mul_nat hi,
    localBlockCoefficient_eq_sign_mul_nat hj,
    hFiZ, hFjZ]
  rw [← hsign]
  ring

/-- Product-rule no-go at one cell.  The value and normalized tangent of
`E*P` vanish for arbitrary prescribed value and first derivatives of `P`. -/
theorem normalizedEquation_multiple_cell_jet_zero
    {k i j : ℕ}
    (hi : i ∈ Finset.Icc 1 k) (hj : j ∈ Finset.Icc 1 k)
    (p px py : ℤ) :
    normalizedEquationValue k (j : ℤ) ((i : ℤ) - j) * p = 0 ∧
      (reducedMatchingRight k i j : ℤ) *
          (normalizedEquationDXAtCell k i j * p +
            normalizedEquationValue k (j : ℤ) ((i : ℤ) - j) * px) +
        normalizedDirectionCoefficient k i j *
          (normalizedEquationDYAtCell k i * p +
            normalizedEquationValue k (j : ℤ) ((i : ℤ) - j) * py) = 0 := by
  have hvalue := normalizedEquationValue_at_cell hi hj
  have hdirection := normalizedEquation_directional_at_cell hi hj
  constructor
  · rw [hvalue]
    ring
  · rw [hvalue]
    calc
      (reducedMatchingRight k i j : ℤ) *
            (normalizedEquationDXAtCell k i j * p + 0 * px) +
          normalizedDirectionCoefficient k i j *
            (normalizedEquationDYAtCell k i * p + 0 * py) =
          ((reducedMatchingRight k i j : ℤ) *
              normalizedEquationDXAtCell k i j +
            normalizedDirectionCoefficient k i j *
              normalizedEquationDYAtCell k i) * p := by ring
      _ = 0 := by rw [hdirection]; ring

/-- Exact global jet countermodel: for every nonunit modulus, the constant
cofactor `P=1` satisfies every complete-grid value/tangent equation but is
not divisible by that modulus. -/
theorem normalizedEquation_cell_jets_do_not_force_cofactor_divisibility
    {k M : ℕ} (hM : 1 < M) :
    ∃ p px py : ℤ,
      (∀ i ∈ Finset.Icc 1 k, ∀ j ∈ Finset.Icc 1 k,
        normalizedEquationValue k (j : ℤ) ((i : ℤ) - j) * p = 0 ∧
        (reducedMatchingRight k i j : ℤ) *
            (normalizedEquationDXAtCell k i j * p +
              normalizedEquationValue k (j : ℤ) ((i : ℤ) - j) * px) +
          normalizedDirectionCoefficient k i j *
            (normalizedEquationDYAtCell k i * p +
              normalizedEquationValue k (j : ℤ) ((i : ℤ) - j) * py) = 0) ∧
      ¬ (M : ℤ) ∣ p := by
  refine ⟨1, 0, 0, ?_, ?_⟩
  · intro i hi j hj
    exact normalizedEquation_multiple_cell_jet_zero hi hj 1 0 0
  · intro hdiv
    have hunit : IsUnit (M : ℤ) := isUnit_iff_dvd_one.mpr hdiv
    rcases Int.isUnit_iff.mp hunit with h | h <;> omega

/-- The root product at a negative natural argument is the signed lower
block product. -/
theorem gridRootProduct_neg_nat (k n : ℕ) :
    gridRootProduct k (-(n : ℤ)) =
      (-1 : ℤ) ^ k * (blockProduct k n : ℤ) := by
  unfold gridRootProduct blockProduct
  have hterm : ∀ h : ℕ, -(n : ℤ) - (h : ℤ) = -((n + h : ℕ) : ℤ) := by
    intro h
    push_cast
    ring
  simp_rw [hterm]
  rw [Finset.prod_neg]
  have hcard : (Finset.Icc 1 k).card = k := by
    rw [Nat.card_Icc]
    omega
  rw [hcard]
  push_cast
  rfl

/-- At a hypothetical block solution, the actual equation component
vanishes at the global arithmetic target. -/
theorem normalizedEquationValue_at_target
    {k n d : ℕ}
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    normalizedEquationValue k (-(n : ℤ)) (-(d : ℤ)) = 0 := by
  unfold normalizedEquationValue
  rw [gridRootProduct_neg_nat]
  have hsum : -(n : ℤ) + -(d : ℤ) = -((n + d : ℕ) : ℤ) := by
    push_cast
    ring
  rw [hsum, gridRootProduct_neg_nat]
  have heqZ : (blockProduct k (n + d) : ℤ) =
      4 * (blockProduct k n : ℤ) := by exact_mod_cast heq
  rw [heqZ]
  ring

/-- Rational bivariate root product `R(X)`. -/
noncomputable def gridRootPolynomialX (k : ℕ) : BivariateRatPolynomial :=
  ∏ h ∈ Finset.Icc 1 k,
    (MvPolynomial.X 0 - MvPolynomial.C (h : ℚ))

/-- Rational bivariate root product `C(X+Y)`. -/
noncomputable def gridRootPolynomialZ (k : ℕ) : BivariateRatPolynomial :=
  ∏ h ∈ Finset.Icc 1 k,
    (MvPolynomial.X 0 + MvPolynomial.X 1 - MvPolynomial.C (h : ℚ))

/-- The actual normalized equation polynomial `4R(X)-C(X+Y)`. -/
noncomputable def normalizedEquationPolynomial (k : ℕ) :
    BivariateRatPolynomial :=
  MvPolynomial.C 4 * gridRootPolynomialX k - gridRootPolynomialZ k

theorem evalRatAt_gridRootPolynomialX
    (k : ℕ) (p : Fin 2 → ℚ) :
    evalRatAt p (gridRootPolynomialX k) =
      ∏ h ∈ Finset.Icc 1 k, (p 0 - h) := by
  simp [evalRatAt, gridRootPolynomialX]

theorem evalRatAt_gridRootPolynomialZ
    (k : ℕ) (p : Fin 2 → ℚ) :
    evalRatAt p (gridRootPolynomialZ k) =
      ∏ h ∈ Finset.Icc 1 k, (p 0 + p 1 - h) := by
  simp [evalRatAt, gridRootPolynomialZ]

theorem evalRatAt_pderiv_gridRootPolynomialX
    (k : ℕ) (p : Fin 2 → ℚ) :
    evalRatAt p (MvPolynomial.pderiv 0 (gridRootPolynomialX k)) =
      ∑ h ∈ Finset.Icc 1 k,
        ∏ q ∈ (Finset.Icc 1 k).erase h, (p 0 - q) := by
  rw [gridRootPolynomialX, pderiv_finset_prod]
  simp [evalRatAt]

theorem evalRatAt_pderiv_gridRootPolynomialZ_X
    (k : ℕ) (p : Fin 2 → ℚ) :
    evalRatAt p (MvPolynomial.pderiv 0 (gridRootPolynomialZ k)) =
      ∑ h ∈ Finset.Icc 1 k,
        ∏ q ∈ (Finset.Icc 1 k).erase h, (p 0 + p 1 - q) := by
  rw [gridRootPolynomialZ, pderiv_finset_prod]
  simp [evalRatAt]

theorem evalRatAt_pderiv_gridRootPolynomialZ_Y
    (k : ℕ) (p : Fin 2 → ℚ) :
    evalRatAt p (MvPolynomial.pderiv 1 (gridRootPolynomialZ k)) =
      ∑ h ∈ Finset.Icc 1 k,
        ∏ q ∈ (Finset.Icc 1 k).erase h, (p 0 + p 1 - q) := by
  rw [gridRootPolynomialZ, pderiv_finset_prod]
  simp [evalRatAt]

theorem pderiv_gridRootPolynomialX_Y (k : ℕ) :
    MvPolynomial.pderiv 1 (gridRootPolynomialX k) = 0 := by
  rw [gridRootPolynomialX, pderiv_finset_prod]
  simp

theorem rootDerivativeProduct_eq_localBlockCoefficient
    {k i : ℕ} (hi : i ∈ Finset.Icc 1 k) :
    (∏ q ∈ (Finset.Icc 1 k).erase i,
        ((i : ℤ) - (q : ℤ))) =
      (-1 : ℤ) ^ (k - 1) * localBlockCoefficient k i := by
  have hcard : ((Finset.Icc 1 k).erase i).card = k - 1 := by
    rw [Finset.card_erase_of_mem hi, Nat.card_Icc]
    omega
  unfold localBlockCoefficient localBlockCofactor
  simp_rw [show ∀ q : ℕ,
      (i : ℤ) - (q : ℤ) = -(-(i : ℤ) + (q : ℤ)) by
        intro q
        ring]
  rw [Finset.prod_neg, hcard]

theorem rootDerivativeSum_at_root
    {k i : ℕ} (hi : i ∈ Finset.Icc 1 k) :
    (∑ h ∈ Finset.Icc 1 k,
        ∏ q ∈ (Finset.Icc 1 k).erase h,
          ((i : ℚ) - (q : ℚ))) =
      (((-1 : ℤ) ^ (k - 1) * localBlockCoefficient k i : ℤ) : ℚ) := by
  rw [Finset.sum_eq_single i]
  · exact_mod_cast rootDerivativeProduct_eq_localBlockCoefficient hi
  · intro h hh hne
    apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hne.symm, hi⟩)
    simp
  · exact fun h => (h hi).elim

/-- Rational owner-grid point `(j,i-j)`. -/
def normalizedCellPoint (i j : ℕ) : Fin 2 → ℚ :=
  fun t => if t = 0 then (j : ℚ) else (i : ℚ) - j

theorem evalRatAt_pderiv_normalizedEquationPolynomial_X_at_cell
    {k i j : ℕ}
    (hi : i ∈ Finset.Icc 1 k) (hj : j ∈ Finset.Icc 1 k) :
    evalRatAt (normalizedCellPoint i j)
        (MvPolynomial.pderiv 0 (normalizedEquationPolynomial k)) =
      (normalizedEquationDXAtCell k i j : ℚ) := by
  rw [normalizedEquationPolynomial, map_sub, MvPolynomial.pderiv_mul]
  simp only [MvPolynomial.pderiv_C, zero_mul, zero_add]
  rw [map_sub, map_mul, map_ofNat,
    evalRatAt_pderiv_gridRootPolynomialX,
    evalRatAt_pderiv_gridRootPolynomialZ_X]
  simp [evalRatAt, normalizedCellPoint]
  ring_nf
  rw [rootDerivativeSum_at_root hj, rootDerivativeSum_at_root hi]
  unfold normalizedEquationDXAtCell
  push_cast
  ring

theorem evalRatAt_pderiv_normalizedEquationPolynomial_Y_at_cell
    {k i j : ℕ}
    (hi : i ∈ Finset.Icc 1 k) :
    evalRatAt (normalizedCellPoint i j)
        (MvPolynomial.pderiv 1 (normalizedEquationPolynomial k)) =
      (normalizedEquationDYAtCell k i : ℚ) := by
  rw [normalizedEquationPolynomial, map_sub, MvPolynomial.pderiv_mul,
    pderiv_gridRootPolynomialX_Y]
  simp only [MvPolynomial.pderiv_C, zero_mul, mul_zero, add_zero]
  rw [map_sub, map_zero,
    evalRatAt_pderiv_gridRootPolynomialZ_Y]
  simp [normalizedCellPoint]
  ring_nf
  rw [rootDerivativeSum_at_root hi]
  unfold normalizedEquationDYAtCell
  push_cast
  ring

/-- Polynomial specialization agrees with the concrete integer equation
value at integral points. -/
theorem evalRatAt_normalizedEquationPolynomial_int
    (k : ℕ) (x y : ℤ) :
    evalRatAt (fun t => if t = 0 then (x : ℚ) else (y : ℚ))
        (normalizedEquationPolynomial k) =
      (normalizedEquationValue k x y : ℚ) := by
  rw [normalizedEquationPolynomial, map_sub, map_mul,
    evalRatAt_gridRootPolynomialX, evalRatAt_gridRootPolynomialZ]
  simp only [map_ofNat, if_pos, Fin.isValue]
  unfold normalizedEquationValue gridRootProduct
  push_cast
  rfl

/-- The actual rational polynomial vanishes at every complete-grid node. -/
theorem evalRatAt_normalizedEquationPolynomial_at_cell
    {k i j : ℕ}
    (hi : i ∈ Finset.Icc 1 k) (hj : j ∈ Finset.Icc 1 k) :
    evalRatAt (normalizedCellPoint i j)
        (normalizedEquationPolynomial k) = 0 := by
  have h := evalRatAt_normalizedEquationPolynomial_int k (j : ℤ)
    ((i : ℤ) - (j : ℤ))
  rw [normalizedEquationValue_at_cell hi hj] at h
  simpa [normalizedCellPoint] using h

/-- The actual `MvPolynomial.pderiv` values have zero normalized owner
tangent at every complete-grid node. -/
theorem normalizedEquationPolynomial_directional_pderiv_at_cell
    {k i j : ℕ}
    (hi : i ∈ Finset.Icc 1 k) (hj : j ∈ Finset.Icc 1 k) :
    (reducedMatchingRight k i j : ℚ) *
          evalRatAt (normalizedCellPoint i j)
            (MvPolynomial.pderiv 0 (normalizedEquationPolynomial k)) +
        (normalizedDirectionCoefficient k i j : ℚ) *
          evalRatAt (normalizedCellPoint i j)
            (MvPolynomial.pderiv 1 (normalizedEquationPolynomial k)) = 0 := by
  rw [evalRatAt_pderiv_normalizedEquationPolynomial_X_at_cell hi hj,
    evalRatAt_pderiv_normalizedEquationPolynomial_Y_at_cell hi]
  exact_mod_cast normalizedEquation_directional_at_cell hi hj

/-- Actual-polynomial product-rule no-go: every multiple `E*P` obeys the
complete-grid value and first-order owner-tangent equations, with no
condition at all on the cofactor polynomial `P`. -/
theorem normalizedEquationPolynomial_multiple_cell_jet_zero
    {k i j : ℕ}
    (hi : i ∈ Finset.Icc 1 k) (hj : j ∈ Finset.Icc 1 k)
    (P : BivariateRatPolynomial) :
    evalRatAt (normalizedCellPoint i j)
        (normalizedEquationPolynomial k * P) = 0 ∧
      (reducedMatchingRight k i j : ℚ) *
          evalRatAt (normalizedCellPoint i j)
            (MvPolynomial.pderiv 0 (normalizedEquationPolynomial k * P)) +
        (normalizedDirectionCoefficient k i j : ℚ) *
          evalRatAt (normalizedCellPoint i j)
            (MvPolynomial.pderiv 1 (normalizedEquationPolynomial k * P)) = 0 := by
  have hE := evalRatAt_normalizedEquationPolynomial_at_cell hi hj
  have hDX := evalRatAt_pderiv_normalizedEquationPolynomial_X_at_cell hi hj
  have hDY := evalRatAt_pderiv_normalizedEquationPolynomial_Y_at_cell
    (j := j) hi
  have hdir :
      (reducedMatchingRight k i j : ℚ) *
            (normalizedEquationDXAtCell k i j : ℚ) +
          (normalizedDirectionCoefficient k i j : ℚ) *
            (normalizedEquationDYAtCell k i : ℚ) = 0 := by
    exact_mod_cast normalizedEquation_directional_at_cell hi hj
  constructor
  · rw [map_mul, hE, zero_mul]
  · simp only [MvPolynomial.pderiv_mul, map_add, map_mul]
    rw [hE, hDX, hDY]
    calc
      (reducedMatchingRight k i j : ℚ) *
              ((normalizedEquationDXAtCell k i j : ℚ) *
                evalRatAt (normalizedCellPoint i j) P +
                0 * evalRatAt (normalizedCellPoint i j)
                  (MvPolynomial.pderiv 0 P)) +
            (normalizedDirectionCoefficient k i j : ℚ) *
              ((normalizedEquationDYAtCell k i : ℚ) *
                evalRatAt (normalizedCellPoint i j) P +
                0 * evalRatAt (normalizedCellPoint i j)
                  (MvPolynomial.pderiv 1 P)) =
          ((reducedMatchingRight k i j : ℚ) *
                (normalizedEquationDXAtCell k i j : ℚ) +
              (normalizedDirectionCoefficient k i j : ℚ) *
                (normalizedEquationDYAtCell k i : ℚ)) *
            evalRatAt (normalizedCellPoint i j) P := by ring
      _ = 0 := by rw [hdir]; ring

/-- Exact actual-polynomial countermodel: the constant cofactor `P=1`
satisfies every full-grid first-order jet after multiplication by `E`, yet
its value is identically one at every specialization. -/
theorem normalizedEquationPolynomial_full_grid_jet_countermodel (k : ℕ) :
    ∃ P : BivariateRatPolynomial,
      (∀ i ∈ Finset.Icc 1 k, ∀ j ∈ Finset.Icc 1 k,
        evalRatAt (normalizedCellPoint i j)
            (normalizedEquationPolynomial k * P) = 0 ∧
          (reducedMatchingRight k i j : ℚ) *
              evalRatAt (normalizedCellPoint i j)
                (MvPolynomial.pderiv 0
                  (normalizedEquationPolynomial k * P)) +
            (normalizedDirectionCoefficient k i j : ℚ) *
              evalRatAt (normalizedCellPoint i j)
                (MvPolynomial.pderiv 1
                  (normalizedEquationPolynomial k * P)) = 0) ∧
        ∀ p : Fin 2 → ℚ, evalRatAt p P = 1 := by
  refine ⟨1, ?_, ?_⟩
  · intro i hi j hj
    exact normalizedEquationPolynomial_multiple_cell_jet_zero hi hj 1
  · intro p
    simp

/-- Actual polynomial form of the target base-locus statement. -/
theorem normalizedEquationPolynomial_at_target
    {k n d : ℕ}
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    evalRatAt (fun t => if t = 0 then (-(n : ℤ) : ℚ)
        else (-(d : ℤ) : ℚ)) (normalizedEquationPolynomial k) = 0 := by
  calc
    evalRatAt (fun t => if t = 0 then (-(n : ℤ) : ℚ)
        else (-(d : ℤ) : ℚ)) (normalizedEquationPolynomial k) =
        (normalizedEquationValue k (-(n : ℤ)) (-(d : ℤ)) : ℚ) :=
      evalRatAt_normalizedEquationPolynomial_int k (-(n : ℤ)) (-(d : ℤ))
    _ = 0 := by exact_mod_cast normalizedEquationValue_at_target heq

/-- Combined dense-branch countermodel at the arithmetic target.  Under the
block equation, `E*1` satisfies every full-grid value/tangent jet and
vanishes at `(-n,-d)`, while its cofactor still evaluates to one there. -/
theorem normalizedEquationPolynomial_target_full_grid_countermodel
    {k n d : ℕ}
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    ∃ P : BivariateRatPolynomial,
      (∀ i ∈ Finset.Icc 1 k, ∀ j ∈ Finset.Icc 1 k,
        evalRatAt (normalizedCellPoint i j)
            (normalizedEquationPolynomial k * P) = 0 ∧
          (reducedMatchingRight k i j : ℚ) *
              evalRatAt (normalizedCellPoint i j)
                (MvPolynomial.pderiv 0
                  (normalizedEquationPolynomial k * P)) +
            (normalizedDirectionCoefficient k i j : ℚ) *
              evalRatAt (normalizedCellPoint i j)
                (MvPolynomial.pderiv 1
                  (normalizedEquationPolynomial k * P)) = 0) ∧
      evalRatAt (fun t => if t = 0 then (-(n : ℤ) : ℚ)
          else (-(d : ℤ) : ℚ))
        (normalizedEquationPolynomial k * P) = 0 ∧
      evalRatAt (fun t => if t = 0 then (-(n : ℤ) : ℚ)
          else (-(d : ℤ) : ℚ)) P = 1 := by
  refine ⟨1, ?_, ?_, ?_⟩
  · intro i hi j hj
    exact normalizedEquationPolynomial_multiple_cell_jet_zero hi hj 1
  · rw [map_mul, normalizedEquationPolynomial_at_target heq, zero_mul]
  · simp

/-- Dense-branch no-go in the already banked equation-multiple-space
interface: every bounded multiple vanishes at the arithmetic target, while
the constant cofactor has value one. -/
theorem degreeBounded_normalizedEquationMultiples_target_noGo
    {k n d : ℕ}
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    (∀ F ∈ degreeBoundedEquationMultipleSpace k
        (normalizedEquationPolynomial k),
      evalRatAt (fun t => if t = 0 then (-(n : ℤ) : ℚ)
        else (-(d : ℤ) : ℚ)) F = 0) ∧
      evalRatAt (fun _ => (0 : ℚ)) (1 : BivariateRatPolynomial) = 1 := by
  constructor
  · intro F hF
    exact degreeBoundedEquationMultipleSpace_specialization_vanishes hF
      (normalizedEquationPolynomial_at_target heq)
  · simp

#print axioms normalizedEquationValue_at_cell
#print axioms normalizedEquation_directional_at_cell
#print axioms normalizedEquation_multiple_cell_jet_zero
#print axioms normalizedEquation_cell_jets_do_not_force_cofactor_divisibility
#print axioms gridRootProduct_neg_nat
#print axioms normalizedEquationValue_at_target
#print axioms evalRatAt_normalizedEquationPolynomial_int
#print axioms evalRatAt_pderiv_normalizedEquationPolynomial_X_at_cell
#print axioms evalRatAt_pderiv_normalizedEquationPolynomial_Y_at_cell
#print axioms normalizedEquationPolynomial_directional_pderiv_at_cell
#print axioms normalizedEquationPolynomial_multiple_cell_jet_zero
#print axioms normalizedEquationPolynomial_full_grid_jet_countermodel
#print axioms normalizedEquationPolynomial_at_target
#print axioms normalizedEquationPolynomial_target_full_grid_countermodel
#print axioms degreeBounded_normalizedEquationMultiples_target_noGo

end Erdos686Variant
end Erdos686
