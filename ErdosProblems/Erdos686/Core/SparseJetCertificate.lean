/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.Core.JetCompressionArithmetic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Bool.AllAny

/-!
# Erdős 686: sparse integral jet-certificate algebra

Concrete puncture certificates are emitted as sparse lists of integral
bivariate monomials.  This module provides the generic kernel lemmas needed
to interpret those lists:

* a polynomial whose shifted monomials all have total order at least `mu`
  evaluates to a multiple of `A^mu` whenever `A` divides both local
  coordinates;
* evaluation is bounded by the coefficient `l1` norm times a supplied
  monomial envelope.

The generated files therefore only need finite coefficient identities and
ordinary arithmetic checks.
-/

namespace Erdos686
namespace Erdos686Variant

structure SparseBivariateTerm where
  coefficient : ℤ
  xExponent : ℕ
  yExponent : ℕ
deriving DecidableEq, Repr

def SparseBivariateTerm.eval
    (term : SparseBivariateTerm) (x y : ℕ) : ℤ :=
  term.coefficient * (x : ℤ) ^ term.xExponent * (y : ℤ) ^ term.yExponent

def SparseBivariateTerm.evalInt
    (term : SparseBivariateTerm) (x y : ℤ) : ℤ :=
  term.coefficient * x ^ term.xExponent * y ^ term.yExponent

def sparseBivariateEval
    (terms : List SparseBivariateTerm) (x y : ℕ) : ℤ :=
  (terms.map fun term => term.eval x y).sum

def sparseBivariateEvalInt
    (terms : List SparseBivariateTerm) (x y : ℤ) : ℤ :=
  (terms.map fun term => term.evalInt x y).sum

@[simp]
theorem sparseBivariateEvalInt_natCast
    (terms : List SparseBivariateTerm) (x y : ℕ) :
    sparseBivariateEvalInt terms (x : ℤ) (y : ℤ) =
      sparseBivariateEval terms x y := by
  induction terms with
  | nil =>
      simp [sparseBivariateEvalInt, sparseBivariateEval]
  | cons term terms ih =>
      simp [sparseBivariateEvalInt, sparseBivariateEval,
        SparseBivariateTerm.evalInt, SparseBivariateTerm.eval, ih]

def sparseBivariateL1Norm
    (terms : List SparseBivariateTerm) : ℕ :=
  (terms.map fun term => term.coefficient.natAbs).sum

def sparseBivariateOrderAtLeast
    (mu : ℕ) (terms : List SparseBivariateTerm) : Prop :=
  ∀ term ∈ terms, mu ≤ term.xExponent + term.yExponent

def sparseBivariateDegreeAtMost
    (r : ℕ) (terms : List SparseBivariateTerm) : Prop :=
  ∀ term ∈ terms, term.xExponent + term.yExponent ≤ r

abbrev BivariateIntPolynomial := MvPolynomial (Fin 2) ℤ

/-- A decidable total-order condition on the actual support of a bivariate
integral polynomial.  This is the compact condition checked by generated
puncture certificates. -/
def mvBivariateOrderAtLeast
    (mu : ℕ) (P : BivariateIntPolynomial) : Prop :=
  P.support.toList.all fun exponent =>
    mu ≤ exponent 0 + exponent 1

noncomputable def SparseBivariateTerm.toMvPolynomial
    (term : SparseBivariateTerm) : BivariateIntPolynomial :=
  MvPolynomial.C term.coefficient *
    MvPolynomial.X 0 ^ term.xExponent *
    MvPolynomial.X 1 ^ term.yExponent

noncomputable def sparseToMvPolynomial
    (terms : List SparseBivariateTerm) : BivariateIntPolynomial :=
  (terms.map SparseBivariateTerm.toMvPolynomial).sum

/-- The exponent pair `(a,b)` as a finitely supported function on two
variables. -/
noncomputable def bivariateExponent (a b : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 a + Finsupp.single 1 b

@[simp]
theorem bivariateExponent_apply_zero (a b : ℕ) :
    bivariateExponent a b 0 = a := by
  simp [bivariateExponent]

@[simp]
theorem bivariateExponent_apply_one (a b : ℕ) :
    bivariateExponent a b 1 = b := by
  simp [bivariateExponent]

theorem bivariateExponent_eq_iff
    {a b c d : ℕ} :
    bivariateExponent a b = bivariateExponent c d ↔
      a = c ∧ b = d := by
  constructor
  · intro h
    constructor
    · have := DFunLike.congr_fun h 0
      simpa using this
    · have := DFunLike.congr_fun h 1
      simpa using this
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Sum of the coefficients attached to one exponent pair in a possibly
unnormalized sparse list. -/
def sparseCoefficientAt
    (a b : ℕ) (terms : List SparseBivariateTerm) : ℤ :=
  (terms.map fun term =>
    if term.xExponent = a ∧ term.yExponent = b then
      term.coefficient
    else
      0).sum

theorem SparseBivariateTerm.toMvPolynomial_eq_monomial
    (term : SparseBivariateTerm) :
    term.toMvPolynomial =
      MvPolynomial.monomial
        (bivariateExponent term.xExponent term.yExponent)
        term.coefficient := by
  rw [SparseBivariateTerm.toMvPolynomial,
    MvPolynomial.C_mul_X_pow_eq_monomial]
  rw [← MvPolynomial.monomial_add_single]
  rfl

theorem sparseToMvPolynomial_coeff
    (terms : List SparseBivariateTerm) (a b : ℕ) :
    (sparseToMvPolynomial terms).coeff (bivariateExponent a b) =
      sparseCoefficientAt a b terms := by
  induction terms with
  | nil =>
      simp [sparseToMvPolynomial, sparseCoefficientAt]
  | cons term terms ih =>
      change
        (term.toMvPolynomial + sparseToMvPolynomial terms).coeff
            (bivariateExponent a b) =
          (if term.xExponent = a ∧ term.yExponent = b then
            term.coefficient
          else
            0) + sparseCoefficientAt a b terms
      rw [MvPolynomial.coeff_add,
        SparseBivariateTerm.toMvPolynomial_eq_monomial,
        MvPolynomial.coeff_monomial, ih]
      simp [bivariateExponent_eq_iff, and_comm]

/-- Insert one monomial into a sparse polynomial, combining the first
monomial with the same exponent pair.  `sparseNormalize` folds this operation
over a list whose tail is already normalized. -/
def sparseInsertTerm
    (term : SparseBivariateTerm) :
    List SparseBivariateTerm → List SparseBivariateTerm
  | [] => [term]
  | head :: tail =>
      if term.xExponent = head.xExponent ∧
          term.yExponent = head.yExponent then
        { coefficient := term.coefficient + head.coefficient
          xExponent := head.xExponent
          yExponent := head.yExponent } :: tail
      else
        head :: sparseInsertTerm term tail

def sparseNormalize
    (terms : List SparseBivariateTerm) : List SparseBivariateTerm :=
  terms.foldr sparseInsertTerm []

/-- Lexicographic comparison of exponent pairs.  Sorting before coefficient
combination keeps generated kernel checks balanced instead of building the
quadratic-depth insertion-normalization term. -/
def sparseTermExponentLE
    (left right : SparseBivariateTerm) : Bool :=
  decide
    (left.xExponent < right.xExponent ∨
      (left.xExponent = right.xExponent ∧
        left.yExponent ≤ right.yExponent))

def sparseCombineSortedAux
    (current : SparseBivariateTerm) :
    List SparseBivariateTerm → List SparseBivariateTerm
  | [] => [current]
  | head :: tail =>
      if current.xExponent = head.xExponent ∧
          current.yExponent = head.yExponent then
        sparseCombineSortedAux
          { coefficient := current.coefficient + head.coefficient
            xExponent := current.xExponent
            yExponent := current.yExponent }
          tail
      else
        current :: sparseCombineSortedAux head tail

def sparseCombineSorted :
    List SparseBivariateTerm → List SparseBivariateTerm
  | [] => []
  | head :: tail => sparseCombineSortedAux head tail

def sparseSortNormalize
    (terms : List SparseBivariateTerm) : List SparseBivariateTerm :=
  sparseCombineSorted
    (terms.mergeSort sparseTermExponentLE)

def SparseBivariateTerm.mul
    (left right : SparseBivariateTerm) : SparseBivariateTerm where
  coefficient := left.coefficient * right.coefficient
  xExponent := left.xExponent + right.xExponent
  yExponent := left.yExponent + right.yExponent

def sparseBivariateNeg
    (terms : List SparseBivariateTerm) : List SparseBivariateTerm :=
  terms.map fun term =>
    { term with coefficient := -term.coefficient }

def sparseBivariateAdd
    (left right : List SparseBivariateTerm) : List SparseBivariateTerm :=
  left ++ right

def sparseBivariateSub
    (left right : List SparseBivariateTerm) : List SparseBivariateTerm :=
  sparseBivariateAdd left (sparseBivariateNeg right)

def sparseBivariateMul
    (left right : List SparseBivariateTerm) : List SparseBivariateTerm :=
  left.flatMap fun leftTerm =>
    right.map fun rightTerm => leftTerm.mul rightTerm

def sparseBivariateScale
    (coefficient : ℤ)
    (terms : List SparseBivariateTerm) : List SparseBivariateTerm :=
  terms.map fun term =>
    { term with coefficient := coefficient * term.coefficient }

def sparseXAffinePower
    (offset : ℤ) (exponent : ℕ) : List SparseBivariateTerm :=
  (List.range (exponent + 1)).map fun degree =>
    { coefficient :=
        (exponent.choose degree : ℤ) * offset ^ (exponent - degree)
      xExponent := degree
      yExponent := 0 }

def sparseYAffinePower
    (offset : ℤ) (exponent : ℕ) : List SparseBivariateTerm :=
  (List.range (exponent + 1)).map fun degree =>
    { coefficient :=
        (exponent.choose degree : ℤ) * offset ^ (exponent - degree)
      xExponent := 0
      yExponent := degree }

def SparseBivariateTerm.shift
    (term : SparseBivariateTerm) (xOffset yOffset : ℤ) :
    List SparseBivariateTerm :=
  sparseBivariateScale term.coefficient
    (sparseBivariateMul
      (sparseXAffinePower xOffset term.xExponent)
      (sparseYAffinePower yOffset term.yExponent))

def sparseBivariateShift
    (terms : List SparseBivariateTerm) (xOffset yOffset : ℤ) :
    List SparseBivariateTerm :=
  terms.flatMap fun term => term.shift xOffset yOffset

/-- One Taylor coefficient of a shifted monomial, computed without expanding
the full affine powers. -/
def SparseBivariateTerm.shiftCoefficient
    (term : SparseBivariateTerm)
    (xOffset yOffset : ℤ) (a b : ℕ) : ℤ :=
  if a ≤ term.xExponent ∧ b ≤ term.yExponent then
    term.coefficient *
      (term.xExponent.choose a : ℤ) *
      xOffset ^ (term.xExponent - a) *
      (term.yExponent.choose b : ℤ) *
      yOffset ^ (term.yExponent - b)
  else
    0

/-- One Taylor coefficient of a shifted sparse polynomial.  This traverses
the original sparse support and never constructs the full shifted list. -/
def sparseShiftCoefficientAt
    (terms : List SparseBivariateTerm)
    (xOffset yOffset : ℤ) (a b : ℕ) : ℤ :=
  (terms.map fun term =>
    term.shiftCoefficient xOffset yOffset a b).sum

private theorem int_sum_map_flatMap
    {α β : Type*} (terms : List α)
    (f : α → List β) (g : β → ℤ) :
    ((terms.flatMap f).map g).sum =
      (terms.map fun term => ((f term).map g).sum).sum := by
  induction terms with
  | nil =>
      simp
  | cons term terms ih =>
      simp [ih, add_assoc]

private theorem int_sum_range_ite_eq
    (n a : ℕ) (f : ℕ → ℤ) :
    ((List.range n).map fun i =>
      if i = a then f i else 0).sum =
        if a < n then f a else 0 := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih]
      by_cases han : a < n
      · have hne : n ≠ a := by omega
        simp [han, hne, Nat.lt.step han]
      · by_cases hea : n = a
        · subst a
          simp
        · have hnot : ¬a < n + 1 := by omega
          simp [han, hea, hnot]

theorem sparseCoefficientAt_scale
    (coefficient : ℤ) (terms : List SparseBivariateTerm)
    (a b : ℕ) :
    sparseCoefficientAt a b
        (sparseBivariateScale coefficient terms) =
      coefficient * sparseCoefficientAt a b terms := by
  unfold sparseBivariateScale sparseCoefficientAt
  simp only [List.map_map, Function.comp_apply]
  rw [← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro term _
  by_cases h : term.xExponent = a ∧ term.yExponent = b
  · simp [h]
  · simp [h]

private theorem int_sum_double_range_ite_eq
    (nx ny a b : ℕ) (f : ℕ → ℕ → ℤ) :
    ((List.range nx).map fun i =>
      ((List.range ny).map fun j =>
        if i = a ∧ j = b then f i j else 0).sum).sum =
        if a < nx ∧ b < ny then f a b else 0 := by
  have hinner : ∀ i,
      ((List.range ny).map fun j =>
        if i = a ∧ j = b then f i j else 0).sum =
          if i = a then
            (if b < ny then f i b else 0)
          else
            0 := by
    intro i
    by_cases hia : i = a
    · subst i
      simpa using int_sum_range_ite_eq ny b (fun j => f a j)
    · simp [hia]
  simp_rw [hinner]
  rw [int_sum_range_ite_eq]
  by_cases hax : a < nx
  · by_cases hby : b < ny
    · simp [hax, hby]
    · simp [hax, hby]
  · simp [hax]

private theorem sparseCoefficientAt_mul_affinePowers
    (xOffset yOffset : ℤ)
    (xExponent yExponent a b : ℕ) :
    sparseCoefficientAt a b
        (sparseBivariateMul
          (sparseXAffinePower xOffset xExponent)
          (sparseYAffinePower yOffset yExponent)) =
      if a ≤ xExponent ∧ b ≤ yExponent then
        (xExponent.choose a : ℤ) *
          xOffset ^ (xExponent - a) *
          (yExponent.choose b : ℤ) *
          yOffset ^ (yExponent - b)
      else
        0 := by
  unfold sparseBivariateMul sparseXAffinePower
    sparseYAffinePower sparseCoefficientAt
  rw [int_sum_map_flatMap]
  simp only [List.map_map]
  simp only [Function.comp_def, SparseBivariateTerm.mul,
    Nat.add_zero, Nat.zero_add]
  change
    ((List.range (xExponent + 1)).map fun i =>
      ((List.range (yExponent + 1)).map fun j =>
        if i = a ∧ j = b then
          ((xExponent.choose i : ℤ) *
              xOffset ^ (xExponent - i)) *
            ((yExponent.choose j : ℤ) *
              yOffset ^ (yExponent - j))
        else
          0).sum).sum =
      if a ≤ xExponent ∧ b ≤ yExponent then
        (xExponent.choose a : ℤ) *
          xOffset ^ (xExponent - a) *
          (yExponent.choose b : ℤ) *
          yOffset ^ (yExponent - b)
      else
        0
  rw [int_sum_double_range_ite_eq]
  by_cases hxa : a ≤ xExponent
  · have hax : a < xExponent + 1 := by omega
    by_cases hyb : b ≤ yExponent
    · have hby : b < yExponent + 1 := by omega
      simp [hxa, hyb, hax, hby]
      ring
    · have hby : ¬b < yExponent + 1 := by omega
      simp [hxa, hyb, hax, hby]
  · have hax : ¬a < xExponent + 1 := by omega
    simp [hxa, hax]

theorem sparseCoefficientAt_term_shift
    (term : SparseBivariateTerm)
    (xOffset yOffset : ℤ) (a b : ℕ) :
    sparseCoefficientAt a b (term.shift xOffset yOffset) =
      term.shiftCoefficient xOffset yOffset a b := by
  rw [SparseBivariateTerm.shift, sparseCoefficientAt_scale,
    sparseCoefficientAt_mul_affinePowers]
  unfold SparseBivariateTerm.shiftCoefficient
  split_ifs <;> ring

theorem sparseCoefficientAt_shift
    (terms : List SparseBivariateTerm)
    (xOffset yOffset : ℤ) (a b : ℕ) :
    sparseCoefficientAt a b
        (sparseBivariateShift terms xOffset yOffset) =
      sparseShiftCoefficientAt terms xOffset yOffset a b := by
  unfold sparseBivariateShift sparseCoefficientAt
    sparseShiftCoefficientAt
  rw [int_sum_map_flatMap]
  congr 1
  apply List.map_congr_left
  intro term _
  exact sparseCoefficientAt_term_shift term xOffset yOffset a b

theorem sparseCoefficientAt_neg
    (terms : List SparseBivariateTerm) (a b : ℕ) :
    sparseCoefficientAt a b (sparseBivariateNeg terms) =
      -sparseCoefficientAt a b terms := by
  have hneg :
      sparseBivariateNeg terms =
        sparseBivariateScale (-1) terms := by
    induction terms with
    | nil =>
        rfl
    | cons term terms ih =>
        simp [sparseBivariateNeg, sparseBivariateScale, ih]
  rw [hneg, sparseCoefficientAt_scale]
  ring

theorem sparseCoefficientAt_add
    (left right : List SparseBivariateTerm) (a b : ℕ) :
    sparseCoefficientAt a b (sparseBivariateAdd left right) =
      sparseCoefficientAt a b left +
        sparseCoefficientAt a b right := by
  simp [sparseBivariateAdd, sparseCoefficientAt]

theorem sparseCoefficientAt_sub
    (left right : List SparseBivariateTerm) (a b : ℕ) :
    sparseCoefficientAt a b (sparseBivariateSub left right) =
      sparseCoefficientAt a b left -
        sparseCoefficientAt a b right := by
  rw [sparseBivariateSub, sparseCoefficientAt_add,
    sparseCoefficientAt_neg]
  ring

private theorem sparseCoefficientAt_mul_leftTerm
    (leftTerm : SparseBivariateTerm)
    (right : List SparseBivariateTerm) (a b : ℕ) :
    sparseCoefficientAt a b
        (right.map fun rightTerm => leftTerm.mul rightTerm) =
      if leftTerm.xExponent ≤ a ∧ leftTerm.yExponent ≤ b then
        leftTerm.coefficient *
          sparseCoefficientAt
            (a - leftTerm.xExponent)
            (b - leftTerm.yExponent) right
      else
        0 := by
  unfold sparseCoefficientAt
  rw [List.map_map]
  simp only [Function.comp_def, SparseBivariateTerm.mul]
  by_cases hleft :
      leftTerm.xExponent ≤ a ∧ leftTerm.yExponent ≤ b
  · have hpoint :
        (right.map fun rightTerm =>
          if leftTerm.xExponent + rightTerm.xExponent = a ∧
              leftTerm.yExponent + rightTerm.yExponent = b then
            leftTerm.coefficient * rightTerm.coefficient
          else
            0) =
          right.map fun rightTerm =>
            leftTerm.coefficient *
              (if rightTerm.xExponent =
                    a - leftTerm.xExponent ∧
                  rightTerm.yExponent =
                    b - leftTerm.yExponent then
                rightTerm.coefficient
              else
                0) := by
        apply List.map_congr_left
        intro rightTerm _
        by_cases hright :
            rightTerm.xExponent =
                a - leftTerm.xExponent ∧
              rightTerm.yExponent =
                b - leftTerm.yExponent
        · have hsum :
              leftTerm.xExponent + rightTerm.xExponent = a ∧
                leftTerm.yExponent + rightTerm.yExponent = b := by
            omega
          rw [if_pos hsum, if_pos hright]
        · have hsum :
              ¬(leftTerm.xExponent + rightTerm.xExponent = a ∧
                leftTerm.yExponent + rightTerm.yExponent = b) := by
            omega
          rw [if_neg hsum, if_neg hright]
          ring
    rw [hpoint, List.sum_map_mul_left]
    simp [hleft]
  · have hpoint :
        (right.map fun rightTerm =>
          if leftTerm.xExponent + rightTerm.xExponent = a ∧
              leftTerm.yExponent + rightTerm.yExponent = b then
            leftTerm.coefficient * rightTerm.coefficient
          else
            0) =
          right.map fun _ => (0 : ℤ) := by
        apply List.map_congr_left
        intro rightTerm _
        have hsum :
            ¬(leftTerm.xExponent + rightTerm.xExponent = a ∧
              leftTerm.yExponent + rightTerm.yExponent = b) := by
          omega
        simp [hsum]
    rw [hpoint]
    simp [hleft]

private theorem sparseCoefficientAt_flatMap
    {α : Type*} (terms : List α)
    (f : α → List SparseBivariateTerm) (a b : ℕ) :
    sparseCoefficientAt a b (terms.flatMap f) =
      (terms.map fun term =>
        sparseCoefficientAt a b (f term)).sum := by
  unfold sparseCoefficientAt
  exact int_sum_map_flatMap terms f
    (fun term =>
      if term.xExponent = a ∧ term.yExponent = b then
        term.coefficient
      else
        0)

/-- One coefficient of a product whose right factor is shifted.  This avoids
constructing either the shifted right support or the product support. -/
def sparseMulShiftCoefficientAt
    (left right : List SparseBivariateTerm)
    (xOffset yOffset : ℤ) (a b : ℕ) : ℤ :=
  (left.map fun leftTerm =>
    if leftTerm.xExponent ≤ a ∧ leftTerm.yExponent ≤ b then
      leftTerm.coefficient *
        sparseShiftCoefficientAt right xOffset yOffset
          (a - leftTerm.xExponent)
          (b - leftTerm.yExponent)
    else
      0).sum

theorem sparseCoefficientAt_mul_shift
    (left right : List SparseBivariateTerm)
    (xOffset yOffset : ℤ) (a b : ℕ) :
    sparseCoefficientAt a b
        (sparseBivariateMul left
          (sparseBivariateShift right xOffset yOffset)) =
      sparseMulShiftCoefficientAt left right
        xOffset yOffset a b := by
  unfold sparseBivariateMul
  rw [sparseCoefficientAt_flatMap]
  unfold sparseMulShiftCoefficientAt
  congr 1
  apply List.map_congr_left
  intro leftTerm _
  rw [sparseCoefficientAt_mul_leftTerm]
  split_ifs
  · rw [sparseCoefficientAt_shift]
  · rfl

/-- A compact finite checker for the Taylor coefficients below total degree
`mu`.  Only the large section is traversed by the direct shift recurrence;
the quotient-times-curve side uses the matching direct convolution. -/
def sparseLocalTaylorCheck
    (mu : ℕ)
    (sectionTerms quotient curveTerms : List SparseBivariateTerm)
    (xOffset yOffset : ℤ) : Bool :=
  (List.range mu).all fun a =>
    (List.range (mu - a)).all fun b =>
      decide (
        sparseShiftCoefficientAt sectionTerms xOffset yOffset a b =
          sparseMulShiftCoefficientAt quotient curveTerms
            xOffset yOffset a b)

/-- One total-degree checker row, with the first exponent fixed. -/
def sparseLocalTaylorRowCheck
    (mu a : ℕ)
    (sectionTerms quotient curveTerms : List SparseBivariateTerm)
    (xOffset yOffset : ℤ) : Bool :=
  (List.range (mu - a)).all fun b =>
    decide (
      sparseShiftCoefficientAt sectionTerms xOffset yOffset a b =
        sparseMulShiftCoefficientAt quotient curveTerms
          xOffset yOffset a b)

def SparseLocalTaylorRowsCertificate
    (mu : ℕ)
    (sectionTerms quotient curveTerms : List SparseBivariateTerm)
    (xOffset yOffset : ℤ) : Prop :=
  ∀ a < mu,
    sparseLocalTaylorRowCheck mu a sectionTerms quotient curveTerms
      xOffset yOffset = true

theorem sparseLocalTaylorRowCheck_eq
    {mu a : ℕ}
    {sectionTerms quotient curveTerms : List SparseBivariateTerm}
    {xOffset yOffset : ℤ}
    (hcheck :
      sparseLocalTaylorRowCheck mu a
        sectionTerms quotient curveTerms xOffset yOffset = true)
    {b : ℕ}
    (hdegree : a + b < mu) :
    sparseShiftCoefficientAt sectionTerms xOffset yOffset a b =
      sparseMulShiftCoefficientAt quotient curveTerms
        xOffset yOffset a b := by
  have hb : b < mu - a := by omega
  have hab :=
    List.all_eq_true.mp hcheck b (List.mem_range.mpr hb)
  exact of_decide_eq_true hab

theorem sparseLocalTaylorCheck_eq
    {mu : ℕ}
    {sectionTerms quotient curveTerms : List SparseBivariateTerm}
    {xOffset yOffset : ℤ}
    (hcheck :
      sparseLocalTaylorCheck mu sectionTerms quotient curveTerms
        xOffset yOffset = true)
    {a b : ℕ}
    (hdegree : a + b < mu) :
    sparseShiftCoefficientAt sectionTerms xOffset yOffset a b =
      sparseMulShiftCoefficientAt quotient curveTerms
        xOffset yOffset a b := by
  have ha : a < mu := by omega
  have hb : b < mu - a := by omega
  have haAll :=
    List.all_eq_true.mp hcheck a (List.mem_range.mpr ha)
  have hab :=
    List.all_eq_true.mp haAll b (List.mem_range.mpr hb)
  exact of_decide_eq_true hab

theorem mvBivariateOrderAtLeast_of_low_coefficients_zero
    {mu : ℕ} {P : BivariateIntPolynomial}
    (hzero :
      ∀ a b : ℕ, a + b < mu →
        P.coeff (bivariateExponent a b) = 0) :
    mvBivariateOrderAtLeast mu P := by
  apply List.all_iff_forall_prop.mpr
  intro exponent hexponent
  by_contra hdegree
  have hlt : exponent 0 + exponent 1 < mu := by omega
  have hexponentEq :
      exponent =
        bivariateExponent (exponent 0) (exponent 1) := by
    ext index
    fin_cases index <;> simp [bivariateExponent]
  have hcoeff :
      P.coeff exponent = 0 := by
    rw [hexponentEq]
    exact hzero (exponent 0) (exponent 1) hlt
  exact (MvPolynomial.mem_support_iff.mp
    (by simpa using hexponent)) hcoeff

theorem sparseLocalTaylorCheck_order
    {mu : ℕ}
    {sectionTerms quotient curveTerms : List SparseBivariateTerm}
    {xOffset yOffset : ℤ}
    (hcheck :
      sparseLocalTaylorCheck mu sectionTerms quotient curveTerms
        xOffset yOffset = true) :
    mvBivariateOrderAtLeast mu
      (sparseToMvPolynomial
        (sparseBivariateSub
          (sparseBivariateShift sectionTerms xOffset yOffset)
          (sparseBivariateMul quotient
            (sparseBivariateShift curveTerms xOffset yOffset)))) := by
  apply mvBivariateOrderAtLeast_of_low_coefficients_zero
  intro a b hdegree
  rw [sparseToMvPolynomial_coeff, sparseCoefficientAt_sub,
    sparseCoefficientAt_shift, sparseCoefficientAt_mul_shift]
  rw [sparseLocalTaylorCheck_eq hcheck hdegree]
  ring

theorem sparseLocalTaylorRowsCertificate_order
    {mu : ℕ}
    {sectionTerms quotient curveTerms : List SparseBivariateTerm}
    {xOffset yOffset : ℤ}
    (hrows :
      SparseLocalTaylorRowsCertificate mu
        sectionTerms quotient curveTerms xOffset yOffset) :
    mvBivariateOrderAtLeast mu
      (sparseToMvPolynomial
        (sparseBivariateSub
          (sparseBivariateShift sectionTerms xOffset yOffset)
          (sparseBivariateMul quotient
            (sparseBivariateShift curveTerms xOffset yOffset)))) := by
  apply mvBivariateOrderAtLeast_of_low_coefficients_zero
  intro a b hdegree
  rw [sparseToMvPolynomial_coeff, sparseCoefficientAt_sub,
    sparseCoefficientAt_shift, sparseCoefficientAt_mul_shift]
  rw [sparseLocalTaylorRowCheck_eq
    (hrows a (by omega)) hdegree]
  ring

/-- Unlike `sparseBivariateOrderAtLeast`, this condition ignores terms whose
coefficient has normalized to zero. -/
def sparseEffectiveOrderAtLeast
    (mu : ℕ) (terms : List SparseBivariateTerm) : Prop :=
  terms.all fun term =>
    term.coefficient = 0 ∨
      mu ≤ term.xExponent + term.yExponent

def sparseNormalizedOrderAtLeast
    (mu : ℕ) (terms : List SparseBivariateTerm) : Prop :=
  sparseEffectiveOrderAtLeast mu (sparseNormalize terms)

def sparseSortNormalizedOrderAtLeast
    (mu : ℕ) (terms : List SparseBivariateTerm) : Prop :=
  sparseEffectiveOrderAtLeast mu (sparseSortNormalize terms)

def sparseDecidableDegreeAtMost
    (r : ℕ) (terms : List SparseBivariateTerm) : Prop :=
  terms.all fun term =>
    term.xExponent + term.yExponent ≤ r

theorem sparseDegreeAtMost_of_decidable
    {r : ℕ} {terms : List SparseBivariateTerm}
    (hdegree : sparseDecidableDegreeAtMost r terms) :
    sparseBivariateDegreeAtMost r terms :=
  List.all_iff_forall_prop.mp hdegree

/-! ## Executable dense polynomial checker

Large elimination identities are much faster to audit as polynomials in `Y`
whose coefficients are dense polynomials in `X`.  The following elementary
list implementation is fully executable by `native_decide`. -/

abbrev DenseIntPolynomial := List ℤ
abbrev DenseBivariateIntPolynomial := List DenseIntPolynomial

def denseIntEval : DenseIntPolynomial → ℤ → ℤ
  | [], _ => 0
  | coefficient :: coefficients, x =>
      coefficient + x * denseIntEval coefficients x

def denseIntAdd : DenseIntPolynomial → DenseIntPolynomial → DenseIntPolynomial
  | [], right => right
  | left, [] => left
  | a :: left, b :: right => (a + b) :: denseIntAdd left right

def denseIntNeg : DenseIntPolynomial → DenseIntPolynomial
  | [] => []
  | coefficient :: coefficients =>
      (-coefficient) :: denseIntNeg coefficients

def denseIntSub
    (left right : DenseIntPolynomial) : DenseIntPolynomial :=
  denseIntAdd left (denseIntNeg right)

def denseIntScale
    (coefficient : ℤ) : DenseIntPolynomial → DenseIntPolynomial
  | [] => []
  | value :: values =>
      (coefficient * value) :: denseIntScale coefficient values

def denseIntMul :
    DenseIntPolynomial → DenseIntPolynomial → DenseIntPolynomial
  | [], _ => []
  | coefficient :: coefficients, right =>
      denseIntAdd (denseIntScale coefficient right)
        (0 :: denseIntMul coefficients right)

def denseIntPow
    (polynomial : DenseIntPolynomial) : ℕ → DenseIntPolynomial
  | 0 => [1]
  | exponent + 1 =>
      denseIntMul polynomial (denseIntPow polynomial exponent)

def denseBivariateEval :
    DenseBivariateIntPolynomial → ℤ → ℤ → ℤ
  | [], _, _ => 0
  | row :: rows, x, y =>
      denseIntEval row x + y * denseBivariateEval rows x y

def denseBivariateAdd :
    DenseBivariateIntPolynomial →
      DenseBivariateIntPolynomial → DenseBivariateIntPolynomial
  | [], right => right
  | left, [] => left
  | row :: left, other :: right =>
      denseIntAdd row other :: denseBivariateAdd left right

def denseBivariateNeg :
    DenseBivariateIntPolynomial → DenseBivariateIntPolynomial
  | [] => []
  | row :: rows =>
      denseIntNeg row :: denseBivariateNeg rows

def denseBivariateSub
    (left right : DenseBivariateIntPolynomial) :
    DenseBivariateIntPolynomial :=
  denseBivariateAdd left (denseBivariateNeg right)

def denseBivariateScaleRow
    (row : DenseIntPolynomial) :
    DenseBivariateIntPolynomial → DenseBivariateIntPolynomial
  | [] => []
  | other :: rows =>
      denseIntMul row other :: denseBivariateScaleRow row rows

def denseBivariateMul :
    DenseBivariateIntPolynomial →
      DenseBivariateIntPolynomial → DenseBivariateIntPolynomial
  | [], _ => []
  | row :: rows, right =>
      denseBivariateAdd (denseBivariateScaleRow row right)
        ([] :: denseBivariateMul rows right)

def denseIntIsZero (polynomial : DenseIntPolynomial) : Prop :=
  polynomial.all fun coefficient => coefficient = 0

def denseBivariateIsZero
    (polynomial : DenseBivariateIntPolynomial) : Prop :=
  polynomial.all fun row =>
    row.all fun coefficient => coefficient = 0

def denseRowToSparseAux :
    DenseIntPolynomial → ℕ → ℕ → List SparseBivariateTerm
  | [], _, _ => []
  | coefficient :: coefficients, xExponent, yExponent =>
      { coefficient := coefficient
        xExponent := xExponent
        yExponent := yExponent } ::
        denseRowToSparseAux coefficients (xExponent + 1) yExponent

def denseBivariateToSparseAux :
    DenseBivariateIntPolynomial → ℕ → List SparseBivariateTerm
  | [], _ => []
  | row :: rows, yExponent =>
      denseRowToSparseAux row 0 yExponent ++
        denseBivariateToSparseAux rows (yExponent + 1)

def denseBivariateToSparse
    (polynomial : DenseBivariateIntPolynomial) :
    List SparseBivariateTerm :=
  denseBivariateToSparseAux polynomial 0

lemma list_sum_range_binomial
    (x offset : ℤ) (exponent : ℕ) :
    ((List.range (exponent + 1)).map fun degree =>
      x ^ degree * offset ^ (exponent - degree) *
        (exponent.choose degree : ℤ)).sum =
      (x + offset) ^ exponent := by
  simpa using (add_pow x offset exponent).symm

@[simp]
theorem denseIntAdd_eval
    (left right : DenseIntPolynomial) (x : ℤ) :
    denseIntEval (denseIntAdd left right) x =
      denseIntEval left x + denseIntEval right x := by
  induction left generalizing right with
  | nil =>
      simp [denseIntAdd, denseIntEval]
  | cons coefficient coefficients ih =>
      cases right with
      | nil =>
          simp [denseIntAdd, denseIntEval]
      | cons other others =>
          simp [denseIntAdd, denseIntEval, ih]
          ring

@[simp]
theorem denseIntNeg_eval
    (polynomial : DenseIntPolynomial) (x : ℤ) :
    denseIntEval (denseIntNeg polynomial) x =
      -denseIntEval polynomial x := by
  induction polynomial with
  | nil =>
      simp [denseIntNeg, denseIntEval]
  | cons coefficient coefficients ih =>
      simp [denseIntNeg, denseIntEval, ih]
      ring

@[simp]
theorem denseIntSub_eval
    (left right : DenseIntPolynomial) (x : ℤ) :
    denseIntEval (denseIntSub left right) x =
      denseIntEval left x - denseIntEval right x := by
  simp [denseIntSub, sub_eq_add_neg]

@[simp]
theorem denseIntScale_eval
    (coefficient : ℤ) (polynomial : DenseIntPolynomial) (x : ℤ) :
    denseIntEval (denseIntScale coefficient polynomial) x =
      coefficient * denseIntEval polynomial x := by
  induction polynomial with
  | nil =>
      simp [denseIntScale, denseIntEval]
  | cons value values ih =>
      simp [denseIntScale, denseIntEval, ih]
      ring

@[simp]
theorem denseIntMul_eval
    (left right : DenseIntPolynomial) (x : ℤ) :
    denseIntEval (denseIntMul left right) x =
      denseIntEval left x * denseIntEval right x := by
  induction left with
  | nil =>
      simp [denseIntMul, denseIntEval]
  | cons coefficient coefficients ih =>
      simp [denseIntMul, denseIntEval, ih]
      ring

@[simp]
theorem denseIntPow_eval
    (polynomial : DenseIntPolynomial) (exponent : ℕ) (x : ℤ) :
    denseIntEval (denseIntPow polynomial exponent) x =
      denseIntEval polynomial x ^ exponent := by
  induction exponent with
  | zero =>
      simp [denseIntPow, denseIntEval]
  | succ exponent ih =>
      simp [denseIntPow, ih, pow_succ]
      ring

@[simp]
theorem denseBivariateAdd_eval
    (left right : DenseBivariateIntPolynomial) (x y : ℤ) :
    denseBivariateEval (denseBivariateAdd left right) x y =
      denseBivariateEval left x y + denseBivariateEval right x y := by
  induction left generalizing right with
  | nil =>
      simp [denseBivariateAdd, denseBivariateEval]
  | cons row rows ih =>
      cases right with
      | nil =>
          simp [denseBivariateAdd, denseBivariateEval]
      | cons other others =>
          simp [denseBivariateAdd, denseBivariateEval, ih]
          ring

@[simp]
theorem denseBivariateNeg_eval
    (polynomial : DenseBivariateIntPolynomial) (x y : ℤ) :
    denseBivariateEval (denseBivariateNeg polynomial) x y =
      -denseBivariateEval polynomial x y := by
  induction polynomial with
  | nil =>
      simp [denseBivariateNeg, denseBivariateEval]
  | cons row rows ih =>
      simp [denseBivariateNeg, denseBivariateEval, ih]
      ring

@[simp]
theorem denseBivariateSub_eval
    (left right : DenseBivariateIntPolynomial) (x y : ℤ) :
    denseBivariateEval (denseBivariateSub left right) x y =
      denseBivariateEval left x y -
        denseBivariateEval right x y := by
  simp [denseBivariateSub, sub_eq_add_neg]

@[simp]
theorem denseBivariateScaleRow_eval
    (row : DenseIntPolynomial)
    (right : DenseBivariateIntPolynomial) (x y : ℤ) :
    denseBivariateEval (denseBivariateScaleRow row right) x y =
      denseIntEval row x * denseBivariateEval right x y := by
  induction right with
  | nil =>
      simp [denseBivariateScaleRow, denseBivariateEval]
  | cons other others ih =>
      simp [denseBivariateScaleRow, denseBivariateEval, ih]
      ring

@[simp]
theorem denseBivariateMul_eval
    (left right : DenseBivariateIntPolynomial) (x y : ℤ) :
    denseBivariateEval (denseBivariateMul left right) x y =
      denseBivariateEval left x y *
        denseBivariateEval right x y := by
  induction left with
  | nil =>
      simp [denseBivariateMul, denseBivariateEval]
  | cons row rows ih =>
      simp [denseBivariateMul, denseBivariateEval, denseIntEval, ih]
      ring

theorem denseIntEval_eq_zero_of_isZero
    {polynomial : DenseIntPolynomial}
    (hzero : denseIntIsZero polynomial) (x : ℤ) :
    denseIntEval polynomial x = 0 := by
  induction polynomial with
  | nil =>
      simp [denseIntEval]
  | cons coefficient coefficients ih =>
      have hall :
          ∀ value ∈ coefficient :: coefficients, value = 0 :=
        List.all_iff_forall_prop.mp hzero
      have hcoefficient : coefficient = 0 := hall coefficient (by simp)
      have htail : denseIntIsZero coefficients := by
        apply List.all_iff_forall_prop.mpr
        intro value hvalue
        exact hall value (by simp [hvalue])
      simp [denseIntEval, hcoefficient, ih htail]

theorem denseBivariateEval_eq_zero_of_isZero
    {polynomial : DenseBivariateIntPolynomial}
    (hzero : denseBivariateIsZero polynomial) (x y : ℤ) :
    denseBivariateEval polynomial x y = 0 := by
  induction polynomial with
  | nil =>
      simp [denseBivariateEval]
  | cons row rows ih =>
      unfold denseBivariateIsZero at hzero
      simp only [List.all_cons, Bool.and_eq_true] at hzero
      have hrow : denseIntIsZero row := hzero.1
      have htail : denseBivariateIsZero rows := hzero.2
      rw [denseBivariateEval]
      rw [denseIntEval_eq_zero_of_isZero hrow, ih htail]
      ring

lemma denseRowToSparseAux_eval
    (row : DenseIntPolynomial) (xExponent yExponent x y : ℕ) :
    sparseBivariateEval
        (denseRowToSparseAux row xExponent yExponent) x y =
      (x : ℤ) ^ xExponent * (y : ℤ) ^ yExponent *
        denseIntEval row (x : ℤ) := by
  induction row generalizing xExponent with
  | nil =>
      simp [denseRowToSparseAux, sparseBivariateEval, denseIntEval]
  | cons coefficient coefficients ih =>
      change
        coefficient * (x : ℤ) ^ xExponent *
              (y : ℤ) ^ yExponent +
            sparseBivariateEval
              (denseRowToSparseAux coefficients
                (xExponent + 1) yExponent) x y =
          (x : ℤ) ^ xExponent * (y : ℤ) ^ yExponent *
            (coefficient + (x : ℤ) *
              denseIntEval coefficients (x : ℤ))
      rw [ih]
      rw [pow_add, pow_one]
      ring

lemma denseBivariateToSparseAux_eval
    (polynomial : DenseBivariateIntPolynomial)
    (yExponent x y : ℕ) :
    sparseBivariateEval
        (denseBivariateToSparseAux polynomial yExponent) x y =
      (y : ℤ) ^ yExponent *
        denseBivariateEval polynomial (x : ℤ) (y : ℤ) := by
  induction polynomial generalizing yExponent with
  | nil =>
      simp [denseBivariateToSparseAux, sparseBivariateEval,
        denseBivariateEval]
  | cons row rows ih =>
      rw [denseBivariateToSparseAux]
      rw [sparseBivariateEval]
      simp only [List.map_append, List.sum_append]
      change
        sparseBivariateEval
              (denseRowToSparseAux row 0 yExponent) x y +
            sparseBivariateEval
              (denseBivariateToSparseAux rows
                (yExponent + 1)) x y =
          (y : ℤ) ^ yExponent *
            (denseIntEval row (x : ℤ) +
              (y : ℤ) * denseBivariateEval rows (x : ℤ) (y : ℤ))
      rw [denseRowToSparseAux_eval, ih]
      rw [pow_zero, one_mul, pow_add, pow_one]
      ring

@[simp]
theorem denseBivariateToSparse_eval
    (polynomial : DenseBivariateIntPolynomial) (x y : ℕ) :
    sparseBivariateEval (denseBivariateToSparse polynomial) x y =
      denseBivariateEval polynomial (x : ℤ) (y : ℤ) := by
  simpa [denseBivariateToSparse] using
    denseBivariateToSparseAux_eval polynomial 0 x y

theorem denseBivariate_identity_eval
    {left right : DenseBivariateIntPolynomial}
    (hidentity :
      denseBivariateIsZero (denseBivariateSub left right))
    (x y : ℤ) :
    denseBivariateEval left x y =
      denseBivariateEval right x y := by
  have hzero :=
    denseBivariateEval_eq_zero_of_isZero hidentity x y
  rw [denseBivariateSub_eval] at hzero
  linarith

theorem denseBivariate_elimination_eval_zero
    {cofactorSection sectionDense cofactorCurve curveDense
      eliminant : DenseBivariateIntPolynomial}
    (hidentity :
      denseBivariateIsZero
        (denseBivariateSub
          (denseBivariateAdd
            (denseBivariateMul cofactorSection sectionDense)
            (denseBivariateMul cofactorCurve curveDense))
          eliminant))
    {x y : ℤ}
    (hsection : denseBivariateEval sectionDense x y = 0)
    (hcurve : denseBivariateEval curveDense x y = 0) :
    denseBivariateEval eliminant x y = 0 := by
  have hid := denseBivariate_identity_eval hidentity x y
  simp [hsection, hcurve] at hid
  exact hid.symm

theorem denseInt_identity_eval
    {left right : DenseIntPolynomial}
    (hidentity : denseIntIsZero (denseIntSub left right))
    (x : ℤ) :
    denseIntEval left x = denseIntEval right x := by
  have hzero := denseIntEval_eq_zero_of_isZero hidentity x
  rw [denseIntSub_eval] at hzero
  linarith

theorem denseInt_bezout_eval_zero
    {leftCoefficient left rightCoefficient right target :
      DenseIntPolynomial}
    (hidentity :
      denseIntIsZero
        (denseIntSub
          (denseIntAdd
            (denseIntMul leftCoefficient left)
            (denseIntMul rightCoefficient right))
          target))
    {x : ℤ}
    (hleft : denseIntEval left x = 0)
    (hright : denseIntEval right x = 0) :
    denseIntEval target x = 0 := by
  have hid := denseInt_identity_eval hidentity x
  simp [hleft, hright] at hid
  exact hid.symm

@[simp]
theorem sparseToMvPolynomial_eval₂
    (terms : List SparseBivariateTerm) (x y : ℕ) :
    (sparseToMvPolynomial terms).eval₂
        (RingHom.id ℤ) ![(x : ℤ), (y : ℤ)] =
      sparseBivariateEval terms x y := by
  induction terms with
  | nil =>
      simp [sparseToMvPolynomial, sparseBivariateEval]
  | cons term terms ih =>
      change
        (term.toMvPolynomial + sparseToMvPolynomial terms).eval₂
            (RingHom.id ℤ) ![(x : ℤ), (y : ℤ)] =
          term.eval x y + sparseBivariateEval terms x y
      rw [MvPolynomial.eval₂_add, ih]
      simp [SparseBivariateTerm.toMvPolynomial, SparseBivariateTerm.eval,
        mul_assoc]

theorem sparseInsertTerm_eval
    (term : SparseBivariateTerm) (terms : List SparseBivariateTerm)
    (x y : ℕ) :
    sparseBivariateEval (sparseInsertTerm term terms) x y =
      term.eval x y + sparseBivariateEval terms x y := by
  induction terms with
  | nil =>
      simp [sparseInsertTerm, sparseBivariateEval]
  | cons head tail ih =>
      by_cases h :
          term.xExponent = head.xExponent ∧
            term.yExponent = head.yExponent
      · rcases h with ⟨hx, hy⟩
        simp [sparseInsertTerm, hx, hy, sparseBivariateEval,
          SparseBivariateTerm.eval]
        ring
      · simp only [sparseInsertTerm, h, ↓reduceIte,
          sparseBivariateEval, List.map_cons, List.sum_cons]
        change
          head.eval x y +
              sparseBivariateEval (sparseInsertTerm term tail) x y =
            term.eval x y +
              (head.eval x y + sparseBivariateEval tail x y)
        rw [ih]
        ring

@[simp]
theorem sparseNormalize_eval
    (terms : List SparseBivariateTerm) (x y : ℕ) :
    sparseBivariateEval (sparseNormalize terms) x y =
      sparseBivariateEval terms x y := by
  induction terms with
  | nil =>
      simp [sparseNormalize, sparseBivariateEval]
  | cons term terms ih =>
      change
        sparseBivariateEval
            (sparseInsertTerm term (sparseNormalize terms)) x y =
          term.eval x y + sparseBivariateEval terms x y
      rw [sparseInsertTerm_eval, ih]

theorem sparseMergeSort_eval
    (terms : List SparseBivariateTerm) (x y : ℕ) :
    sparseBivariateEval
        (terms.mergeSort sparseTermExponentLE) x y =
      sparseBivariateEval terms x y := by
  unfold sparseBivariateEval
  have hperm :
      ((terms.mergeSort sparseTermExponentLE).map
          fun term => term.eval x y).Perm
        (terms.map fun term => term.eval x y) :=
    (List.mergeSort_perm terms sparseTermExponentLE).map _
  simpa [List.sum_eq_foldr] using hperm.foldr_eq (0 : ℤ)

theorem sparseCombineSortedAux_eval
    (current : SparseBivariateTerm)
    (terms : List SparseBivariateTerm) (x y : ℕ) :
    sparseBivariateEval
        (sparseCombineSortedAux current terms) x y =
      current.eval x y + sparseBivariateEval terms x y := by
  induction terms generalizing current with
  | nil =>
      simp [sparseCombineSortedAux, sparseBivariateEval]
  | cons head tail ih =>
      by_cases h :
          current.xExponent = head.xExponent ∧
            current.yExponent = head.yExponent
      · rcases h with ⟨hx, hy⟩
        simp only [sparseCombineSortedAux, hx, hy, and_self,
          ↓reduceIte]
        rw [ih]
        simp only [sparseBivariateEval, List.map_cons,
          List.sum_cons]
        simp [SparseBivariateTerm.eval, hx, hy]
        ring
      · simp only [sparseCombineSortedAux, h, ↓reduceIte,
          sparseBivariateEval, List.map_cons, List.sum_cons]
        simpa [sparseBivariateEval] using
          congrArg (fun value => current.eval x y + value)
            (ih head)

@[simp]
theorem sparseCombineSorted_eval
    (terms : List SparseBivariateTerm) (x y : ℕ) :
    sparseBivariateEval (sparseCombineSorted terms) x y =
      sparseBivariateEval terms x y := by
  cases terms with
  | nil =>
      simp [sparseCombineSorted, sparseBivariateEval]
  | cons head tail =>
      exact sparseCombineSortedAux_eval head tail x y

@[simp]
theorem sparseSortNormalize_eval
    (terms : List SparseBivariateTerm) (x y : ℕ) :
    sparseBivariateEval (sparseSortNormalize terms) x y =
      sparseBivariateEval terms x y := by
  rw [sparseSortNormalize, sparseCombineSorted_eval,
    sparseMergeSort_eval]

@[simp]
theorem sparseBivariateNeg_eval
    (terms : List SparseBivariateTerm) (x y : ℕ) :
    sparseBivariateEval (sparseBivariateNeg terms) x y =
      -sparseBivariateEval terms x y := by
  induction terms with
  | nil =>
      simp [sparseBivariateNeg, sparseBivariateEval]
  | cons term terms ih =>
      change
        (-term.coefficient) * (x : ℤ) ^ term.xExponent *
              (y : ℤ) ^ term.yExponent +
            sparseBivariateEval (sparseBivariateNeg terms) x y =
          -(term.eval x y + sparseBivariateEval terms x y)
      rw [ih]
      simp [SparseBivariateTerm.eval]
      ring

@[simp]
theorem sparseBivariateAdd_eval
    (left right : List SparseBivariateTerm) (x y : ℕ) :
    sparseBivariateEval (sparseBivariateAdd left right) x y =
      sparseBivariateEval left x y + sparseBivariateEval right x y := by
  simp [sparseBivariateAdd, sparseBivariateEval]

@[simp]
theorem sparseBivariateSub_eval
    (left right : List SparseBivariateTerm) (x y : ℕ) :
    sparseBivariateEval (sparseBivariateSub left right) x y =
      sparseBivariateEval left x y - sparseBivariateEval right x y := by
  simp [sparseBivariateSub, sub_eq_add_neg]

@[simp]
theorem sparseTerm_mul_eval
    (left right : SparseBivariateTerm) (x y : ℕ) :
    (left.mul right).eval x y = left.eval x y * right.eval x y := by
  simp [SparseBivariateTerm.mul, SparseBivariateTerm.eval, pow_add]
  ring

lemma sparseBivariate_map_mul_eval
    (leftTerm : SparseBivariateTerm)
    (right : List SparseBivariateTerm) (x y : ℕ) :
    sparseBivariateEval
        (right.map fun rightTerm => leftTerm.mul rightTerm) x y =
      leftTerm.eval x y * sparseBivariateEval right x y := by
  induction right with
  | nil =>
      simp [sparseBivariateEval]
  | cons rightTerm right ih =>
      change
        (leftTerm.mul rightTerm).eval x y +
              sparseBivariateEval
                (right.map fun q => leftTerm.mul q) x y =
            leftTerm.eval x y *
              (rightTerm.eval x y + sparseBivariateEval right x y)
      rw [sparseTerm_mul_eval, ih]
      ring

@[simp]
theorem sparseBivariateMul_eval
    (left right : List SparseBivariateTerm) (x y : ℕ) :
    sparseBivariateEval (sparseBivariateMul left right) x y =
      sparseBivariateEval left x y * sparseBivariateEval right x y := by
  induction left with
  | nil =>
      simp [sparseBivariateMul, sparseBivariateEval]
  | cons leftTerm left ih =>
      simp only [sparseBivariateMul, List.flatMap_cons,
        sparseBivariateEval, List.map_append, List.sum_append,
        List.map_cons, List.sum_cons]
      change
        sparseBivariateEval
              (right.map fun rightTerm => leftTerm.mul rightTerm) x y +
            sparseBivariateEval (sparseBivariateMul left right) x y =
          (leftTerm.eval x y + sparseBivariateEval left x y) *
            sparseBivariateEval right x y
      rw [sparseBivariate_map_mul_eval, ih]
      ring

@[simp]
theorem sparseBivariateScale_evalInt
    (coefficient : ℤ) (terms : List SparseBivariateTerm)
    (x y : ℤ) :
    sparseBivariateEvalInt
        (sparseBivariateScale coefficient terms) x y =
      coefficient * sparseBivariateEvalInt terms x y := by
  induction terms with
  | nil =>
      simp [sparseBivariateScale, sparseBivariateEvalInt]
  | cons term terms ih =>
      change
        (coefficient * term.coefficient) * x ^ term.xExponent *
              y ^ term.yExponent +
            sparseBivariateEvalInt
              (sparseBivariateScale coefficient terms) x y =
          coefficient *
            (term.evalInt x y + sparseBivariateEvalInt terms x y)
      rw [ih]
      simp [SparseBivariateTerm.evalInt]
      ring

@[simp]
theorem sparseTerm_mul_evalInt
    (left right : SparseBivariateTerm) (x y : ℤ) :
    (left.mul right).evalInt x y =
      left.evalInt x y * right.evalInt x y := by
  simp [SparseBivariateTerm.mul, SparseBivariateTerm.evalInt, pow_add]
  ring

lemma sparseBivariate_map_mul_evalInt
    (leftTerm : SparseBivariateTerm)
    (right : List SparseBivariateTerm) (x y : ℤ) :
    sparseBivariateEvalInt
        (right.map fun rightTerm => leftTerm.mul rightTerm) x y =
      leftTerm.evalInt x y * sparseBivariateEvalInt right x y := by
  induction right with
  | nil =>
      simp [sparseBivariateEvalInt]
  | cons rightTerm right ih =>
      change
        (leftTerm.mul rightTerm).evalInt x y +
              sparseBivariateEvalInt
                (right.map fun q => leftTerm.mul q) x y =
            leftTerm.evalInt x y *
              (rightTerm.evalInt x y +
                sparseBivariateEvalInt right x y)
      rw [sparseTerm_mul_evalInt, ih]
      ring

@[simp]
theorem sparseBivariateMul_evalInt
    (left right : List SparseBivariateTerm) (x y : ℤ) :
    sparseBivariateEvalInt (sparseBivariateMul left right) x y =
      sparseBivariateEvalInt left x y *
        sparseBivariateEvalInt right x y := by
  induction left with
  | nil =>
      simp [sparseBivariateMul, sparseBivariateEvalInt]
  | cons leftTerm left ih =>
      simp only [sparseBivariateMul, List.flatMap_cons,
        sparseBivariateEvalInt, List.map_append, List.sum_append,
        List.map_cons, List.sum_cons]
      change
        sparseBivariateEvalInt
              (right.map fun rightTerm => leftTerm.mul rightTerm) x y +
            sparseBivariateEvalInt (sparseBivariateMul left right) x y =
          (leftTerm.evalInt x y +
              sparseBivariateEvalInt left x y) *
            sparseBivariateEvalInt right x y
      rw [sparseBivariate_map_mul_evalInt, ih]
      ring

@[simp]
theorem sparseXAffinePower_evalInt
    (offset x y : ℤ) (exponent : ℕ) :
    sparseBivariateEvalInt
        (sparseXAffinePower offset exponent) x y =
      (x + offset) ^ exponent := by
  calc
    sparseBivariateEvalInt
        (sparseXAffinePower offset exponent) x y =
        ((List.range (exponent + 1)).map fun degree =>
          x ^ degree * offset ^ (exponent - degree) *
            (exponent.choose degree : ℤ)).sum := by
          unfold sparseBivariateEvalInt sparseXAffinePower
          rw [List.map_map]
          apply congrArg List.sum
          apply List.map_congr_left
          intro degree hdegree
          simp [SparseBivariateTerm.evalInt]
          ring
    _ = (x + offset) ^ exponent :=
      list_sum_range_binomial x offset exponent

@[simp]
theorem sparseYAffinePower_evalInt
    (offset x y : ℤ) (exponent : ℕ) :
    sparseBivariateEvalInt
        (sparseYAffinePower offset exponent) x y =
      (y + offset) ^ exponent := by
  calc
    sparseBivariateEvalInt
        (sparseYAffinePower offset exponent) x y =
        ((List.range (exponent + 1)).map fun degree =>
          y ^ degree * offset ^ (exponent - degree) *
            (exponent.choose degree : ℤ)).sum := by
          unfold sparseBivariateEvalInt sparseYAffinePower
          rw [List.map_map]
          apply congrArg List.sum
          apply List.map_congr_left
          intro degree hdegree
          simp [SparseBivariateTerm.evalInt]
          ring
    _ = (y + offset) ^ exponent :=
      list_sum_range_binomial y offset exponent

@[simp]
theorem sparseTerm_shift_evalInt
    (term : SparseBivariateTerm) (xOffset yOffset x y : ℤ) :
    sparseBivariateEvalInt (term.shift xOffset yOffset) x y =
      term.evalInt (x + xOffset) (y + yOffset) := by
  simp [SparseBivariateTerm.shift, SparseBivariateTerm.evalInt, mul_assoc]

@[simp]
theorem sparseBivariateShift_evalInt
    (terms : List SparseBivariateTerm) (xOffset yOffset x y : ℤ) :
    sparseBivariateEvalInt
        (sparseBivariateShift terms xOffset yOffset) x y =
      sparseBivariateEvalInt terms (x + xOffset) (y + yOffset) := by
  induction terms with
  | nil =>
      simp [sparseBivariateShift, sparseBivariateEvalInt]
  | cons term terms ih =>
      simp only [sparseBivariateShift, List.flatMap_cons,
        sparseBivariateEvalInt, List.map_append, List.sum_append,
        List.map_cons, List.sum_cons]
      change
        sparseBivariateEvalInt (term.shift xOffset yOffset) x y +
              sparseBivariateEvalInt
                (sparseBivariateShift terms xOffset yOffset) x y =
            term.evalInt (x + xOffset) (y + yOffset) +
              sparseBivariateEvalInt
                terms (x + xOffset) (y + yOffset)
      rw [sparseTerm_shift_evalInt, ih]

theorem sparseBivariateShift_eval_natOffset
    (terms : List SparseBivariateTerm) (j i n d : ℕ) :
    sparseBivariateEval
        (sparseBivariateShift terms (-(j : ℤ)) (-(i : ℤ)))
        (n + j) (n + d + i) =
      sparseBivariateEval terms n (n + d) := by
  calc
    sparseBivariateEval
        (sparseBivariateShift terms (-(j : ℤ)) (-(i : ℤ)))
        (n + j) (n + d + i) =
        sparseBivariateEvalInt
          (sparseBivariateShift terms (-(j : ℤ)) (-(i : ℤ)))
          ((n + j : ℕ) : ℤ) ((n + d + i : ℕ) : ℤ) :=
      (sparseBivariateEvalInt_natCast _ _ _).symm
    _ = sparseBivariateEvalInt terms
          (((n + j : ℕ) : ℤ) - (j : ℤ))
          (((n + d + i : ℕ) : ℤ) - (i : ℤ)) := by
      simpa [sub_eq_add_neg] using
        sparseBivariateShift_evalInt
          terms (-(j : ℤ)) (-(i : ℤ))
            ((n + j : ℕ) : ℤ) ((n + d + i : ℕ) : ℤ)
    _ = sparseBivariateEvalInt terms (n : ℤ) ((n + d : ℕ) : ℤ) := by
      congr 2 <;> push_cast <;> ring
    _ = sparseBivariateEval terms n (n + d) :=
      sparseBivariateEvalInt_natCast _ _ _

/-- Expanded equation `B₅(Y) - 4 B₅(X)` for
`B₅(Z) = (Z+1)(Z+2)(Z+3)(Z+4)(Z+5)`. -/
def k5CurveTerms : List SparseBivariateTerm :=
  [ { coefficient := -360, xExponent := 0, yExponent := 0 }
  , { coefficient := -1096, xExponent := 1, yExponent := 0 }
  , { coefficient := -900, xExponent := 2, yExponent := 0 }
  , { coefficient := -340, xExponent := 3, yExponent := 0 }
  , { coefficient := -60, xExponent := 4, yExponent := 0 }
  , { coefficient := -4, xExponent := 5, yExponent := 0 }
  , { coefficient := 274, xExponent := 0, yExponent := 1 }
  , { coefficient := 225, xExponent := 0, yExponent := 2 }
  , { coefficient := 85, xExponent := 0, yExponent := 3 }
  , { coefficient := 15, xExponent := 0, yExponent := 4 }
  , { coefficient := 1, xExponent := 0, yExponent := 5 } ]

theorem k5CurveTerms_eval_eq_zero
    {n d : ℕ}
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n) :
    sparseBivariateEval k5CurveTerms n (n + d) = 0 := by
  have heqNat :
      (n + d + 1) * (n + d + 2) * (n + d + 3) *
          (n + d + 4) * (n + d + 5) =
        4 * ((n + 1) * (n + 2) * (n + 3) *
          (n + 4) * (n + 5)) := by
    simpa [blockProduct, Finset.prod_Icc_succ_top, Finset.Icc_self,
      Finset.prod_singleton] using heq
  have heqInt :
      (((n + d + 1) * (n + d + 2) * (n + d + 3) *
          (n + d + 4) * (n + d + 5) : ℕ) : ℤ) =
        (4 : ℤ) * (((n + 1) * (n + 2) * (n + 3) *
          (n + 4) * (n + 5) : ℕ) : ℤ) := by
    exact_mod_cast heqNat
  norm_num [k5CurveTerms, sparseBivariateEval,
    SparseBivariateTerm.eval]
  push_cast at heqInt
  ring_nf at heqInt ⊢
  linarith

theorem k5CurveTerms_shift_eval_eq_zero
    {n d j i : ℕ}
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n) :
    sparseBivariateEval
        (sparseBivariateShift k5CurveTerms (-(j : ℤ)) (-(i : ℤ)))
        (n + j) (n + d + i) = 0 := by
  rw [sparseBivariateShift_eval_natOffset]
  exact k5CurveTerms_eval_eq_zero heq

lemma sparseTerm_pow_dvd_eval_of_order
    {A x y mu : ℕ} {term : SparseBivariateTerm}
    (hx : A ∣ x)
    (hy : A ∣ y)
    (horder : mu ≤ term.xExponent + term.yExponent) :
    ((A ^ mu : ℕ) : ℤ) ∣ term.eval x y := by
  have hxPow : A ^ term.xExponent ∣ x ^ term.xExponent :=
    pow_dvd_pow_of_dvd hx term.xExponent
  have hyPow : A ^ term.yExponent ∣ y ^ term.yExponent :=
    pow_dvd_pow_of_dvd hy term.yExponent
  have hsum :
      A ^ (term.xExponent + term.yExponent) ∣
        x ^ term.xExponent * y ^ term.yExponent := by
    rw [pow_add]
    exact Nat.mul_dvd_mul hxPow hyPow
  have hmu :
      A ^ mu ∣ A ^ (term.xExponent + term.yExponent) :=
    pow_dvd_pow A horder
  have hNat :
      A ^ mu ∣ x ^ term.xExponent * y ^ term.yExponent :=
    dvd_trans hmu hsum
  have hInt :
      ((A ^ mu : ℕ) : ℤ) ∣
        ((x ^ term.xExponent * y ^ term.yExponent : ℕ) : ℤ) :=
    Int.natCast_dvd_natCast.mpr hNat
  have hCoeff :
      ((A ^ mu : ℕ) : ℤ) ∣
        term.coefficient *
          ((x ^ term.xExponent * y ^ term.yExponent : ℕ) : ℤ) :=
    dvd_mul_of_dvd_right hInt term.coefficient
  simpa [SparseBivariateTerm.eval, Nat.cast_mul, Nat.cast_pow,
    mul_assoc, mul_comm, mul_left_comm] using hCoeff

theorem sparseBivariate_pow_dvd_eval_of_order
    {A x y mu : ℕ} {terms : List SparseBivariateTerm}
    (hx : A ∣ x)
    (hy : A ∣ y)
    (horder : sparseBivariateOrderAtLeast mu terms) :
    ((A ^ mu : ℕ) : ℤ) ∣ sparseBivariateEval terms x y := by
  induction terms with
  | nil =>
      simp [sparseBivariateEval]
  | cons term terms ih =>
      have htermOrder : mu ≤ term.xExponent + term.yExponent :=
        horder term (by simp)
      have htailOrder : sparseBivariateOrderAtLeast mu terms := by
        intro q hq
        exact horder q (by simp [hq])
      have hterm := sparseTerm_pow_dvd_eval_of_order hx hy htermOrder
      have htail := ih htailOrder
      simpa [sparseBivariateEval] using dvd_add hterm htail

theorem sparseEffective_pow_dvd_eval_of_order
    {A x y mu : ℕ} {terms : List SparseBivariateTerm}
    (hx : A ∣ x)
    (hy : A ∣ y)
    (horder : sparseEffectiveOrderAtLeast mu terms) :
    ((A ^ mu : ℕ) : ℤ) ∣ sparseBivariateEval terms x y := by
  induction terms with
  | nil =>
      simp [sparseBivariateEval]
  | cons term terms ih =>
      have hall :
          ∀ q ∈ term :: terms,
            q.coefficient = 0 ∨
              mu ≤ q.xExponent + q.yExponent := by
        exact List.all_iff_forall_prop.mp horder
      have htermCondition :
          term.coefficient = 0 ∨
            mu ≤ term.xExponent + term.yExponent :=
        hall term (by simp)
      have htailOrder :
          sparseEffectiveOrderAtLeast mu terms := by
        apply List.all_iff_forall_prop.mpr
        intro q hq
        exact hall q (by simp [hq])
      have hterm :
          ((A ^ mu : ℕ) : ℤ) ∣ term.eval x y := by
        rcases htermCondition with hzero | hdegree
        · simp [SparseBivariateTerm.eval, hzero]
        · exact sparseTerm_pow_dvd_eval_of_order hx hy hdegree
      have htail := ih htailOrder
      simpa [sparseBivariateEval] using dvd_add hterm htail

theorem sparseNormalized_pow_dvd_eval_of_order
    {A x y mu : ℕ} {terms : List SparseBivariateTerm}
    (hx : A ∣ x)
    (hy : A ∣ y)
    (horder : sparseNormalizedOrderAtLeast mu terms) :
    ((A ^ mu : ℕ) : ℤ) ∣ sparseBivariateEval terms x y := by
  have hnormalized :
      ((A ^ mu : ℕ) : ℤ) ∣
        sparseBivariateEval (sparseNormalize terms) x y :=
    sparseEffective_pow_dvd_eval_of_order hx hy horder
  simpa using hnormalized

theorem sparseSortNormalized_pow_dvd_eval_of_order
    {A x y mu : ℕ} {terms : List SparseBivariateTerm}
    (hx : A ∣ x)
    (hy : A ∣ y)
    (horder : sparseSortNormalizedOrderAtLeast mu terms) :
    ((A ^ mu : ℕ) : ℤ) ∣ sparseBivariateEval terms x y := by
  have hnormalized :
      ((A ^ mu : ℕ) : ℤ) ∣
        sparseBivariateEval (sparseSortNormalize terms) x y :=
    sparseEffective_pow_dvd_eval_of_order hx hy horder
  simpa using hnormalized

theorem sparseNormalized_pow_dvd_natAbs_eval_of_order
    {A x y mu : ℕ} {terms : List SparseBivariateTerm}
    (hx : A ∣ x)
    (hy : A ∣ y)
    (horder : sparseNormalizedOrderAtLeast mu terms) :
    A ^ mu ∣ (sparseBivariateEval terms x y).natAbs := by
  have hInt := sparseNormalized_pow_dvd_eval_of_order hx hy horder
  simpa using Int.natAbs_dvd_natAbs.mpr hInt

theorem sparseSortNormalized_pow_dvd_natAbs_eval_of_order
    {A x y mu : ℕ} {terms : List SparseBivariateTerm}
    (hx : A ∣ x)
    (hy : A ∣ y)
    (horder : sparseSortNormalizedOrderAtLeast mu terms) :
    A ^ mu ∣ (sparseBivariateEval terms x y).natAbs := by
  have hInt :=
    sparseSortNormalized_pow_dvd_eval_of_order hx hy horder
  simpa using Int.natAbs_dvd_natAbs.mpr hInt

/-- One local certificate identity implies the required cell-power
divisibility for the global section value. -/
theorem k5_local_certificate_pow_dvd_section_natAbs
    {A n d j i mu : ℕ}
    {sectionTerms quotient : List SparseBivariateTerm}
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n)
    (hx : A ∣ n + j)
    (hy : A ∣ n + d + i)
    (horder :
      sparseNormalizedOrderAtLeast mu
        (sparseBivariateSub
          (sparseBivariateShift sectionTerms (-(j : ℤ)) (-(i : ℤ)))
          (sparseBivariateMul quotient
            (sparseBivariateShift k5CurveTerms
              (-(j : ℤ)) (-(i : ℤ)))))) :
    A ^ mu ∣
      (sparseBivariateEval sectionTerms n (n + d)).natAbs := by
  have hdvd :=
    sparseNormalized_pow_dvd_eval_of_order hx hy horder
  have hcurve :=
    k5CurveTerms_shift_eval_eq_zero
      (n := n) (d := d) (j := j) (i := i) heq
  have hshift :=
    sparseBivariateShift_eval_natOffset sectionTerms j i n d
  rw [sparseBivariateSub_eval, sparseBivariateMul_eval,
    hcurve, mul_zero, sub_zero, hshift] at hdvd
  simpa using Int.natAbs_dvd_natAbs.mpr hdvd

/-- Sorted normalization is semantically identical to the insertion-based
checker but produces much smaller kernel proof terms for generated data. -/
theorem k5_sorted_local_certificate_pow_dvd_section_natAbs
    {A n d j i mu : ℕ}
    {sectionTerms quotient : List SparseBivariateTerm}
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n)
    (hx : A ∣ n + j)
    (hy : A ∣ n + d + i)
    (horder :
      sparseSortNormalizedOrderAtLeast mu
        (sparseBivariateSub
          (sparseBivariateShift sectionTerms (-(j : ℤ)) (-(i : ℤ)))
          (sparseBivariateMul quotient
            (sparseBivariateShift k5CurveTerms
              (-(j : ℤ)) (-(i : ℤ)))))) :
    A ^ mu ∣
      (sparseBivariateEval sectionTerms n (n + d)).natAbs := by
  have hdvd :=
    sparseSortNormalized_pow_dvd_eval_of_order hx hy horder
  have hcurve :=
    k5CurveTerms_shift_eval_eq_zero
      (n := n) (d := d) (j := j) (i := i) heq
  have hshift :=
    sparseBivariateShift_eval_natOffset sectionTerms j i n d
  rw [sparseBivariateSub_eval, sparseBivariateMul_eval,
    hcurve, mul_zero, sub_zero, hshift] at hdvd
  simpa using Int.natAbs_dvd_natAbs.mpr hdvd

/-- The `MvPolynomial` version of the sparse jet divisibility kernel.
Generated certificates can define their remainder by polynomial arithmetic
and discharge `mvBivariateOrderAtLeast` with `by decide`; no expanded
high-order remainder identity is required. -/
theorem mvBivariate_pow_dvd_eval_of_order
    {A x y mu : ℕ} {P : BivariateIntPolynomial}
    (hx : A ∣ x)
    (hy : A ∣ y)
    (horder : mvBivariateOrderAtLeast mu P) :
    ((A ^ mu : ℕ) : ℤ) ∣
      P.eval₂ (RingHom.id ℤ) ![(x : ℤ), (y : ℤ)] := by
  rw [MvPolynomial.eval₂_eq']
  apply Finset.dvd_sum
  intro exponent hexponent
  have hxPow : A ^ exponent 0 ∣ x ^ exponent 0 :=
    pow_dvd_pow_of_dvd hx (exponent 0)
  have hyPow : A ^ exponent 1 ∣ y ^ exponent 1 :=
    pow_dvd_pow_of_dvd hy (exponent 1)
  have hsum :
      A ^ (exponent 0 + exponent 1) ∣
        x ^ exponent 0 * y ^ exponent 1 := by
    rw [pow_add]
    exact Nat.mul_dvd_mul hxPow hyPow
  have hmu :
      A ^ mu ∣ A ^ (exponent 0 + exponent 1) :=
    pow_dvd_pow A
      (List.all_iff_forall_prop.mp horder exponent (by simpa using hexponent))
  have hNat :
      A ^ mu ∣ x ^ exponent 0 * y ^ exponent 1 :=
    dvd_trans hmu hsum
  have hInt :
      ((A ^ mu : ℕ) : ℤ) ∣
        (((x ^ exponent 0) * (y ^ exponent 1) : ℕ) : ℤ) :=
    Int.natCast_dvd_natCast.mpr hNat
  have hMonomial :
      ((A ^ mu : ℕ) : ℤ) ∣
        ∏ i : Fin 2, ![(x : ℤ), (y : ℤ)] i ^ exponent i := by
    simpa [Fin.prod_univ_two, Nat.cast_mul, Nat.cast_pow] using hInt
  exact dvd_mul_of_dvd_right hMonomial ((RingHom.id ℤ) (P.coeff exponent))

/-- A direct finite Taylor-coefficient certificate implies the required
cell-power divisibility without normalizing the expanded high-degree shift. -/
theorem k5_direct_local_certificate_pow_dvd_section_natAbs
    {A n d j i mu : ℕ}
    {sectionTerms quotient : List SparseBivariateTerm}
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n)
    (hx : A ∣ n + j)
    (hy : A ∣ n + d + i)
    (hcheck :
      sparseLocalTaylorCheck mu sectionTerms quotient k5CurveTerms
        (-(j : ℤ)) (-(i : ℤ)) = true) :
    A ^ mu ∣
      (sparseBivariateEval sectionTerms n (n + d)).natAbs := by
  have horder :=
    sparseLocalTaylorCheck_order hcheck
  have hdvd :=
    mvBivariate_pow_dvd_eval_of_order hx hy horder
  rw [sparseToMvPolynomial_eval₂, sparseBivariateSub_eval,
    sparseBivariateMul_eval] at hdvd
  have hcurve :=
    k5CurveTerms_shift_eval_eq_zero
      (n := n) (d := d) (j := j) (i := i) heq
  have hshift :=
    sparseBivariateShift_eval_natOffset sectionTerms j i n d
  rw [hcurve, mul_zero, sub_zero, hshift] at hdvd
  simpa using Int.natAbs_dvd_natAbs.mpr hdvd

/-- Row-chunked version of the direct Taylor certificate. -/
theorem k5_direct_rows_certificate_pow_dvd_section_natAbs
    {A n d j i mu : ℕ}
    {sectionTerms quotient : List SparseBivariateTerm}
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n)
    (hx : A ∣ n + j)
    (hy : A ∣ n + d + i)
    (hrows :
      SparseLocalTaylorRowsCertificate mu
        sectionTerms quotient k5CurveTerms
        (-(j : ℤ)) (-(i : ℤ))) :
    A ^ mu ∣
      (sparseBivariateEval sectionTerms n (n + d)).natAbs := by
  have horder :=
    sparseLocalTaylorRowsCertificate_order hrows
  have hdvd :=
    mvBivariate_pow_dvd_eval_of_order hx hy horder
  rw [sparseToMvPolynomial_eval₂, sparseBivariateSub_eval,
    sparseBivariateMul_eval] at hdvd
  have hcurve :=
    k5CurveTerms_shift_eval_eq_zero
      (n := n) (d := d) (j := j) (i := i) heq
  have hshift :=
    sparseBivariateShift_eval_natOffset sectionTerms j i n d
  rw [hcurve, mul_zero, sub_zero, hshift] at hdvd
  simpa using Int.natAbs_dvd_natAbs.mpr hdvd

lemma sparseTerm_natAbs_eval
    (term : SparseBivariateTerm) (x y : ℕ) :
    (term.eval x y).natAbs =
      term.coefficient.natAbs * x ^ term.xExponent * y ^ term.yExponent := by
  simp [SparseBivariateTerm.eval, Int.natAbs_mul, mul_assoc]

theorem sparseBivariateEval_natAbs_le
    {terms : List SparseBivariateTerm} {x y M r : ℕ}
    (hmono :
      ∀ term ∈ terms,
        x ^ term.xExponent * y ^ term.yExponent ≤ M ^ r) :
    (sparseBivariateEval terms x y).natAbs ≤
      sparseBivariateL1Norm terms * M ^ r := by
  induction terms with
  | nil =>
      simp [sparseBivariateEval, sparseBivariateL1Norm]
  | cons term terms ih =>
      have htermMono :
          x ^ term.xExponent * y ^ term.yExponent ≤ M ^ r :=
        hmono term (by simp)
      have htailMono :
          ∀ q ∈ terms,
            x ^ q.xExponent * y ^ q.yExponent ≤ M ^ r := by
        intro q hq
        exact hmono q (by simp [hq])
      have htail := ih htailMono
      calc
        (sparseBivariateEval (term :: terms) x y).natAbs ≤
            (term.eval x y).natAbs +
              (sparseBivariateEval terms x y).natAbs := by
                simpa [sparseBivariateEval] using
                  Int.natAbs_add_le (term.eval x y)
                    (sparseBivariateEval terms x y)
        _ ≤ term.coefficient.natAbs * M ^ r +
            sparseBivariateL1Norm terms * M ^ r := by
              apply Nat.add_le_add
              · rw [sparseTerm_natAbs_eval]
                simpa [mul_assoc] using
                  Nat.mul_le_mul_left term.coefficient.natAbs htermMono
              · exact htail
        _ = sparseBivariateL1Norm (term :: terms) * M ^ r := by
              simp [sparseBivariateL1Norm]
              ring

theorem sparseBivariateEval_natAbs_le_of_degree
    {terms : List SparseBivariateTerm} {x y M r : ℕ}
    (hM : 1 ≤ M)
    (hx : x ≤ M)
    (hy : y ≤ M)
    (hdegree : sparseBivariateDegreeAtMost r terms) :
    (sparseBivariateEval terms x y).natAbs ≤
      sparseBivariateL1Norm terms * M ^ r := by
  apply sparseBivariateEval_natAbs_le
  intro term hterm
  calc
    x ^ term.xExponent * y ^ term.yExponent ≤
        M ^ term.xExponent * M ^ term.yExponent :=
      Nat.mul_le_mul
        (Nat.pow_le_pow_left hx term.xExponent)
        (Nat.pow_le_pow_left hy term.yExponent)
    _ = M ^ (term.xExponent + term.yExponent) := by
      rw [pow_add]
    _ ≤ M ^ r :=
      Nat.pow_le_pow_right hM (hdegree term hterm)

theorem k5_section_natAbs_bound
    {n d : ℕ} {sectionTerms : List SparseBivariateTerm}
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n)
    (hdegree : sparseBivariateDegreeAtMost 84 sectionTerms)
    (hl1 :
      sparseBivariateL1Norm sectionTerms ≤
        k5PunctureCoefficientNorm) :
    (sparseBivariateEval sectionTerms n (n + d)).natAbs ≤
      k5PunctureCoefficientNorm * (6 * d) ^ 84 := by
  have hbase :
      n + 1 < 4 * d :=
    row_base_upper_k5 (ratio_window_four_nat heq).2
  have hdpos : 0 < d := by omega
  have hn : n ≤ 6 * d := by omega
  have hnd : n + d ≤ 6 * d := by omega
  have hM : 1 ≤ 6 * d := by omega
  calc
    (sparseBivariateEval sectionTerms n (n + d)).natAbs ≤
        sparseBivariateL1Norm sectionTerms * (6 * d) ^ 84 :=
      sparseBivariateEval_natAbs_le_of_degree
        hM hn hnd hdegree
    _ ≤ k5PunctureCoefficientNorm * (6 * d) ^ 84 :=
      Nat.mul_le_mul_right _ hl1

/-- Convert the integral divisibility output into the natural divisibility
used by the arithmetic endpoint. -/
theorem sparseBivariate_pow_dvd_natAbs_eval_of_order
    {A x y mu : ℕ} {terms : List SparseBivariateTerm}
    (hx : A ∣ x)
    (hy : A ∣ y)
    (horder : sparseBivariateOrderAtLeast mu terms) :
    A ^ mu ∣ (sparseBivariateEval terms x y).natAbs := by
  have hInt :=
    sparseBivariate_pow_dvd_eval_of_order hx hy horder
  simpa using Int.natAbs_dvd_natAbs.mpr hInt

#print axioms sparseBivariate_pow_dvd_eval_of_order
#print axioms sparseBivariateEval_natAbs_le
#print axioms sparseBivariateEval_natAbs_le_of_degree
#print axioms sparseBivariate_pow_dvd_natAbs_eval_of_order

end Erdos686Variant
end Erdos686
