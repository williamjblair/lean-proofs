/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.Core.FifthLocalLift

/-!
# Erdős 686: ordinary-kernel fifth-quotient finite ledger

This module imports the exact 3,024-position computation from
`compute/campaign686/fifth_quotient_short_window_verify.py` into Lean using
ordinary-kernel reduction.  The finite checker uses exact rational arithmetic and a
five-coefficient recurrence for the local affine product.  The accompanying
soundness lemmas turn the checked interval bounds into nonvanishing of the
fourth and normalized fifth eliminants at `d >= 10^1000`.

The result is restricted to the 1,008 nonreflected triples in the six odd
target rows.  It does not close the simultaneous all-nonzero branch.
-/

namespace Erdos686
namespace Erdos686Variant

open Polynomial

/-- First five coefficients of a product of affine monic factors. -/
structure FifthAffineCoefficients where
  c0 : ℤ
  c1 : ℤ
  c2 : ℤ
  c3 : ℤ
  c4 : ℤ
deriving DecidableEq, Repr

/-- Multiplication by `X+a`, truncated after degree four. -/
def FifthAffineCoefficients.prepend
    (a : ℤ) (s : FifthAffineCoefficients) : FifthAffineCoefficients :=
  { c0 := a * s.c0
    c1 := s.c0 + a * s.c1
    c2 := s.c1 + a * s.c2
    c3 := s.c2 + a * s.c3
    c4 := s.c3 + a * s.c4 }

/-- Computable recurrence for the first five affine-product coefficients. -/
def fifthAffineCoefficients : List ℤ → FifthAffineCoefficients
  | [] => { c0 := 1, c1 := 0, c2 := 0, c3 := 0, c4 := 0 }
  | a :: rest => FifthAffineCoefficients.prepend a
      (fifthAffineCoefficients rest)

/-- The ordered owner-offset list in the row `1,...,k`, omitting `i`. -/
def fifthLocalOffsets (k i : ℕ) : List ℤ :=
  (((List.range k).map Nat.succ).erase i).map
    (fun j => (j : ℤ) - (i : ℤ))

/-- Computable first-five coefficient vector for owner `i` in row `k`. -/
def fifthLocalCoefficients (k i : ℕ) : FifthAffineCoefficients :=
  fifthAffineCoefficients (fifthLocalOffsets k i)

/-- One cyclic position: `owner` is distinguished and `left < right` are the
two opposite indices. -/
structure FifthQuotientPosition where
  k : ℕ
  owner : ℕ
  left : ℕ
  right : ℕ
deriving DecidableEq, Repr

/-- A reflected triple is exactly a center together with a symmetric pair. -/
def fifthPositionNonreflected (k owner left right : ℕ) : Bool :=
  let center := (k + 1) / 2
  !((owner = center && left + right = 2 * center) ||
    (left = center && owner + right = 2 * center) ||
    (right = center && owner + left = 2 * center))

/-- Valid ordered encoding of one cyclic nonreflected triple position. -/
def fifthPositionValid (k owner left right : ℕ) : Bool :=
  1 ≤ owner && owner ≤ k &&
  1 ≤ left && left ≤ k &&
  1 ≤ right && right ≤ k &&
  owner ≠ left && owner ≠ right && left < right &&
  fifthPositionNonreflected k owner left right

/-- All cyclic nonreflected positions in one row. -/
def fifthQuotientRowPositions (k : ℕ) : List FifthQuotientPosition :=
  ((List.range k).map Nat.succ).flatMap fun owner =>
    ((List.range k).map Nat.succ).flatMap fun left =>
      ((List.range k).map Nat.succ).filterMap fun right =>
        if fifthPositionValid k owner left right then
          some { k, owner, left, right }
        else none

/-- The exact six-row finite domain. -/
def fifthQuotientTargetPositions : List FifthQuotientPosition :=
  [5, 7, 9, 11, 13, 15].flatMap fifthQuotientRowPositions

/-- Padded lower endpoint for the normalized residual ratio. -/
def fifthResidualRatioLower : ℕ → ℚ
  | 5 => 26772949 / 3195100
  | 7 => 13893949 / 1095100
  | 9 => 9439349 / 555100
  | 11 => 3580421 / 167900
  | 13 => 14431673 / 562700
  | 15 => 29022017 / 968300
  | _ => 0

/-- Padded upper endpoint for the normalized residual ratio. -/
def fifthResidualRatioUpper : ℕ → ℚ
  | 5 => 178913 / 21300
  | 7 => 27831801 / 2190100
  | 9 => 7087863 / 416300
  | 11 => 9556777 / 447700
  | 13 => 9628651 / 375100
  | 15 => 14520741 / 484100
  | _ => 0

/-- Lower interval enclosure for one signed monomial coefficient. -/
def fifthMonomialLower (a : ℤ) (lo hi : ℚ) (power : ℕ) : ℚ :=
  if 0 ≤ a then (a : ℚ) * lo ^ power else (a : ℚ) * hi ^ power

/-- Upper interval enclosure for one signed monomial coefficient. -/
def fifthMonomialUpper (a : ℤ) (lo hi : ℚ) (power : ℕ) : ℚ :=
  if 0 ≤ a then (a : ℚ) * hi ^ power else (a : ℚ) * lo ^ power

/-- Coarse coefficient multiplying `d^4` in the fifth-eliminant remainder.
The constants come from `|X|<=36d`, `|X-3 delta|<=81d`,
`|YZ-X^2|<=5265d`, and `|YZ+X^2|<=7857d^2`. -/
def fifthEliminantRemainderBound
    (C D E K deltaLeft deltaRight : ℤ) : ℕ :=
  729 * (Int.natAbs C) ^ 2 *
      (9 * Int.natAbs C * 36 * 5265 * 7857 +
        Int.natAbs (deltaLeft * deltaRight) *
          (180 * Int.natAbs E * 5265 +
            108 * Int.natAbs D * 6561)) +
    27 * Int.natAbs K

/-- Analogous coarse coefficient for the fourth eliminant. -/
def fourthEliminantRemainderBound
    (C D E K deltaLeft deltaRight : ℤ) : ℕ :=
  27 * (Int.natAbs C) ^ 2 *
      (9 * Int.natAbs C * 36 * 5265 * 7857 +
        Int.natAbs (deltaLeft * deltaRight) *
          (180 * Int.natAbs E * 5265 +
            108 * Int.natAbs D * 6561)) +
    Int.natAbs K

/-- The complete finite predicate checked at a cyclic position.  The leading
interval is separated from zero by more than one, and both remainder
coefficients are below `10^80` (far below the live `10^1000` cutoff). -/
abbrev FifthQuotientPositionGood (p : FifthQuotientPosition) : Prop :=
  let s := fifthLocalCoefficients p.k p.owner
  let dl : ℤ := (p.owner : ℤ) - (p.left : ℤ)
  let dr : ℤ := (p.owner : ℤ) - (p.right : ℤ)
  let K := threeBucketReducedFourthCoefficient
    s.c0 s.c1 s.c2 s.c3 dl dr
  let R1 := threeBucketReducedFifthLinearCoefficient
    s.c0 s.c1 s.c2 s.c3 s.c4 dl dr
  let lo := fifthResidualRatioLower p.k
  let hi := fifthResidualRatioUpper p.k
  let a5 := -6561 * s.c0 ^ 3
  let b5 := 131220 * s.c0 ^ 2 * s.c2 * (dl * dr)
  let a4 := -243 * s.c0 ^ 3
  let b4 := 4860 * s.c0 ^ 2 * s.c2 * (dl * dr)
  (((1 : ℚ) < fifthMonomialLower a5 lo hi 5 +
      fifthMonomialLower b5 lo hi 2 + R1 ∨
    fifthMonomialUpper a5 lo hi 5 +
      fifthMonomialUpper b5 lo hi 2 + R1 < (-1 : ℚ)) ∧
  ((1 : ℚ) < fifthMonomialLower a4 lo hi 5 +
      fifthMonomialLower b4 lo hi 2 ∨
    fifthMonomialUpper a4 lo hi 5 +
      fifthMonomialUpper b4 lo hi 2 < (-1 : ℚ)) ∧
  fifthEliminantRemainderBound s.c0 s.c1 s.c2 K dl dr < 10 ^ 80 ∧
  fourthEliminantRemainderBound s.c0 s.c1 s.c2 K dl dr < 10 ^ 80)

set_option maxHeartbeats 200000000 in
-- The ordinary-kernel evaluator checks the full 3,024-position exact table.
set_option maxRecDepth 1000000 in
/-- Ordinary-kernel exact certificate for all 3,024 cyclic positions. -/
theorem fifth_quotient_target_position_certificate :
    ∀ p ∈ fifthQuotientTargetPositions, FifthQuotientPositionGood p := by
  decide +kernel

/-- Kernel-checked cardinality of the imported finite domain. -/
theorem fifth_quotient_target_position_count :
    fifthQuotientTargetPositions.length = 3024 := by
  decide +kernel

/-- Every generated ledger entry satisfies the advertised row, range,
distinctness, ordering, and nonreflection predicate. -/
theorem fifth_quotient_target_positions_valid :
    ∀ p ∈ fifthQuotientTargetPositions,
      fifthPositionValid p.k p.owner p.left p.right = true := by
  decide +kernel

private lemma mem_fifthRowIndices_iff {k i : ℕ} :
    i ∈ (List.range k).map Nat.succ ↔ 1 ≤ i ∧ i ≤ k := by
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨a, ha, rfl⟩
    omega
  · rintro ⟨hi, hik⟩
    refine ⟨i - 1, ?_, ?_⟩
    · omega
    · omega

/-- The row generator contains exactly the valid cyclic positions and records
the supplied row in every generated structure. -/
theorem fifth_quotient_row_position_mem_iff
    {row k owner left right : ℕ} :
    ({ k := k, owner := owner, left := left, right := right } :
        FifthQuotientPosition) ∈ fifthQuotientRowPositions row ↔
      k = row ∧ fifthPositionValid row owner left right = true := by
  simp [fifthQuotientRowPositions, mem_fifthRowIndices_iff]
  constructor
  · rintro ⟨_ho, _hl, x, _hx, hv, hrk, hxr⟩
    exact ⟨hrk.symm, by simpa [hxr] using hv⟩
  · rintro ⟨hkr, hv⟩
    have hv' := hv
    simp [fifthPositionValid] at hv'
    have ho : 1 ≤ owner ∧ owner ≤ row := by omega
    have hl : 1 ≤ left ∧ left ≤ row := by omega
    have hr : 1 ≤ right ∧ right ≤ row := by omega
    have hri : right - 1 + 1 = right := by omega
    refine ⟨ho, hl, right - 1, ?_, ?_, ?_, ?_⟩
    · omega
    · simpa [hri] using hv
    · exact hkr.symm
    · exact hri

/-- The target generator contains exactly the valid cyclic positions in the
six advertised odd rows. -/
theorem fifth_quotient_target_position_mem_iff
    {k owner left right : ℕ} :
    ({ k := k, owner := owner, left := left, right := right } :
        FifthQuotientPosition) ∈ fifthQuotientTargetPositions ↔
      (k = 5 ∨ k = 7 ∨ k = 9 ∨ k = 11 ∨ k = 13 ∨ k = 15) ∧
        fifthPositionValid k owner left right = true := by
  simp [fifthQuotientTargetPositions, fifth_quotient_row_position_mem_iff]
  aesop

/-! ## Bridge from the computable recurrence to the Taylor coefficients -/

/-- Polynomial represented by the same affine-factor recurrence. -/
noncomputable def fifthAffinePolynomial : List ℤ → Polynomial ℤ
  | [] => 1
  | a :: rest =>
      (Polynomial.X + Polynomial.C a) * fifthAffinePolynomial rest

private lemma fifthAffinePolynomial_coeff_succ
    (a : ℤ) (P : Polynomial ℤ) (n : ℕ) :
    ((Polynomial.X + Polynomial.C a) * P).coeff (n + 1) =
      P.coeff n + a * P.coeff (n + 1) := by
  rw [add_mul, Polynomial.coeff_add, Polynomial.coeff_X_mul,
    Polynomial.coeff_C_mul]

private lemma fifthAffineCoefficients_coeff_zero (l : List ℤ) :
    (fifthAffinePolynomial l).coeff 0 = (fifthAffineCoefficients l).c0 := by
  induction l with
  | nil =>
      norm_num [fifthAffinePolynomial, fifthAffineCoefficients,
        Polynomial.coeff_one]
  | cons a l ih =>
      simp only [fifthAffinePolynomial, fifthAffineCoefficients,
        FifthAffineCoefficients.prepend]
      rw [Polynomial.mul_coeff_zero, ih]
      simp

private lemma fifthAffineCoefficients_coeff_one (l : List ℤ) :
    (fifthAffinePolynomial l).coeff 1 = (fifthAffineCoefficients l).c1 := by
  induction l with
  | nil =>
      norm_num [fifthAffinePolynomial, fifthAffineCoefficients,
        Polynomial.coeff_one]
  | cons a l ih =>
      simp only [fifthAffinePolynomial, fifthAffineCoefficients,
        FifthAffineCoefficients.prepend]
      rw [show 1 = 0 + 1 by omega, fifthAffinePolynomial_coeff_succ,
        fifthAffineCoefficients_coeff_zero, ih]

private lemma fifthAffineCoefficients_coeff_two (l : List ℤ) :
    (fifthAffinePolynomial l).coeff 2 = (fifthAffineCoefficients l).c2 := by
  induction l with
  | nil =>
      norm_num [fifthAffinePolynomial, fifthAffineCoefficients,
        Polynomial.coeff_one]
  | cons a l ih =>
      simp only [fifthAffinePolynomial, fifthAffineCoefficients,
        FifthAffineCoefficients.prepend]
      rw [show 2 = 1 + 1 by omega, fifthAffinePolynomial_coeff_succ,
        fifthAffineCoefficients_coeff_one, ih]

private lemma fifthAffineCoefficients_coeff_three (l : List ℤ) :
    (fifthAffinePolynomial l).coeff 3 = (fifthAffineCoefficients l).c3 := by
  induction l with
  | nil =>
      norm_num [fifthAffinePolynomial, fifthAffineCoefficients,
        Polynomial.coeff_one]
  | cons a l ih =>
      simp only [fifthAffinePolynomial, fifthAffineCoefficients,
        FifthAffineCoefficients.prepend]
      rw [show 3 = 2 + 1 by omega, fifthAffinePolynomial_coeff_succ,
        fifthAffineCoefficients_coeff_two, ih]

private lemma fifthAffineCoefficients_coeff_four (l : List ℤ) :
    (fifthAffinePolynomial l).coeff 4 = (fifthAffineCoefficients l).c4 := by
  induction l with
  | nil =>
      norm_num [fifthAffinePolynomial, fifthAffineCoefficients,
        Polynomial.coeff_one]
  | cons a l ih =>
      simp only [fifthAffinePolynomial, fifthAffineCoefficients,
        FifthAffineCoefficients.prepend]
      rw [show 4 = 3 + 1 by omega, fifthAffinePolynomial_coeff_succ,
        fifthAffineCoefficients_coeff_three, ih]

private def fifthLocalIndexList (k i : ℕ) : List ℕ :=
  ((List.range k).map Nat.succ).erase i

private lemma fifthLocalIndexList_nodup (k i : ℕ) :
    (fifthLocalIndexList k i).Nodup := by
  apply List.Nodup.erase
  exact List.Nodup.map Nat.succ_injective List.nodup_range

private lemma fifthLocalIndexList_toFinset (k i : ℕ) :
    (fifthLocalIndexList k i).toFinset = (Finset.Icc 1 k).erase i := by
  have hnodup : ((List.range k).map Nat.succ).Nodup :=
    List.Nodup.map Nat.succ_injective List.nodup_range
  ext j
  rw [List.mem_toFinset, fifthLocalIndexList, hnodup.mem_erase_iff,
    Finset.mem_erase, Finset.mem_Icc]
  rw [List.mem_map]
  constructor
  · rintro ⟨hne, a, ha, haj⟩
    subst j
    exact ⟨hne, by omega, by simpa using ha⟩
  · rintro ⟨hne, hj1, hjk⟩
    refine ⟨hne, j - 1, ?_, Nat.succ_pred_eq_of_pos hj1⟩
    simpa [List.mem_range] using (show j - 1 < k by omega)

private lemma fifthLocalOffsets_eq_indexList (k i : ℕ) :
    fifthLocalOffsets k i =
      (fifthLocalIndexList k i).map
        (fun (j : ℕ) => (j : ℤ) - (i : ℤ)) := by
  unfold fifthLocalOffsets fifthLocalIndexList
  rw [List.bind_eq_flatMap]
  change List.map (fun j : ℤ => j - (i : ℤ))
      (List.flatMap (Function.comp pure (fun a : ℕ => (a : ℤ)))
        ((List.range k).map Nat.succ |>.erase i)) = _
  rw [List.flatMap_pure_eq_map, List.map_map]
  rfl

private lemma fifthAffinePolynomial_eq_map_prod (l : List ℤ) :
    fifthAffinePolynomial l =
      (l.map (fun a => Polynomial.X + Polynomial.C a)).prod := by
  induction l with
  | nil => simp [fifthAffinePolynomial]
  | cons a l ih => simp [fifthAffinePolynomial, ih]

private lemma localThirdPolynomial_eq_fifthAffinePolynomial (k i : ℕ) :
    localThirdPolynomial k i =
      fifthAffinePolynomial (fifthLocalOffsets k i) := by
  rw [fifthLocalOffsets_eq_indexList,
    fifthAffinePolynomial_eq_map_prod]
  unfold localThirdPolynomial
  rw [List.map_map]
  change (∏ j ∈ (Finset.Icc 1 k).erase i,
      (Polynomial.X + Polynomial.C ((j : ℤ) - (i : ℤ)))) =
    ((fifthLocalIndexList k i).map (fun (j : ℕ) =>
      Polynomial.X + Polynomial.C ((j : ℤ) - (i : ℤ)))).prod
  rw [← fifthLocalIndexList_toFinset]
  exact List.prod_toFinset
    (l := fifthLocalIndexList k i)
    (fun j : ℕ => Polynomial.X + Polynomial.C ((j : ℤ) - (i : ℤ)))
    (fifthLocalIndexList_nodup k i)

private lemma localThirdPolynomial_coeff_zero_fifth (k i : ℕ) :
    (localThirdPolynomial k i).coeff 0 = localSecondConstant k i := by
  unfold localThirdPolynomial localSecondConstant finsetAffineConstant
  simp [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_prod]

private lemma affinePolynomial_coeff_one_fifth_certificate
    {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℤ) :
    (∏ x ∈ s, (Polynomial.X + Polynomial.C (f x))).coeff 1 =
      finsetAffineLinear s f := by
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty]
      rw [Polynomial.coeff_one]
      simp [finsetAffineLinear]
  | @insert a s ha ih =>
      have hzero :
          (∏ x ∈ s, (Polynomial.X + Polynomial.C (f x))).coeff 0 =
            finsetAffineConstant s f := by
        rw [Polynomial.coeff_zero_eq_eval_zero]
        simp [finsetAffineConstant, Polynomial.eval_prod]
      have hleftZero :
          (Polynomial.X + Polynomial.C (f a)).coeff 0 = f a := by
        rw [Polynomial.coeff_add, Polynomial.coeff_X,
          Polynomial.coeff_C_zero]
        norm_num
      have hCOne : (Polynomial.C (f a)).coeff 1 = 0 :=
        Polynomial.coeff_C_ne_zero (by norm_num)
      have hleftOne :
          (Polynomial.X + Polynomial.C (f a)).coeff 1 = 1 := by
        rw [Polynomial.coeff_add, Polynomial.coeff_X, hCOne]
        norm_num
      rw [Finset.prod_insert ha, Polynomial.mul_coeff_one, ih,
        finsetAffineLinear_insert f ha, hzero, hleftZero, hleftOne]
      ring

private lemma localThirdPolynomial_coeff_one_fifth (k i : ℕ) :
    (localThirdPolynomial k i).coeff 1 = localSecondLinear k i := by
  unfold localThirdPolynomial localSecondLinear
  exact affinePolynomial_coeff_one_fifth_certificate
    ((Finset.Icc 1 k).erase i) (fun j => (j : ℤ) - (i : ℤ))

/-- The computable recurrence agrees with all five Taylor coefficients used
by the fourth/fifth eliminants. -/
theorem fifthLocalCoefficients_eq_localTaylor (k i : ℕ) :
    let s := fifthLocalCoefficients k i
    s.c0 = localSecondConstant k i ∧
    s.c1 = localSecondLinear k i ∧
    s.c2 = localThirdQuadratic k i ∧
    s.c3 = localFourthCubic k i ∧
    s.c4 = localFifthQuartic k i := by
  dsimp [fifthLocalCoefficients]
  have hpoly := localThirdPolynomial_eq_fifthAffinePolynomial k i
  constructor
  · rw [← localThirdPolynomial_coeff_zero_fifth, hpoly,
      fifthAffineCoefficients_coeff_zero]
  constructor
  · rw [← localThirdPolynomial_coeff_one_fifth, hpoly,
      fifthAffineCoefficients_coeff_one]
  constructor
  · simp only [localThirdQuadratic]
    rw [hpoly, fifthAffineCoefficients_coeff_two]
  constructor
  · simp only [localFourthCubic]
    rw [hpoly, fifthAffineCoefficients_coeff_three]
  · simp only [localFifthQuartic]
    rw [hpoly, fifthAffineCoefficients_coeff_four]

/-! ## Soundness of the finite leading-sign and remainder certificate -/

def threeBucketFourthEliminant
    (C D E K X gap deltaLeft deltaRight : ℤ) : ℤ :=
  let Y := X - 3 * deltaLeft
  let Z := X - 3 * deltaRight
  let delta := deltaLeft * deltaRight
  27 * C ^ 2 *
      (-9 * C * X * (Y * Z) ^ 2 +
        delta * gap ^ 2 * Y * Z * (180 * E * gap + 108 * D)) +
    gap ^ 4 * K

def fifthEliminantLeading
    (C E R1 X gap deltaLeft deltaRight : ℤ) : ℤ :=
  -6561 * C ^ 3 * X ^ 5 +
    131220 * C ^ 2 * E * (deltaLeft * deltaRight) * X ^ 2 * gap ^ 3 +
    R1 * gap ^ 5

def fourthEliminantLeading
    (C E X gap deltaLeft deltaRight : ℤ) : ℤ :=
  -243 * C ^ 3 * X ^ 5 +
    4860 * C ^ 2 * E * (deltaLeft * deltaRight) * X ^ 2 * gap ^ 3

/-- Exact elimination identity for the named fourth quotient. -/
theorem three_bucket_fourth_eliminant_identity
    {C D E K X gap deltaLeft deltaRight Y Z t T b c z P w g : ℤ}
    (hY : Y = X - 3 * deltaLeft)
    (hZ : Z = X - 3 * deltaRight)
    (hproduct : gap ^ 2 * t = g ^ 2 * X * Y * Z)
    (hthird :
      T = -9 * C * t +
        (deltaLeft * deltaRight) * g ^ 2 *
          (180 * E * gap + 108 * D))
    (hopposite : gap ^ 2 * b * c * z = g ^ 2 * Y * Z * T)
    (hfourth : P * w = 27 * C ^ 2 * b * c * z + K * g ^ 4) :
    gap ^ 4 * P * w =
      g ^ 4 * threeBucketFourthEliminant
        C D E K X gap deltaLeft deltaRight := by
  have hcore :
      gap ^ 4 * b * c * z =
        g ^ 4 *
          (-9 * C * X * (Y * Z) ^ 2 +
            (deltaLeft * deltaRight) * gap ^ 2 * Y * Z *
              (180 * E * gap + 108 * D)) := by
    calc
      gap ^ 4 * b * c * z = gap ^ 2 * (gap ^ 2 * b * c * z) := by ring
      _ = gap ^ 2 * (g ^ 2 * Y * Z * T) := by rw [hopposite]
      _ = gap ^ 2 * (g ^ 2 * Y * Z *
          (-9 * C * t + (deltaLeft * deltaRight) * g ^ 2 *
            (180 * E * gap + 108 * D))) := by rw [hthird]
      _ = -9 * C * g ^ 2 * Y * Z * (gap ^ 2 * t) +
          (deltaLeft * deltaRight) * gap ^ 2 * g ^ 4 * Y * Z *
            (180 * E * gap + 108 * D) := by ring
      _ = -9 * C * g ^ 2 * Y * Z * (g ^ 2 * X * Y * Z) +
          (deltaLeft * deltaRight) * gap ^ 2 * g ^ 4 * Y * Z *
            (180 * E * gap + 108 * D) := by rw [hproduct]
      _ = g ^ 4 *
          (-9 * C * X * (Y * Z) ^ 2 +
            (deltaLeft * deltaRight) * gap ^ 2 * Y * Z *
              (180 * E * gap + 108 * D)) := by ring
  calc
    gap ^ 4 * P * w = gap ^ 4 * (P * w) := by ring
    _ = gap ^ 4 * (27 * C ^ 2 * b * c * z + K * g ^ 4) := by rw [hfourth]
    _ = 27 * C ^ 2 * (gap ^ 4 * b * c * z) + gap ^ 4 * K * g ^ 4 := by ring
    _ = 27 * C ^ 2 *
          (g ^ 4 *
            (-9 * C * X * (Y * Z) ^ 2 +
              (deltaLeft * deltaRight) * gap ^ 2 * Y * Z *
                (180 * E * gap + 108 * D))) + gap ^ 4 * K * g ^ 4 := by
      rw [hcore]
    _ = g ^ 4 * threeBucketFourthEliminant
          C D E K X gap deltaLeft deltaRight := by
      rw [hY, hZ]
      simp only [threeBucketFourthEliminant]
      ring

lemma fifthMonomialLower_le
    {a : ℤ} {lo hi x : ℚ} {power : ℕ}
    (hlo0 : 0 ≤ lo) (hlo : lo ≤ x) (hhi : x ≤ hi) :
    fifthMonomialLower a lo hi power ≤ (a : ℚ) * x ^ power := by
  by_cases ha : 0 ≤ a
  · simp only [fifthMonomialLower, if_pos ha]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hlo0 hlo power) (by exact_mod_cast ha)
  · simp only [fifthMonomialLower, if_neg ha]
    have hhi0 : 0 ≤ hi := le_trans (le_trans hlo0 hlo) hhi
    exact mul_le_mul_of_nonpos_left
      (pow_le_pow_left₀ (le_trans hlo0 hlo) hhi power)
      (by exact_mod_cast (le_of_not_ge ha))

lemma fifthMonomial_le_upper
    {a : ℤ} {lo hi x : ℚ} {power : ℕ}
    (hlo0 : 0 ≤ lo) (hlo : lo ≤ x) (hhi : x ≤ hi) :
    (a : ℚ) * x ^ power ≤ fifthMonomialUpper a lo hi power := by
  by_cases ha : 0 ≤ a
  · simp only [fifthMonomialUpper, if_pos ha]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (le_trans hlo0 hlo) hhi power)
      (by exact_mod_cast ha)
  · simp only [fifthMonomialUpper, if_neg ha]
    exact mul_le_mul_of_nonpos_left
      (pow_le_pow_left₀ hlo0 hlo power)
      (by exact_mod_cast (le_of_not_ge ha))

lemma leading_separated_of_interval_certificate
    {a b c : ℤ} {lo hi x : ℚ}
    (hlo0 : 0 ≤ lo) (hlo : lo ≤ x) (hhi : x ≤ hi)
    (hcert :
      (1 : ℚ) < fifthMonomialLower a lo hi 5 +
          fifthMonomialLower b lo hi 2 + c ∨
        fifthMonomialUpper a lo hi 5 +
          fifthMonomialUpper b lo hi 2 + c < (-1 : ℚ)) :
    (1 : ℚ) < (a : ℚ) * x ^ 5 + (b : ℚ) * x ^ 2 + c ∨
      (a : ℚ) * x ^ 5 + (b : ℚ) * x ^ 2 + c < (-1 : ℚ) := by
  have hamin := fifthMonomialLower_le (a := a) (power := 5) hlo0 hlo hhi
  have hbmin := fifthMonomialLower_le (a := b) (power := 2) hlo0 hlo hhi
  have hamax := fifthMonomial_le_upper (a := a) (power := 5) hlo0 hlo hhi
  have hbmax := fifthMonomial_le_upper (a := b) (power := 2) hlo0 hlo hhi
  rcases hcert with hcert | hcert
  · left
    linarith
  · right
    linarith

lemma fifth_shift_natAbs_le
    {X delta gap : ℤ}
    (hgap : 1 ≤ Int.natAbs gap)
    (hX : Int.natAbs X ≤ 36 * Int.natAbs gap)
    (hdelta : Int.natAbs delta ≤ 15) :
    Int.natAbs (X - 3 * delta) ≤ 81 * Int.natAbs gap := by
  calc
    Int.natAbs (X - 3 * delta) ≤
        Int.natAbs X + Int.natAbs (3 * delta) := Int.natAbs_sub_le _ _
    _ = Int.natAbs X + 3 * Int.natAbs delta := by
      simp [Int.natAbs_mul]
    _ ≤ 36 * Int.natAbs gap + 3 * 15 :=
      Nat.add_le_add hX (Nat.mul_le_mul_left 3 hdelta)
    _ ≤ 81 * Int.natAbs gap := by omega

lemma fifth_shift_product_natAbs_le
    {X deltaLeft deltaRight gap : ℤ}
    (hgap : 1 ≤ Int.natAbs gap)
    (hX : Int.natAbs X ≤ 36 * Int.natAbs gap)
    (hleft : Int.natAbs deltaLeft ≤ 15)
    (hright : Int.natAbs deltaRight ≤ 15) :
    Int.natAbs ((X - 3 * deltaLeft) * (X - 3 * deltaRight)) ≤
      6561 * Int.natAbs gap ^ 2 := by
  have hY := fifth_shift_natAbs_le hgap hX hleft
  have hZ := fifth_shift_natAbs_le hgap hX hright
  rw [Int.natAbs_mul]
  calc
    Int.natAbs (X - 3 * deltaLeft) *
        Int.natAbs (X - 3 * deltaRight) ≤
      (81 * Int.natAbs gap) * (81 * Int.natAbs gap) :=
        Nat.mul_le_mul hY hZ
    _ = 6561 * Int.natAbs gap ^ 2 := by ring

lemma fifth_shift_product_sub_sq_natAbs_le
    {X deltaLeft deltaRight gap : ℤ}
    (hgap : 1 ≤ Int.natAbs gap)
    (hX : Int.natAbs X ≤ 36 * Int.natAbs gap)
    (hleft : Int.natAbs deltaLeft ≤ 15)
    (hright : Int.natAbs deltaRight ≤ 15) :
    Int.natAbs
        ((X - 3 * deltaLeft) * (X - 3 * deltaRight) - X ^ 2) ≤
      5265 * Int.natAbs gap := by
  have hsum : Int.natAbs (deltaLeft + deltaRight) ≤ 30 := by
    calc
      Int.natAbs (deltaLeft + deltaRight) ≤
          Int.natAbs deltaLeft + Int.natAbs deltaRight :=
        Int.natAbs_add_le _ _
      _ ≤ 15 + 15 := Nat.add_le_add hleft hright
      _ = 30 := by norm_num
  have hfirst :
      3 * Int.natAbs (deltaLeft + deltaRight) * Int.natAbs X ≤
        3240 * Int.natAbs gap := by
    calc
      3 * Int.natAbs (deltaLeft + deltaRight) * Int.natAbs X ≤
          3 * 30 * (36 * Int.natAbs gap) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 3 hsum) hX
      _ = 3240 * Int.natAbs gap := by ring
  have hsecond :
      9 * Int.natAbs deltaLeft * Int.natAbs deltaRight ≤
        2025 * Int.natAbs gap := by
    calc
      9 * Int.natAbs deltaLeft * Int.natAbs deltaRight ≤ 9 * 15 * 15 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 9 hleft) hright
      _ ≤ 2025 * Int.natAbs gap := by omega
  have hid :
      (X - 3 * deltaLeft) * (X - 3 * deltaRight) - X ^ 2 =
        -3 * (deltaLeft + deltaRight) * X + 9 * deltaLeft * deltaRight := by
    ring
  rw [hid]
  calc
    Int.natAbs
        (-3 * (deltaLeft + deltaRight) * X + 9 * deltaLeft * deltaRight) ≤
      Int.natAbs (-3 * (deltaLeft + deltaRight) * X) +
        Int.natAbs (9 * deltaLeft * deltaRight) := Int.natAbs_add_le _ _
    _ = 3 * Int.natAbs (deltaLeft + deltaRight) * Int.natAbs X +
        9 * Int.natAbs deltaLeft * Int.natAbs deltaRight := by
      simp [Int.natAbs_mul]
    _ ≤ 3240 * Int.natAbs gap + 2025 * Int.natAbs gap :=
      Nat.add_le_add hfirst hsecond
    _ = 5265 * Int.natAbs gap := by ring

lemma fifth_shift_product_add_sq_natAbs_le
    {X deltaLeft deltaRight gap : ℤ}
    (hgap : 1 ≤ Int.natAbs gap)
    (hX : Int.natAbs X ≤ 36 * Int.natAbs gap)
    (hleft : Int.natAbs deltaLeft ≤ 15)
    (hright : Int.natAbs deltaRight ≤ 15) :
    Int.natAbs
        ((X - 3 * deltaLeft) * (X - 3 * deltaRight) + X ^ 2) ≤
      7857 * Int.natAbs gap ^ 2 := by
  have hYZ := fifth_shift_product_natAbs_le hgap hX hleft hright
  have hXsq : Int.natAbs (X ^ 2) ≤ 1296 * Int.natAbs gap ^ 2 := by
    rw [Int.natAbs_pow]
    calc
      Int.natAbs X ^ 2 ≤ (36 * Int.natAbs gap) ^ 2 :=
        Nat.pow_le_pow_left hX 2
      _ = 1296 * Int.natAbs gap ^ 2 := by ring
  calc
    Int.natAbs
        ((X - 3 * deltaLeft) * (X - 3 * deltaRight) + X ^ 2) ≤
      Int.natAbs ((X - 3 * deltaLeft) * (X - 3 * deltaRight)) +
        Int.natAbs (X ^ 2) := Int.natAbs_add_le _ _
    _ ≤ 6561 * Int.natAbs gap ^ 2 + 1296 * Int.natAbs gap ^ 2 :=
      Nat.add_le_add hYZ hXsq
    _ = 7857 * Int.natAbs gap ^ 2 := by ring

lemma fifth_shift_square_difference_natAbs_le
    {X deltaLeft deltaRight gap : ℤ}
    (hgap : 1 ≤ Int.natAbs gap)
    (hX : Int.natAbs X ≤ 36 * Int.natAbs gap)
    (hleft : Int.natAbs deltaLeft ≤ 15)
    (hright : Int.natAbs deltaRight ≤ 15) :
    Int.natAbs
        (((X - 3 * deltaLeft) * (X - 3 * deltaRight)) ^ 2 - X ^ 4) ≤
      5265 * 7857 * Int.natAbs gap ^ 3 := by
  have hminus := fifth_shift_product_sub_sq_natAbs_le
    hgap hX hleft hright
  have hplus := fifth_shift_product_add_sq_natAbs_le
    hgap hX hleft hright
  have hid :
      ((X - 3 * deltaLeft) * (X - 3 * deltaRight)) ^ 2 - X ^ 4 =
        (((X - 3 * deltaLeft) * (X - 3 * deltaRight)) - X ^ 2) *
          (((X - 3 * deltaLeft) * (X - 3 * deltaRight)) + X ^ 2) := by
    ring
  rw [hid, Int.natAbs_mul]
  calc
    Int.natAbs
          ((X - 3 * deltaLeft) * (X - 3 * deltaRight) - X ^ 2) *
        Int.natAbs
          ((X - 3 * deltaLeft) * (X - 3 * deltaRight) + X ^ 2) ≤
      (5265 * Int.natAbs gap) * (7857 * Int.natAbs gap ^ 2) :=
        Nat.mul_le_mul hminus hplus
    _ = 5265 * 7857 * Int.natAbs gap ^ 3 := by ring

lemma fifth_inner_remainder_natAbs_le
    {C D E X gap deltaLeft deltaRight : ℤ}
    (hgap : 1 ≤ Int.natAbs gap)
    (hX : Int.natAbs X ≤ 36 * Int.natAbs gap)
    (hleft : Int.natAbs deltaLeft ≤ 15)
    (hright : Int.natAbs deltaRight ≤ 15) :
    let Y := X - 3 * deltaLeft
    let Z := X - 3 * deltaRight
    let delta := deltaLeft * deltaRight
    Int.natAbs
        ((-9 * C * X * (Y * Z) ^ 2 +
            delta * gap ^ 2 * Y * Z * (180 * E * gap + 108 * D)) -
          (-9 * C * X ^ 5 + 180 * E * delta * X ^ 2 * gap ^ 3)) ≤
      (9 * Int.natAbs C * 36 * 5265 * 7857 +
        Int.natAbs delta *
          (180 * Int.natAbs E * 5265 +
            108 * Int.natAbs D * 6561)) * Int.natAbs gap ^ 4 := by
  dsimp
  let Y : ℤ := X - 3 * deltaLeft
  let Z : ℤ := X - 3 * deltaRight
  let delta : ℤ := deltaLeft * deltaRight
  have hsq := fifth_shift_square_difference_natAbs_le
    hgap hX hleft hright
  have hYZ := fifth_shift_product_natAbs_le hgap hX hleft hright
  have hfirst :
      Int.natAbs (-9 * C * X * ((Y * Z) ^ 2 - X ^ 4)) ≤
        9 * Int.natAbs C * 36 * 5265 * 7857 * Int.natAbs gap ^ 4 := by
    have hmul := Nat.mul_le_mul hX hsq
    have hmul' := Nat.mul_le_mul_left (9 * Int.natAbs C) hmul
    simp only [Y, Z, Int.natAbs_mul, Int.natAbs_pow,
      Int.natAbs_natCast, Int.natAbs_neg] at hmul' ⊢
    convert hmul' using 1 <;> ring
  have hE :
      Int.natAbs (180 * E * gap * (Y * Z - X ^ 2)) ≤
        180 * Int.natAbs E * 5265 * Int.natAbs gap ^ 2 := by
    have hdiff := fifth_shift_product_sub_sq_natAbs_le
      hgap hX hleft hright
    have hmul := Nat.mul_le_mul_left
      (180 * Int.natAbs E * Int.natAbs gap) hdiff
    simp only [Y, Z, Int.natAbs_mul, Int.natAbs_natCast] at hmul ⊢
    convert hmul using 1 <;> ring
  have hD :
      Int.natAbs (108 * D * (Y * Z)) ≤
        108 * Int.natAbs D * 6561 * Int.natAbs gap ^ 2 := by
    have hmul := Nat.mul_le_mul_left (108 * Int.natAbs D) hYZ
    simp only [Y, Z, Int.natAbs_mul, Int.natAbs_natCast] at hmul ⊢
    convert hmul using 1 <;> ring
  have hinside :
      Int.natAbs
          (180 * E * gap * (Y * Z - X ^ 2) + 108 * D * (Y * Z)) ≤
        (180 * Int.natAbs E * 5265 +
          108 * Int.natAbs D * 6561) * Int.natAbs gap ^ 2 := by
    calc
      Int.natAbs
          (180 * E * gap * (Y * Z - X ^ 2) + 108 * D * (Y * Z)) ≤
        Int.natAbs (180 * E * gap * (Y * Z - X ^ 2)) +
          Int.natAbs (108 * D * (Y * Z)) := Int.natAbs_add_le _ _
      _ ≤ 180 * Int.natAbs E * 5265 * Int.natAbs gap ^ 2 +
          108 * Int.natAbs D * 6561 * Int.natAbs gap ^ 2 :=
        Nat.add_le_add hE hD
      _ = (180 * Int.natAbs E * 5265 +
          108 * Int.natAbs D * 6561) * Int.natAbs gap ^ 2 := by ring
  have hsecond :
      Int.natAbs
          (delta * gap ^ 2 *
            (180 * E * gap * (Y * Z - X ^ 2) + 108 * D * (Y * Z))) ≤
        Int.natAbs delta *
            (180 * Int.natAbs E * 5265 +
              108 * Int.natAbs D * 6561) * Int.natAbs gap ^ 4 := by
    have hmul := Nat.mul_le_mul_left
      (Int.natAbs delta * Int.natAbs gap ^ 2) hinside
    simp only [Int.natAbs_mul, Int.natAbs_pow] at hmul ⊢
    convert hmul using 1 <;> ring
  have hid :
      (-9 * C * X * (Y * Z) ^ 2 +
          delta * gap ^ 2 * Y * Z * (180 * E * gap + 108 * D)) -
        (-9 * C * X ^ 5 + 180 * E * delta * X ^ 2 * gap ^ 3) =
      -9 * C * X * ((Y * Z) ^ 2 - X ^ 4) +
        delta * gap ^ 2 *
          (180 * E * gap * (Y * Z - X ^ 2) + 108 * D * (Y * Z)) := by
    ring
  rw [hid]
  calc
    Int.natAbs
        (-9 * C * X * ((Y * Z) ^ 2 - X ^ 4) +
          delta * gap ^ 2 *
            (180 * E * gap * (Y * Z - X ^ 2) + 108 * D * (Y * Z))) ≤
      Int.natAbs (-9 * C * X * ((Y * Z) ^ 2 - X ^ 4)) +
        Int.natAbs
          (delta * gap ^ 2 *
            (180 * E * gap * (Y * Z - X ^ 2) + 108 * D * (Y * Z))) :=
      Int.natAbs_add_le _ _
    _ ≤ 9 * Int.natAbs C * 36 * 5265 * 7857 * Int.natAbs gap ^ 4 +
        Int.natAbs delta *
          (180 * Int.natAbs E * 5265 +
            108 * Int.natAbs D * 6561) * Int.natAbs gap ^ 4 :=
      Nat.add_le_add hfirst hsecond
    _ = (9 * Int.natAbs C * 36 * 5265 * 7857 +
        Int.natAbs delta *
          (180 * Int.natAbs E * 5265 +
            108 * Int.natAbs D * 6561)) * Int.natAbs gap ^ 4 := by ring

theorem fifth_eliminant_remainder_natAbs_le
    {C D E K R1 X gap deltaLeft deltaRight : ℤ}
    (hgap : 1 ≤ Int.natAbs gap)
    (hX : Int.natAbs X ≤ 36 * Int.natAbs gap)
    (hleft : Int.natAbs deltaLeft ≤ 15)
    (hright : Int.natAbs deltaRight ≤ 15) :
    Int.natAbs
        (threeBucketNormalizedFifthEliminant
            C D E K R1 X gap deltaLeft deltaRight -
          fifthEliminantLeading C E R1 X gap deltaLeft deltaRight) ≤
      fifthEliminantRemainderBound C D E K deltaLeft deltaRight *
        Int.natAbs gap ^ 4 := by
  let inner : ℤ :=
    (-9 * C * X *
          ((X - 3 * deltaLeft) * (X - 3 * deltaRight)) ^ 2 +
      (deltaLeft * deltaRight) * gap ^ 2 *
        (X - 3 * deltaLeft) * (X - 3 * deltaRight) *
          (180 * E * gap + 108 * D)) -
      (-9 * C * X ^ 5 +
        180 * E * (deltaLeft * deltaRight) * X ^ 2 * gap ^ 3)
  let B : ℕ :=
    9 * Int.natAbs C * 36 * 5265 * 7857 +
      Int.natAbs (deltaLeft * deltaRight) *
        (180 * Int.natAbs E * 5265 + 108 * Int.natAbs D * 6561)
  have hinner : Int.natAbs inner ≤ B * Int.natAbs gap ^ 4 := by
    simpa [inner, B] using
      (fifth_inner_remainder_natAbs_le
        (C := C) (D := D) (E := E) hgap hX hleft hright)
  have hfirst :
      Int.natAbs (729 * C ^ 2 * inner) ≤
        729 * Int.natAbs C ^ 2 * B * Int.natAbs gap ^ 4 := by
    have hmul := Nat.mul_le_mul_left (729 * Int.natAbs C ^ 2) hinner
    simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast] at hmul ⊢
    convert hmul using 1 <;> ring
  have hsecond :
      Int.natAbs (27 * K * gap ^ 4) =
        27 * Int.natAbs K * Int.natAbs gap ^ 4 := by
    simp [Int.natAbs_mul, Int.natAbs_pow]
  have hid :
      threeBucketNormalizedFifthEliminant
          C D E K R1 X gap deltaLeft deltaRight -
        fifthEliminantLeading C E R1 X gap deltaLeft deltaRight =
      729 * C ^ 2 * inner + 27 * K * gap ^ 4 := by
    simp only [threeBucketNormalizedFifthEliminant,
      fifthEliminantLeading, inner]
    ring
  rw [hid]
  calc
    Int.natAbs (729 * C ^ 2 * inner + 27 * K * gap ^ 4) ≤
      Int.natAbs (729 * C ^ 2 * inner) +
        Int.natAbs (27 * K * gap ^ 4) := Int.natAbs_add_le _ _
    _ ≤ 729 * Int.natAbs C ^ 2 * B * Int.natAbs gap ^ 4 +
        27 * Int.natAbs K * Int.natAbs gap ^ 4 := by
      rw [hsecond]
      exact Nat.add_le_add_right hfirst _
    _ = fifthEliminantRemainderBound C D E K deltaLeft deltaRight *
        Int.natAbs gap ^ 4 := by
      simp only [fifthEliminantRemainderBound, B]
      ring

theorem fourth_eliminant_remainder_natAbs_le
    {C D E K X gap deltaLeft deltaRight : ℤ}
    (hgap : 1 ≤ Int.natAbs gap)
    (hX : Int.natAbs X ≤ 36 * Int.natAbs gap)
    (hleft : Int.natAbs deltaLeft ≤ 15)
    (hright : Int.natAbs deltaRight ≤ 15) :
    Int.natAbs
        (threeBucketFourthEliminant
            C D E K X gap deltaLeft deltaRight -
          fourthEliminantLeading C E X gap deltaLeft deltaRight) ≤
      fourthEliminantRemainderBound C D E K deltaLeft deltaRight *
        Int.natAbs gap ^ 4 := by
  let inner : ℤ :=
    (-9 * C * X *
          ((X - 3 * deltaLeft) * (X - 3 * deltaRight)) ^ 2 +
      (deltaLeft * deltaRight) * gap ^ 2 *
        (X - 3 * deltaLeft) * (X - 3 * deltaRight) *
          (180 * E * gap + 108 * D)) -
      (-9 * C * X ^ 5 +
        180 * E * (deltaLeft * deltaRight) * X ^ 2 * gap ^ 3)
  let B : ℕ :=
    9 * Int.natAbs C * 36 * 5265 * 7857 +
      Int.natAbs (deltaLeft * deltaRight) *
        (180 * Int.natAbs E * 5265 + 108 * Int.natAbs D * 6561)
  have hinner : Int.natAbs inner ≤ B * Int.natAbs gap ^ 4 := by
    simpa [inner, B] using
      (fifth_inner_remainder_natAbs_le
        (C := C) (D := D) (E := E) hgap hX hleft hright)
  have hfirst :
      Int.natAbs (27 * C ^ 2 * inner) ≤
        27 * Int.natAbs C ^ 2 * B * Int.natAbs gap ^ 4 := by
    have hmul := Nat.mul_le_mul_left (27 * Int.natAbs C ^ 2) hinner
    simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast] at hmul ⊢
    convert hmul using 1 <;> ring
  have hsecond :
      Int.natAbs (K * gap ^ 4) =
        Int.natAbs K * Int.natAbs gap ^ 4 := by
    simp [Int.natAbs_mul, Int.natAbs_pow]
  have hid :
      threeBucketFourthEliminant
          C D E K X gap deltaLeft deltaRight -
        fourthEliminantLeading C E X gap deltaLeft deltaRight =
      27 * C ^ 2 * inner + K * gap ^ 4 := by
    simp only [threeBucketFourthEliminant,
      fourthEliminantLeading, inner]
    ring
  rw [hid]
  calc
    Int.natAbs (27 * C ^ 2 * inner + K * gap ^ 4) ≤
      Int.natAbs (27 * C ^ 2 * inner) + Int.natAbs (K * gap ^ 4) :=
        Int.natAbs_add_le _ _
    _ ≤ 27 * Int.natAbs C ^ 2 * B * Int.natAbs gap ^ 4 +
        Int.natAbs K * Int.natAbs gap ^ 4 := by
      rw [hsecond]
      exact Nat.add_le_add_right hfirst _
    _ = fourthEliminantRemainderBound C D E K deltaLeft deltaRight *
        Int.natAbs gap ^ 4 := by
      simp only [fourthEliminantRemainderBound, B]
      ring

lemma integral_leading_natAbs_gt_gap_fifth
    {a b c : ℤ} {X gap : ℕ}
    (hgap : 0 < gap)
    (hsep :
      (1 : ℚ) < (a : ℚ) * ((X : ℚ) / gap) ^ 5 +
          (b : ℚ) * ((X : ℚ) / gap) ^ 2 + c ∨
        (a : ℚ) * ((X : ℚ) / gap) ^ 5 +
          (b : ℚ) * ((X : ℚ) / gap) ^ 2 + c < (-1 : ℚ)) :
    gap ^ 5 < Int.natAbs
      (a * (X : ℤ) ^ 5 + b * (X : ℤ) ^ 2 * (gap : ℤ) ^ 3 +
        c * (gap : ℤ) ^ 5) := by
  let H : ℤ :=
    a * (X : ℤ) ^ 5 + b * (X : ℤ) ^ 2 * (gap : ℤ) ^ 3 +
      c * (gap : ℤ) ^ 5
  let f : ℚ :=
    (a : ℚ) * ((X : ℚ) / gap) ^ 5 +
      (b : ℚ) * ((X : ℚ) / gap) ^ 2 + c
  have hgapQ : (0 : ℚ) < (gap : ℚ) := by exact_mod_cast hgap
  have hgapPow : (0 : ℚ) < (gap : ℚ) ^ 5 := pow_pos hgapQ 5
  have hid : (H : ℚ) = (gap : ℚ) ^ 5 * f := by
    dsimp [H, f]
    push_cast
    field_simp
  have habsCast : ((Int.natAbs H : ℕ) : ℚ) = |(H : ℚ)| := by
    rw [Int.cast_natAbs, Int.cast_abs]
  have hrat : ((gap ^ 5 : ℕ) : ℚ) < ((Int.natAbs H : ℕ) : ℚ) := by
    rw [Nat.cast_pow, habsCast]
    rcases hsep with hsep | hsep
    · have hmul : (gap : ℚ) ^ 5 < (gap : ℚ) ^ 5 * f := by
        simpa using mul_lt_mul_of_pos_left hsep hgapPow
      rw [← hid] at hmul
      exact lt_of_lt_of_le hmul (le_abs_self _)
    · have hmul : (gap : ℚ) ^ 5 * f < -(gap : ℚ) ^ 5 := by
        have := mul_lt_mul_of_pos_left hsep hgapPow
        linarith
      rw [← hid] at hmul
      have hneg : (gap : ℚ) ^ 5 < -(H : ℚ) := by linarith
      exact lt_of_lt_of_le hneg (neg_le_abs _)
  exact_mod_cast hrat

theorem fifth_eliminant_ne_zero_of_interval_certificate
    {C D E K R1 X gap deltaLeft deltaRight : ℤ}
    {Xnat gapNat : ℕ}
    (hXcast : X = (Xnat : ℤ)) (hgapCast : gap = (gapNat : ℤ))
    (hgapTarget : 10 ^ 1000 ≤ gapNat)
    (hXbound : Xnat ≤ 36 * gapNat)
    (hleft : Int.natAbs deltaLeft ≤ 15)
    (hright : Int.natAbs deltaRight ≤ 15)
    (hsep :
      (1 : ℚ) < (-6561 * C ^ 3 : ℤ) *
          ((Xnat : ℚ) / gapNat) ^ 5 +
          (131220 * C ^ 2 * E * (deltaLeft * deltaRight) : ℤ) *
            ((Xnat : ℚ) / gapNat) ^ 2 + R1 ∨
        (-6561 * C ^ 3 : ℤ) * ((Xnat : ℚ) / gapNat) ^ 5 +
          (131220 * C ^ 2 * E * (deltaLeft * deltaRight) : ℤ) *
            ((Xnat : ℚ) / gapNat) ^ 2 + R1 < (-1 : ℚ))
    (hB : fifthEliminantRemainderBound C D E K deltaLeft deltaRight <
      10 ^ 80) :
    threeBucketNormalizedFifthEliminant
      C D E K R1 X gap deltaLeft deltaRight ≠ 0 := by
  subst X
  subst gap
  have hgapPos : 0 < gapNat := lt_of_lt_of_le (by norm_num) hgapTarget
  have hgapAbs : Int.natAbs (gapNat : ℤ) = gapNat := by simp
  have hXAbs : Int.natAbs (Xnat : ℤ) = Xnat := by simp
  have hgapOne : 1 ≤ Int.natAbs (gapNat : ℤ) := by simp; omega
  let H := fifthEliminantLeading C E R1 (Xnat : ℤ) (gapNat : ℤ)
      deltaLeft deltaRight
  have hlead : gapNat ^ 5 < Int.natAbs H := by
    simpa [H, fifthEliminantLeading] using
      (integral_leading_natAbs_gt_gap_fifth
        (a := -6561 * C ^ 3)
        (b := 131220 * C ^ 2 * E * (deltaLeft * deltaRight))
        (c := R1) hgapPos hsep)
  have hrem := fifth_eliminant_remainder_natAbs_le
    (C := C) (D := D) (E := E) (K := K) (R1 := R1)
    (X := (Xnat : ℤ)) (gap := (gapNat : ℤ))
    (deltaLeft := deltaLeft) (deltaRight := deltaRight)
    hgapOne (by simpa [hXAbs, hgapAbs] using hXbound) hleft hright
  have hBGap : fifthEliminantRemainderBound C D E K deltaLeft deltaRight <
      gapNat := by
    calc
      fifthEliminantRemainderBound C D E K deltaLeft deltaRight < 10 ^ 80 := hB
      _ < 10 ^ 1000 := Nat.pow_lt_pow_right (by norm_num) (by norm_num)
      _ ≤ gapNat := hgapTarget
  have hremLt :
      Int.natAbs
          (threeBucketNormalizedFifthEliminant C D E K R1
              (Xnat : ℤ) (gapNat : ℤ) deltaLeft deltaRight - H) <
        gapNat ^ 5 := by
    calc
      Int.natAbs
          (threeBucketNormalizedFifthEliminant C D E K R1
              (Xnat : ℤ) (gapNat : ℤ) deltaLeft deltaRight - H) ≤
        fifthEliminantRemainderBound C D E K deltaLeft deltaRight *
          gapNat ^ 4 := by simpa [H, hgapAbs] using hrem
      _ < gapNat * gapNat ^ 4 :=
        Nat.mul_lt_mul_of_pos_right hBGap (pow_pos hgapPos 4)
      _ = gapNat ^ 5 := by ring
  intro hzero
  have heq :
      Int.natAbs H =
        Int.natAbs
          (threeBucketNormalizedFifthEliminant C D E K R1
              (Xnat : ℤ) (gapNat : ℤ) deltaLeft deltaRight - H) := by
    rw [hzero]
    simp
  omega

theorem fourth_eliminant_ne_zero_of_interval_certificate
    {C D E K X gap deltaLeft deltaRight : ℤ}
    {Xnat gapNat : ℕ}
    (hXcast : X = (Xnat : ℤ)) (hgapCast : gap = (gapNat : ℤ))
    (hgapTarget : 10 ^ 1000 ≤ gapNat)
    (hXbound : Xnat ≤ 36 * gapNat)
    (hleft : Int.natAbs deltaLeft ≤ 15)
    (hright : Int.natAbs deltaRight ≤ 15)
    (hsep :
      (1 : ℚ) < (-243 * C ^ 3 : ℤ) * ((Xnat : ℚ) / gapNat) ^ 5 +
          (4860 * C ^ 2 * E * (deltaLeft * deltaRight) : ℤ) *
            ((Xnat : ℚ) / gapNat) ^ 2 ∨
        (-243 * C ^ 3 : ℤ) * ((Xnat : ℚ) / gapNat) ^ 5 +
          (4860 * C ^ 2 * E * (deltaLeft * deltaRight) : ℤ) *
            ((Xnat : ℚ) / gapNat) ^ 2 < (-1 : ℚ))
    (hB : fourthEliminantRemainderBound C D E K deltaLeft deltaRight <
      10 ^ 80) :
    threeBucketFourthEliminant C D E K X gap deltaLeft deltaRight ≠ 0 := by
  subst X
  subst gap
  have hgapPos : 0 < gapNat := lt_of_lt_of_le (by norm_num) hgapTarget
  have hgapAbs : Int.natAbs (gapNat : ℤ) = gapNat := by simp
  have hXAbs : Int.natAbs (Xnat : ℤ) = Xnat := by simp
  have hgapOne : 1 ≤ Int.natAbs (gapNat : ℤ) := by simp; omega
  let H := fourthEliminantLeading C E (Xnat : ℤ) (gapNat : ℤ)
      deltaLeft deltaRight
  have hlead : gapNat ^ 5 < Int.natAbs H := by
    have hraw := integral_leading_natAbs_gt_gap_fifth
        (a := -243 * C ^ 3)
        (b := 4860 * C ^ 2 * E * (deltaLeft * deltaRight))
        (c := 0) hgapPos (by simpa using hsep)
    simp only [H, fourthEliminantLeading]
    convert hraw using 1 <;> ring
  have hrem := fourth_eliminant_remainder_natAbs_le
    (C := C) (D := D) (E := E) (K := K)
    (X := (Xnat : ℤ)) (gap := (gapNat : ℤ))
    (deltaLeft := deltaLeft) (deltaRight := deltaRight)
    hgapOne (by simpa [hXAbs, hgapAbs] using hXbound) hleft hright
  have hBGap : fourthEliminantRemainderBound C D E K deltaLeft deltaRight <
      gapNat := by
    calc
      fourthEliminantRemainderBound C D E K deltaLeft deltaRight < 10 ^ 80 := hB
      _ < 10 ^ 1000 := Nat.pow_lt_pow_right (by norm_num) (by norm_num)
      _ ≤ gapNat := hgapTarget
  have hremLt :
      Int.natAbs
          (threeBucketFourthEliminant C D E K
              (Xnat : ℤ) (gapNat : ℤ) deltaLeft deltaRight - H) <
        gapNat ^ 5 := by
    calc
      Int.natAbs
          (threeBucketFourthEliminant C D E K
              (Xnat : ℤ) (gapNat : ℤ) deltaLeft deltaRight - H) ≤
        fourthEliminantRemainderBound C D E K deltaLeft deltaRight *
          gapNat ^ 4 := by simpa [H, hgapAbs] using hrem
      _ < gapNat * gapNat ^ 4 :=
        Nat.mul_lt_mul_of_pos_right hBGap (pow_pos hgapPos 4)
      _ = gapNat ^ 5 := by ring
  intro hzero
  have heq :
      Int.natAbs H =
        Int.natAbs
          (threeBucketFourthEliminant C D E K
              (Xnat : ℤ) (gapNat : ℤ) deltaLeft deltaRight - H) := by
    rw [hzero]
    simp
  omega

set_option maxHeartbeats 100000000 in
-- The ordinary-kernel evaluator checks the full 3,024-position geometry table.
set_option maxRecDepth 1000000 in
theorem fifth_quotient_target_position_geometry_certificate :
    ∀ p ∈ fifthQuotientTargetPositions,
      (0 : ℚ) ≤ fifthResidualRatioLower p.k ∧
      fifthResidualRatioLower p.k ≤ fifthResidualRatioUpper p.k ∧
      fifthResidualRatioUpper p.k ≤ 36 ∧
      Int.natAbs ((p.owner : ℤ) - (p.left : ℤ)) ≤ 15 ∧
      Int.natAbs ((p.owner : ℤ) - (p.right : ℤ)) ≤ 15 := by
  decide +kernel

set_option maxHeartbeats 100000000 in
-- The exact interval and remainder argument specializes the full finite table.
set_option maxRecDepth 1000000 in
theorem fifth_quotient_target_eliminants_ne_zero_fast
    {p : FifthQuotientPosition}
    (hp : p ∈ fifthQuotientTargetPositions)
    {X gap : ℕ}
    (hgap : 10 ^ 1000 ≤ gap)
    (hXbound : X ≤ 36 * gap)
    (hratioLower : fifthResidualRatioLower p.k ≤ (X : ℚ) / gap)
    (hratioUpper : (X : ℚ) / gap ≤ fifthResidualRatioUpper p.k) :
    let s := fifthLocalCoefficients p.k p.owner
    let dl : ℤ := (p.owner : ℤ) - (p.left : ℤ)
    let dr : ℤ := (p.owner : ℤ) - (p.right : ℤ)
    let K := threeBucketReducedFourthCoefficient
      s.c0 s.c1 s.c2 s.c3 dl dr
    let R1 := threeBucketReducedFifthLinearCoefficient
      s.c0 s.c1 s.c2 s.c3 s.c4 dl dr
    threeBucketFourthEliminant s.c0 s.c1 s.c2 K
        (X : ℤ) (gap : ℤ) dl dr ≠ 0 ∧
      threeBucketNormalizedFifthEliminant s.c0 s.c1 s.c2 K R1
        (X : ℤ) (gap : ℤ) dl dr ≠ 0 := by
  dsimp
  let s := fifthLocalCoefficients p.k p.owner
  let dl : ℤ := (p.owner : ℤ) - (p.left : ℤ)
  let dr : ℤ := (p.owner : ℤ) - (p.right : ℤ)
  let K := threeBucketReducedFourthCoefficient
    s.c0 s.c1 s.c2 s.c3 dl dr
  let R1 := threeBucketReducedFifthLinearCoefficient
    s.c0 s.c1 s.c2 s.c3 s.c4 dl dr
  change threeBucketFourthEliminant s.c0 s.c1 s.c2 K
        (X : ℤ) (gap : ℤ) dl dr ≠ 0 ∧
      threeBucketNormalizedFifthEliminant s.c0 s.c1 s.c2 K R1
        (X : ℤ) (gap : ℤ) dl dr ≠ 0
  have hcert := fifth_quotient_target_position_certificate p hp
  change
    (((1 : ℚ) < fifthMonomialLower (-6561 * s.c0 ^ 3)
          (fifthResidualRatioLower p.k) (fifthResidualRatioUpper p.k) 5 +
        fifthMonomialLower
          (131220 * s.c0 ^ 2 * s.c2 * (dl * dr))
          (fifthResidualRatioLower p.k) (fifthResidualRatioUpper p.k) 2 + R1 ∨
      fifthMonomialUpper (-6561 * s.c0 ^ 3)
          (fifthResidualRatioLower p.k) (fifthResidualRatioUpper p.k) 5 +
        fifthMonomialUpper
          (131220 * s.c0 ^ 2 * s.c2 * (dl * dr))
          (fifthResidualRatioLower p.k) (fifthResidualRatioUpper p.k) 2 + R1 <
          (-1 : ℚ)) ∧
    ((1 : ℚ) < fifthMonomialLower (-243 * s.c0 ^ 3)
          (fifthResidualRatioLower p.k) (fifthResidualRatioUpper p.k) 5 +
        fifthMonomialLower (4860 * s.c0 ^ 2 * s.c2 * (dl * dr))
          (fifthResidualRatioLower p.k) (fifthResidualRatioUpper p.k) 2 ∨
      fifthMonomialUpper (-243 * s.c0 ^ 3)
          (fifthResidualRatioLower p.k) (fifthResidualRatioUpper p.k) 5 +
        fifthMonomialUpper (4860 * s.c0 ^ 2 * s.c2 * (dl * dr))
          (fifthResidualRatioLower p.k) (fifthResidualRatioUpper p.k) 2 <
          (-1 : ℚ)) ∧
    fifthEliminantRemainderBound s.c0 s.c1 s.c2 K dl dr < 10 ^ 80 ∧
    fourthEliminantRemainderBound s.c0 s.c1 s.c2 K dl dr < 10 ^ 80) at hcert
  have hgeometry := fifth_quotient_target_position_geometry_certificate p hp
  change (0 : ℚ) ≤ fifthResidualRatioLower p.k ∧
      fifthResidualRatioLower p.k ≤ fifthResidualRatioUpper p.k ∧
      fifthResidualRatioUpper p.k ≤ 36 ∧
      Int.natAbs dl ≤ 15 ∧ Int.natAbs dr ≤ 15 at hgeometry
  have hsep5 := leading_separated_of_interval_certificate
    hgeometry.1 hratioLower hratioUpper hcert.1
  have hsep4 := leading_separated_of_interval_certificate
    (a := -243 * s.c0 ^ 3)
    (b := 4860 * s.c0 ^ 2 * s.c2 * (dl * dr)) (c := 0)
    hgeometry.1 hratioLower hratioUpper (by simpa using hcert.2.1)
  constructor
  · exact fourth_eliminant_ne_zero_of_interval_certificate
      (C := s.c0) (D := s.c1) (E := s.c2) (K := K)
      (X := (X : ℤ)) (gap := (gap : ℤ))
      (deltaLeft := dl) (deltaRight := dr)
      rfl rfl hgap hXbound hgeometry.2.2.2.1 hgeometry.2.2.2.2
      (by simpa using hsep4) hcert.2.2.2
  · exact fifth_eliminant_ne_zero_of_interval_certificate
      (C := s.c0) (D := s.c1) (E := s.c2) (K := K) (R1 := R1)
      (X := (X : ℤ)) (gap := (gap : ℤ))
      (deltaLeft := dl) (deltaRight := dr)
      rfl rfl hgap hXbound hgeometry.2.2.2.1 hgeometry.2.2.2.2
      (by simpa using hsep5) hcert.2.2.1

theorem fifth_quotient_target_eliminants_ne_zero
    {p : FifthQuotientPosition}
    (hp : p ∈ fifthQuotientTargetPositions)
    {X gap : ℕ}
    (hgap : 10 ^ 1000 ≤ gap)
    (hXbound : X ≤ 36 * gap)
    (hratioLower : fifthResidualRatioLower p.k ≤ (X : ℚ) / gap)
    (hratioUpper : (X : ℚ) / gap ≤ fifthResidualRatioUpper p.k) :
    let C := localSecondConstant p.k p.owner
    let D := localSecondLinear p.k p.owner
    let E := localThirdQuadratic p.k p.owner
    let F := localFourthCubic p.k p.owner
    let G := localFifthQuartic p.k p.owner
    let dl : ℤ := (p.owner : ℤ) - (p.left : ℤ)
    let dr : ℤ := (p.owner : ℤ) - (p.right : ℤ)
    let K := threeBucketReducedFourthCoefficient C D E F dl dr
    let R1 := threeBucketReducedFifthLinearCoefficient C D E F G dl dr
    threeBucketFourthEliminant C D E K (X : ℤ) (gap : ℤ) dl dr ≠ 0 ∧
      threeBucketNormalizedFifthEliminant C D E K R1
        (X : ℤ) (gap : ℤ) dl dr ≠ 0 := by
  have hfast := fifth_quotient_target_eliminants_ne_zero_fast
    hp hgap hXbound hratioLower hratioUpper
  have hc := fifthLocalCoefficients_eq_localTaylor p.k p.owner
  rcases hc with ⟨hc0, hc1, hc2, hc3, hc4⟩
  dsimp at hfast ⊢
  rw [hc0, hc1, hc2, hc3, hc4] at hfast
  exact hfast

noncomputable def fifthPositionC (p : FifthQuotientPosition) : ℤ :=
  localSecondConstant p.k p.owner

noncomputable def fifthPositionD (p : FifthQuotientPosition) : ℤ :=
  localSecondLinear p.k p.owner

noncomputable def fifthPositionE (p : FifthQuotientPosition) : ℤ :=
  localThirdQuadratic p.k p.owner

noncomputable def fifthPositionF (p : FifthQuotientPosition) : ℤ :=
  localFourthCubic p.k p.owner

noncomputable def fifthPositionG (p : FifthQuotientPosition) : ℤ :=
  localFifthQuartic p.k p.owner

def fifthPositionDeltaLeft (p : FifthQuotientPosition) : ℤ :=
  (p.owner : ℤ) - (p.left : ℤ)

def fifthPositionDeltaRight (p : FifthQuotientPosition) : ℤ :=
  (p.owner : ℤ) - (p.right : ℤ)

noncomputable def fifthPositionK (p : FifthQuotientPosition) : ℤ :=
  threeBucketReducedFourthCoefficient
    (fifthPositionC p) (fifthPositionD p) (fifthPositionE p)
    (fifthPositionF p) (fifthPositionDeltaLeft p) (fifthPositionDeltaRight p)

noncomputable def fifthPositionR1 (p : FifthQuotientPosition) : ℤ :=
  threeBucketReducedFifthLinearCoefficient
    (fifthPositionC p) (fifthPositionD p) (fifthPositionE p)
    (fifthPositionF p) (fifthPositionG p)
    (fifthPositionDeltaLeft p) (fifthPositionDeltaRight p)

/-- Equation-facing endpoint of the finite certificate: once the exact
product, third-quotient, fourth-quotient, and normalized fifth identities are
supplied at a certified target position, both named quotients are nonzero. -/
theorem fifth_quotient_target_fourth_and_normalized_nonzero
    {p : FifthQuotientPosition}
    (hp : p ∈ fifthQuotientTargetPositions)
    {X gap : ℕ}
    (hgapTarget : 10 ^ 1000 ≤ gap)
    (hXbound : X ≤ 36 * gap)
    (hratioLower : fifthResidualRatioLower p.k ≤ (X : ℚ) / gap)
    (hratioUpper : (X : ℚ) / gap ≤ fifthResidualRatioUpper p.k)
    {Y Z t T b c z P M w N g : ℤ}
    (hg : g ≠ 0)
    (hY : Y = (X : ℤ) - 3 * fifthPositionDeltaLeft p)
    (hZ : Z = (X : ℤ) - 3 * fifthPositionDeltaRight p)
    (hgap : (gap : ℤ) = P * M)
    (hproduct : (gap : ℤ) ^ 2 * t = g ^ 2 * (X : ℤ) * Y * Z)
    (hthird :
      T = -9 * fifthPositionC p * t +
        (fifthPositionDeltaLeft p * fifthPositionDeltaRight p) * g ^ 2 *
          (180 * fifthPositionE p * (gap : ℤ) + 108 * fifthPositionD p))
    (hopposite : (gap : ℤ) ^ 2 * b * c * z = g ^ 2 * Y * Z * T)
    (hfourth :
      P * w = 27 * fifthPositionC p ^ 2 * b * c * z +
        fifthPositionK p * g ^ 4)
    (hnormalized : N = 27 * w + M * fifthPositionR1 p * g ^ 4) :
    w ≠ 0 ∧ N ≠ 0 := by
  have hJ := fifth_quotient_target_eliminants_ne_zero
    hp hgapTarget hXbound hratioLower hratioUpper
  change
    threeBucketFourthEliminant
        (fifthPositionC p) (fifthPositionD p) (fifthPositionE p)
        (fifthPositionK p) (X : ℤ) (gap : ℤ)
        (fifthPositionDeltaLeft p) (fifthPositionDeltaRight p) ≠ 0 ∧
      threeBucketNormalizedFifthEliminant
        (fifthPositionC p) (fifthPositionD p) (fifthPositionE p)
        (fifthPositionK p) (fifthPositionR1 p) (X : ℤ) (gap : ℤ)
        (fifthPositionDeltaLeft p) (fifthPositionDeltaRight p) ≠ 0 at hJ
  have hfourthIdentity := three_bucket_fourth_eliminant_identity
    (C := fifthPositionC p) (D := fifthPositionD p) (E := fifthPositionE p)
    (K := fifthPositionK p) (X := (X : ℤ)) (gap := (gap : ℤ))
    (deltaLeft := fifthPositionDeltaLeft p)
    (deltaRight := fifthPositionDeltaRight p)
    hY hZ hproduct hthird hopposite hfourth
  have hfifthIdentity := three_bucket_normalized_fifth_eliminant_identity
    (C := fifthPositionC p) (D := fifthPositionD p) (E := fifthPositionE p)
    (K := fifthPositionK p) (R1 := fifthPositionR1 p)
    (X := (X : ℤ)) (gap := (gap : ℤ))
    (deltaLeft := fifthPositionDeltaLeft p)
    (deltaRight := fifthPositionDeltaRight p)
    hY hZ hgap hproduct hthird hopposite hfourth hnormalized
  constructor
  · intro hw
    have hrhs :
        g ^ 4 * threeBucketFourthEliminant
          (fifthPositionC p) (fifthPositionD p) (fifthPositionE p)
          (fifthPositionK p) (X : ℤ) (gap : ℤ)
          (fifthPositionDeltaLeft p) (fifthPositionDeltaRight p) ≠ 0 :=
      mul_ne_zero (pow_ne_zero 4 hg) hJ.1
    apply hrhs
    rw [← hfourthIdentity, hw]
    ring
  · intro hN
    have hrhs :
        g ^ 4 * threeBucketNormalizedFifthEliminant
          (fifthPositionC p) (fifthPositionD p) (fifthPositionE p)
          (fifthPositionK p) (fifthPositionR1 p) (X : ℤ) (gap : ℤ)
          (fifthPositionDeltaLeft p) (fifthPositionDeltaRight p) ≠ 0 :=
      mul_ne_zero (pow_ne_zero 4 hg) hJ.2
    apply hrhs
    rw [← hfifthIdentity, hN]
    ring

/-! ## Equation-derived residual window -/

/-- Lower endpoint of the adjacent `100000`-denominator root bracket. -/
def fifthResidualRootLower : ℕ → ℕ
  | 5 => 131950
  | 7 => 121901
  | 9 => 116652
  | 11 => 113431
  | 13 => 111253
  | 15 => 109682
  | _ => 0

/-- Upper endpoint of the adjacent `100000`-denominator root bracket. -/
def fifthResidualRootUpper : ℕ → ℕ
  | 5 => 131951
  | 7 => 121902
  | 9 => 116653
  | 11 => 113432
  | 13 => 111254
  | 15 => 109683
  | _ => 0

/-- Common denominator of the adjacent root brackets. -/
def fifthResidualRootDenominator : ℕ := 100000

/-- Ordinary-kernel metadata certificate for the imported position table. -/
theorem fifth_quotient_target_position_metadata_certificate :
    ∀ p ∈ fifthQuotientTargetPositions,
      (p.k = 5 ∨ p.k = 7 ∨ p.k = 9 ∨ p.k = 11 ∨ p.k = 13 ∨ p.k = 15) ∧
      p.owner ∈ Finset.Icc 1 p.k := by
  decide +kernel

/-- Exact adjacent rational brackets around `4^(1/k)` in every target row. -/
theorem fifth_residual_root_brackets_certificate
    {k : ℕ}
    (hk : k = 5 ∨ k = 7 ∨ k = 9 ∨ k = 11 ∨ k = 13 ∨ k = 15) :
    fifthResidualRootLower k ^ k < 4 * fifthResidualRootDenominator ^ k ∧
      4 * fifthResidualRootDenominator ^ k < fifthResidualRootUpper k ^ k := by
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [fifthResidualRootLower, fifthResidualRootUpper,
      fifthResidualRootDenominator]

private theorem fifth_residual_lower_padding_of_linear
    {k : ℕ}
    (hk : k = 5 ∨ k = 7 ∨ k = 9 ∨ k = 11 ∨ k = 13 ∨ k = 15)
    {n d i : ℚ}
    (hlinear : (fifthResidualRootDenominator : ℚ) * (n + d + k) <
      fifthResidualRootUpper k * (n + k))
    (hi : 1 ≤ i)
    (hd : 4500 ≤ d) :
    fifthResidualRatioLower k * d ≤ 3 * (n + i) - d := by
  rcases hk with hk | hk | hk | hk | hk | hk <;>
    norm_num [hk, fifthResidualRatioLower, fifthResidualRootUpper,
      fifthResidualRootDenominator] at hlinear ⊢ <;>
    linarith

private theorem fifth_residual_upper_padding_of_linear
    {k : ℕ}
    (hk : k = 5 ∨ k = 7 ∨ k = 9 ∨ k = 11 ∨ k = 13 ∨ k = 15)
    {n d i : ℚ}
    (hlinear : (fifthResidualRootLower k : ℚ) * (n + 1) <
      fifthResidualRootDenominator * (n + d + 1))
    (hi : i ≤ k)
    (hd : 4500 ≤ d) :
    3 * (n + i) - d ≤ fifthResidualRatioUpper k * d := by
  rcases hk with hk | hk | hk | hk | hk | hk <;>
    norm_num [hk, fifthResidualRatioUpper, fifthResidualRootLower,
      fifthResidualRootDenominator] at hlinear hi ⊢ <;>
    linarith

/-- The exact block-product equation supplies the padded residual-ratio
interval and the coarse `36*d` cap required by the finite eliminant ledger. -/
theorem fifth_target_localResidual_ratio_window
    {p : FifthQuotientPosition}
    (hp : p ∈ fifthQuotientTargetPositions)
    {n d : ℕ}
    (hd : 10 ^ 1000 ≤ d)
    (heq : blockProduct p.k (n + d) = 4 * blockProduct p.k n) :
    fifthResidualRatioLower p.k ≤ (localResidual n d p.owner : ℚ) / d ∧
      (localResidual n d p.owner : ℚ) / d ≤ fifthResidualRatioUpper p.k ∧
      localResidual n d p.owner ≤ 36 * d := by
  obtain ⟨hk, hi⟩ := fifth_quotient_target_position_metadata_certificate p hp
  have hk1 : 1 ≤ p.k := by
    rcases hk with hk | hk | hk | hk | hk | hk <;> omega
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hdq : (0 : ℚ) < d := by exact_mod_cast hdpos
  have hwin := ratio_window_four_nat heq
  have hbrackets := fifth_residual_root_brackets_certificate hk
  have hlowerLinear := ratio_window_linearize_of_pow_bracket
    (N := 4) (A := fifthResidualRootUpper p.k)
    (B := fifthResidualRootDenominator) (k := p.k) (n := n) (d := d)
    hk1 hbrackets.2 hwin.1
  have hupperLinear := ratio_window_upper_linearize_of_pow_bracket
    (N := 4) (A := fifthResidualRootLower p.k)
    (B := fifthResidualRootDenominator) (k := p.k) (n := n) (d := d)
    hk1 hbrackets.1 hwin.2
  rw [Finset.mem_Icc] at hi
  have hnontrunc : d ≤ 3 * (n + p.owner) := by
    rcases hk with hk | hk | hk | hk | hk | hk <;>
      norm_num [hk, fifthResidualRootUpper,
        fifthResidualRootDenominator] at hlowerLinear hi ⊢ <;>
      omega
  have hresCast : ((localResidual n d p.owner : ℕ) : ℚ) =
      3 * ((n : ℚ) + p.owner) - d := by
    unfold localResidual
    rw [Nat.cast_sub hnontrunc]
    push_cast
    ring
  have hlowerLinearQ :
      (fifthResidualRootDenominator : ℚ) * (n + d + p.k) <
        fifthResidualRootUpper p.k * (n + p.k) := by
    exact_mod_cast hlowerLinear
  have hupperLinearQ :
      (fifthResidualRootLower p.k : ℚ) * (n + 1) <
        fifthResidualRootDenominator * (n + d + 1) := by
    exact_mod_cast hupperLinear
  have hiLowerQ : (1 : ℚ) ≤ p.owner := by exact_mod_cast hi.1
  have hiUpperQ : (p.owner : ℚ) ≤ p.k := by exact_mod_cast hi.2
  have hpow : 10 ^ 4 ≤ 10 ^ 1000 :=
    Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hdSmall : 4500 ≤ d :=
    le_trans (by norm_num : 4500 ≤ 10 ^ 4) (le_trans hpow hd)
  have hdSmallQ : (4500 : ℚ) ≤ d := by exact_mod_cast hdSmall
  have hratioLower :
      fifthResidualRatioLower p.k ≤ (localResidual n d p.owner : ℚ) / d := by
    rw [le_div_iff₀ hdq, hresCast]
    exact fifth_residual_lower_padding_of_linear hk hlowerLinearQ hiLowerQ hdSmallQ
  have hratioUpper :
      (localResidual n d p.owner : ℚ) / d ≤ fifthResidualRatioUpper p.k := by
    rw [div_le_iff₀ hdq, hresCast]
    exact fifth_residual_upper_padding_of_linear hk hupperLinearQ hiUpperQ hdSmallQ
  have hcap : fifthResidualRatioUpper p.k ≤ (36 : ℚ) :=
    (fifth_quotient_target_position_geometry_certificate p hp).2.2.1
  have hXq : (localResidual n d p.owner : ℚ) ≤
      fifthResidualRatioUpper p.k * d := (div_le_iff₀ hdq).mp hratioUpper
  have hcapMul : fifthResidualRatioUpper p.k * (d : ℚ) ≤ 36 * d :=
    mul_le_mul_of_nonneg_right hcap (le_of_lt hdq)
  have hXbound : localResidual n d p.owner ≤ 36 * d := by
    exact_mod_cast hXq.trans hcapMul
  exact ⟨hratioLower, hratioUpper, hXbound⟩

/-- Equation-specialized endpoint: the power-window interval is derived from
the exact block-product equation, while the local configuration identities
remain explicit premises. -/
theorem fifth_quotient_target_equation_fourth_and_normalized_nonzero
    {p : FifthQuotientPosition}
    (hp : p ∈ fifthQuotientTargetPositions)
    {n gap : ℕ}
    (hgapTarget : 10 ^ 1000 ≤ gap)
    (heq : blockProduct p.k (n + gap) = 4 * blockProduct p.k n)
    {Y Z t T b c z P M w N g : ℤ}
    (hg : g ≠ 0)
    (hY : Y = (localResidual n gap p.owner : ℤ) -
      3 * fifthPositionDeltaLeft p)
    (hZ : Z = (localResidual n gap p.owner : ℤ) -
      3 * fifthPositionDeltaRight p)
    (hgapFactor : (gap : ℤ) = P * M)
    (hproduct :
      (gap : ℤ) ^ 2 * t =
        g ^ 2 * (localResidual n gap p.owner : ℤ) * Y * Z)
    (hthird :
      T = -9 * fifthPositionC p * t +
        (fifthPositionDeltaLeft p * fifthPositionDeltaRight p) * g ^ 2 *
          (180 * fifthPositionE p * (gap : ℤ) + 108 * fifthPositionD p))
    (hopposite : (gap : ℤ) ^ 2 * b * c * z = g ^ 2 * Y * Z * T)
    (hfourth :
      P * w = 27 * fifthPositionC p ^ 2 * b * c * z +
        fifthPositionK p * g ^ 4)
    (hnormalized : N = 27 * w + M * fifthPositionR1 p * g ^ 4) :
    w ≠ 0 ∧ N ≠ 0 := by
  obtain ⟨hratioLower, hratioUpper, hXbound⟩ :=
    fifth_target_localResidual_ratio_window hp hgapTarget heq
  exact fifth_quotient_target_fourth_and_normalized_nonzero
    hp hgapTarget hXbound hratioLower hratioUpper hg hY hZ hgapFactor
      hproduct hthird hopposite hfourth hnormalized

#print axioms fifth_quotient_target_position_certificate
#print axioms fifth_quotient_target_position_count
#print axioms fifth_quotient_target_positions_valid
#print axioms fifth_quotient_row_position_mem_iff
#print axioms fifth_quotient_target_position_mem_iff
#print axioms fifthLocalCoefficients_eq_localTaylor
#print axioms three_bucket_fourth_eliminant_identity
#print axioms fifth_quotient_target_position_geometry_certificate
#print axioms fifth_quotient_target_eliminants_ne_zero
#print axioms fifth_quotient_target_fourth_and_normalized_nonzero
#print axioms fifth_quotient_target_position_metadata_certificate
#print axioms fifth_residual_root_brackets_certificate
#print axioms fifth_target_localResidual_ratio_window
#print axioms fifth_quotient_target_equation_fourth_and_normalized_nonzero

end Erdos686Variant
end Erdos686
