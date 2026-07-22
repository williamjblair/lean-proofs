/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.EvenK.Base

/-!
# Erdős Problem 686: the `k = 14` strip for `N = 4`, `d ≥ 221`

`ErdosProblems/Erdos686EvenK.lean` banks the large-gap branch
`no_gap_solution_four_even_fourteen_of_large_gap` (`d ≥ 663000`), where the
trapped center `m = T₁₄(w) - 2T₁₄(v)` falls in `(-7, 0)` and dies by
`7 ∣ m`.  This module closes the whole range `d ≥ 221` (in particular the
strip `221 ≤ d < 663000`) for

  `blockProduct 14 (n + d) = 4 * blockProduct 14 n`.

Normalizations (identical to the EvenK module): `w = 2(n+d) + 15`,
`v = 2n + 15`, `S₁₄(W) = ∏_{l odd, 1 ≤ l ≤ 13} (W² - l²)`,
`T₁₄ = 16W⁷ - 3640W⁵ + 202566W³ - 2656355W`, `D₁₄ = T₁₄² - 256·S₁₄`, and on
the curve `S₁₄(w) = 4S₁₄(v)` the integers `m = T₁₄(w) - 2T₁₄(v)`,
`X = T₁₄(w) + 2T₁₄(v)` satisfy `m·X = D₁₄(w) - 4D₁₄(v)`.

The banked window linearizations give `19w ≤ 21v + 24`, `11v ≤ 10w + 11`,
and `d ≥ 221` forces `v ≥ 3991` (`row_base_lower_k14`).  Two univariate
shifted-coefficient certificates at `v₀ = 3991` (lower-bounding `T₁₄(w)`
*and* `D₁₄(w)` termwise through the window) trap `m` in `(-11680, 0)`;
`11680` is the minimal shifted-certifiable width.  Since `m` is odd (`T₁₄`
is odd at odd arguments) and `7 ∣ m` (Fermat mod 7), the candidate set is
the `834` values `m = -7(2j+1)`, `j < 834`.

Each candidate is killed modulo one of the 31 primes
`31, 139, 67, 131, 83, 71, 107, 163, 193, 101, 113, 199, 73, 137, 181,
157, 239, 97, 151, 271, 241, 223, 149, 109, 251, 311, 233, 191, 211,
263, 337`:
for each prime `p` a kernel `decide` shows that on the curve
`S₁₄(x) = 4S₁₄(y)` over `(ZMod p)²` the value `T₁₄(x) - 2T₁₄(y)` never
lands in an explicit `badList p`, while a second kernel `decide` shows
every candidate hits some `badList` (`strip_dispatch`).  The greedy
cost-weighted cover was computed and exactly verified (twice,
independently) in `compute/erdos686_k14_strip.py` and
`compute/erdos686_k14_strip_gen_lean.py`; total kernel work is
`Σ p² ≈ 1.06·10⁶` pairs.

The corollary `no_gap_solution_four_even_k` packages the five even-`k`
theorems (`k ∈ {6, 8, 10, 12, 14}`, `d ≥ 221`).
-/

namespace Erdos686

namespace Erdos686Variant

/-! ## Block-product expansion and centered bridge (private copies of the
EvenK lemmas, which are `private` there) -/

private lemma strip_blockProduct_fourteen_prod (x : ℕ) :
    blockProduct 14 x =
      (x + 1) * (x + 2) * (x + 3) * (x + 4) * (x + 5) * (x + 6) * (x + 7) *
        (x + 8) * (x + 9) * (x + 10) * (x + 11) * (x + 12) * (x + 13) *
        (x + 14) := by
  norm_num [blockProduct, Finset.prod_Icc_succ_top, Finset.Icc_self,
    Finset.prod_singleton]

private lemma strip_s14_bridge (x : ℕ) :
    ((2 * (x : ℤ) + 15) ^ 2 - 1) * ((2 * (x : ℤ) + 15) ^ 2 - 9) *
        ((2 * (x : ℤ) + 15) ^ 2 - 25) * ((2 * (x : ℤ) + 15) ^ 2 - 49) *
        ((2 * (x : ℤ) + 15) ^ 2 - 81) * ((2 * (x : ℤ) + 15) ^ 2 - 121) *
        ((2 * (x : ℤ) + 15) ^ 2 - 169) = 16384 * (blockProduct 14 x : ℤ) := by
  rw [strip_blockProduct_fourteen_prod]
  push_cast
  ring

/-- `7 ∣ T₁₄(x) = 16x⁷ - 3640x⁵ + 202566x³ - 2656355x` for every integer `x`
(`T₁₄ = 16(x⁷ - x) + 7(-520x⁵ + 28938x³ - 379477x)`). -/
private lemma strip_seven_dvd_T14 (x : ℤ) :
    (7 : ℤ) ∣ 16 * x ^ 7 - 3640 * x ^ 5 + 202566 * x ^ 3 - 2656355 * x := by
  have h7 : (7 : ℤ) ∣ x ^ 7 - x := by
    have hx : ((x ^ 7 - x : ℤ) : ZMod 7) = 0 := by
      push_cast
      have hz : ∀ y : ZMod 7, y ^ 7 - y = 0 := by decide
      exact hz (x : ZMod 7)
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mp hx
  obtain ⟨y, hy⟩ := h7
  exact ⟨16 * y - 520 * x ^ 5 + 28938 * x ^ 3 - 379477 * x,
    by linear_combination 16 * hy⟩

/-! ## Univariate shifted-coefficient certificates at `v₀ = 3991`

All three were verified exactly (all shifted coefficients nonnegative,
constant term positive) in `compute/erdos686_k14_strip.py`. -/

private lemma strip_k14_T_pos {W : ℤ} (hW : 3991 ≤ W) :
    0 < 16 * W ^ 7 - 3640 * W ^ 5 + 202566 * W ^ 3 - 2656355 * W := by
  obtain ⟨t, ht, rfl⟩ : ∃ t : ℤ, 0 ≤ t ∧ W = 3991 + t :=
    ⟨W - 3991, by omega, by omega⟩
  linarith [ht, pow_nonneg ht 2, pow_nonneg ht 3, pow_nonneg ht 4,
    pow_nonneg ht 5, pow_nonneg ht 6, pow_nonneg ht 7]

/-- Upper certificate: through the window `19w ≤ 21v + 24`, `v⁴ ≤ w⁴` this
forces `D₁₄(w) - 4D₁₄(v) < 0` for `v ≥ 3991`. -/
private lemma strip_k14_upper {v : ℤ} (hv : 3991 ≤ v) :
    1318847348 * (21 * v + 24) ^ 6 +
        130321 * 1455430979401 * (21 * v + 24) ^ 2 +
        47045881 * 4674935865600 <
      47045881 * 92807039780 * v ^ 4 +
        188183524 * (1318847348 * v ^ 6 - 92807039780 * v ^ 4 +
          1455430979401 * v ^ 2 + 4674935865600) := by
  obtain ⟨t, ht, rfl⟩ : ∃ t : ℤ, 0 ≤ t ∧ v = 3991 + t :=
    ⟨v - 3991, by omega, by omega⟩
  linarith [ht, pow_nonneg ht 2, pow_nonneg ht 3, pow_nonneg ht 4,
    pow_nonneg ht 5, pow_nonneg ht 6]

/-- Lower certificate: termwise through the window
(`11v - 11 ≤ 10w ≤ 10/19·(21v + 24)`, scaled by `10⁷·19⁵ = 24760990000000`)
this forces `-11680·X < D₁₄(w) - 4D₁₄(v)` for `v ≥ 3991`; the width `11680`
is minimal for this certificate shape. -/
private lemma strip_k14_lower {v : ℤ} (hv : 3991 ≤ v) :
    0 < 11680 * (39617584 * (11 * v - 11) ^ 7 -
          36400000000 * (21 * v + 24) ^ 5 +
          202566 * 24760990000000 * v ^ 3 -
          2656355 * 10000000 * 130321 * (21 * v + 24) +
          2 * 24760990000000 *
            (16 * v ^ 7 - 3640 * v ^ 5 + 202566 * v ^ 3 - 2656355 * v)) +
        190 * (1318847348 * 130321 * (11 * v - 11) ^ 6 -
          92807039780 * 1000000 * (21 * v + 24) ^ 4 +
          1455430979401 * 1000000 * 130321 * v ^ 2 +
          4674935865600 * 1000000 * 130321) -
        4 * 24760990000000 *
          (1318847348 * v ^ 6 - 92807039780 * v ^ 4 +
            1455430979401 * v ^ 2 + 4674935865600) := by
  obtain ⟨t, ht, rfl⟩ : ∃ t : ℤ, 0 ≤ t ∧ v = 3991 + t :=
    ⟨v - 3991, by omega, by omega⟩
  linarith [ht, pow_nonneg ht 2, pow_nonneg ht 3, pow_nonneg ht 4,
    pow_nonneg ht 5, pow_nonneg ht 6, pow_nonneg ht 7]

/-! ## Modular curve certificates

For each cover prime `p`: on the curve `S₁₄(x) = 4S₁₄(y)` over `(ZMod p)²`
the value `T₁₄(x) - 2T₁₄(y)` avoids the listed residues (the residues of
the candidates assigned to `p`). -/

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
-- Kernel enumeration of the 31² pairs `(x, y) ∈ (ZMod 31)²`; each pair
-- evaluates two degree-14 products, so the heartbeat cap is sized at
-- roughly 10³ heartbeats per pair.
private theorem strip_curve_p31 :
    ∀ x y : ZMod 31,
      (x ^ 2 - 1) * (x ^ 2 - 9) * (x ^ 2 - 25) * (x ^ 2 - 49) *
          (x ^ 2 - 81) * (x ^ 2 - 121) * (x ^ 2 - 169) =
        4 * ((y ^ 2 - 1) * (y ^ 2 - 9) * (y ^ 2 - 25) * (y ^ 2 - 49) *
          (y ^ 2 - 81) * (y ^ 2 - 121) * (y ^ 2 - 169)) →
      (16 * x ^ 7 - 3640 * x ^ 5 + 202566 * x ^ 3 - 2656355 * x) -
          2 * (16 * y ^ 7 - 3640 * y ^ 5 + 202566 * y ^ 3 - 2656355 * y) ∉
        ([0] : List (ZMod 31)) := by
  decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 19321000 in
-- Kernel enumeration of the 139² pairs `(x, y) ∈ (ZMod 139)²`; each pair
-- evaluates two degree-14 products, so the heartbeat cap is sized at
-- roughly 10³ heartbeats per pair.
private theorem strip_curve_p139 :
    ∀ x y : ZMod 139,
      (x ^ 2 - 1) * (x ^ 2 - 9) * (x ^ 2 - 25) * (x ^ 2 - 49) *
          (x ^ 2 - 81) * (x ^ 2 - 121) * (x ^ 2 - 169) =
        4 * ((y ^ 2 - 1) * (y ^ 2 - 9) * (y ^ 2 - 25) * (y ^ 2 - 49) *
          (y ^ 2 - 81) * (y ^ 2 - 121) * (y ^ 2 - 169)) →
      (16 * x ^ 7 - 3640 * x ^ 5 + 202566 * x ^ 3 - 2656355 * x) -
          2 * (16 * y ^ 7 - 3640 * y ^ 5 + 202566 * y ^ 3 - 2656355 * y) ∉
        ([0, 1, 7, 8, 12, 14, 15, 25, 28, 29, 52, 54, 56, 57, 59, 80, 82,
          83, 85, 87, 110, 111, 114, 124, 125, 127, 131, 132, 138] : List (ZMod 139)) := by
  decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
-- Kernel enumeration of the 67² pairs `(x, y) ∈ (ZMod 67)²`; each pair
-- evaluates two degree-14 products, so the heartbeat cap is sized at
-- roughly 10³ heartbeats per pair.
private theorem strip_curve_p67 :
    ∀ x y : ZMod 67,
      (x ^ 2 - 1) * (x ^ 2 - 9) * (x ^ 2 - 25) * (x ^ 2 - 49) *
          (x ^ 2 - 81) * (x ^ 2 - 121) * (x ^ 2 - 169) =
        4 * ((y ^ 2 - 1) * (y ^ 2 - 9) * (y ^ 2 - 25) * (y ^ 2 - 49) *
          (y ^ 2 - 81) * (y ^ 2 - 121) * (y ^ 2 - 169)) →
      (16 * x ^ 7 - 3640 * x ^ 5 + 202566 * x ^ 3 - 2656355 * x) -
          2 * (16 * y ^ 7 - 3640 * y ^ 5 + 202566 * y ^ 3 - 2656355 * y) ∉
        ([0, 32, 35] : List (ZMod 67)) := by
  decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 17161000 in
-- Kernel enumeration of the 131² pairs `(x, y) ∈ (ZMod 131)²`; each pair
-- evaluates two degree-14 products, so the heartbeat cap is sized at
-- roughly 10³ heartbeats per pair.
private theorem strip_curve_p131 :
    ∀ x y : ZMod 131,
      (x ^ 2 - 1) * (x ^ 2 - 9) * (x ^ 2 - 25) * (x ^ 2 - 49) *
          (x ^ 2 - 81) * (x ^ 2 - 121) * (x ^ 2 - 169) =
        4 * ((y ^ 2 - 1) * (y ^ 2 - 9) * (y ^ 2 - 25) * (y ^ 2 - 49) *
          (y ^ 2 - 81) * (y ^ 2 - 121) * (y ^ 2 - 169)) →
      (16 * x ^ 7 - 3640 * x ^ 5 + 202566 * x ^ 3 - 2656355 * x) -
          2 * (16 * y ^ 7 - 3640 * y ^ 5 + 202566 * y ^ 3 - 2656355 * y) ∉
        ([5, 7, 12, 13, 36, 37, 44, 45, 50, 60, 62, 69, 71, 81, 86, 87, 94,
          95, 118, 119, 124, 126] : List (ZMod 131)) := by
  decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
-- Kernel enumeration of the 83² pairs `(x, y) ∈ (ZMod 83)²`; each pair
-- evaluates two degree-14 products, so the heartbeat cap is sized at
-- roughly 10³ heartbeats per pair.
private theorem strip_curve_p83 :
    ∀ x y : ZMod 83,
      (x ^ 2 - 1) * (x ^ 2 - 9) * (x ^ 2 - 25) * (x ^ 2 - 49) *
          (x ^ 2 - 81) * (x ^ 2 - 121) * (x ^ 2 - 169) =
        4 * ((y ^ 2 - 1) * (y ^ 2 - 9) * (y ^ 2 - 25) * (y ^ 2 - 49) *
          (y ^ 2 - 81) * (y ^ 2 - 121) * (y ^ 2 - 169)) →
      (16 * x ^ 7 - 3640 * x ^ 5 + 202566 * x ^ 3 - 2656355 * x) -
          2 * (16 * y ^ 7 - 3640 * y ^ 5 + 202566 * y ^ 3 - 2656355 * y) ∉
        ([1, 16, 37, 46, 67, 82] : List (ZMod 83)) := by
  decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
-- Kernel enumeration of the 71² pairs `(x, y) ∈ (ZMod 71)²`; each pair
-- evaluates two degree-14 products, so the heartbeat cap is sized at
-- roughly 10³ heartbeats per pair.
private theorem strip_curve_p71 :
    ∀ x y : ZMod 71,
      (x ^ 2 - 1) * (x ^ 2 - 9) * (x ^ 2 - 25) * (x ^ 2 - 49) *
          (x ^ 2 - 81) * (x ^ 2 - 121) * (x ^ 2 - 169) =
        4 * ((y ^ 2 - 1) * (y ^ 2 - 9) * (y ^ 2 - 25) * (y ^ 2 - 49) *
          (y ^ 2 - 81) * (y ^ 2 - 121) * (y ^ 2 - 169)) →
      (16 * x ^ 7 - 3640 * x ^ 5 + 202566 * x ^ 3 - 2656355 * x) -
          2 * (16 * y ^ 7 - 3640 * y ^ 5 + 202566 * y ^ 3 - 2656355 * y) ∉
        ([0, 19, 52] : List (ZMod 71)) := by
  decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 11449000 in
-- Kernel enumeration of the 107² pairs `(x, y) ∈ (ZMod 107)²`; each pair
-- evaluates two degree-14 products, so the heartbeat cap is sized at
-- roughly 10³ heartbeats per pair.
private theorem strip_curve_p107 :
    ∀ x y : ZMod 107,
      (x ^ 2 - 1) * (x ^ 2 - 9) * (x ^ 2 - 25) * (x ^ 2 - 49) *
          (x ^ 2 - 81) * (x ^ 2 - 121) * (x ^ 2 - 169) =
        4 * ((y ^ 2 - 1) * (y ^ 2 - 9) * (y ^ 2 - 25) * (y ^ 2 - 49) *
          (y ^ 2 - 81) * (y ^ 2 - 121) * (y ^ 2 - 169)) →
      (16 * x ^ 7 - 3640 * x ^ 5 + 202566 * x ^ 3 - 2656355 * x) -
          2 * (16 * y ^ 7 - 3640 * y ^ 5 + 202566 * y ^ 3 - 2656355 * y) ∉
        ([0, 4, 14, 19, 30, 77, 88, 93, 103] : List (ZMod 107)) := by
  decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 26569000 in
-- Kernel enumeration of the 163² pairs `(x, y) ∈ (ZMod 163)²`; each pair
-- evaluates two degree-14 products, so the heartbeat cap is sized at
-- roughly 10³ heartbeats per pair.
private theorem strip_curve_p163 :
    ∀ x y : ZMod 163,
      (x ^ 2 - 1) * (x ^ 2 - 9) * (x ^ 2 - 25) * (x ^ 2 - 49) *
          (x ^ 2 - 81) * (x ^ 2 - 121) * (x ^ 2 - 169) =
        4 * ((y ^ 2 - 1) * (y ^ 2 - 9) * (y ^ 2 - 25) * (y ^ 2 - 49) *
          (y ^ 2 - 81) * (y ^ 2 - 121) * (y ^ 2 - 169)) →
      (16 * x ^ 7 - 3640 * x ^ 5 + 202566 * x ^ 3 - 2656355 * x) -
          2 * (16 * y ^ 7 - 3640 * y ^ 5 + 202566 * y ^ 3 - 2656355 * y) ∉
        ([5, 9, 15, 16, 30, 34, 48, 49, 56, 66, 70, 72, 73, 77, 81, 82, 86,
          90, 91, 93, 97, 107, 114, 115, 129, 133, 147, 148, 154, 158] : List (ZMod 163)) := by
  decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 37249000 in
-- Kernel enumeration of the 193² pairs `(x, y) ∈ (ZMod 193)²`; each pair
-- evaluates two degree-14 products, so the heartbeat cap is sized at
-- roughly 10³ heartbeats per pair.
private theorem strip_curve_p193 :
    ∀ x y : ZMod 193,
      (x ^ 2 - 1) * (x ^ 2 - 9) * (x ^ 2 - 25) * (x ^ 2 - 49) *
          (x ^ 2 - 81) * (x ^ 2 - 121) * (x ^ 2 - 169) =
        4 * ((y ^ 2 - 1) * (y ^ 2 - 9) * (y ^ 2 - 25) * (y ^ 2 - 49) *
          (y ^ 2 - 81) * (y ^ 2 - 121) * (y ^ 2 - 169)) →
      (16 * x ^ 7 - 3640 * x ^ 5 + 202566 * x ^ 3 - 2656355 * x) -
          2 * (16 * y ^ 7 - 3640 * y ^ 5 + 202566 * y ^ 3 - 2656355 * y) ∉
        ([0, 3, 4, 10, 14, 15, 26, 27, 31, 32, 35, 38, 41, 45, 47, 49, 53,
          60, 62, 64, 79, 82, 96, 97, 111, 113, 126, 129, 131, 133, 140,
          146, 148, 152, 155, 158, 161, 162, 166, 179, 183, 189, 190] : List (ZMod 193)) := by
  decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 10201000 in
-- Kernel enumeration of the 101² pairs `(x, y) ∈ (ZMod 101)²`; each pair
-- evaluates two degree-14 products, so the heartbeat cap is sized at
-- roughly 10³ heartbeats per pair.
private theorem strip_curve_p101 :
    ∀ x y : ZMod 101,
      (x ^ 2 - 1) * (x ^ 2 - 9) * (x ^ 2 - 25) * (x ^ 2 - 49) *
          (x ^ 2 - 81) * (x ^ 2 - 121) * (x ^ 2 - 169) =
        4 * ((y ^ 2 - 1) * (y ^ 2 - 9) * (y ^ 2 - 25) * (y ^ 2 - 49) *
          (y ^ 2 - 81) * (y ^ 2 - 121) * (y ^ 2 - 169)) →
      (16 * x ^ 7 - 3640 * x ^ 5 + 202566 * x ^ 3 - 2656355 * x) -
          2 * (16 * y ^ 7 - 3640 * y ^ 5 + 202566 * y ^ 3 - 2656355 * y) ∉
        ([36, 41, 45, 56, 60, 65] : List (ZMod 101)) := by
  decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 12769000 in
-- Kernel enumeration of the 113² pairs `(x, y) ∈ (ZMod 113)²`; each pair
-- evaluates two degree-14 products, so the heartbeat cap is sized at
-- roughly 10³ heartbeats per pair.
private theorem strip_curve_p113 :
    ∀ x y : ZMod 113,
      (x ^ 2 - 1) * (x ^ 2 - 9) * (x ^ 2 - 25) * (x ^ 2 - 49) *
          (x ^ 2 - 81) * (x ^ 2 - 121) * (x ^ 2 - 169) =
        4 * ((y ^ 2 - 1) * (y ^ 2 - 9) * (y ^ 2 - 25) * (y ^ 2 - 49) *
          (y ^ 2 - 81) * (y ^ 2 - 121) * (y ^ 2 - 169)) →
      (16 * x ^ 7 - 3640 * x ^ 5 + 202566 * x ^ 3 - 2656355 * x) -
          2 * (16 * y ^ 7 - 3640 * y ^ 5 + 202566 * y ^ 3 - 2656355 * y) ∉
        ([21, 22, 48, 65, 91, 92, 109] : List (ZMod 113)) := by
  decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 39601000 in
-- Kernel enumeration of the 199² pairs `(x, y) ∈ (ZMod 199)²`; each pair
-- evaluates two degree-14 products, so the heartbeat cap is sized at
-- roughly 10³ heartbeats per pair.
private theorem strip_curve_p199 :
    ∀ x y : ZMod 199,
      (x ^ 2 - 1) * (x ^ 2 - 9) * (x ^ 2 - 25) * (x ^ 2 - 49) *
          (x ^ 2 - 81) * (x ^ 2 - 121) * (x ^ 2 - 169) =
        4 * ((y ^ 2 - 1) * (y ^ 2 - 9) * (y ^ 2 - 25) * (y ^ 2 - 49) *
          (y ^ 2 - 81) * (y ^ 2 - 121) * (y ^ 2 - 169)) →
      (16 * x ^ 7 - 3640 * x ^ 5 + 202566 * x ^ 3 - 2656355 * x) -
          2 * (16 * y ^ 7 - 3640 * y ^ 5 + 202566 * y ^ 3 - 2656355 * y) ∉
        ([0, 6, 9, 13, 17, 23, 30, 37, 50, 54, 59, 60, 64, 82, 87, 107, 112,
          117, 135, 139, 145, 149, 156, 162, 182, 186, 190, 191, 193] : List (ZMod 199)) := by
  decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
-- Kernel enumeration of the 73² pairs `(x, y) ∈ (ZMod 73)²`; each pair
-- evaluates two degree-14 products, so the heartbeat cap is sized at
-- roughly 10³ heartbeats per pair.
private theorem strip_curve_p73 :
    ∀ x y : ZMod 73,
      (x ^ 2 - 1) * (x ^ 2 - 9) * (x ^ 2 - 25) * (x ^ 2 - 49) *
          (x ^ 2 - 81) * (x ^ 2 - 121) * (x ^ 2 - 169) =
        4 * ((y ^ 2 - 1) * (y ^ 2 - 9) * (y ^ 2 - 25) * (y ^ 2 - 49) *
          (y ^ 2 - 81) * (y ^ 2 - 121) * (y ^ 2 - 169)) →
      (16 * x ^ 7 - 3640 * x ^ 5 + 202566 * x ^ 3 - 2656355 * x) -
          2 * (16 * y ^ 7 - 3640 * y ^ 5 + 202566 * y ^ 3 - 2656355 * y) ∉
        ([1, 72] : List (ZMod 73)) := by
  decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 18769000 in
-- Kernel enumeration of the 137² pairs `(x, y) ∈ (ZMod 137)²`; each pair
-- evaluates two degree-14 products, so the heartbeat cap is sized at
-- roughly 10³ heartbeats per pair.
private theorem strip_curve_p137 :
    ∀ x y : ZMod 137,
      (x ^ 2 - 1) * (x ^ 2 - 9) * (x ^ 2 - 25) * (x ^ 2 - 49) *
          (x ^ 2 - 81) * (x ^ 2 - 121) * (x ^ 2 - 169) =
        4 * ((y ^ 2 - 1) * (y ^ 2 - 9) * (y ^ 2 - 25) * (y ^ 2 - 49) *
          (y ^ 2 - 81) * (y ^ 2 - 121) * (y ^ 2 - 169)) →
      (16 * x ^ 7 - 3640 * x ^ 5 + 202566 * x ^ 3 - 2656355 * x) -
          2 * (16 * y ^ 7 - 3640 * y ^ 5 + 202566 * y ^ 3 - 2656355 * y) ∉
        ([0, 1, 8, 29, 46, 53, 84, 91, 107, 129, 136] : List (ZMod 137)) := by
  decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 32761000 in
-- Kernel enumeration of the 181² pairs `(x, y) ∈ (ZMod 181)²`; each pair
-- evaluates two degree-14 products, so the heartbeat cap is sized at
-- roughly 10³ heartbeats per pair.
private theorem strip_curve_p181 :
    ∀ x y : ZMod 181,
      (x ^ 2 - 1) * (x ^ 2 - 9) * (x ^ 2 - 25) * (x ^ 2 - 49) *
          (x ^ 2 - 81) * (x ^ 2 - 121) * (x ^ 2 - 169) =
        4 * ((y ^ 2 - 1) * (y ^ 2 - 9) * (y ^ 2 - 25) * (y ^ 2 - 49) *
          (y ^ 2 - 81) * (y ^ 2 - 121) * (y ^ 2 - 169)) →
      (16 * x ^ 7 - 3640 * x ^ 5 + 202566 * x ^ 3 - 2656355 * x) -
          2 * (16 * y ^ 7 - 3640 * y ^ 5 + 202566 * y ^ 3 - 2656355 * y) ∉
        ([2, 20, 29, 38, 47, 53, 58, 84, 89, 114, 123, 134, 143, 152, 161,
          177, 179] : List (ZMod 181)) := by
  decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 24649000 in
-- Kernel enumeration of the 157² pairs `(x, y) ∈ (ZMod 157)²`; each pair
-- evaluates two degree-14 products, so the heartbeat cap is sized at
-- roughly 10³ heartbeats per pair.
private theorem strip_curve_p157 :
    ∀ x y : ZMod 157,
      (x ^ 2 - 1) * (x ^ 2 - 9) * (x ^ 2 - 25) * (x ^ 2 - 49) *
          (x ^ 2 - 81) * (x ^ 2 - 121) * (x ^ 2 - 169) =
        4 * ((y ^ 2 - 1) * (y ^ 2 - 9) * (y ^ 2 - 25) * (y ^ 2 - 49) *
          (y ^ 2 - 81) * (y ^ 2 - 121) * (y ^ 2 - 169)) →
      (16 * x ^ 7 - 3640 * x ^ 5 + 202566 * x ^ 3 - 2656355 * x) -
          2 * (16 * y ^ 7 - 3640 * y ^ 5 + 202566 * y ^ 3 - 2656355 * y) ∉
        ([3, 13, 18, 28, 53, 64, 66, 76, 81, 88, 91, 93, 104, 107, 129, 139,
          144] : List (ZMod 157)) := by
  decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 57121000 in
-- Kernel enumeration of the 239² pairs `(x, y) ∈ (ZMod 239)²`; each pair
-- evaluates two degree-14 products, so the heartbeat cap is sized at
-- roughly 10³ heartbeats per pair.
private theorem strip_curve_p239 :
    ∀ x y : ZMod 239,
      (x ^ 2 - 1) * (x ^ 2 - 9) * (x ^ 2 - 25) * (x ^ 2 - 49) *
          (x ^ 2 - 81) * (x ^ 2 - 121) * (x ^ 2 - 169) =
        4 * ((y ^ 2 - 1) * (y ^ 2 - 9) * (y ^ 2 - 25) * (y ^ 2 - 49) *
          (y ^ 2 - 81) * (y ^ 2 - 121) * (y ^ 2 - 169)) →
      (16 * x ^ 7 - 3640 * x ^ 5 + 202566 * x ^ 3 - 2656355 * x) -
          2 * (16 * y ^ 7 - 3640 * y ^ 5 + 202566 * y ^ 3 - 2656355 * y) ∉
        ([2, 14, 70, 73, 82, 84, 95, 96, 100, 132, 139, 143, 150, 155, 157,
          159, 169, 173, 180, 198, 208, 228, 237, 238] : List (ZMod 239)) := by
  decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 9409000 in
-- Kernel enumeration of the 97² pairs `(x, y) ∈ (ZMod 97)²`; each pair
-- evaluates two degree-14 products, so the heartbeat cap is sized at
-- roughly 10³ heartbeats per pair.
private theorem strip_curve_p97 :
    ∀ x y : ZMod 97,
      (x ^ 2 - 1) * (x ^ 2 - 9) * (x ^ 2 - 25) * (x ^ 2 - 49) *
          (x ^ 2 - 81) * (x ^ 2 - 121) * (x ^ 2 - 169) =
        4 * ((y ^ 2 - 1) * (y ^ 2 - 9) * (y ^ 2 - 25) * (y ^ 2 - 49) *
          (y ^ 2 - 81) * (y ^ 2 - 121) * (y ^ 2 - 169)) →
      (16 * x ^ 7 - 3640 * x ^ 5 + 202566 * x ^ 3 - 2656355 * x) -
          2 * (16 * y ^ 7 - 3640 * y ^ 5 + 202566 * y ^ 3 - 2656355 * y) ∉
        ([21, 39, 76] : List (ZMod 97)) := by
  decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 22801000 in
-- Kernel enumeration of the 151² pairs `(x, y) ∈ (ZMod 151)²`; each pair
-- evaluates two degree-14 products, so the heartbeat cap is sized at
-- roughly 10³ heartbeats per pair.
private theorem strip_curve_p151 :
    ∀ x y : ZMod 151,
      (x ^ 2 - 1) * (x ^ 2 - 9) * (x ^ 2 - 25) * (x ^ 2 - 49) *
          (x ^ 2 - 81) * (x ^ 2 - 121) * (x ^ 2 - 169) =
        4 * ((y ^ 2 - 1) * (y ^ 2 - 9) * (y ^ 2 - 25) * (y ^ 2 - 49) *
          (y ^ 2 - 81) * (y ^ 2 - 121) * (y ^ 2 - 169)) →
      (16 * x ^ 7 - 3640 * x ^ 5 + 202566 * x ^ 3 - 2656355 * x) -
          2 * (16 * y ^ 7 - 3640 * y ^ 5 + 202566 * y ^ 3 - 2656355 * y) ∉
        ([54, 59, 92, 97, 149] : List (ZMod 151)) := by
  decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 73441000 in
-- Kernel enumeration of the 271² pairs `(x, y) ∈ (ZMod 271)²`; each pair
-- evaluates two degree-14 products, so the heartbeat cap is sized at
-- roughly 10³ heartbeats per pair.
private theorem strip_curve_p271 :
    ∀ x y : ZMod 271,
      (x ^ 2 - 1) * (x ^ 2 - 9) * (x ^ 2 - 25) * (x ^ 2 - 49) *
          (x ^ 2 - 81) * (x ^ 2 - 121) * (x ^ 2 - 169) =
        4 * ((y ^ 2 - 1) * (y ^ 2 - 9) * (y ^ 2 - 25) * (y ^ 2 - 49) *
          (y ^ 2 - 81) * (y ^ 2 - 121) * (y ^ 2 - 169)) →
      (16 * x ^ 7 - 3640 * x ^ 5 + 202566 * x ^ 3 - 2656355 * x) -
          2 * (16 * y ^ 7 - 3640 * y ^ 5 + 202566 * y ^ 3 - 2656355 * y) ∉
        ([7, 24, 28, 48, 55, 71, 82, 91, 122, 136, 150, 166, 168, 190, 208,
          213, 239, 255, 264] : List (ZMod 271)) := by
  decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 58081000 in
-- Kernel enumeration of the 241² pairs `(x, y) ∈ (ZMod 241)²`; each pair
-- evaluates two degree-14 products, so the heartbeat cap is sized at
-- roughly 10³ heartbeats per pair.
private theorem strip_curve_p241 :
    ∀ x y : ZMod 241,
      (x ^ 2 - 1) * (x ^ 2 - 9) * (x ^ 2 - 25) * (x ^ 2 - 49) *
          (x ^ 2 - 81) * (x ^ 2 - 121) * (x ^ 2 - 169) =
        4 * ((y ^ 2 - 1) * (y ^ 2 - 9) * (y ^ 2 - 25) * (y ^ 2 - 49) *
          (y ^ 2 - 81) * (y ^ 2 - 121) * (y ^ 2 - 169)) →
      (16 * x ^ 7 - 3640 * x ^ 5 + 202566 * x ^ 3 - 2656355 * x) -
          2 * (16 * y ^ 7 - 3640 * y ^ 5 + 202566 * y ^ 3 - 2656355 * y) ∉
        ([35, 44, 54, 92, 114, 115, 133, 181, 206, 227] : List (ZMod 241)) := by
  decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 49729000 in
-- Kernel enumeration of the 223² pairs `(x, y) ∈ (ZMod 223)²`; each pair
-- evaluates two degree-14 products, so the heartbeat cap is sized at
-- roughly 10³ heartbeats per pair.
private theorem strip_curve_p223 :
    ∀ x y : ZMod 223,
      (x ^ 2 - 1) * (x ^ 2 - 9) * (x ^ 2 - 25) * (x ^ 2 - 49) *
          (x ^ 2 - 81) * (x ^ 2 - 121) * (x ^ 2 - 169) =
        4 * ((y ^ 2 - 1) * (y ^ 2 - 9) * (y ^ 2 - 25) * (y ^ 2 - 49) *
          (y ^ 2 - 81) * (y ^ 2 - 121) * (y ^ 2 - 169)) →
      (16 * x ^ 7 - 3640 * x ^ 5 + 202566 * x ^ 3 - 2656355 * x) -
          2 * (16 * y ^ 7 - 3640 * y ^ 5 + 202566 * y ^ 3 - 2656355 * y) ∉
        ([3, 51, 73, 91, 103, 113] : List (ZMod 223)) := by
  decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 22201000 in
-- Kernel enumeration of the 149² pairs `(x, y) ∈ (ZMod 149)²`; each pair
-- evaluates two degree-14 products, so the heartbeat cap is sized at
-- roughly 10³ heartbeats per pair.
private theorem strip_curve_p149 :
    ∀ x y : ZMod 149,
      (x ^ 2 - 1) * (x ^ 2 - 9) * (x ^ 2 - 25) * (x ^ 2 - 49) *
          (x ^ 2 - 81) * (x ^ 2 - 121) * (x ^ 2 - 169) =
        4 * ((y ^ 2 - 1) * (y ^ 2 - 9) * (y ^ 2 - 25) * (y ^ 2 - 49) *
          (y ^ 2 - 81) * (y ^ 2 - 121) * (y ^ 2 - 169)) →
      (16 * x ^ 7 - 3640 * x ^ 5 + 202566 * x ^ 3 - 2656355 * x) -
          2 * (16 * y ^ 7 - 3640 * y ^ 5 + 202566 * y ^ 3 - 2656355 * y) ∉
        ([115, 117] : List (ZMod 149)) := by
  decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 11881000 in
-- Kernel enumeration of the 109² pairs `(x, y) ∈ (ZMod 109)²`; each pair
-- evaluates two degree-14 products, so the heartbeat cap is sized at
-- roughly 10³ heartbeats per pair.
private theorem strip_curve_p109 :
    ∀ x y : ZMod 109,
      (x ^ 2 - 1) * (x ^ 2 - 9) * (x ^ 2 - 25) * (x ^ 2 - 49) *
          (x ^ 2 - 81) * (x ^ 2 - 121) * (x ^ 2 - 169) =
        4 * ((y ^ 2 - 1) * (y ^ 2 - 9) * (y ^ 2 - 25) * (y ^ 2 - 49) *
          (y ^ 2 - 81) * (y ^ 2 - 121) * (y ^ 2 - 169)) →
      (16 * x ^ 7 - 3640 * x ^ 5 + 202566 * x ^ 3 - 2656355 * x) -
          2 * (16 * y ^ 7 - 3640 * y ^ 5 + 202566 * y ^ 3 - 2656355 * y) ∉
        ([3] : List (ZMod 109)) := by
  decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 63001000 in
-- Kernel enumeration of the 251² pairs `(x, y) ∈ (ZMod 251)²`; each pair
-- evaluates two degree-14 products, so the heartbeat cap is sized at
-- roughly 10³ heartbeats per pair.
private theorem strip_curve_p251 :
    ∀ x y : ZMod 251,
      (x ^ 2 - 1) * (x ^ 2 - 9) * (x ^ 2 - 25) * (x ^ 2 - 49) *
          (x ^ 2 - 81) * (x ^ 2 - 121) * (x ^ 2 - 169) =
        4 * ((y ^ 2 - 1) * (y ^ 2 - 9) * (y ^ 2 - 25) * (y ^ 2 - 49) *
          (y ^ 2 - 81) * (y ^ 2 - 121) * (y ^ 2 - 169)) →
      (16 * x ^ 7 - 3640 * x ^ 5 + 202566 * x ^ 3 - 2656355 * x) -
          2 * (16 * y ^ 7 - 3640 * y ^ 5 + 202566 * y ^ 3 - 2656355 * y) ∉
        ([47, 73, 94, 235, 248] : List (ZMod 251)) := by
  decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 96721000 in
-- Kernel enumeration of the 311² pairs `(x, y) ∈ (ZMod 311)²`; each pair
-- evaluates two degree-14 products, so the heartbeat cap is sized at
-- roughly 10³ heartbeats per pair.
private theorem strip_curve_p311 :
    ∀ x y : ZMod 311,
      (x ^ 2 - 1) * (x ^ 2 - 9) * (x ^ 2 - 25) * (x ^ 2 - 49) *
          (x ^ 2 - 81) * (x ^ 2 - 121) * (x ^ 2 - 169) =
        4 * ((y ^ 2 - 1) * (y ^ 2 - 9) * (y ^ 2 - 25) * (y ^ 2 - 49) *
          (y ^ 2 - 81) * (y ^ 2 - 121) * (y ^ 2 - 169)) →
      (16 * x ^ 7 - 3640 * x ^ 5 + 202566 * x ^ 3 - 2656355 * x) -
          2 * (16 * y ^ 7 - 3640 * y ^ 5 + 202566 * y ^ 3 - 2656355 * y) ∉
        ([79, 93, 95, 200, 244] : List (ZMod 311)) := by
  decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 54289000 in
-- Kernel enumeration of the 233² pairs `(x, y) ∈ (ZMod 233)²`; each pair
-- evaluates two degree-14 products, so the heartbeat cap is sized at
-- roughly 10³ heartbeats per pair.
private theorem strip_curve_p233 :
    ∀ x y : ZMod 233,
      (x ^ 2 - 1) * (x ^ 2 - 9) * (x ^ 2 - 25) * (x ^ 2 - 49) *
          (x ^ 2 - 81) * (x ^ 2 - 121) * (x ^ 2 - 169) =
        4 * ((y ^ 2 - 1) * (y ^ 2 - 9) * (y ^ 2 - 25) * (y ^ 2 - 49) *
          (y ^ 2 - 81) * (y ^ 2 - 121) * (y ^ 2 - 169)) →
      (16 * x ^ 7 - 3640 * x ^ 5 + 202566 * x ^ 3 - 2656355 * x) -
          2 * (16 * y ^ 7 - 3640 * y ^ 5 + 202566 * y ^ 3 - 2656355 * y) ∉
        ([161, 183] : List (ZMod 233)) := by
  decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 36481000 in
-- Kernel enumeration of the 191² pairs `(x, y) ∈ (ZMod 191)²`; each pair
-- evaluates two degree-14 products, so the heartbeat cap is sized at
-- roughly 10³ heartbeats per pair.
private theorem strip_curve_p191 :
    ∀ x y : ZMod 191,
      (x ^ 2 - 1) * (x ^ 2 - 9) * (x ^ 2 - 25) * (x ^ 2 - 49) *
          (x ^ 2 - 81) * (x ^ 2 - 121) * (x ^ 2 - 169) =
        4 * ((y ^ 2 - 1) * (y ^ 2 - 9) * (y ^ 2 - 25) * (y ^ 2 - 49) *
          (y ^ 2 - 81) * (y ^ 2 - 121) * (y ^ 2 - 169)) →
      (16 * x ^ 7 - 3640 * x ^ 5 + 202566 * x ^ 3 - 2656355 * x) -
          2 * (16 * y ^ 7 - 3640 * y ^ 5 + 202566 * y ^ 3 - 2656355 * y) ∉
        ([183] : List (ZMod 191)) := by
  decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 44521000 in
-- Kernel enumeration of the 211² pairs `(x, y) ∈ (ZMod 211)²`; each pair
-- evaluates two degree-14 products, so the heartbeat cap is sized at
-- roughly 10³ heartbeats per pair.
private theorem strip_curve_p211 :
    ∀ x y : ZMod 211,
      (x ^ 2 - 1) * (x ^ 2 - 9) * (x ^ 2 - 25) * (x ^ 2 - 49) *
          (x ^ 2 - 81) * (x ^ 2 - 121) * (x ^ 2 - 169) =
        4 * ((y ^ 2 - 1) * (y ^ 2 - 9) * (y ^ 2 - 25) * (y ^ 2 - 49) *
          (y ^ 2 - 81) * (y ^ 2 - 121) * (y ^ 2 - 169)) →
      (16 * x ^ 7 - 3640 * x ^ 5 + 202566 * x ^ 3 - 2656355 * x) -
          2 * (16 * y ^ 7 - 3640 * y ^ 5 + 202566 * y ^ 3 - 2656355 * y) ∉
        ([165] : List (ZMod 211)) := by
  decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 69169000 in
-- Kernel enumeration of the 263² pairs `(x, y) ∈ (ZMod 263)²`; each pair
-- evaluates two degree-14 products, so the heartbeat cap is sized at
-- roughly 10³ heartbeats per pair.
private theorem strip_curve_p263 :
    ∀ x y : ZMod 263,
      (x ^ 2 - 1) * (x ^ 2 - 9) * (x ^ 2 - 25) * (x ^ 2 - 49) *
          (x ^ 2 - 81) * (x ^ 2 - 121) * (x ^ 2 - 169) =
        4 * ((y ^ 2 - 1) * (y ^ 2 - 9) * (y ^ 2 - 25) * (y ^ 2 - 49) *
          (y ^ 2 - 81) * (y ^ 2 - 121) * (y ^ 2 - 169)) →
      (16 * x ^ 7 - 3640 * x ^ 5 + 202566 * x ^ 3 - 2656355 * x) -
          2 * (16 * y ^ 7 - 3640 * y ^ 5 + 202566 * y ^ 3 - 2656355 * y) ∉
        ([25] : List (ZMod 263)) := by
  decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 113569000 in
-- Kernel enumeration of the 337² pairs `(x, y) ∈ (ZMod 337)²`; each pair
-- evaluates two degree-14 products, so the heartbeat cap is sized at
-- roughly 10³ heartbeats per pair.
private theorem strip_curve_p337 :
    ∀ x y : ZMod 337,
      (x ^ 2 - 1) * (x ^ 2 - 9) * (x ^ 2 - 25) * (x ^ 2 - 49) *
          (x ^ 2 - 81) * (x ^ 2 - 121) * (x ^ 2 - 169) =
        4 * ((y ^ 2 - 1) * (y ^ 2 - 9) * (y ^ 2 - 25) * (y ^ 2 - 49) *
          (y ^ 2 - 81) * (y ^ 2 - 121) * (y ^ 2 - 169)) →
      (16 * x ^ 7 - 3640 * x ^ 5 + 202566 * x ^ 3 - 2656355 * x) -
          2 * (16 * y ^ 7 - 3640 * y ^ 5 + 202566 * y ^ 3 - 2656355 * y) ∉
        ([149] : List (ZMod 337)) := by
  decide

/-- Transfer a curve certificate to the trapped integer center: if
`m = T₁₄(w) - 2T₁₄(v)` on the curve and `m = -a`, then `-a mod p` cannot
lie in a residue list avoided by the curve. -/
private lemma strip_kill {p : ℕ} {L : List (ZMod p)}
    (hcurve : ∀ x y : ZMod p,
      (x ^ 2 - 1) * (x ^ 2 - 9) * (x ^ 2 - 25) * (x ^ 2 - 49) *
          (x ^ 2 - 81) * (x ^ 2 - 121) * (x ^ 2 - 169) =
        4 * ((y ^ 2 - 1) * (y ^ 2 - 9) * (y ^ 2 - 25) * (y ^ 2 - 49) *
          (y ^ 2 - 81) * (y ^ 2 - 121) * (y ^ 2 - 169)) →
      (16 * x ^ 7 - 3640 * x ^ 5 + 202566 * x ^ 3 - 2656355 * x) -
          2 * (16 * y ^ 7 - 3640 * y ^ 5 + 202566 * y ^ 3 - 2656355 * y) ∉ L)
    {w v m : ℤ} {a : ℕ}
    (hS : (w ^ 2 - 1) * (w ^ 2 - 9) * (w ^ 2 - 25) * (w ^ 2 - 49) *
        (w ^ 2 - 81) * (w ^ 2 - 121) * (w ^ 2 - 169) =
      4 * ((v ^ 2 - 1) * (v ^ 2 - 9) * (v ^ 2 - 25) * (v ^ 2 - 49) *
        (v ^ 2 - 81) * (v ^ 2 - 121) * (v ^ 2 - 169)))
    (hm : m = (16 * w ^ 7 - 3640 * w ^ 5 + 202566 * w ^ 3 - 2656355 * w) -
        2 * (16 * v ^ 7 - 3640 * v ^ 5 + 202566 * v ^ 3 - 2656355 * v))
    (ha : m = -(a : ℤ)) (hbad : -(a : ZMod p) ∈ L) : False := by
  have hS' := congrArg (fun z : ℤ => (z : ZMod p)) hS
  push_cast at hS'
  have hm' := congrArg (fun z : ℤ => (z : ZMod p)) hm
  push_cast at hm'
  have ha' := congrArg (fun z : ℤ => (z : ZMod p)) ha
  push_cast at ha'
  exact hcurve (w : ZMod p) (v : ZMod p) hS' (by rw [← hm', ha']; exact hbad)

-- The 31-fold disjunction of list memberships needs a larger-than-default
-- `Decidable` instance term (the default `synthInstance.maxSize` is 128).
set_option synthInstance.maxSize 1024 in
set_option maxRecDepth 200000 in
-- Kernel scan of the 834 candidates: each evaluates at most 31 literal
-- casts into `ZMod p` plus short list-membership scans, so the heartbeat
-- cap is sized at roughly 10⁵ heartbeats per candidate.
set_option maxHeartbeats 100000000 in
-- Dispatch: every candidate `m = -7(2j+1)`, `j < 834`, hits the bad-residue
-- list of one of the cover primes.
private theorem strip_dispatch :
    ∀ j : Fin 834,
      -((7 * (2 * (j : ℕ) + 1) : ℕ) : ZMod 31) ∈
        ([0] : List (ZMod 31)) ∨
      -((7 * (2 * (j : ℕ) + 1) : ℕ) : ZMod 139) ∈
        ([0, 1, 7, 8, 12, 14, 15, 25, 28, 29, 52, 54, 56, 57, 59, 80, 82,
          83, 85, 87, 110, 111, 114, 124, 125, 127, 131, 132, 138] : List (ZMod 139)) ∨
      -((7 * (2 * (j : ℕ) + 1) : ℕ) : ZMod 67) ∈
        ([0, 32, 35] : List (ZMod 67)) ∨
      -((7 * (2 * (j : ℕ) + 1) : ℕ) : ZMod 131) ∈
        ([5, 7, 12, 13, 36, 37, 44, 45, 50, 60, 62, 69, 71, 81, 86, 87, 94,
          95, 118, 119, 124, 126] : List (ZMod 131)) ∨
      -((7 * (2 * (j : ℕ) + 1) : ℕ) : ZMod 83) ∈
        ([1, 16, 37, 46, 67, 82] : List (ZMod 83)) ∨
      -((7 * (2 * (j : ℕ) + 1) : ℕ) : ZMod 71) ∈
        ([0, 19, 52] : List (ZMod 71)) ∨
      -((7 * (2 * (j : ℕ) + 1) : ℕ) : ZMod 107) ∈
        ([0, 4, 14, 19, 30, 77, 88, 93, 103] : List (ZMod 107)) ∨
      -((7 * (2 * (j : ℕ) + 1) : ℕ) : ZMod 163) ∈
        ([5, 9, 15, 16, 30, 34, 48, 49, 56, 66, 70, 72, 73, 77, 81, 82, 86,
          90, 91, 93, 97, 107, 114, 115, 129, 133, 147, 148, 154, 158] : List (ZMod 163)) ∨
      -((7 * (2 * (j : ℕ) + 1) : ℕ) : ZMod 193) ∈
        ([0, 3, 4, 10, 14, 15, 26, 27, 31, 32, 35, 38, 41, 45, 47, 49, 53,
          60, 62, 64, 79, 82, 96, 97, 111, 113, 126, 129, 131, 133, 140,
          146, 148, 152, 155, 158, 161, 162, 166, 179, 183, 189, 190] : List (ZMod 193)) ∨
      -((7 * (2 * (j : ℕ) + 1) : ℕ) : ZMod 101) ∈
        ([36, 41, 45, 56, 60, 65] : List (ZMod 101)) ∨
      -((7 * (2 * (j : ℕ) + 1) : ℕ) : ZMod 113) ∈
        ([21, 22, 48, 65, 91, 92, 109] : List (ZMod 113)) ∨
      -((7 * (2 * (j : ℕ) + 1) : ℕ) : ZMod 199) ∈
        ([0, 6, 9, 13, 17, 23, 30, 37, 50, 54, 59, 60, 64, 82, 87, 107, 112,
          117, 135, 139, 145, 149, 156, 162, 182, 186, 190, 191, 193] : List (ZMod 199)) ∨
      -((7 * (2 * (j : ℕ) + 1) : ℕ) : ZMod 73) ∈
        ([1, 72] : List (ZMod 73)) ∨
      -((7 * (2 * (j : ℕ) + 1) : ℕ) : ZMod 137) ∈
        ([0, 1, 8, 29, 46, 53, 84, 91, 107, 129, 136] : List (ZMod 137)) ∨
      -((7 * (2 * (j : ℕ) + 1) : ℕ) : ZMod 181) ∈
        ([2, 20, 29, 38, 47, 53, 58, 84, 89, 114, 123, 134, 143, 152, 161,
          177, 179] : List (ZMod 181)) ∨
      -((7 * (2 * (j : ℕ) + 1) : ℕ) : ZMod 157) ∈
        ([3, 13, 18, 28, 53, 64, 66, 76, 81, 88, 91, 93, 104, 107, 129, 139,
          144] : List (ZMod 157)) ∨
      -((7 * (2 * (j : ℕ) + 1) : ℕ) : ZMod 239) ∈
        ([2, 14, 70, 73, 82, 84, 95, 96, 100, 132, 139, 143, 150, 155, 157,
          159, 169, 173, 180, 198, 208, 228, 237, 238] : List (ZMod 239)) ∨
      -((7 * (2 * (j : ℕ) + 1) : ℕ) : ZMod 97) ∈
        ([21, 39, 76] : List (ZMod 97)) ∨
      -((7 * (2 * (j : ℕ) + 1) : ℕ) : ZMod 151) ∈
        ([54, 59, 92, 97, 149] : List (ZMod 151)) ∨
      -((7 * (2 * (j : ℕ) + 1) : ℕ) : ZMod 271) ∈
        ([7, 24, 28, 48, 55, 71, 82, 91, 122, 136, 150, 166, 168, 190, 208,
          213, 239, 255, 264] : List (ZMod 271)) ∨
      -((7 * (2 * (j : ℕ) + 1) : ℕ) : ZMod 241) ∈
        ([35, 44, 54, 92, 114, 115, 133, 181, 206, 227] : List (ZMod 241)) ∨
      -((7 * (2 * (j : ℕ) + 1) : ℕ) : ZMod 223) ∈
        ([3, 51, 73, 91, 103, 113] : List (ZMod 223)) ∨
      -((7 * (2 * (j : ℕ) + 1) : ℕ) : ZMod 149) ∈
        ([115, 117] : List (ZMod 149)) ∨
      -((7 * (2 * (j : ℕ) + 1) : ℕ) : ZMod 109) ∈
        ([3] : List (ZMod 109)) ∨
      -((7 * (2 * (j : ℕ) + 1) : ℕ) : ZMod 251) ∈
        ([47, 73, 94, 235, 248] : List (ZMod 251)) ∨
      -((7 * (2 * (j : ℕ) + 1) : ℕ) : ZMod 311) ∈
        ([79, 93, 95, 200, 244] : List (ZMod 311)) ∨
      -((7 * (2 * (j : ℕ) + 1) : ℕ) : ZMod 233) ∈
        ([161, 183] : List (ZMod 233)) ∨
      -((7 * (2 * (j : ℕ) + 1) : ℕ) : ZMod 191) ∈
        ([183] : List (ZMod 191)) ∨
      -((7 * (2 * (j : ℕ) + 1) : ℕ) : ZMod 211) ∈
        ([165] : List (ZMod 211)) ∨
      -((7 * (2 * (j : ℕ) + 1) : ℕ) : ZMod 263) ∈
        ([25] : List (ZMod 263)) ∨
      -((7 * (2 * (j : ℕ) + 1) : ℕ) : ZMod 337) ∈
        ([149] : List (ZMod 337)) := by
  decide

/-! ## `k = 14`, all `d ≥ 221` -/

set_option maxHeartbeats 16000000 in
-- The two window `linarith` certificates expand degree-7 polynomials with
-- 10²⁰-scale coefficients, and the final `omega`/`rcases` dispatch walks a
-- 31-fold disjunction, so this proof needs more than the default budget.
/-- **Erdős 686, `k = 14`, `N = 4`, `d ≥ 221`**: fourteen-blocks in quotient
`4` with gap `d ≥ 221` do not exist.  The trapped center
`m = T₁₄(w) - 2T₁₄(v)` lies in `(-11680, 0)`, is odd, and is divisible by
`7`; each of the `834` candidates `m = -7(2j+1)` dies modulo one of
31 primes (kernel certificates `strip_curve_p*` + `strip_dispatch`).
This covers the strip `221 ≤ d < 663000` left open by
`no_gap_solution_four_even_fourteen_of_large_gap`, and reproves the
large-gap branch along the way. -/
theorem no_gap_solution_four_even_fourteen {n d : ℕ} (hd : 221 ≤ d) :
    blockProduct 14 (n + d) ≠ 4 * blockProduct 14 n := by
  intro heq
  obtain ⟨hup, hlo⟩ := ratio_window_four_nat heq
  have hnlow : 9 * d ≤ n + 1 := row_base_lower_k14 hd hup
  have hlin :=
    ratio_window_linearize_of_pow_bracket (N := 4) (A := 21) (B := 19)
      (k := 14) (n := n) (d := d) (by norm_num) (by norm_num) hup
  have hlin2 :=
    ratio_window_upper_linearize_of_pow_bracket (N := 4) (A := 11) (B := 10)
      (k := 14) (n := n) (d := d) (by norm_num) (by norm_num) hlo
  have hZ : ((blockProduct 14 (n + d) : ℕ) : ℤ) =
      4 * ((blockProduct 14 n : ℕ) : ℤ) := by exact_mod_cast heq
  obtain ⟨w, hwdef⟩ : ∃ w : ℤ, w = 2 * ((n : ℤ) + (d : ℤ)) + 15 := ⟨_, rfl⟩
  obtain ⟨v, hvdef⟩ : ∃ v : ℤ, v = 2 * (n : ℤ) + 15 := ⟨_, rfl⟩
  have hv0 : (3991 : ℤ) ≤ v := by omega
  have hw0 : (3991 : ℤ) ≤ w := by omega
  have hlink : 19 * w ≤ 21 * v + 24 := by omega
  have hlink2 : 11 * v ≤ 10 * w + 11 := by omega
  have h1 := strip_s14_bridge (n + d)
  have h2 := strip_s14_bridge n
  have hcw : 2 * ((n + d : ℕ) : ℤ) + 15 = w := by push_cast; omega
  have hcv : 2 * ((n : ℕ) : ℤ) + 15 = v := by omega
  rw [hcw] at h1
  rw [hcv] at h2
  have hS : (w ^ 2 - 1) * (w ^ 2 - 9) * (w ^ 2 - 25) * (w ^ 2 - 49) *
        (w ^ 2 - 81) * (w ^ 2 - 121) * (w ^ 2 - 169) =
      4 * ((v ^ 2 - 1) * (v ^ 2 - 9) * (v ^ 2 - 25) * (v ^ 2 - 49) *
        (v ^ 2 - 81) * (v ^ 2 - 121) * (v ^ 2 - 169)) := by
    rw [h1, h2, hZ]; ring
  obtain ⟨m, hm⟩ : ∃ m : ℤ,
      m = (16 * w ^ 7 - 3640 * w ^ 5 + 202566 * w ^ 3 - 2656355 * w) -
        2 * (16 * v ^ 7 - 3640 * v ^ 5 + 202566 * v ^ 3 - 2656355 * v) :=
    ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X : ℤ,
      X = (16 * w ^ 7 - 3640 * w ^ 5 + 202566 * w ^ 3 - 2656355 * w) +
        2 * (16 * v ^ 7 - 3640 * v ^ 5 + 202566 * v ^ 3 - 2656355 * v) :=
    ⟨_, rfl⟩
  have hTw : 0 < 16 * w ^ 7 - 3640 * w ^ 5 + 202566 * w ^ 3 - 2656355 * w :=
    strip_k14_T_pos hw0
  have hTv : 0 < 16 * v ^ 7 - 3640 * v ^ 5 + 202566 * v ^ 3 - 2656355 * v :=
    strip_k14_T_pos hv0
  have hXpos : 0 < X := by rw [hX]; linarith
  have hmX : m * X =
      (1318847348 * w ^ 6 - 92807039780 * w ^ 4 + 1455430979401 * w ^ 2 +
          4674935865600) -
        4 * (1318847348 * v ^ 6 - 92807039780 * v ^ 4 +
          1455430979401 * v ^ 2 + 4674935865600) := by
    rw [hm, hX]; linear_combination 256 * hS
  have h19w6 : (19 * w) ^ 6 ≤ (21 * v + 24) ^ 6 :=
    pow_le_pow_left₀ (by omega) (by omega) 6
  have hw4 : v ^ 4 ≤ w ^ 4 := pow_le_pow_left₀ (by omega) (by omega) 4
  have h19w2 : (19 * w) ^ 2 ≤ (21 * v + 24) ^ 2 :=
    pow_le_pow_left₀ (by omega) (by omega) 2
  have hΔneg : (1318847348 * w ^ 6 - 92807039780 * w ^ 4 +
      1455430979401 * w ^ 2 + 4674935865600) -
      4 * (1318847348 * v ^ 6 - 92807039780 * v ^ 4 + 1455430979401 * v ^ 2 +
        4674935865600) < 0 := by
    linarith [h19w6, hw4, h19w2, strip_k14_upper hv0]
  have h10w7 : (11 * v - 11) ^ 7 ≤ (10 * w) ^ 7 :=
    pow_le_pow_left₀ (by omega) (by omega) 7
  have h10w6 : (11 * v - 11) ^ 6 ≤ (10 * w) ^ 6 :=
    pow_le_pow_left₀ (by omega) (by omega) 6
  have h19w5 : (19 * w) ^ 5 ≤ (21 * v + 24) ^ 5 :=
    pow_le_pow_left₀ (by omega) (by omega) 5
  have h19w4 : (19 * w) ^ 4 ≤ (21 * v + 24) ^ 4 :=
    pow_le_pow_left₀ (by omega) (by omega) 4
  have hw3 : v ^ 3 ≤ w ^ 3 := pow_le_pow_left₀ (by omega) (by omega) 3
  have hw2 : v ^ 2 ≤ w ^ 2 := pow_le_pow_left₀ (by omega) (by omega) 2
  have hΔlo : -11680 * X < (1318847348 * w ^ 6 - 92807039780 * w ^ 4 +
      1455430979401 * w ^ 2 + 4674935865600) -
      4 * (1318847348 * v ^ 6 - 92807039780 * v ^ 4 + 1455430979401 * v ^ 2 +
        4674935865600) := by
    rw [hX]
    linarith [h10w7, h10w6, h19w5, h19w4, hw3, hw2, hlink,
      strip_k14_lower hv0]
  have hmneg : m < 0 := by
    by_contra hcon
    have hge := mul_nonneg (not_lt.mp hcon) hXpos.le
    rw [hmX] at hge
    linarith
  have hmgt : -11680 < m := by
    by_contra hcon
    have hmul := mul_le_mul_of_nonneg_right (not_lt.mp hcon) hXpos.le
    rw [hmX] at hmul
    linarith
  -- parity: m = 2c + w with w odd, and 7 ∣ m
  obtain ⟨cpar, hcpar⟩ : ∃ c : ℤ, m = 2 * c + w :=
    ⟨8 * w ^ 7 - 1820 * w ^ 5 + 101283 * w ^ 3 - 1328178 * w -
      (16 * v ^ 7 - 3640 * v ^ 5 + 202566 * v ^ 3 - 2656355 * v),
      by rw [hm]; ring⟩
  have h7m : (7 : ℤ) ∣ m := by
    rw [hm]
    exact dvd_sub (strip_seven_dvd_T14 w) ((strip_seven_dvd_T14 v).mul_left 2)
  -- the candidate index: m = -7(2j+1) with j < 834
  obtain ⟨j, hj, hjm⟩ : ∃ j : ℕ, j < 834 ∧ m = -((7 * (2 * j + 1) : ℕ) : ℤ) :=
    ⟨((-m).toNat / 7 - 1) / 2, by omega, by omega⟩
  rcases strip_dispatch ⟨j, hj⟩ with
      hbad | hbad | hbad | hbad | hbad | hbad | hbad | hbad |
      hbad | hbad | hbad | hbad | hbad | hbad | hbad | hbad |
      hbad | hbad | hbad | hbad | hbad | hbad | hbad | hbad |
      hbad | hbad | hbad | hbad | hbad | hbad | hbad
  · exact strip_kill strip_curve_p31 hS hm hjm hbad
  · exact strip_kill strip_curve_p139 hS hm hjm hbad
  · exact strip_kill strip_curve_p67 hS hm hjm hbad
  · exact strip_kill strip_curve_p131 hS hm hjm hbad
  · exact strip_kill strip_curve_p83 hS hm hjm hbad
  · exact strip_kill strip_curve_p71 hS hm hjm hbad
  · exact strip_kill strip_curve_p107 hS hm hjm hbad
  · exact strip_kill strip_curve_p163 hS hm hjm hbad
  · exact strip_kill strip_curve_p193 hS hm hjm hbad
  · exact strip_kill strip_curve_p101 hS hm hjm hbad
  · exact strip_kill strip_curve_p113 hS hm hjm hbad
  · exact strip_kill strip_curve_p199 hS hm hjm hbad
  · exact strip_kill strip_curve_p73 hS hm hjm hbad
  · exact strip_kill strip_curve_p137 hS hm hjm hbad
  · exact strip_kill strip_curve_p181 hS hm hjm hbad
  · exact strip_kill strip_curve_p157 hS hm hjm hbad
  · exact strip_kill strip_curve_p239 hS hm hjm hbad
  · exact strip_kill strip_curve_p97 hS hm hjm hbad
  · exact strip_kill strip_curve_p151 hS hm hjm hbad
  · exact strip_kill strip_curve_p271 hS hm hjm hbad
  · exact strip_kill strip_curve_p241 hS hm hjm hbad
  · exact strip_kill strip_curve_p223 hS hm hjm hbad
  · exact strip_kill strip_curve_p149 hS hm hjm hbad
  · exact strip_kill strip_curve_p109 hS hm hjm hbad
  · exact strip_kill strip_curve_p251 hS hm hjm hbad
  · exact strip_kill strip_curve_p311 hS hm hjm hbad
  · exact strip_kill strip_curve_p233 hS hm hjm hbad
  · exact strip_kill strip_curve_p191 hS hm hjm hbad
  · exact strip_kill strip_curve_p211 hS hm hjm hbad
  · exact strip_kill strip_curve_p263 hS hm hjm hbad
  · exact strip_kill strip_curve_p337 hS hm hjm hbad

/-! ## Packaged even-`k` corollary -/

/-- **Erdős 686, even `k ≤ 14`, `N = 4`, `d ≥ 221`**: for
`k ∈ {6, 8, 10, 12, 14}` no `k`-block is `4` times another `k`-block at
gap `d ≥ 221`. -/
theorem no_gap_solution_four_even_k {k n d : ℕ}
    (hk : k ∈ ({6, 8, 10, 12, 14} : Finset ℕ)) (hd : 221 ≤ d) :
    blockProduct k (n + d) ≠ 4 * blockProduct k n := by
  fin_cases hk
  · exact no_gap_solution_four_even_six hd
  · exact no_gap_solution_four_even_eight hd
  · exact no_gap_solution_four_even_ten hd
  · exact no_gap_solution_four_even_twelve hd
  · exact no_gap_solution_four_even_fourteen hd

end Erdos686Variant

end Erdos686
