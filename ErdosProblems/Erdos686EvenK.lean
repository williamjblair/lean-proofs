/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686QuotientConfinement

/-!
# Erdős Problem 686: even-`k` exclusion for `N = 4`, `d ≥ 221`

For even `k` write `w = 2(n+d)+k+1`, `v = 2n+k+1` (both odd) and
`S_k(W) = ∏_{l odd, 1 ≤ l ≤ k-1} (W² - l²)`, so that
`2^k · blockProduct k x = S_k(2x+k+1)` and the equation
`blockProduct k (n+d) = 4 · blockProduct k n` becomes `S_k(w) = 4·S_k(v)`.

Let `P_k` be the polynomial part of `√S_k`, let `c` be the minimal power of
two making `T := c·P_k` integral, and `D := T² - c²·S_k` (an integer
polynomial of degree `< deg T`).  Pure algebra then gives, for
`m := T(w) - 2T(v)` and `X := T(w) + 2T(v)`,

  `m · X = c²(S_k(w) - 4S_k(v)) + D(w) - 4D(v) = D(w) - 4D(v)`.

The banked ratio-window linearizations (`Erdos686.lean`) confine `w` to a
narrow multiple of `v`, and the banked per-`k` lower bounds
(`Erdos686QuotientConfinement.lean`, `d ≥ 221`) force `v ≥ V₀(k)`; together
these make `D(w) - 4D(v)` negative and small against `X`, so the integer
`m` is trapped in a short open interval `(-B, 0)`:

* `k = 6`  (`T = 2W³-35W`, `D = 189W²+900`, `V₀ = 1331`): `B = 1`,
  no integer in `(-1, 0)` — contradiction.
* `k = 8`  (`T = W⁴-42W²+105`, `D = 4096W²`, `V₀ = 2217`): `B = 1`.
* `k = 12` (`T = W⁶-143W⁴+4147W²-24453`,
  `D = 2223936W⁴-73996416W²+489893184`, `V₀ = 3547`): `B = 1`.
* `k = 10` (`T = 8W⁵-660W³+7887W`,
  `D = 649000W⁴-5457375W²+57153600`, `V₀ = 2661`): only `B = 25` is
  available, but `m` is odd (`T` is odd at odd arguments) and `5 ∣ m`
  (Fermat: `T ≡ 0 mod 5` identically), leaving `m ∈ {-5, -15}`; both are
  impossible modulo `11`, checked by `decide` on `(ZMod 11)²`.
* `k = 14` (`T = 16W⁷-3640W⁵+202566W³-2656355W`): the deficit
  `D = 1318847348W⁶ - …` is so large relative to `T` that trapping `m` in
  `(-7, 0)` (which kills it via `7 ∣ m`, Fermat mod `7`) needs
  `v ≥ 11 928 357`, i.e. `d ≥ 663 000`.  This module therefore only banks
  the large-gap branch `no_gap_solution_four_even_fourteen_of_large_gap`;
  the strip `221 ≤ d < 663 000` for `k = 14` remains open here.

All inequalities are single `linarith` certificates, linear in a handful of
supplied power-monotonicity facts plus one univariate shifted-positivity
lemma each; their feasibility (all shifted coefficients nonnegative at the
stated thresholds) was verified exactly in
`compute/erdos686_evenk_verify.py`.
-/

namespace Erdos686

namespace Erdos686Variant

/-! ## Block-product expansions -/

private lemma evenk_blockProduct_six_prod (x : ℕ) :
    blockProduct 6 x =
      (x + 1) * (x + 2) * (x + 3) * (x + 4) * (x + 5) * (x + 6) := by
  norm_num [blockProduct, Finset.prod_Icc_succ_top, Finset.Icc_self,
    Finset.prod_singleton]

private lemma evenk_blockProduct_eight_prod (x : ℕ) :
    blockProduct 8 x =
      (x + 1) * (x + 2) * (x + 3) * (x + 4) * (x + 5) * (x + 6) * (x + 7) *
        (x + 8) := by
  norm_num [blockProduct, Finset.prod_Icc_succ_top, Finset.Icc_self,
    Finset.prod_singleton]

private lemma evenk_blockProduct_ten_prod (x : ℕ) :
    blockProduct 10 x =
      (x + 1) * (x + 2) * (x + 3) * (x + 4) * (x + 5) * (x + 6) * (x + 7) *
        (x + 8) * (x + 9) * (x + 10) := by
  norm_num [blockProduct, Finset.prod_Icc_succ_top, Finset.Icc_self,
    Finset.prod_singleton]

private lemma evenk_blockProduct_twelve_prod (x : ℕ) :
    blockProduct 12 x =
      (x + 1) * (x + 2) * (x + 3) * (x + 4) * (x + 5) * (x + 6) * (x + 7) *
        (x + 8) * (x + 9) * (x + 10) * (x + 11) * (x + 12) := by
  norm_num [blockProduct, Finset.prod_Icc_succ_top, Finset.Icc_self,
    Finset.prod_singleton]

private lemma evenk_blockProduct_fourteen_prod (x : ℕ) :
    blockProduct 14 x =
      (x + 1) * (x + 2) * (x + 3) * (x + 4) * (x + 5) * (x + 6) * (x + 7) *
        (x + 8) * (x + 9) * (x + 10) * (x + 11) * (x + 12) * (x + 13) *
        (x + 14) := by
  norm_num [blockProduct, Finset.prod_Icc_succ_top, Finset.Icc_self,
    Finset.prod_singleton]

/-! ## Centered bridges `S_k(2x+k+1) = 2^k · blockProduct k x` -/

private lemma evenk_s6_bridge (x : ℕ) :
    ((2 * (x : ℤ) + 7) ^ 2 - 1) * ((2 * (x : ℤ) + 7) ^ 2 - 9) *
        ((2 * (x : ℤ) + 7) ^ 2 - 25) = 64 * (blockProduct 6 x : ℤ) := by
  rw [evenk_blockProduct_six_prod]
  push_cast
  ring

private lemma evenk_s8_bridge (x : ℕ) :
    ((2 * (x : ℤ) + 9) ^ 2 - 1) * ((2 * (x : ℤ) + 9) ^ 2 - 9) *
        ((2 * (x : ℤ) + 9) ^ 2 - 25) * ((2 * (x : ℤ) + 9) ^ 2 - 49) =
      256 * (blockProduct 8 x : ℤ) := by
  rw [evenk_blockProduct_eight_prod]
  push_cast
  ring

private lemma evenk_s10_bridge (x : ℕ) :
    ((2 * (x : ℤ) + 11) ^ 2 - 1) * ((2 * (x : ℤ) + 11) ^ 2 - 9) *
        ((2 * (x : ℤ) + 11) ^ 2 - 25) * ((2 * (x : ℤ) + 11) ^ 2 - 49) *
        ((2 * (x : ℤ) + 11) ^ 2 - 81) = 1024 * (blockProduct 10 x : ℤ) := by
  rw [evenk_blockProduct_ten_prod]
  push_cast
  ring

private lemma evenk_s12_bridge (x : ℕ) :
    ((2 * (x : ℤ) + 13) ^ 2 - 1) * ((2 * (x : ℤ) + 13) ^ 2 - 9) *
        ((2 * (x : ℤ) + 13) ^ 2 - 25) * ((2 * (x : ℤ) + 13) ^ 2 - 49) *
        ((2 * (x : ℤ) + 13) ^ 2 - 81) * ((2 * (x : ℤ) + 13) ^ 2 - 121) =
      4096 * (blockProduct 12 x : ℤ) := by
  rw [evenk_blockProduct_twelve_prod]
  push_cast
  ring

private lemma evenk_s14_bridge (x : ℕ) :
    ((2 * (x : ℤ) + 15) ^ 2 - 1) * ((2 * (x : ℤ) + 15) ^ 2 - 9) *
        ((2 * (x : ℤ) + 15) ^ 2 - 25) * ((2 * (x : ℤ) + 15) ^ 2 - 49) *
        ((2 * (x : ℤ) + 15) ^ 2 - 81) * ((2 * (x : ℤ) + 15) ^ 2 - 121) *
        ((2 * (x : ℤ) + 15) ^ 2 - 169) = 16384 * (blockProduct 14 x : ℤ) := by
  rw [evenk_blockProduct_fourteen_prod]
  push_cast
  ring

/-! ## Fermat divisibilities for the `k = 10` and `k = 14` centers -/

/-- `5 ∣ T₁₀(x) = 8x⁵ - 660x³ + 7887x` for every integer `x`
(`T₁₀ = 8(x⁵ - x) + 5(-132x³ + 1579x)`). -/
private lemma evenk_five_dvd_T10 (x : ℤ) :
    (5 : ℤ) ∣ 8 * x ^ 5 - 660 * x ^ 3 + 7887 * x := by
  have h5 : (5 : ℤ) ∣ x ^ 5 - x := by
    have hx : ((x ^ 5 - x : ℤ) : ZMod 5) = 0 := by
      push_cast
      have hz : ∀ y : ZMod 5, y ^ 5 - y = 0 := by decide
      exact hz (x : ZMod 5)
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mp hx
  obtain ⟨y, hy⟩ := h5
  exact ⟨8 * y - 132 * x ^ 3 + 1579 * x, by linear_combination 8 * hy⟩

/-- `7 ∣ T₁₄(x) = 16x⁷ - 3640x⁵ + 202566x³ - 2656355x` for every integer `x`
(`T₁₄ = 16(x⁷ - x) + 7(-520x⁵ + 28938x³ - 379477x)`). -/
private lemma evenk_seven_dvd_T14 (x : ℤ) :
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

/-! ## The mod-11 kill for `k = 10`

On the curve `S₁₀(x) = 4·S₁₀(y)` over `ZMod 11` the value
`T₁₀(x) - 2T₁₀(y)` never equals `6 = (-5 : ℤ)` or `7 = (-15 : ℤ)`
(indeed `S₁₀ ≡ x¹⁰ - 1` and `T₁₀ ≡ 8x⁵ (mod 11)`, so the equation forces
`x, y ≢ 0` and `T₁₀(x) - 2T₁₀(y) ≡ ±8 ∓ 16 ∈ {2, 3, 8, 9}`). -/
private lemma evenk_k10_mod_eleven :
    ∀ x y : ZMod 11,
      (x ^ 2 - 1) * (x ^ 2 - 9) * (x ^ 2 - 25) * (x ^ 2 - 49) * (x ^ 2 - 81) =
          4 * ((y ^ 2 - 1) * (y ^ 2 - 9) * (y ^ 2 - 25) * (y ^ 2 - 49) *
            (y ^ 2 - 81)) →
      (8 * x ^ 5 - 660 * x ^ 3 + 7887 * x) -
          2 * (8 * y ^ 5 - 660 * y ^ 3 + 7887 * y) ≠ 6 ∧
        (8 * x ^ 5 - 660 * x ^ 3 + 7887 * x) -
          2 * (8 * y ^ 5 - 660 * y ^ 3 + 7887 * y) ≠ 7 := by
  decide

/-! ## Univariate positivity certificates (shifted-coefficient proofs) -/

private lemma evenk_k6_T_pos {W : ℤ} (hW : 1331 ≤ W) :
    0 < 2 * W ^ 3 - 35 * W := by
  obtain ⟨t, ht, rfl⟩ : ∃ t : ℤ, 0 ≤ t ∧ W = 1331 + t :=
    ⟨W - 1331, by omega, by omega⟩
  linarith [ht, pow_nonneg ht 2, pow_nonneg ht 3]

private lemma evenk_k6_lower {v : ℤ} (hv : 1331 ≤ v) :
    756 * v ^ 2 + 3600 < 2 * (2 * v ^ 3 - 35 * v) := by
  obtain ⟨t, ht, rfl⟩ : ∃ t : ℤ, 0 ≤ t ∧ v = 1331 + t :=
    ⟨v - 1331, by omega, by omega⟩
  linarith [ht, pow_nonneg ht 2, pow_nonneg ht 3]

private lemma evenk_k8_P_pos {W : ℤ} (hW : 2217 ≤ W) :
    0 < W ^ 4 - 42 * W ^ 2 + 105 := by
  obtain ⟨t, ht, rfl⟩ : ∃ t : ℤ, 0 ≤ t ∧ W = 2217 + t :=
    ⟨W - 2217, by omega, by omega⟩
  linarith [ht, pow_nonneg ht 2, pow_nonneg ht 3, pow_nonneg ht 4]

private lemma evenk_k8_lower {v : ℤ} (hv : 2217 ≤ v) :
    16384 * v ^ 2 < 2 * (v ^ 4 - 42 * v ^ 2 + 105) := by
  obtain ⟨t, ht, rfl⟩ : ∃ t : ℤ, 0 ≤ t ∧ v = 2217 + t :=
    ⟨v - 2217, by omega, by omega⟩
  linarith [ht, pow_nonneg ht 2, pow_nonneg ht 3, pow_nonneg ht 4]

private lemma evenk_k10_T_pos {W : ℤ} (hW : 2661 ≤ W) :
    0 < 8 * W ^ 5 - 660 * W ^ 3 + 7887 * W := by
  obtain ⟨t, ht, rfl⟩ : ∃ t : ℤ, 0 ≤ t ∧ W = 2661 + t :=
    ⟨W - 2661, by omega, by omega⟩
  linarith [ht, pow_nonneg ht 2, pow_nonneg ht 3, pow_nonneg ht 4,
    pow_nonneg ht 5]

/-- `D₁₀ > 0` for every integer `W`:
`2596000·D₁₀ = (1298000W² - 5457375)² + 118587803709375`. -/
private lemma evenk_k10_D_nonneg (W : ℤ) :
    0 ≤ 649000 * W ^ 4 - 5457375 * W ^ 2 + 57153600 := by
  linarith [sq_nonneg (1298000 * W ^ 2 - 5457375)]

private lemma evenk_k10_upper {v : ℤ} (hv : 2661 ≤ v) :
    649000 * (23 * v + 26) ^ 4 <
      160000 * (2596000 * v ^ 4 - 16372125 * v ^ 2 + 171460800) := by
  obtain ⟨t, ht, rfl⟩ : ∃ t : ℤ, 0 ≤ t ∧ v = 2661 + t :=
    ⟨v - 2661, by omega, by omega⟩
  linarith [ht, pow_nonneg ht 2, pow_nonneg ht 3, pow_nonneg ht 4]

private lemma evenk_k10_lower {v : ℤ} (hv : 2661 ≤ v) :
    0 < 1600000 * (8 * v - 8) ^ 5 - 277315500 * (23 * v + 26) ^ 3 +
        36344000000 * (8 * v - 8) ^ 4 -
        5457375 * 336140 * (23 * v + 26) ^ 2 +
        134456000 * (57153600 + 50 * (8 * v ^ 5 - 660 * v ^ 3 + 7887 * v) -
          4 * (649000 * v ^ 4 - 5457375 * v ^ 2 + 57153600)) := by
  obtain ⟨t, ht, rfl⟩ : ∃ t : ℤ, 0 ≤ t ∧ v = 2661 + t :=
    ⟨v - 2661, by omega, by omega⟩
  linarith [ht, pow_nonneg ht 2, pow_nonneg ht 3, pow_nonneg ht 4,
    pow_nonneg ht 5]

private lemma evenk_k12_P_pos {W : ℤ} (hW : 3547 ≤ W) :
    0 < W ^ 6 - 143 * W ^ 4 + 4147 * W ^ 2 - 24453 := by
  obtain ⟨t, ht, rfl⟩ : ∃ t : ℤ, 0 ≤ t ∧ W = 3547 + t :=
    ⟨W - 3547, by omega, by omega⟩
  linarith [ht, pow_nonneg ht 2, pow_nonneg ht 3, pow_nonneg ht 4,
    pow_nonneg ht 5, pow_nonneg ht 6]

private lemma evenk_k12_D_nonneg {W : ℤ} (hW : 3547 ≤ W) :
    0 ≤ 2223936 * W ^ 4 - 73996416 * W ^ 2 + 489893184 := by
  obtain ⟨t, ht, rfl⟩ : ∃ t : ℤ, 0 ≤ t ∧ W = 3547 + t :=
    ⟨W - 3547, by omega, by omega⟩
  linarith [ht, pow_nonneg ht 2, pow_nonneg ht 3, pow_nonneg ht 4]

private lemma evenk_k12_upper {v : ℤ} (hv : 3547 ≤ v) :
    2223936 * (73 * v + 87) ^ 4 <
      17850625 * (8895744 * v ^ 4 - 221989248 * v ^ 2 + 1469679552) := by
  obtain ⟨t, ht, rfl⟩ : ∃ t : ℤ, 0 ≤ t ∧ v = 3547 + t :=
    ⟨v - 3547, by omega, by omega⟩
  linarith [ht, pow_nonneg ht 2, pow_nonneg ht 3, pow_nonneg ht 4]

private lemma evenk_k12_lower {v : ℤ} (hv : 3547 ≤ v) :
    4 * (2223936 * v ^ 4 - 73996416 * v ^ 2 + 489893184) <
      2 * (v ^ 6 - 143 * v ^ 4 + 4147 * v ^ 2 - 24453) := by
  obtain ⟨t, ht, rfl⟩ : ∃ t : ℤ, 0 ≤ t ∧ v = 3547 + t :=
    ⟨v - 3547, by omega, by omega⟩
  linarith [ht, pow_nonneg ht 2, pow_nonneg ht 3, pow_nonneg ht 4,
    pow_nonneg ht 5, pow_nonneg ht 6]

private lemma evenk_k14_T_pos {W : ℤ} (hW : 11934013 ≤ W) :
    0 < 16 * W ^ 7 - 3640 * W ^ 5 + 202566 * W ^ 3 - 2656355 * W := by
  obtain ⟨t, ht, rfl⟩ : ∃ t : ℤ, 0 ≤ t ∧ W = 11934013 + t :=
    ⟨W - 11934013, by omega, by omega⟩
  linarith [ht, pow_nonneg ht 2, pow_nonneg ht 3, pow_nonneg ht 4,
    pow_nonneg ht 5, pow_nonneg ht 6, pow_nonneg ht 7]

private lemma evenk_k14_D_nonneg {W : ℤ} (hW : 11934013 ≤ W) :
    0 ≤ 1318847348 * W ^ 6 - 92807039780 * W ^ 4 + 1455430979401 * W ^ 2 +
        4674935865600 := by
  obtain ⟨t, ht, rfl⟩ : ∃ t : ℤ, 0 ≤ t ∧ W = 11934013 + t :=
    ⟨W - 11934013, by omega, by omega⟩
  linarith [ht, pow_nonneg ht 2, pow_nonneg ht 3, pow_nonneg ht 4,
    pow_nonneg ht 5, pow_nonneg ht 6]

private lemma evenk_k14_upper {v : ℤ} (hv : 11934013 ≤ v) :
    1318847348 * (21 * v + 24) ^ 6 +
        130321 * 1455430979401 * (21 * v + 24) ^ 2 +
        47045881 * 4674935865600 <
      47045881 * 92807039780 * v ^ 4 +
        188183524 * (1318847348 * v ^ 6 - 92807039780 * v ^ 4 +
          1455430979401 * v ^ 2 + 4674935865600) := by
  obtain ⟨t, ht, rfl⟩ : ∃ t : ℤ, 0 ≤ t ∧ v = 11934013 + t :=
    ⟨v - 11934013, by omega, by omega⟩
  linarith [ht, pow_nonneg ht 2, pow_nonneg ht 3, pow_nonneg ht 4,
    pow_nonneg ht 5, pow_nonneg ht 6]

private lemma evenk_k14_lower {v : ℤ} (hv : 11934013 ≤ v) :
    0 < 7 * (39617584 * (11 * v - 11) ^ 7 - 36400000000 * (21 * v + 24) ^ 5 +
          202566 * 24760990000000 * v ^ 3 -
          2656355 * 10000000 * 130321 * (21 * v + 24)) +
        24760990000000 *
          (14 * (16 * v ^ 7 - 3640 * v ^ 5 + 202566 * v ^ 3 - 2656355 * v) -
            4 * (1318847348 * v ^ 6 - 92807039780 * v ^ 4 +
              1455430979401 * v ^ 2 + 4674935865600)) := by
  obtain ⟨t, ht, rfl⟩ : ∃ t : ℤ, 0 ≤ t ∧ v = 11934013 + t :=
    ⟨v - 11934013, by omega, by omega⟩
  linarith [ht, pow_nonneg ht 2, pow_nonneg ht 3, pow_nonneg ht 4,
    pow_nonneg ht 5, pow_nonneg ht 6, pow_nonneg ht 7]

/-! ## `k = 6` -/

/-- **Erdős 686, `k = 6`, `N = 4`, `d ≥ 221`**: six-blocks in quotient `4`
with gap `d ≥ 221` do not exist. -/
theorem no_gap_solution_four_even_six {n d : ℕ} (hd : 221 ≤ d) :
    blockProduct 6 (n + d) ≠ 4 * blockProduct 6 n := by
  intro heq
  obtain ⟨hup, _hlo⟩ := ratio_window_four_nat heq
  have hnlow : 3 * d ≤ n + 1 := row_base_lower_k6 hd hup
  have hlin :=
    ratio_window_linearize_of_pow_bracket (N := 4) (A := 24) (B := 19)
      (k := 6) (n := n) (d := d) (by norm_num) (by norm_num) hup
  have hZ : ((blockProduct 6 (n + d) : ℕ) : ℤ) =
      4 * ((blockProduct 6 n : ℕ) : ℤ) := by exact_mod_cast heq
  obtain ⟨w, hwdef⟩ : ∃ w : ℤ, w = 2 * ((n : ℤ) + (d : ℤ)) + 7 := ⟨_, rfl⟩
  obtain ⟨v, hvdef⟩ : ∃ v : ℤ, v = 2 * (n : ℤ) + 7 := ⟨_, rfl⟩
  have hv0 : (1331 : ℤ) ≤ v := by omega
  have hw0 : (1331 : ℤ) ≤ w := by omega
  have hlink : 19 * w ≤ 24 * v + 24 := by omega
  have h1 := evenk_s6_bridge (n + d)
  have h2 := evenk_s6_bridge n
  have hcw : 2 * ((n + d : ℕ) : ℤ) + 7 = w := by push_cast; omega
  have hcv : 2 * ((n : ℕ) : ℤ) + 7 = v := by omega
  rw [hcw] at h1
  rw [hcv] at h2
  have hS : (w ^ 2 - 1) * (w ^ 2 - 9) * (w ^ 2 - 25) =
      4 * ((v ^ 2 - 1) * (v ^ 2 - 9) * (v ^ 2 - 25)) := by
    rw [h1, h2, hZ]; ring
  -- the trapped integer m = T(w) - 2T(v)
  obtain ⟨m, hm⟩ : ∃ m : ℤ,
      m = (2 * w ^ 3 - 35 * w) - 2 * (2 * v ^ 3 - 35 * v) := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X : ℤ,
      X = (2 * w ^ 3 - 35 * w) + 2 * (2 * v ^ 3 - 35 * v) := ⟨_, rfl⟩
  have hTw : 0 < 2 * w ^ 3 - 35 * w := evenk_k6_T_pos hw0
  have hTv : 0 < 2 * v ^ 3 - 35 * v := evenk_k6_T_pos hv0
  have hXpos : 0 < X := by rw [hX]; linarith
  have hmX : m * X = (189 * w ^ 2 + 900) - 4 * (189 * v ^ 2 + 900) := by
    rw [hm, hX]; linear_combination 4 * hS
  have hΔneg : (189 * w ^ 2 + 900) - 4 * (189 * v ^ 2 + 900) < 0 := by
    linarith [mul_pos (show (0 : ℤ) < 2 * v - w by omega)
      (show (0 : ℤ) < 2 * v + w by omega)]
  have hΔlo : -X < (189 * w ^ 2 + 900) - 4 * (189 * v ^ 2 + 900) := by
    rw [hX]
    linarith [hTw, evenk_k6_lower hv0, sq_nonneg w]
  have hmneg : m < 0 := by
    by_contra hcon
    have hge := mul_nonneg (not_lt.mp hcon) hXpos.le
    rw [hmX] at hge
    linarith
  have hmgt : -1 < m := by
    by_contra hcon
    have hmul := mul_le_mul_of_nonneg_right (not_lt.mp hcon) hXpos.le
    rw [hmX] at hmul
    linarith
  omega

/-! ## `k = 8` -/

/-- **Erdős 686, `k = 8`, `N = 4`, `d ≥ 221`**: eight-blocks in quotient `4`
with gap `d ≥ 221` do not exist. -/
theorem no_gap_solution_four_even_eight {n d : ℕ} (hd : 221 ≤ d) :
    blockProduct 8 (n + d) ≠ 4 * blockProduct 8 n := by
  intro heq
  obtain ⟨hup, _hlo⟩ := ratio_window_four_nat heq
  have hnlow : 5 * d ≤ n + 1 := row_base_lower_k8 hd hup
  have hlin :=
    ratio_window_linearize_of_pow_bracket (N := 4) (A := 25) (B := 21)
      (k := 8) (n := n) (d := d) (by norm_num) (by norm_num) hup
  have hZ : ((blockProduct 8 (n + d) : ℕ) : ℤ) =
      4 * ((blockProduct 8 n : ℕ) : ℤ) := by exact_mod_cast heq
  obtain ⟨w, hwdef⟩ : ∃ w : ℤ, w = 2 * ((n : ℤ) + (d : ℤ)) + 9 := ⟨_, rfl⟩
  obtain ⟨v, hvdef⟩ : ∃ v : ℤ, v = 2 * (n : ℤ) + 9 := ⟨_, rfl⟩
  have hv0 : (2217 : ℤ) ≤ v := by omega
  have hw0 : (2217 : ℤ) ≤ w := by omega
  have hlink : 21 * w ≤ 25 * v + 27 := by omega
  have h1 := evenk_s8_bridge (n + d)
  have h2 := evenk_s8_bridge n
  have hcw : 2 * ((n + d : ℕ) : ℤ) + 9 = w := by push_cast; omega
  have hcv : 2 * ((n : ℕ) : ℤ) + 9 = v := by omega
  rw [hcw] at h1
  rw [hcv] at h2
  have hS : (w ^ 2 - 1) * (w ^ 2 - 9) * (w ^ 2 - 25) * (w ^ 2 - 49) =
      4 * ((v ^ 2 - 1) * (v ^ 2 - 9) * (v ^ 2 - 25) * (v ^ 2 - 49)) := by
    rw [h1, h2, hZ]; ring
  obtain ⟨m, hm⟩ : ∃ m : ℤ,
      m = (w ^ 4 - 42 * w ^ 2 + 105) - 2 * (v ^ 4 - 42 * v ^ 2 + 105) :=
    ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X : ℤ,
      X = (w ^ 4 - 42 * w ^ 2 + 105) + 2 * (v ^ 4 - 42 * v ^ 2 + 105) :=
    ⟨_, rfl⟩
  have hPw : 0 < w ^ 4 - 42 * w ^ 2 + 105 := evenk_k8_P_pos hw0
  have hPv : 0 < v ^ 4 - 42 * v ^ 2 + 105 := evenk_k8_P_pos hv0
  have hXpos : 0 < X := by rw [hX]; linarith
  have hmX : m * X = 4096 * w ^ 2 - 4 * (4096 * v ^ 2) := by
    rw [hm, hX]; linear_combination hS
  have hΔneg : 4096 * w ^ 2 - 4 * (4096 * v ^ 2) < 0 := by
    linarith [mul_pos (show (0 : ℤ) < 2 * v - w by omega)
      (show (0 : ℤ) < 2 * v + w by omega)]
  have hΔlo : -X < 4096 * w ^ 2 - 4 * (4096 * v ^ 2) := by
    rw [hX]
    linarith [hPw, evenk_k8_lower hv0, sq_nonneg w]
  have hmneg : m < 0 := by
    by_contra hcon
    have hge := mul_nonneg (not_lt.mp hcon) hXpos.le
    rw [hmX] at hge
    linarith
  have hmgt : -1 < m := by
    by_contra hcon
    have hmul := mul_le_mul_of_nonneg_right (not_lt.mp hcon) hXpos.le
    rw [hmX] at hmul
    linarith
  omega

/-! ## `k = 12` -/

/-- **Erdős 686, `k = 12`, `N = 4`, `d ≥ 221`**: twelve-blocks in quotient
`4` with gap `d ≥ 221` do not exist. -/
theorem no_gap_solution_four_even_twelve {n d : ℕ} (hd : 221 ≤ d) :
    blockProduct 12 (n + d) ≠ 4 * blockProduct 12 n := by
  intro heq
  obtain ⟨hup, _hlo⟩ := ratio_window_four_nat heq
  have hnlow : 8 * d ≤ n + 1 := row_base_lower_k12 hd hup
  have hlin :=
    ratio_window_linearize_of_pow_bracket (N := 4) (A := 73) (B := 65)
      (k := 12) (n := n) (d := d) (by norm_num) (by norm_num) hup
  have hZ : ((blockProduct 12 (n + d) : ℕ) : ℤ) =
      4 * ((blockProduct 12 n : ℕ) : ℤ) := by exact_mod_cast heq
  obtain ⟨w, hwdef⟩ : ∃ w : ℤ, w = 2 * ((n : ℤ) + (d : ℤ)) + 13 := ⟨_, rfl⟩
  obtain ⟨v, hvdef⟩ : ∃ v : ℤ, v = 2 * (n : ℤ) + 13 := ⟨_, rfl⟩
  have hv0 : (3547 : ℤ) ≤ v := by omega
  have hw0 : (3547 : ℤ) ≤ w := by omega
  have hlink : 65 * w ≤ 73 * v + 87 := by omega
  have h1 := evenk_s12_bridge (n + d)
  have h2 := evenk_s12_bridge n
  have hcw : 2 * ((n + d : ℕ) : ℤ) + 13 = w := by push_cast; omega
  have hcv : 2 * ((n : ℕ) : ℤ) + 13 = v := by omega
  rw [hcw] at h1
  rw [hcv] at h2
  have hS : (w ^ 2 - 1) * (w ^ 2 - 9) * (w ^ 2 - 25) * (w ^ 2 - 49) *
        (w ^ 2 - 81) * (w ^ 2 - 121) =
      4 * ((v ^ 2 - 1) * (v ^ 2 - 9) * (v ^ 2 - 25) * (v ^ 2 - 49) *
        (v ^ 2 - 81) * (v ^ 2 - 121)) := by
    rw [h1, h2, hZ]; ring
  obtain ⟨m, hm⟩ : ∃ m : ℤ,
      m = (w ^ 6 - 143 * w ^ 4 + 4147 * w ^ 2 - 24453) -
        2 * (v ^ 6 - 143 * v ^ 4 + 4147 * v ^ 2 - 24453) := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X : ℤ,
      X = (w ^ 6 - 143 * w ^ 4 + 4147 * w ^ 2 - 24453) +
        2 * (v ^ 6 - 143 * v ^ 4 + 4147 * v ^ 2 - 24453) := ⟨_, rfl⟩
  have hPw : 0 < w ^ 6 - 143 * w ^ 4 + 4147 * w ^ 2 - 24453 :=
    evenk_k12_P_pos hw0
  have hPv : 0 < v ^ 6 - 143 * v ^ 4 + 4147 * v ^ 2 - 24453 :=
    evenk_k12_P_pos hv0
  have hXpos : 0 < X := by rw [hX]; linarith
  have hmX : m * X =
      (2223936 * w ^ 4 - 73996416 * w ^ 2 + 489893184) -
        4 * (2223936 * v ^ 4 - 73996416 * v ^ 2 + 489893184) := by
    rw [hm, hX]; linear_combination hS
  have h65 : (65 * w) ^ 4 ≤ (73 * v + 87) ^ 4 :=
    pow_le_pow_left₀ (by omega) (by omega) 4
  have hw2 : v ^ 2 ≤ w ^ 2 := pow_le_pow_left₀ (by omega) (by omega) 2
  have hΔneg : (2223936 * w ^ 4 - 73996416 * w ^ 2 + 489893184) -
      4 * (2223936 * v ^ 4 - 73996416 * v ^ 2 + 489893184) < 0 := by
    linarith [h65, hw2, evenk_k12_upper hv0]
  have hΔlo : -X < (2223936 * w ^ 4 - 73996416 * w ^ 2 + 489893184) -
      4 * (2223936 * v ^ 4 - 73996416 * v ^ 2 + 489893184) := by
    rw [hX]
    linarith [hPw, evenk_k12_D_nonneg hw0, evenk_k12_lower hv0]
  have hmneg : m < 0 := by
    by_contra hcon
    have hge := mul_nonneg (not_lt.mp hcon) hXpos.le
    rw [hmX] at hge
    linarith
  have hmgt : -1 < m := by
    by_contra hcon
    have hmul := mul_le_mul_of_nonneg_right (not_lt.mp hcon) hXpos.le
    rw [hmX] at hmul
    linarith
  omega

/-! ## `k = 10` -/

/-- **Erdős 686, `k = 10`, `N = 4`, `d ≥ 221`**: ten-blocks in quotient `4`
with gap `d ≥ 221` do not exist.  The trapped center `m = T₁₀(w) - 2T₁₀(v)`
lies in `(-25, 0)`, is odd, and is divisible by `5`; the two survivors
`m ∈ {-5, -15}` die modulo `11`. -/
theorem no_gap_solution_four_even_ten {n d : ℕ} (hd : 221 ≤ d) :
    blockProduct 10 (n + d) ≠ 4 * blockProduct 10 n := by
  intro heq
  obtain ⟨hup, hlo⟩ := ratio_window_four_nat heq
  have hnlow : 6 * d ≤ n + 1 := row_base_lower_k10 hd hup
  have hlin :=
    ratio_window_linearize_of_pow_bracket (N := 4) (A := 23) (B := 20)
      (k := 10) (n := n) (d := d) (by norm_num) (by norm_num) hup
  have hlin2 :=
    ratio_window_upper_linearize_of_pow_bracket (N := 4) (A := 8) (B := 7)
      (k := 10) (n := n) (d := d) (by norm_num) (by norm_num) hlo
  have hZ : ((blockProduct 10 (n + d) : ℕ) : ℤ) =
      4 * ((blockProduct 10 n : ℕ) : ℤ) := by exact_mod_cast heq
  obtain ⟨w, hwdef⟩ : ∃ w : ℤ, w = 2 * ((n : ℤ) + (d : ℤ)) + 11 := ⟨_, rfl⟩
  obtain ⟨v, hvdef⟩ : ∃ v : ℤ, v = 2 * (n : ℤ) + 11 := ⟨_, rfl⟩
  have hv0 : (2661 : ℤ) ≤ v := by omega
  have hw0 : (2661 : ℤ) ≤ w := by omega
  have hlink : 20 * w ≤ 23 * v + 26 := by omega
  have hlink2 : 8 * v ≤ 7 * w + 8 := by omega
  have h1 := evenk_s10_bridge (n + d)
  have h2 := evenk_s10_bridge n
  have hcw : 2 * ((n + d : ℕ) : ℤ) + 11 = w := by push_cast; omega
  have hcv : 2 * ((n : ℕ) : ℤ) + 11 = v := by omega
  rw [hcw] at h1
  rw [hcv] at h2
  have hS : (w ^ 2 - 1) * (w ^ 2 - 9) * (w ^ 2 - 25) * (w ^ 2 - 49) *
        (w ^ 2 - 81) =
      4 * ((v ^ 2 - 1) * (v ^ 2 - 9) * (v ^ 2 - 25) * (v ^ 2 - 49) *
        (v ^ 2 - 81)) := by
    rw [h1, h2, hZ]; ring
  obtain ⟨m, hm⟩ : ∃ m : ℤ,
      m = (8 * w ^ 5 - 660 * w ^ 3 + 7887 * w) -
        2 * (8 * v ^ 5 - 660 * v ^ 3 + 7887 * v) := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X : ℤ,
      X = (8 * w ^ 5 - 660 * w ^ 3 + 7887 * w) +
        2 * (8 * v ^ 5 - 660 * v ^ 3 + 7887 * v) := ⟨_, rfl⟩
  have hTw : 0 < 8 * w ^ 5 - 660 * w ^ 3 + 7887 * w := evenk_k10_T_pos hw0
  have hTv : 0 < 8 * v ^ 5 - 660 * v ^ 3 + 7887 * v := evenk_k10_T_pos hv0
  have hXpos : 0 < X := by rw [hX]; linarith
  have hmX : m * X =
      (649000 * w ^ 4 - 5457375 * w ^ 2 + 57153600) -
        4 * (649000 * v ^ 4 - 5457375 * v ^ 2 + 57153600) := by
    rw [hm, hX]; linear_combination 64 * hS
  have h20w4 : (20 * w) ^ 4 ≤ (23 * v + 26) ^ 4 :=
    pow_le_pow_left₀ (by omega) (by omega) 4
  have hw2 : v ^ 2 ≤ w ^ 2 := pow_le_pow_left₀ (by omega) (by omega) 2
  have hΔneg : (649000 * w ^ 4 - 5457375 * w ^ 2 + 57153600) -
      4 * (649000 * v ^ 4 - 5457375 * v ^ 2 + 57153600) < 0 := by
    linarith [h20w4, hw2, evenk_k10_upper hv0]
  have h7w5 : (8 * v - 8) ^ 5 ≤ (7 * w) ^ 5 :=
    pow_le_pow_left₀ (by omega) (by omega) 5
  have h7w4 : (8 * v - 8) ^ 4 ≤ (7 * w) ^ 4 :=
    pow_le_pow_left₀ (by omega) (by omega) 4
  have h20w3 : (20 * w) ^ 3 ≤ (23 * v + 26) ^ 3 :=
    pow_le_pow_left₀ (by omega) (by omega) 3
  have h20w2 : (20 * w) ^ 2 ≤ (23 * v + 26) ^ 2 :=
    pow_le_pow_left₀ (by omega) (by omega) 2
  have hΔlo : -25 * X < (649000 * w ^ 4 - 5457375 * w ^ 2 + 57153600) -
      4 * (649000 * v ^ 4 - 5457375 * v ^ 2 + 57153600) := by
    rw [hX]
    linarith [h7w5, h7w4, h20w3, h20w2, evenk_k10_lower hv0,
      show (0 : ℤ) ≤ w by omega]
  have hmneg : m < 0 := by
    by_contra hcon
    have hge := mul_nonneg (not_lt.mp hcon) hXpos.le
    rw [hmX] at hge
    linarith
  have hmgt : -25 < m := by
    by_contra hcon
    have hmul := mul_le_mul_of_nonneg_right (not_lt.mp hcon) hXpos.le
    rw [hmX] at hmul
    linarith
  -- parity: m = 2c + w with w odd, and 5 ∣ m
  obtain ⟨cpar, hcpar⟩ : ∃ c : ℤ, m = 2 * c + w :=
    ⟨4 * w ^ 5 - 330 * w ^ 3 + 3943 * w -
      (8 * v ^ 5 - 660 * v ^ 3 + 7887 * v), by rw [hm]; ring⟩
  have h5m : (5 : ℤ) ∣ m := by
    rw [hm]
    exact dvd_sub (evenk_five_dvd_T10 w) ((evenk_five_dvd_T10 v).mul_left 2)
  have hmcase : m = -5 ∨ m = -15 := by omega
  -- the mod-11 kill
  have hS11 : ((w : ZMod 11) ^ 2 - 1) * ((w : ZMod 11) ^ 2 - 9) *
      ((w : ZMod 11) ^ 2 - 25) * ((w : ZMod 11) ^ 2 - 49) *
      ((w : ZMod 11) ^ 2 - 81) =
      4 * (((v : ZMod 11) ^ 2 - 1) * ((v : ZMod 11) ^ 2 - 9) *
        ((v : ZMod 11) ^ 2 - 25) * ((v : ZMod 11) ^ 2 - 49) *
        ((v : ZMod 11) ^ 2 - 81)) := by
    have h := congrArg (fun z : ℤ => (z : ZMod 11)) hS
    push_cast at h
    exact h
  have hm11 : ((m : ZMod 11)) =
      (8 * (w : ZMod 11) ^ 5 - 660 * (w : ZMod 11) ^ 3 +
          7887 * (w : ZMod 11)) -
        2 * (8 * (v : ZMod 11) ^ 5 - 660 * (v : ZMod 11) ^ 3 +
          7887 * (v : ZMod 11)) := by
    have h := congrArg (fun z : ℤ => (z : ZMod 11)) hm
    push_cast at h
    exact h
  have hK := evenk_k10_mod_eleven (w : ZMod 11) (v : ZMod 11) hS11
  rcases hmcase with rfl | rfl
  · exact hK.1 (by rw [← hm11]; decide)
  · exact hK.2 (by rw [← hm11]; decide)

/-! ## `k = 14` (large-gap branch) -/

/-- **Erdős 686, `k = 14`, `N = 4`, large gap**: fourteen-blocks in quotient
`4` with gap `d ≥ 663000` do not exist.  Here the trapped center
`m = T₁₄(w) - 2T₁₄(v)` lies in `(-7, 0)` and is divisible by `7` — empty.
The deficit `D₁₄ = 1318847348·W⁶ - …` is too large relative to
`T₁₄ ≈ 16W⁷` to reach gaps below `663000` by this route (the `(-B, 0)`
window at `v ≈ 4000` has width `≈ 11300`). -/
theorem no_gap_solution_four_even_fourteen_of_large_gap {n d : ℕ}
    (hd : 663000 ≤ d) :
    blockProduct 14 (n + d) ≠ 4 * blockProduct 14 n := by
  intro heq
  obtain ⟨hup, hlo⟩ := ratio_window_four_nat heq
  have hnlow : 9 * d ≤ n + 1 := row_base_lower_k14 (by omega) hup
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
  have hv0 : (11934013 : ℤ) ≤ v := by omega
  have hw0 : (11934013 : ℤ) ≤ w := by omega
  have hlink : 19 * w ≤ 21 * v + 24 := by omega
  have hlink2 : 11 * v ≤ 10 * w + 11 := by omega
  have h1 := evenk_s14_bridge (n + d)
  have h2 := evenk_s14_bridge n
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
    evenk_k14_T_pos hw0
  have hTv : 0 < 16 * v ^ 7 - 3640 * v ^ 5 + 202566 * v ^ 3 - 2656355 * v :=
    evenk_k14_T_pos hv0
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
    linarith [h19w6, hw4, h19w2, evenk_k14_upper hv0]
  have h10w7 : (11 * v - 11) ^ 7 ≤ (10 * w) ^ 7 :=
    pow_le_pow_left₀ (by omega) (by omega) 7
  have h19w5 : (19 * w) ^ 5 ≤ (21 * v + 24) ^ 5 :=
    pow_le_pow_left₀ (by omega) (by omega) 5
  have hw3 : v ^ 3 ≤ w ^ 3 := pow_le_pow_left₀ (by omega) (by omega) 3
  have hΔlo : -7 * X < (1318847348 * w ^ 6 - 92807039780 * w ^ 4 +
      1455430979401 * w ^ 2 + 4674935865600) -
      4 * (1318847348 * v ^ 6 - 92807039780 * v ^ 4 + 1455430979401 * v ^ 2 +
        4674935865600) := by
    rw [hX]
    linarith [h10w7, h19w5, hw3, hlink, evenk_k14_D_nonneg hw0,
      evenk_k14_lower hv0]
  have hmneg : m < 0 := by
    by_contra hcon
    have hge := mul_nonneg (not_lt.mp hcon) hXpos.le
    rw [hmX] at hge
    linarith
  have hmgt : -7 < m := by
    by_contra hcon
    have hmul := mul_le_mul_of_nonneg_right (not_lt.mp hcon) hXpos.le
    rw [hmX] at hmul
    linarith
  have h7m : (7 : ℤ) ∣ m := by
    rw [hm]
    exact dvd_sub (evenk_seven_dvd_T14 w) ((evenk_seven_dvd_T14 v).mul_left 2)
  omega

end Erdos686Variant

end Erdos686
