/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.Core.ConvergentMachinery

/-!
# Erdős 686, k = 5: centered-Thue/convergent certificate

Instance of the Farey/Stern–Brocot descent machinery
(`Erdos686ConvergentMachinery`) for `k = 5`, `N = 4`, closing the gap
equation `(n+d+1)⋯(n+d+5) = 4·(n+1)⋯(n+5)` for all `221 ≤ d < 10^120`
(headline statement at `10^60`, matching the campaign tail interface).
Mathematics: `compute/theory/k5_third_row_note.md` §6 and
`compute/theory/odd_k_thue_synthesis.md`; certificate generated and
pre-verified by `compute/erdos686_thue_gen_lean.py` (cross-checked against
`compute/artifacts/thue_convergents_k5.json`).

The chain, entirely in integer arithmetic:

1. **Centering** (`k5_centered_of_eq`): with `X = n+d+3`, `Y = n+3` the
   equation is exactly `X⁵ − 5X³ + 4X = 4(Y⁵ − 5Y³ + 4Y)`, stated
   ℕ-safely as `X⁵ + 4X + 20Y³ = 4Y⁵ + 16Y + 5X³` (`K5CenteredEq`).
2. **Ratio bracket** (`k5_bracket_lower/upper`): for `Y ≥ 665`,
   `131·Y < 100·X < 132·Y`, via the monotone scaled polynomial
   `Q(u) = u⁵ − 5·10⁴·u³ + 4·10⁸·u` (`Q(100T) = 10¹⁰·P₅(T)`) and the
   quintic bracket certificates `131⁵ < 4·10¹⁰ < 132⁵`.
3. **Thue window** (`k5_thue_window`): `5·|X⁵ − 4Y⁵| ≤ 44·Y³`
   (constant `8.8`, true value `≈ 8.51`, bracket-sup `≈ 8.76`).
4. **Handoff from the banked window**: `ratio_window_four_nat` +
   `row_base_lower_k5`/`row_base_upper_k5` give `3d ≤ n+1 < 4d` for
   `d ≥ 221`, hence `665 ≤ Y ≤ 4·10^120` for `221 ≤ d < 10^120`.
5. **Descent certificate** (`k5FareyCert`, `k5FareyCert_check`): a
   3181-node Farey tree rooted at `1/1 < 4^(1/5) < 4/3`; one kernel
   `decide` checks every side certificate, mediant multiple bound, and
   the 285 exact candidate refutations (`Y` up to `4·10^120`,
   ~2000-bit integers).  No `native_decide`.
-/

namespace Erdos686

namespace Erdos686Variant

/--
The exact centered equation for `k = 5`, `N = 4` in ℕ-safe form:
`X⁵ + 4X + 20Y³ = 4Y⁵ + 16Y + 5X³` ⟺ `P₅(X) = 4·P₅(Y)` with
`P₅(T) = T⁵ − 5T³ + 4T`, at `X = n+d+3`, `Y = n+3`.
-/
def K5CenteredEq (X Y : ℕ) : Prop :=
  X ^ 5 + 4 * X + 20 * Y ^ 3 = 4 * Y ^ 5 + 16 * Y + 5 * X ^ 3

/-- Boolean refuter for the exact centered equation (kernel-decidable). -/
def k5EqRefuted (X Y : ℕ) : Bool :=
  decide (X ^ 5 + 4 * X + 20 * Y ^ 3 ≠ 4 * Y ^ 5 + 16 * Y + 5 * X ^ 3)

lemma k5EqRefuted_sound (X Y : ℕ) (h : k5EqRefuted X Y = true) :
    ¬ K5CenteredEq X Y := by
  intro hc
  have h' : X ^ 5 + 4 * X + 20 * Y ^ 3 ≠ 4 * Y ^ 5 + 16 * Y + 5 * X ^ 3 :=
    of_decide_eq_true h
  exact h' hc

/-! ## Centering -/

private lemma blockProduct_five_prod (x : ℕ) :
    blockProduct 5 x = (x + 1) * (x + 2) * (x + 3) * (x + 4) * (x + 5) := by
  norm_num [blockProduct, Finset.prod_Icc_succ_top, Finset.Icc_self,
    Finset.prod_singleton]

/-- The centered identity `∏_{i=1}^{5}(m+i) = P₅(m+3)` in additive ℕ form. -/
private lemma blockProduct_five_centered (m : ℕ) :
    blockProduct 5 m + 5 * (m + 3) ^ 3 = (m + 3) ^ 5 + 4 * (m + 3) := by
  rw [blockProduct_five_prod]; ring

/-- A gap solution satisfies the exact centered equation. -/
lemma k5_centered_of_eq {n d : ℕ}
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n) :
    K5CenteredEq (n + d + 3) (n + 3) := by
  have h1 := blockProduct_five_centered (n + d)
  have h2 := blockProduct_five_centered n
  unfold K5CenteredEq
  linarith

/-! ## Ratio bracket `131/100 < X/Y < 132/100` from the equation

`Q(u) = u⁵ − 50000·u³ + 4·10⁸·u` satisfies `Q(100T) = 10¹⁰·P₅(T)` and is
monotone for `u ≥ 400`; comparing `Q(100X) = 10¹⁰·4·P₅(Y)` against
`Q(131Y)` resp. `Q(132Y)` yields the bracket, since
`131⁵ = 38579489651 < 4·10¹⁰ < 40074642432 = 132⁵`. -/

private lemma q5_mono {u v : ℤ} (hu : 400 ≤ u) (huv : u ≤ v) :
    u ^ 5 - 50000 * u ^ 3 + 400000000 * u ≤
      v ^ 5 - 50000 * v ^ 3 + 400000000 * v := by
  have hu0 : (0 : ℤ) ≤ u := by linarith
  have hv0 : (0 : ℤ) ≤ v := by linarith
  have hu2 : (50000 : ℤ) ≤ u ^ 2 := by nlinarith
  have hv2 : (50000 : ℤ) ≤ v ^ 2 := by nlinarith
  have hvu : (0 : ℤ) ≤ v - u := by linarith
  have t1 : (0 : ℤ) ≤ (v - u) * (v ^ 2 * (v ^ 2 - 50000)) :=
    mul_nonneg hvu (mul_nonneg (sq_nonneg v) (by linarith))
  have t2 : (0 : ℤ) ≤ (v - u) * (v * u * (v ^ 2 - 50000)) :=
    mul_nonneg hvu (mul_nonneg (mul_nonneg hv0 hu0) (by linarith))
  have t3 : (0 : ℤ) ≤ (v - u) * (u ^ 2 * (u ^ 2 - 50000)) :=
    mul_nonneg hvu (mul_nonneg (sq_nonneg u) (by linarith))
  have t4 : (0 : ℤ) ≤ (v - u) * (v ^ 2 * u ^ 2 + v * u ^ 3 + 400000000) := by
    refine mul_nonneg hvu ?_
    have h1 : (0 : ℤ) ≤ v ^ 2 * u ^ 2 := mul_nonneg (sq_nonneg v) (sq_nonneg u)
    have h2 : (0 : ℤ) ≤ v * u ^ 3 := mul_nonneg hv0 (pow_nonneg hu0 3)
    linarith
  have key : v ^ 5 - 50000 * v ^ 3 + 400000000 * v -
      (u ^ 5 - 50000 * u ^ 3 + 400000000 * u) =
      (v - u) * (v ^ 2 * (v ^ 2 - 50000)) +
        (v - u) * (v * u * (v ^ 2 - 50000)) +
        (v - u) * (u ^ 2 * (u ^ 2 - 50000)) +
        (v - u) * (v ^ 2 * u ^ 2 + v * u ^ 3 + 400000000) := by ring
  linarith

/-- A solution with `Y ≥ 665` has `X > Y` (else `3Y⁵ ≤ 20Y³`). -/
private lemma k5_Y_lt_X {X Y : ℕ} (hsol : K5CenteredEq X Y) (hY : 665 ≤ Y) :
    Y < X := by
  by_contra hnot
  have hXY : X ≤ Y := Nat.le_of_not_lt hnot
  have h5 : X ^ 5 ≤ Y ^ 5 := Nat.pow_le_pow_left hXY 5
  unfold K5CenteredEq at hsol
  have hkey : 3 * Y ^ 5 + 12 * Y ≤ 20 * Y ^ 3 := by
    linarith [Nat.zero_le (5 * X ^ 3), h5, hXY]
  have hY2 : 442225 ≤ Y ^ 2 := by nlinarith
  have hcube : 442225 * Y ^ 3 ≤ Y ^ 2 * Y ^ 3 :=
    Nat.mul_le_mul hY2 (le_refl (Y ^ 3))
  have hpow : Y ^ 2 * Y ^ 3 = Y ^ 5 := by ring
  have hY3 : 0 < Y ^ 3 := pow_pos (by omega) 3
  rw [hpow] at hcube
  linarith

/-- Lower ratio bracket: `131·Y < 100·X` for any solution with `Y ≥ 665`. -/
lemma k5_bracket_lower {X Y : ℕ} (hsol : K5CenteredEq X Y) (hY : 665 ≤ Y) :
    131 * Y < 100 * X := by
  have hYX := k5_Y_lt_X hsol hY
  by_contra hnot
  have hle : 100 * X ≤ 131 * Y := by omega
  have hz : (X : ℤ) ^ 5 + 4 * X + 20 * (Y : ℤ) ^ 3 =
      4 * (Y : ℤ) ^ 5 + 16 * Y + 5 * (X : ℤ) ^ 3 := by exact_mod_cast hsol
  have hYz : (665 : ℤ) ≤ (Y : ℤ) := by exact_mod_cast hY
  have hXz : (Y : ℤ) < (X : ℤ) := by exact_mod_cast hYX
  have hu : (400 : ℤ) ≤ 100 * (X : ℤ) := by linarith
  have huv : 100 * (X : ℤ) ≤ 131 * (Y : ℤ) := by exact_mod_cast hle
  have hmono := q5_mono hu huv
  have hP : (X : ℤ) ^ 5 - 5 * (X : ℤ) ^ 3 + 4 * (X : ℤ) =
      4 * (Y : ℤ) ^ 5 - 20 * (Y : ℤ) ^ 3 + 16 * (Y : ℤ) := by linarith
  have hexp : (100 * (X : ℤ)) ^ 5 - 50000 * (100 * (X : ℤ)) ^ 3 +
      400000000 * (100 * (X : ℤ)) =
      10000000000 * (4 * (Y : ℤ) ^ 5 - 20 * (Y : ℤ) ^ 3 + 16 * (Y : ℤ)) := by
    linear_combination (10000000000 : ℤ) * hP
  have hY3 : (0 : ℤ) < (Y : ℤ) ^ 3 := pow_pos (by linarith) 3
  have hY2 : (442225 : ℤ) ≤ (Y : ℤ) ^ 2 := by nlinarith
  have hprod : 1420510349 * (442225 * (Y : ℤ) ^ 3) ≤
      1420510349 * ((Y : ℤ) ^ 2 * (Y : ℤ) ^ 3) := by
    have := mul_le_mul_of_nonneg_right hY2 (le_of_lt hY3)
    linarith
  nlinarith [hmono, hexp, hprod, hY3]

/-- Upper ratio bracket: `100·X < 132·Y` for any solution with `Y ≥ 665`. -/
lemma k5_bracket_upper {X Y : ℕ} (hsol : K5CenteredEq X Y) (hY : 665 ≤ Y) :
    100 * X < 132 * Y := by
  by_contra hnot
  have hle : 132 * Y ≤ 100 * X := by omega
  have hz : (X : ℤ) ^ 5 + 4 * X + 20 * (Y : ℤ) ^ 3 =
      4 * (Y : ℤ) ^ 5 + 16 * Y + 5 * (X : ℤ) ^ 3 := by exact_mod_cast hsol
  have hYz : (665 : ℤ) ≤ (Y : ℤ) := by exact_mod_cast hY
  have hu : (400 : ℤ) ≤ 132 * (Y : ℤ) := by linarith
  have huv : 132 * (Y : ℤ) ≤ 100 * (X : ℤ) := by exact_mod_cast hle
  have hmono := q5_mono hu huv
  have hP : (X : ℤ) ^ 5 - 5 * (X : ℤ) ^ 3 + 4 * (X : ℤ) =
      4 * (Y : ℤ) ^ 5 - 20 * (Y : ℤ) ^ 3 + 16 * (Y : ℤ) := by linarith
  have hexp : (100 * (X : ℤ)) ^ 5 - 50000 * (100 * (X : ℤ)) ^ 3 +
      400000000 * (100 * (X : ℤ)) =
      10000000000 * (4 * (Y : ℤ) ^ 5 - 20 * (Y : ℤ) ^ 3 + 16 * (Y : ℤ)) := by
    linear_combination (10000000000 : ℤ) * hP
  have hY1 : (0 : ℤ) < (Y : ℤ) := by linarith
  have hY2 : (442225 : ℤ) ≤ (Y : ℤ) ^ 2 := by nlinarith
  have hprod : 85001600000 * (442225 * (Y : ℤ)) ≤
      85001600000 * ((Y : ℤ) ^ 2 * (Y : ℤ)) := by
    have := mul_le_mul_of_nonneg_right hY2 (le_of_lt hY1)
    linarith
  nlinarith [hmono, hexp, hprod, hY1]

/-! ## The Thue window `5·|X⁵ − 4Y⁵| ≤ 44·Y³` -/

/--
Two-sided Thue window in the exact shape consumed by `fareyCheck_sound`
(`N = 4`, `cnum = 44`, `cden = 5`, `e = 3`): for any solution with
`Y ≥ 665`, `5·(4Y⁵) ≤ 5X⁵ + 44Y³` and `5X⁵ ≤ 5·(4Y⁵) + 44Y³`.
-/
lemma k5_thue_window {X Y : ℕ} (hsol : K5CenteredEq X Y) (hY : 665 ≤ Y) :
    5 * (4 * Y ^ 5) ≤ 5 * X ^ 5 + 44 * Y ^ 3 ∧
      5 * X ^ 5 ≤ 5 * (4 * Y ^ 5) + 44 * Y ^ 3 := by
  have hbl := k5_bracket_lower hsol hY
  have hbu := k5_bracket_upper hsol hY
  have hz : (X : ℤ) ^ 5 + 4 * X + 20 * (Y : ℤ) ^ 3 =
      4 * (Y : ℤ) ^ 5 + 16 * Y + 5 * (X : ℤ) ^ 3 := by exact_mod_cast hsol
  have hblz : 131 * (Y : ℤ) < 100 * (X : ℤ) := by exact_mod_cast hbl
  have hbuz : 100 * (X : ℤ) < 132 * (Y : ℤ) := by exact_mod_cast hbu
  have hYz : (665 : ℤ) ≤ (Y : ℤ) := by exact_mod_cast hY
  have hX0 : (0 : ℤ) ≤ (X : ℤ) := Int.natCast_nonneg X
  have hY0 : (0 : ℤ) ≤ (Y : ℤ) := by linarith
  have hc_lo : (131 * (Y : ℤ)) ^ 3 ≤ (100 * (X : ℤ)) ^ 3 :=
    pow_le_pow_left₀ (by linarith) (le_of_lt hblz) 3
  have hc_hi : (100 * (X : ℤ)) ^ 3 ≤ (132 * (Y : ℤ)) ^ 3 :=
    pow_le_pow_left₀ (by linarith) (le_of_lt hbuz) 3
  have hc_lo' : 2248091 * (Y : ℤ) ^ 3 ≤ 1000000 * (X : ℤ) ^ 3 := by
    nlinarith [hc_lo]
  have hc_hi' : 1000000 * (X : ℤ) ^ 3 ≤ 2299968 * (Y : ℤ) ^ 3 := by
    nlinarith [hc_hi]
  have hY3Y : (Y : ℤ) ≤ (Y : ℤ) ^ 3 := by
    have hf : (0 : ℤ) ≤ (Y : ℤ) * ((Y : ℤ) - 1) * ((Y : ℤ) + 1) :=
      mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
    have hexp : (Y : ℤ) * ((Y : ℤ) - 1) * ((Y : ℤ) + 1) =
        (Y : ℤ) ^ 3 - (Y : ℤ) := by ring
    linarith
  have hY3 : (0 : ℤ) ≤ (Y : ℤ) ^ 3 := by positivity
  constructor
  · have hgoal : 5 * (4 * (Y : ℤ) ^ 5) ≤ 5 * (X : ℤ) ^ 5 + 44 * (Y : ℤ) ^ 3 := by
      linarith
    exact_mod_cast hgoal
  · have hgoal : 5 * (X : ℤ) ^ 5 ≤ 5 * (4 * (Y : ℤ) ^ 5) + 44 * (Y : ℤ) ^ 3 := by
      linarith
    exact_mod_cast hgoal

/-! ## The descent certificate

Generated by `compute/erdos686_thue_gen_lean.py 120` (deterministic,
byte-stable); root Farey pair `1/1 < 4^(1/5) < 4/3`, `Ylo = 665`,
`Ymax = 4·10^120`.  3181 nodes: 1590 mediant splits, 1589 side-certificate
kills, 2 `Ymax`-exits; 285 candidate pairs refuted by the exact equation.
Every convergent of `cf(4^(1/5))` with denominator `≤ 4·10^120` (244 of the
341 rows of `compute/artifacts/thue_convergents_k5.json`) occurs among the
mediants; determinants, straddle signs, and sign alternation are re-verified
by the generator before emission. -/

/- AUTOGENERATED by compute/erdos686_thue_gen_lean.py (YMAX_EXP=120).
   Farey/Stern-Brocot descent certificate for k = 5, N = 4:
   root pair 1/1 < 4^(1/5) < 4/3, Thue window 5*|X^5-4Y^5| <= 44*Y^3,
   Ylo = 665, Ymax = 4 * 10^120.  Do not edit by hand. -/

-- generated single-line tree literals (repo precedent: Erdos154.lean)
set_option linter.style.longLine false

private def k5FareyCertC0 : FareyTree :=
  (.node 1 .kill (.node 0 (.node 2 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 0 (.node 0 (.node 0 (.node 0 (.node 2 (.node 0 .kill (.node 0 .kill .kill)) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 0 .kill (.node 0 .kill (.node 2 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 1 (.node 1 .kill (.node 0 (.node 2 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 (.node 0 .kill (.node 1 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 (.node 0 .kill (.node 1 (.node 0 .kill .kill) (.node 0 (.node 0 (.node 0 (.node 1 (.node 0 .kill (.node 0 .kill (.node 4 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 2 (.node 0 .kill .kill) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 2 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 (.node 0 .kill (.node 0 .kill (.node 6 .high .high))) (.node 0 .kill .kill)))))))))) (.node 0 .kill .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)))))))))))))))))))))))))))))))) (.node 0 (.node 0 (.node 0 .kill .kill) .kill) .kill)))) .kill) .kill) .kill) .kill))) (.node 0 .kill .kill))))))) (.node 0 .kill .kill))) (.node 0 .kill .kill)))))))) (.node 0 .kill .kill)) .kill)) (.node 0 .kill .kill))))))))))) (.node 0 (.node 0 .kill .kill) .kill)))) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)) .kill) .kill) .kill) .kill)))))))) (.node 0 .kill .kill)) .kill))

private def k5FareyCertC1 : FareyTree :=
  (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 3 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 (.node 0 .kill (.node 3 (.node 0 .kill (.node 0 .kill .kill)) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 0 .kill .kill) (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 0 .kill (.node 0 .kill (.node 2 (.node 0 .kill .kill) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 2 (.node 0 .kill (.node 0 .kill .kill)) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 2 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 0 (.node 0 (.node 1 (.node 0 .kill (.node 0 .kill (.node 2 (.node 0 .kill .kill) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 0 .kill (.node 1 .kill (.node 1 (.node 1 .kill (.node 1 (.node 1 .kill (.node 1 k5FareyCertC0 .kill)) .kill)) .kill))) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)))) .kill) .kill) .kill))))))))))))) (.node 0 .kill .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill)))) .kill) .kill) .kill) .kill) .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill))) (.node 0 .kill .kill))))))))))))))))))))))))) (.node 0 (.node 0 (.node 0 .kill .kill) .kill) .kill))))))

private def k5FareyCertC2 : FareyTree :=
  (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 0 (.node 0 (.node 0 (.node 0 (.node 2 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 0 (.node 1 (.node 0 .kill (.node 1 .kill (.node 0 (.node 1 (.node 1 .kill (.node 2 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 2 (.node 0 .kill .kill) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 2 (.node 0 .kill (.node 0 .kill .kill)) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 0 .kill (.node 0 .kill (.node 1 (.node 0 .kill .kill) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 1 .kill (.node 2 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 (.node 0 .kill (.node 3 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill k5FareyCertC1))))))))))) (.node 0 (.node 0 .kill .kill) .kill))) (.node 0 .kill .kill)))))))))))) (.node 0 (.node 0 .kill .kill) .kill))) .kill) .kill) .kill) .kill) .kill) .kill)))) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill))))) (.node 0 .kill .kill))))))))) (.node 0 .kill .kill))) .kill) .kill))) .kill) .kill)))) (.node 0 .kill .kill)))))))))))))))) (.node 0 (.node 0 .kill .kill) .kill)) .kill) .kill) .kill) .kill)))))))))))))))))))))

private def k5FareyCertC3 : FareyTree :=
  (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 0 (.node 0 (.node 1 (.node 1 .kill (.node 1 (.node 1 (.node 0 .kill .kill) (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 1 (.node 3 (.node 0 .kill (.node 0 .kill .kill)) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 0 .kill .kill) (.node 1 (.node 1 .kill (.node 1 (.node 0 .kill (.node 0 .kill (.node 1 (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 0 (.node 0 (.node 1 (.node 0 .kill .kill) (.node 0 (.node 0 (.node 0 (.node 1 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 2 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 0 (.node 1 (.node 0 .kill (.node 1 .kill (.node 0 (.node 0 (.node 3 (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill))) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 3 (.node 0 .kill (.node 0 .kill k5FareyCertC2)) (.node 0 (.node 0 .kill .kill) .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)) .kill) .kill))) .kill) .kill))))))) (.node 0 .kill .kill)))))) .kill) .kill) .kill) .kill)) .kill) .kill)))) (.node 0 .kill .kill)))) (.node 0 .kill .kill))) .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)) .kill))))) .kill) .kill) .kill) .kill) .kill)) .kill)) .kill) .kill) .kill)))))))))))))))))))))))))))

private def k5FareyCertC4 : FareyTree :=
  (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 1 (.node 0 .kill (.node 1 .kill (.node 0 (.node 0 (.node 1 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 1 (.node 3 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 (.node 0 .kill (.node 0 .kill (.node 6 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill k5FareyCertC3)))))))))))))))))))))))))))))))))))))))))))))))))) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 .kill .kill) .kill) .kill) .kill) .kill) .kill)))) (.node 0 .kill .kill)))))))))))))))))))))))))) (.node 0 (.node 0 (.node 0 .kill .kill) .kill) .kill)) .kill))))))) (.node 0 .kill .kill)) .kill) .kill))) (.node 0 .kill .kill))))) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)

private def k5FareyCertC5 : FareyTree :=
  (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 0 (.node 0 (.node 1 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 1 (.node 1 (.node 0 .kill .kill) (.node 0 (.node 0 (.node 0 (.node 0 (.node 2 (.node 0 .kill (.node 0 .kill .kill)) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 0 .kill .kill) (.node 0 (.node 0 (.node 1 (.node 0 .kill .kill) (.node 0 (.node 0 (.node 0 (.node 1 (.node 0 .kill (.node 0 .kill (.node 3 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 (.node 1 .kill (.node 1 (.node 0 .kill (.node 1 .kill (.node 1 (.node 1 .kill (.node 1 (.node 0 .kill (.node 5 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill))))) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 k5FareyCertC4 .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill))) .kill)) .kill))) (.node 0 .kill .kill))) (.node 0 .kill .kill))))))))))))))))) (.node 0 (.node 0 .kill .kill) .kill)))) .kill) .kill) .kill) .kill)) .kill) .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill)) .kill) .kill) .kill) .kill)) .kill)))))) (.node 0 .kill .kill)) .kill) .kill))))))))))))))))))))))))))))))))

private def k5FareyCertC6 : FareyTree :=
  (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 (.node 1 .kill (.node 1 (.node 1 (.node 0 .kill .kill) (.node 0 (.node 0 (.node 0 (.node 2 (.node 0 .kill (.node 0 .kill .kill)) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 2 (.node 0 .kill (.node 0 .kill .kill)) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 3 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 (.node 0 .kill (.node 0 .kill (.node 5 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill k5FareyCertC5))))))))))))))))))))))) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 .kill .kill) .kill) .kill) .kill) .kill)))) (.node 0 .kill .kill)))))))))))))))))))))) (.node 0 (.node 0 .kill .kill) .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)) .kill) .kill) .kill)) .kill)) (.node 0 .kill .kill))))))))))))))))))))))))))))))))))))))))))))))

private def k5FareyCertC7 : FareyTree :=
  (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 (.node 0 .kill (.node 1 (.node 0 .kill .kill) (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 0 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 0 (.node 1 (.node 1 .kill (.node 1 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 2 (.node 0 .kill .kill) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 3 (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill))) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 1 (.node 0 .kill (.node 2 (.node 0 .kill .kill) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 5 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill k5FareyCertC6))))) (.node 0 (.node 0 (.node 0 (.node 0 .kill .kill) .kill) .kill) .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill))) .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill))))) (.node 0 .kill .kill))) .kill) .kill)) .kill) .kill))))) .kill) .kill) .kill) .kill) .kill))) (.node 0 .kill .kill))))))))))))))))))))))))))))))))))))))))))))))))))

private def k5FareyCertC8 : FareyTree :=
  (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 (.node 0 .kill (.node 1 (.node 0 .kill .kill) (.node 0 (.node 0 (.node 0 (.node 0 (.node 6 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill))))) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 2 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 1 (.node 1 (.node 0 .kill .kill) (.node 0 (.node 1 (.node 1 .kill (.node 6 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill k5FareyCertC7))))))))))))))) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 .kill .kill) .kill) .kill) .kill) .kill))) .kill) .kill)) .kill)) .kill) .kill) .kill) .kill) .kill))))))))) (.node 0 .kill .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)) .kill) .kill) .kill) .kill))) (.node 0 .kill .kill))))))))))))))))

private def k5FareyCertC9 : FareyTree :=
  (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 3 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 0 (.node 0 (.node 0 (.node 4 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill k5FareyCertC8))))))))))))))))) (.node 0 (.node 0 (.node 0 .kill .kill) .kill) .kill)) .kill) .kill) .kill))))))))))))))))))))))))))) (.node 0 (.node 0 (.node 0 .kill .kill) .kill) .kill)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private def k5FareyCertC10 : FareyTree :=
  (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 (.node 0 .kill (.node 1 .kill (.node 0 (.node 0 (.node 1 (.node 0 .kill .kill) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 0 .kill .kill) (.node 0 (.node 0 (.node 0 (.node 1 (.node 1 .kill (.node 1 (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 0 (.node 0 (.node 1 (.node 1 .kill (.node 1 (.node 0 .kill (.node 0 .kill (.node 2 (.node 0 .kill .kill) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 2 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 (.node 0 .kill (.node 0 .kill (.node 2 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 0 (.node 1 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 1 (.node 2 (.node 0 .kill .kill) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 0 .kill (.node 1 .kill (.node 0 (.node 1 (.node 0 .kill (.node 1 .kill (.node 1 (.node 0 .kill (.node 1 .kill (.node 1 (.node 0 .kill (.node 7 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill k5FareyCertC9))))))))))))))))))))) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 .kill .kill) .kill) .kill) .kill) .kill) .kill) .kill))) .kill))) (.node 0 .kill .kill)))) .kill) .kill))) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)) .kill))))) (.node 0 .kill .kill)) .kill))))))))) (.node 0 (.node 0 .kill .kill) .kill)))) (.node 0 .kill .kill)))))))))))) (.node 0 (.node 0 .kill .kill) .kill)))))) .kill) .kill) .kill) .kill) .kill) .kill) .kill)))) (.node 0 .kill .kill))) .kill) .kill) .kill)))) (.node 0 .kill .kill))) .kill) .kill) .kill) .kill)) .kill) .kill) .kill) .kill) .kill)) .kill) .kill))) (.node 0 .kill .kill))))))))

def k5FareyCert : FareyTree :=
  (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 (.node 0 .kill (.node 1 .kill (.node 0 (.node 1 (.node 1 .kill (.node 0 (.node 1 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 5 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill)))) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 2 (.node 0 .kill (.node 0 .kill .kill)) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 0 .kill (.node 1 .kill (.node 1 (.node 1 (.node 0 .kill .kill) (.node 0 (.node 0 (.node 1 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 (.node 0 .kill .kill) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 0 .kill (.node 1 .kill (.node 1 (.node 1 .kill (.node 0 (.node 1 (.node 1 .kill (.node 2 (.node 0 .kill (.node 0 .kill k5FareyCertC10)) (.node 0 .kill .kill))) .kill) .kill)) .kill))) .kill) .kill) .kill) .kill) .kill) .kill)))))) (.node 0 .kill .kill)) .kill) .kill)) .kill))) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill))))) .kill) .kill)) .kill) .kill))) .kill))))))))

set_option maxRecDepth 40000 in
set_option maxHeartbeats 8000000 in
-- Kernel-only certificate check (`decide`, no `native_decide`): evaluates
-- the 3181-node Farey descent tree, including 285 exact quintic candidate
-- refutations on integers up to ~2000 bits.
theorem k5FareyCert_check :
    fareyCheck 4 44 5 3 665 (4 * 10 ^ 120) k5EqRefuted 1 1 4 3 k5FareyCert =
      true := by
  decide

/--
**No `k = 5`, `N = 4` gap solution with `221 ≤ d < 10^120`** (extended
range; the headline `10^60` statement is
`no_gap_solution_four_five_below`).  Composes the banked ratio window and
row-1 quotient confinement with the centered-Thue descent certificate.
-/
theorem no_gap_solution_four_five_below_ext {n d : ℕ}
    (hd : 221 ≤ d) (hB : d < 10 ^ 120) :
    blockProduct 5 (n + d) ≠ 4 * blockProduct 5 n := by
  intro heq
  obtain ⟨hup, hlo⟩ := ratio_window_four_nat heq
  have h3d : 3 * d ≤ n + 1 := row_base_lower_k5 hd hup
  have h4d : n + 1 < 4 * d := row_base_upper_k5 hlo
  have hsol : K5CenteredEq (n + d + 3) (n + 3) := k5_centered_of_eq heq
  have hYlo : 665 ≤ n + 3 := by omega
  have hYmax : n + 3 ≤ 4 * 10 ^ 120 := by
    generalize hP : (10 : ℕ) ^ 120 = P at hB ⊢
    omega
  have hbr := k5_bracket_upper hsol hYlo
  have hlow : (n + 3) * 1 + 1 ≤ (n + d + 3) * 1 := by omega
  have hhigh : (n + d + 3) * 3 + 1 ≤ (n + 3) * 4 := by omega
  exact fareyCheck_sound (fun X Y h => k5EqRefuted_sound X Y h)
    (fun X Y hS h1 _h2 => k5_thue_window hS h1) hsol hYlo hYmax (by omega)
    k5FareyCert 1 1 4 3 (by norm_num) k5FareyCert_check hlow hhigh

/--
**No `k = 5`, `N = 4` gap solution with `221 ≤ d < 10^60`.**  Together with
the banked `d ≤ 220` small-core certificate this closes `k = 5` up to the
tail `NoLargeGapSolutionFour 5 (10^60)`
(see `no_gap_solution_four_five_of_tail`).
-/
theorem no_gap_solution_four_five_below {n d : ℕ}
    (hd : 221 ≤ d) (hB : d < 10 ^ 60) :
    blockProduct 5 (n + d) ≠ 4 * blockProduct 5 n :=
  no_gap_solution_four_five_below_ext hd
    (lt_of_lt_of_le hB (Nat.pow_le_pow_right (by norm_num) (by norm_num)))

/--
Conditional closure for `k = 5`, `d ≥ 221`: the certified strip
`221 ≤ d < 10^60` plus the tail hypothesis `NoLargeGapSolutionFour 5 (10^60)`
refute every gap solution with `d ≥ 221`.
-/
theorem no_gap_solution_four_five_of_tail
    (htail : NoLargeGapSolutionFour 5 (10 ^ 60)) {n d : ℕ} (hd : 221 ≤ d) :
    blockProduct 5 (n + d) ≠ 4 * blockProduct 5 n := by
  rcases Nat.lt_or_ge d (10 ^ 60) with h | h
  · exact no_gap_solution_four_five_below hd h
  · exact htail n d h

/-- Variant of `no_gap_solution_four_five_of_tail` from the weaker tail at
`10^120` (the full certified range). -/
theorem no_gap_solution_four_five_of_tail_ext
    (htail : NoLargeGapSolutionFour 5 (10 ^ 120)) {n d : ℕ} (hd : 221 ≤ d) :
    blockProduct 5 (n + d) ≠ 4 * blockProduct 5 n := by
  rcases Nat.lt_or_ge d (10 ^ 120) with h | h
  · exact no_gap_solution_four_five_below_ext hd h
  · exact htail n d h

end Erdos686Variant

end Erdos686
