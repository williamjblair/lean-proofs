/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.Core.ConvergentMachinery

/-!
# Erdős 686, k = 15: centered-Thue/convergent certificate

Instance of the Farey/Stern–Brocot descent machinery
(`Erdos686ConvergentMachinery`) for `k = 15`, `N = 4`, closing the gap
equation `(n+d+1)⋯(n+d+15) = 4·(n+1)⋯(n+15)` for all `221 ≤ d < 10^120`
(headline statement at `10^60`, matching the campaign tail interface).
Mathematics: `compute/theory/oddk_15/note.md` and
`compute/theory/odd_k_thue_synthesis.md`; certificate generated and
pre-verified by `compute/erdos686_thue_gen_lean.py` (cross-checked against
`compute/artifacts/thue_convergents_k15.json`).

The chain, entirely in integer arithmetic:

1. **Centering** (`k15_centered_of_eq`): with `X = n+d+8`, `Y = n+8` the
   equation is exactly `P₁₅(X) = 4·P₁₅(Y)` for
   `P₁₅(T) = T¹⁵ − 140T¹³ + 7462T¹¹ − 191620T⁹ + 2475473T⁷ − 15291640T⁵ + 38402064T³ − 25401600T`,
   stated ℕ-safely (`K15CenteredEq`) as
   `X¹⁵ + 7462X¹¹ + 2475473X⁷ + 38402064X³ + 560Y¹³ + 766480Y⁹ + 61166560Y⁵ + 101606400Y`
   `= 4Y¹⁵ + 29848Y¹¹ + 9901892Y⁷ + 153608256Y³ + 140X¹³ + 191620X⁹ + 15291640X⁵ + 25401600X`.
2. **Ratio bracket** (`k15_scaled_lower/upper`): unlike the `k = 5` module
   (which extracted the bracket from the equation via a monotone scaled
   polynomial), here the bracket comes from the *banked ratio window*
   `4(n+1)¹⁵ ≤ (n+d+1)¹⁵`, `(n+d+15)¹⁵ ≤ 4(n+15)¹⁵` and the
   15th-power bracket facts `109682¹⁵ < 4·10^75 < 109683¹⁵`; the
   centered offsets are absorbed by `omega` using `Y ≥ 2217`, giving
   `109651·Y < 10⁵·X < 109714·Y`.
3. **Thue window** (`k15_thue_window`): `1·|X¹⁵ − 4Y¹⁵| ≤ 97·Y¹³`
   (constant `97`; certified sup over the bracket `≈ 96.242`, true
   value `≈ 94.52`).
4. **Handoff from the banked window**: `ratio_window_four_nat` +
   `row_base_lower_k15`/`row_base_upper_k15` give `10d ≤ n+1 < 11d` for
   `d ≥ 221`, hence `2217 ≤ Y ≤ 11·10^120` for `221 ≤ d < 10^120`.
   The `d = 1` telescope `P₁₅(13) = 4·P₁₅(12)` (i.e. `(n,d) = (4,1)`)
   solves the raw centered equation but has `Y = 12 < Ylo = 2217`, so it
   is skipped by the `Ylo` guard of every equality candidate (and
   `d = 1` is banked in the `d ≤ 220` branch anyway).
5. **Descent certificate** (`k15FareyCert`, `k15FareyCert_check`): a
   4173-node Farey tree rooted at `1/1 < 4^(1/15) < 11/10`; one kernel
   `decide` checks every side certificate, mediant multiple bound, and
   the 945 exact candidate refutations (`Y` up to `11·10^120`,
   ~6022-bit integers).  No `native_decide`.
-/

namespace Erdos686

namespace Erdos686Variant

/--
The exact centered equation for `k = 15`, `N = 4` in ℕ-safe form:
`X¹⁵ + 7462X¹¹ + 2475473X⁷ + 38402064X³ + 560Y¹³ + 766480Y⁹ + 61166560Y⁵ + 101606400Y`
`= 4Y¹⁵ + 29848Y¹¹ + 9901892Y⁷ + 153608256Y³ + 140X¹³ + 191620X⁹ + 15291640X⁵ + 25401600X`
⟺ `P₁₅(X) = 4·P₁₅(Y)` with
`P₁₅(T) = T¹⁵ − 140T¹³ + 7462T¹¹ − 191620T⁹ + 2475473T⁷ − 15291640T⁵ + 38402064T³ − 25401600T`,
at `X = n+d+8`, `Y = n+8`.
-/
def K15CenteredEq (X Y : ℕ) : Prop :=
  X ^ 15 + 7462 * X ^ 11 + 2475473 * X ^ 7 + 38402064 * X ^ 3 + 560 * Y ^ 13 + 766480 * Y ^ 9 +
      61166560 * Y ^ 5 + 101606400 * Y =
    4 * Y ^ 15 + 29848 * Y ^ 11 + 9901892 * Y ^ 7 + 153608256 * Y ^ 3 + 140 * X ^ 13 + 191620 *
      X ^ 9 + 15291640 * X ^ 5 + 25401600 * X

/-- Boolean refuter for the exact centered equation (kernel-decidable). -/
def k15EqRefuted (X Y : ℕ) : Bool :=
  decide (X ^ 15 + 7462 * X ^ 11 + 2475473 * X ^ 7 + 38402064 * X ^ 3 + 560 * Y ^ 13 + 766480 *
      Y ^ 9 + 61166560 * Y ^ 5 + 101606400 * Y ≠
    4 * Y ^ 15 + 29848 * Y ^ 11 + 9901892 * Y ^ 7 + 153608256 * Y ^ 3 + 140 * X ^ 13 + 191620 *
      X ^ 9 + 15291640 * X ^ 5 + 25401600 * X)

lemma k15EqRefuted_sound (X Y : ℕ) (h : k15EqRefuted X Y = true) :
    ¬ K15CenteredEq X Y := by
  intro hc
  exact (of_decide_eq_true h) hc

/-! ## Centering -/

private lemma blockProduct_fifteen_prod (x : ℕ) :
    blockProduct 15 x =
      (x + 1) * (x + 2) * (x + 3) * (x + 4) * (x + 5) * (x + 6) * (x + 7) * (x + 8) * (x + 9) *
        (x + 10) * (x + 11) * (x + 12) * (x + 13) * (x + 14) * (x + 15) := by
  norm_num [blockProduct, Finset.prod_Icc_succ_top, Finset.Icc_self,
    Finset.prod_singleton]

/-- The centered identity `∏_{i=1}^{15}(m+i) = P₁₅(m+8)` in additive ℕ form. -/
private lemma blockProduct_fifteen_centered (m : ℕ) :
    blockProduct 15 m + 140 * (m + 8) ^ 13 + 191620 * (m + 8) ^ 9 + 15291640 * (m + 8) ^ 5 +
        25401600 * (m + 8) =
      (m + 8) ^ 15 + 7462 * (m + 8) ^ 11 + 2475473 * (m + 8) ^ 7 + 38402064 * (m + 8) ^ 3 := by
  rw [blockProduct_fifteen_prod]; ring

/-- A gap solution satisfies the exact centered equation. -/
lemma k15_centered_of_eq {n d : ℕ}
    (heq : blockProduct 15 (n + d) = 4 * blockProduct 15 n) :
    K15CenteredEq (n + d + 8) (n + 8) := by
  have h1 := blockProduct_fifteen_centered (n + d)
  have h2 := blockProduct_fifteen_centered n
  unfold K15CenteredEq
  linarith

/-! ## Ratio bracket `109651/10⁵ < X/Y < 109714/10⁵` from the banked window

The banked window inequalities compare `k`-th powers at the row bases
`n+1` and `n+15`; a rational bracket of `4^(1/15)` at scale `10⁵`
(`109682¹⁵ < 4·10^75 < 109683¹⁵`) linearizes them, and `omega` absorbs
the centered-coordinate offsets using `Y = n+8 ≥ 2217` (banked confinement
for `d ≥ 221`). -/

/-- Scaled lower bracket from the banked lower window. -/
lemma k15_scaled_lower {n d : ℕ} (hn : 2209 ≤ n)
    (hlo : 4 * (n + 1) ^ 15 ≤ (n + d + 1) ^ 15) :
    109651 * (n + 8) < 100000 * (n + d + 8) := by
  have hAB : 109682 * (n + 1) < 100000 * (n + d + 1) := by
    by_contra hnot
    have hnot' : 100000 * (n + d + 1) ≤ 109682 * (n + 1) := Nat.le_of_not_lt hnot
    have hp : (100000 * (n + d + 1)) ^ 15 ≤ (109682 * (n + 1)) ^ 15 :=
      Nat.pow_le_pow_left hnot' 15
    rw [mul_pow, mul_pow] at hp
    have h1 : 4 * 100000 ^ 15 * (n + 1) ^ 15 ≤ 109682 ^ 15 * (n + 1) ^ 15 :=
      calc 4 * 100000 ^ 15 * (n + 1) ^ 15
          = 100000 ^ 15 * (4 * (n + 1) ^ 15) := by ring
        _ ≤ 100000 ^ 15 * (n + d + 1) ^ 15 := Nat.mul_le_mul (le_refl _) hlo
        _ ≤ 109682 ^ 15 * (n + 1) ^ 15 := hp
    have h2 : 0 < (n + 1) ^ 15 := pow_pos (by omega) 15
    exact absurd (Nat.le_of_mul_le_mul_right h1 h2) (by norm_num)
  omega

/-- Scaled upper bracket from the banked upper window. -/
lemma k15_scaled_upper {n d : ℕ} (hn : 2209 ≤ n)
    (hup : (n + d + 15) ^ 15 ≤ 4 * (n + 15) ^ 15) :
    100000 * (n + d + 8) < 109714 * (n + 8) := by
  have hCD : 100000 * (n + d + 15) < 109683 * (n + 15) := by
    by_contra hnot
    have hnot' : 109683 * (n + 15) ≤ 100000 * (n + d + 15) := Nat.le_of_not_lt hnot
    have hp : (109683 * (n + 15)) ^ 15 ≤ (100000 * (n + d + 15)) ^ 15 :=
      Nat.pow_le_pow_left hnot' 15
    rw [mul_pow, mul_pow] at hp
    have h1 : 109683 ^ 15 * (n + 15) ^ 15 ≤ 4 * 100000 ^ 15 * (n + 15) ^ 15 :=
      calc 109683 ^ 15 * (n + 15) ^ 15
          ≤ 100000 ^ 15 * (n + d + 15) ^ 15 := hp
        _ ≤ 100000 ^ 15 * (4 * (n + 15) ^ 15) := Nat.mul_le_mul (le_refl _) hup
        _ = 4 * 100000 ^ 15 * (n + 15) ^ 15 := by ring
    have h2 : 0 < (n + 15) ^ 15 := pow_pos (by omega) 15
    exact absurd (Nat.le_of_mul_le_mul_right h1 h2) (by norm_num)
  omega

/-! ## The Thue window `1·|X¹⁵ − 4Y¹⁵| ≤ 97·Y¹³` -/

set_option maxHeartbeats 4000000 in
-- The `nlinarith` bracket-power expansions (degree 13 products of 6-digit
-- scaled brackets) and the two ~33-fact `linarith` calls exceed the
-- default limit at this degree.
/--
Two-sided Thue window in the exact shape consumed by `fareyCheck_sound`
(`N = 4`, `cnum = 97`, `cden = 1`, `e = 13`): for any solution inside
the scaled bracket with `Y ≥ 2217`, `1·(4Y¹⁵) ≤ 1·X¹⁵ + 97·Y¹³` and
`1·X¹⁵ ≤ 1·(4Y¹⁵) + 97·Y¹³`.
-/
lemma k15_thue_window {X Y : ℕ} (hsol : K15CenteredEq X Y)
    (hbl : 109651 * Y < 100000 * X) (hbu : 100000 * X < 109714 * Y)
    (hY : 2217 ≤ Y) :
    1 * (4 * Y ^ 15) ≤ 1 * X ^ 15 + 97 * Y ^ 13 ∧
      1 * X ^ 15 ≤ 1 * (4 * Y ^ 15) + 97 * Y ^ 13 := by
  have hz :  (X : ℤ) ^ 15 + 7462 * (X : ℤ) ^ 11 + 2475473 * (X : ℤ) ^ 7 + 38402064 * (X : ℤ) ^ 3
      + 560 * (Y : ℤ) ^ 13 + 766480 * (Y : ℤ) ^ 9 + 61166560 * (Y : ℤ) ^ 5 + 101606400 * (Y : ℤ)
      = 4 * (Y : ℤ) ^ 15 + 29848 * (Y : ℤ) ^ 11 + 9901892 * (Y : ℤ) ^ 7 + 153608256 * (Y : ℤ) ^
      3 + 140 * (X : ℤ) ^ 13 + 191620 * (X : ℤ) ^ 9 + 15291640 * (X : ℤ) ^ 5 + 25401600 * (X :
      ℤ) := by
    exact_mod_cast hsol
  have hblz : (109651 : ℤ) * Y ≤ 100000 * X := by exact_mod_cast hbl.le
  have hbuz : (100000 : ℤ) * X ≤ 109714 * Y := by exact_mod_cast hbu.le
  have hYz : (2217 : ℤ) ≤ (Y : ℤ) := by exact_mod_cast hY
  have hY0 : (0 : ℤ) ≤ (Y : ℤ) := Int.natCast_nonneg Y
  -- odd powers of the scaled bracket
  have hlo3 :
      (1318371451821451 : ℤ) * (Y : ℤ) ^ 3 ≤
        1000000000000000 * (X : ℤ) ^ 3 := by
    nlinarith [pow_le_pow_left₀ (by positivity : (0 : ℤ) ≤ 109651 * (Y : ℤ))
      hblz 3]
  have hhi3 :
      (1000000000000000 : ℤ) * (X : ℤ) ^ 3 ≤
        1320645169286344 * (Y : ℤ) ^ 3 := by
    nlinarith [pow_le_pow_left₀ (by positivity : (0 : ℤ) ≤ 100000 * (X : ℤ))
      hbuz 3]
  have hlo5 :
      (15851230585929909396773251 : ℤ) * (Y : ℤ) ^ 5 ≤
        10000000000000000000000000 * (X : ℤ) ^ 5 := by
    nlinarith [pow_le_pow_left₀ (by positivity : (0 : ℤ) ≤ 109651 * (Y : ℤ))
      hblz 5]
  have hhi5 :
      (10000000000000000000000000 : ℤ) * (X : ℤ) ^ 5 ≤
        15896819577805532581313824 * (Y : ℤ) ^ 5 := by
    nlinarith [pow_le_pow_left₀ (by positivity : (0 : ℤ) ≤ 100000 * (X : ℤ))
      hbuz 5]
  have hlo7 :
      (190584763301100802106366523266965051 : ℤ) * (Y : ℤ) ^ 7 ≤
        100000000000000000000000000000000000 * (X : ℤ) ^ 7 := by
    nlinarith [pow_le_pow_left₀ (by positivity : (0 : ℤ) ≤ 109651 * (Y : ℤ))
      hblz 7]
  have hhi7 :
      (100000000000000000000000000000000000 : ℤ) * (X : ℤ) ^ 7 ≤
        191352589299865606305224025739467904 * (Y : ℤ) ^ 7 := by
    nlinarith [pow_le_pow_left₀ (by positivity : (0 : ℤ) ≤ 100000 * (X : ℤ))
      hbuz 7]
  have hlo9 :
      (2291465751231816023280105467422739980094396851 : ℤ) * (Y : ℤ) ^ 9 ≤
        1000000000000000000000000000000000000000000000 * (X : ℤ) ^ 9 := by
    nlinarith [pow_le_pow_left₀ (by positivity : (0 : ℤ) ≤ 109651 * (Y : ℤ))
      hblz 9]
  have hhi9 :
      (1000000000000000000000000000000000000000000000 : ℤ) * (X : ℤ) ^ 9 ≤
        2303342077486020664151619357852443703396995584 * (Y : ℤ) ^ 9 := by
    nlinarith [pow_le_pow_left₀ (by positivity : (0 : ℤ) ≤ 100000 * (X : ℤ))
      hbuz 9]
  have hlo11 :
      (27551075952345360833845281198152473340622869584511068651 : ℤ) * (Y : ℤ) ^ 11 ≤
        10000000000000000000000000000000000000000000000000000000 * (X : ℤ) ^ 11 := by
    nlinarith [pow_le_pow_left₀ (by positivity : (0 : ℤ) ≤ 109651 * (Y : ℤ))
      hblz 11]
  have hhi11 :
      (10000000000000000000000000000000000000000000000000000000 : ℤ) * (X : ℤ) ^ 11 ≤
        27725701258233999662592419285875487951771070664905508864 * (Y : ℤ) ^ 11 := by
    nlinarith [pow_le_pow_left₀ (by positivity : (0 : ℤ) ≤ 100000 * (X : ℤ))
      hbuz 11]
  have hlo13 :
      (331256003160359860902000184996345996687849059252023433858748980451 : ℤ) * (Y : ℤ) ^ 13 ≤
        100000000000000000000000000000000000000000000000000000000000000000 * (X : ℤ) ^ 13 := by
    nlinarith [pow_le_pow_left₀ (by positivity : (0 : ℤ) ≤ 109651 * (Y : ℤ))
      hblz 13]
  have hhi13 :
      (100000000000000000000000000000000000000000000000000000000000000000 : ℤ) * (X : ℤ) ^ 13 ≤
        333738751952923431166834359747154025985917022345616909247680159744 * (Y : ℤ) ^ 13 := by
    nlinarith [pow_le_pow_left₀ (by positivity : (0 : ℤ) ≤ 100000 * (X : ℤ))
      hbuz 13]
  -- lower-degree absorption at `Y ≥ 2217`
  have hab1 :
      (14099000221984976417285376299528507300961 : ℤ) * (Y : ℤ) ≤ (Y : ℤ) ^ 13 := by
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℤ) ≤ 2217) hYz 12,
      pow_nonneg hY0 1]
  have hab3 :
      (2868513718059830944523156406634449 : ℤ) * (Y : ℤ) ^ 3 ≤ (Y : ℤ) ^ 13 := by
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℤ) ≤ 2217) hYz 10,
      pow_nonneg hY0 3]
  have hab5 :
      (583613789711606635103282241 : ℤ) * (Y : ℤ) ^ 5 ≤ (Y : ℤ) ^ 13 := by
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℤ) ≤ 2217) hYz 8,
      pow_nonneg hY0 5]
  have hab7 :
      (118739210970870849969 : ℤ) * (Y : ℤ) ^ 7 ≤ (Y : ℤ) ^ 13 := by
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℤ) ≤ 2217) hYz 6,
      pow_nonneg hY0 7]
  have hab9 :
      (24158099877921 : ℤ) * (Y : ℤ) ^ 9 ≤ (Y : ℤ) ^ 13 := by
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℤ) ≤ 2217) hYz 4,
      pow_nonneg hY0 9]
  have hab11 :
      (4915089 : ℤ) * (Y : ℤ) ^ 11 ≤ (Y : ℤ) ^ 13 := by
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℤ) ≤ 2217) hYz 2,
      pow_nonneg hY0 11]
  have hpos1 : (0 : ℤ) ≤ (Y : ℤ) ^ 1 := by positivity
  have hpos3 : (0 : ℤ) ≤ (Y : ℤ) ^ 3 := by positivity
  have hpos5 : (0 : ℤ) ≤ (Y : ℤ) ^ 5 := by positivity
  have hpos7 : (0 : ℤ) ≤ (Y : ℤ) ^ 7 := by positivity
  have hpos9 : (0 : ℤ) ≤ (Y : ℤ) ^ 9 := by positivity
  have hpos11 : (0 : ℤ) ≤ (Y : ℤ) ^ 11 := by positivity
  have hpos13 : (0 : ℤ) ≤ (Y : ℤ) ^ 13 := by positivity
  constructor
  · have hgoal : 1 * (4 * (Y : ℤ) ^ 15) ≤
        1 * (X : ℤ) ^ 15 + 97 * (Y : ℤ) ^ 13 := by
      linarith [hz, hlo3, hhi3, hlo5, hhi5, hlo7, hhi7, hlo9, hhi9, hlo11, hhi11, hlo13, hhi13,
        hab1, hab3, hab5, hab7, hab9, hab11, hpos1, hpos3, hpos5, hpos7, hpos9, hpos11, hpos13,
        hblz, hbuz]
    exact_mod_cast hgoal
  · have hgoal : 1 * (X : ℤ) ^ 15 ≤
        1 * (4 * (Y : ℤ) ^ 15) + 97 * (Y : ℤ) ^ 13 := by
      linarith [hz, hlo3, hhi3, hlo5, hhi5, hlo7, hhi7, hlo9, hhi9, hlo11, hhi11, hlo13, hhi13,
        hab1, hab3, hab5, hab7, hab9, hab11, hpos1, hpos3, hpos5, hpos7, hpos9, hpos11, hpos13,
        hblz, hbuz]
    exact_mod_cast hgoal

/-! ## The descent certificate

Generated by `compute/erdos686_thue_gen_lean.py 120 15` (deterministic,
byte-stable); root Farey pair `1/1 < 4^(1/15) < 11/10`, `Ylo = 2217`,
`Ymax = 11·10^120`.  4173 nodes: 2086 mediant splits, 2083 side-certificate
kills, 4 `Ymax`-exits; 945 candidate pairs refuted by the exact equation.
Every convergent of `cf(4^(1/15))` with denominator `≤ 11·10^120` (244 of the
341 rows of `compute/artifacts/thue_convergents_k15.json`) occurs among the
mediants; determinants, straddle signs, and sign alternation are re-verified
by the generator before emission. -/

/- AUTOGENERATED by compute/erdos686_thue_gen_lean.py (YMAX_EXP=120).
   Farey/Stern-Brocot descent certificate for k = 15, N = 4:
   root pair 1/1 < 4^(1/15) < 11/10, Thue window 1*|X^15-4Y^15| <= 97*Y^13,
   Ylo = 2217, Ymax = 11 * 10^120.  Do not edit by hand. -/

-- generated single-line tree literals (repo precedent: Erdos154.lean)
set_option linter.style.longLine false

private def k15FareyCertC0 : FareyTree :=
  (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 1 (.node 2 (.node 1 (.node 0 .kill .kill) (.node 0 .kill .kill)) (.node 1 (.node 1 (.node 2 (.node 1 (.node 0 .kill .kill) (.node 2 (.node 0 .kill .kill) (.node 1 (.node 2 (.node 1 (.node 0 .kill .kill) (.node 1 .kill (.node 6 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill))))) (.node 1 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 3 (.node 1 (.node 0 .kill .kill) (.node 1 .kill (.node 0 .high .high))) (.node 0 (.node 0 .high .high) .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)))) (.node 0 .kill .kill)) (.node 0 .kill .kill)))) (.node 0 .kill .kill)) .kill) .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)

private def k15FareyCertC1 : FareyTree :=
  (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 k15FareyCertC0 .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)

private def k15FareyCertC2 : FareyTree :=
  (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 2 (.node 0 .kill .kill) (.node 1 (.node 1 (.node 2 (.node 1 (.node 0 .kill .kill) (.node 1 (.node 0 .kill .kill) (.node 3 (.node 1 .kill (.node 1 .kill (.node 0 .kill (.node 1 .kill (.node 1 .kill (.node 1 .kill (.node 3 (.node 1 .kill (.node 1 .kill (.node 1 .kill (.node 2 (.node 0 .kill .kill) (.node 1 (.node 1 (.node 2 (.node 0 .kill .kill) (.node 1 (.node 2 (.node 0 .kill .kill) (.node 1 (.node 2 (.node 1 (.node 0 .kill .kill) (.node 1 (.node 0 .kill .kill) (.node 2 (.node 1 (.node 0 .kill .kill) (.node 6 (.node 1 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill))))) (.node 1 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 2 (.node 1 (.node 0 .kill .kill) (.node 1 (.node 0 .kill .kill) (.node 3 (.node 0 .kill (.node 0 .kill .kill)) (.node 1 (.node 1 (.node 1 (.node 1 (.node 1 (.node 3 (.node 1 (.node 0 .kill .kill) (.node 1 .kill (.node 1 .kill (.node 1 .kill (.node 1 .kill (.node 1 .kill (.node 2 (.node 1 (.node 0 .kill .kill) (.node 19 (.node 1 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill))))))))))))))))))) (.node 1 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 k15FareyCertC1 .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill))) (.node 1 (.node 0 .kill .kill) .kill)))))))) (.node 0 (.node 0 .kill .kill) .kill)) .kill) .kill) .kill) .kill) (.node 0 .kill .kill))))) (.node 0 .kill .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill))) (.node 0 .kill .kill)))) (.node 0 .kill .kill)) (.node 0 .kill .kill))) (.node 0 .kill .kill))) (.node 0 .kill .kill)) (.node 0 .kill .kill)))))) (.node 1 (.node 0 .kill .kill) (.node 0 .kill .kill))))))))) (.node 1 (.node 0 (.node 0 .kill .kill) .kill) .kill)))) (.node 0 .kill .kill)) .kill) (.node 0 .kill .kill)))))))))))))))))))))))))))))))))))

private def k15FareyCertC3 : FareyTree :=
  (.node 1 (.node 2 (.node 1 (.node 0 .kill .kill) (.node 1 (.node 0 .kill .kill) (.node 1 (.node 2 (.node 0 .kill .kill) (.node 1 (.node 2 (.node 0 .kill (.node 0 .kill .kill)) (.node 1 (.node 1 (.node 1 (.node 2 (.node 0 .kill .kill) (.node 1 (.node 2 (.node 0 .kill .kill) (.node 1 (.node 5 (.node 1 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill))))) (.node 1 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 1 (.node 2 (.node 1 (.node 0 .kill .kill) (.node 0 .kill .kill)) (.node 1 (.node 1 (.node 2 (.node 1 (.node 0 .kill .kill) (.node 10 (.node 1 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill)))))))))) (.node 1 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 1 (.node 2 (.node 1 (.node 0 .kill .kill) (.node 0 .kill .kill)) (.node 1 (.node 1 (.node 0 .kill .kill) (.node 2 (.node 1 (.node 0 .kill .kill) (.node 8 (.node 1 .kill (.node 0 .kill (.node 0 .kill k15FareyCertC2))) (.node 1 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 .kill .kill) .kill) .kill) .kill) .kill) .kill) .kill))) (.node 0 .kill .kill))) (.node 0 .kill .kill))) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill))) (.node 0 .kill .kill)) .kill) .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)) (.node 0 .kill .kill))) (.node 0 .kill .kill))) (.node 0 .kill .kill)) .kill) .kill)) (.node 0 .kill .kill))) (.node 0 .kill .kill)))) (.node 0 .kill .kill)) .kill)

private def k15FareyCertC4 : FareyTree :=
  (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 3 (.node 0 .kill (.node 0 .kill .kill)) (.node 1 (.node 1 (.node 1 (.node 1 (.node 3 (.node 1 (.node 0 .kill .kill) (.node 1 .kill (.node 1 .kill (.node 1 .kill (.node 3 (.node 0 .kill (.node 0 .kill .kill)) (.node 1 (.node 1 (.node 1 (.node 1 (.node 1 (.node 2 (.node 1 (.node 0 .kill .kill) (.node 1 .kill (.node 2 (.node 0 .kill .kill) (.node 1 (.node 1 (.node 3 (.node 1 .kill (.node 0 .kill (.node 0 .kill .kill))) (.node 1 (.node 1 (.node 0 (.node 1 (.node 1 (.node 1 (.node 3 (.node 1 (.node 0 .kill .kill) (.node 0 .kill (.node 0 .kill .kill))) (.node 1 (.node 1 (.node 1 (.node 1 (.node 4 (.node 1 (.node 0 .kill .kill) (.node 0 .kill (.node 0 .kill .kill))) (.node 1 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 1 (.node 2 (.node 1 .kill .kill) (.node 2 (.node 1 (.node 0 .kill .kill) (.node 2 (.node 1 .kill (.node 1 .kill (.node 1 (.node 0 .kill .kill) (.node 2 (.node 1 (.node 0 .kill .kill) (.node 2 (.node 1 (.node 0 .kill .kill) (.node 2 (.node 1 (.node 0 .kill .kill) (.node 3 (.node 0 .kill (.node 0 .kill .kill)) (.node 1 (.node 1 (.node 0 (.node 1 (.node 1 (.node 1 (.node 8 (.node 1 (.node 0 .kill .kill) (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill)))))))) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 3 (.node 1 (.node 0 .kill .kill) (.node 1 .kill (.node 1 .kill (.node 1 .kill (.node 4 (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill))) (.node 1 (.node 1 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 k15FareyCertC3 .kill) .kill) .kill) .kill) .kill) .kill) (.node 0 .kill .kill))))))) (.node 0 (.node 0 .kill .kill) .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)) .kill) .kill) .kill) .kill) .kill) .kill))) (.node 0 .kill .kill))) (.node 0 .kill .kill))) (.node 0 .kill .kill))))) (.node 0 (.node 0 .kill .kill) .kill))) (.node 0 .kill .kill))) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)) .kill) .kill) .kill) .kill)) .kill) .kill) .kill) .kill) .kill) .kill)) (.node 0 .kill .kill)) (.node 0 .kill .kill))))) (.node 0 .kill .kill)) .kill) .kill) .kill) .kill) (.node 0 .kill .kill))))))) (.node 0 (.node 0 .kill .kill) .kill)) .kill) .kill) .kill) (.node 0 .kill .kill))))))))

private def k15FareyCertC5 : FareyTree :=
  (.node 1 .kill (.node 1 .kill (.node 2 (.node 1 (.node 0 .kill .kill) (.node 3 (.node 1 .kill (.node 1 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 1 .kill (.node 3 (.node 0 .kill (.node 0 .kill .kill)) (.node 1 (.node 1 (.node 0 (.node 0 (.node 0 (.node 1 (.node 1 (.node 7 (.node 1 (.node 0 .kill .kill) (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 1 .kill (.node 2 (.node 1 .kill (.node 2 (.node 0 .kill .kill) (.node 1 (.node 2 (.node 1 (.node 0 .kill .kill) (.node 2 (.node 0 .kill (.node 0 .kill .kill)) (.node 1 (.node 1 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 3 (.node 1 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 1 .kill (.node 3 (.node 0 .kill (.node 0 .kill .kill)) (.node 1 (.node 1 (.node 1 (.node 1 (.node 9 (.node 1 (.node 0 .kill .kill) (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill k15FareyCertC4))))))))))))))))))))))))))))))))))))))))))))))) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 .kill .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)) .kill) .kill) .kill) (.node 0 .kill .kill)))))))))) (.node 1 (.node 0 (.node 0 .kill .kill) .kill) .kill))) (.node 0 .kill .kill)) .kill) (.node 0 .kill .kill)))) (.node 0 .kill .kill)) (.node 0 .kill .kill)))) (.node 1 (.node 0 .kill .kill) (.node 0 .kill .kill)))))))))))))))))))))))))))))) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 .kill .kill) .kill) .kill) .kill) .kill) .kill)) .kill) .kill) .kill) .kill) .kill) .kill) (.node 0 .kill .kill))))))))) (.node 1 (.node 0 (.node 0 .kill .kill) .kill) .kill))) (.node 1 (.node 0 .kill .kill) (.node 0 .kill .kill)))))

private def k15FareyCertC6 : FareyTree :=
  (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 1 (.node 2 (.node 1 (.node 0 .kill .kill) (.node 0 .kill .kill)) (.node 1 (.node 1 (.node 2 (.node 1 (.node 0 .kill .kill) (.node 3 (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill))) (.node 1 (.node 1 (.node 0 (.node 0 (.node 0 (.node 1 (.node 1 (.node 8 (.node 1 (.node 0 .kill .kill) (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill)))))))) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 4 (.node 1 (.node 0 .kill .kill) (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill)))) (.node 1 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 1 (.node 2 (.node 1 (.node 0 .kill .kill) (.node 1 .kill (.node 2 (.node 0 .kill .kill) (.node 1 (.node 1 (.node 2 (.node 1 (.node 0 .kill .kill) (.node 1 (.node 0 .kill .kill) (.node 4 (.node 1 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 1 .kill (.node 2 (.node 1 (.node 0 .kill .kill) (.node 1 (.node 2 (.node 0 .kill .kill) (.node 1 (.node 2 (.node 1 (.node 0 .kill .kill) (.node 1 (.node 0 .kill .kill) (.node 6 (.node 1 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill k15FareyCertC5))))))))))))))))) (.node 1 (.node 0 (.node 0 (.node 0 (.node 0 .kill .kill) .kill) .kill) .kill) .kill)))) (.node 0 .kill .kill)) (.node 0 .kill .kill))) (.node 0 .kill .kill))) (.node 1 (.node 0 .kill .kill) .kill))))))))))))) (.node 1 (.node 0 (.node 0 (.node 0 .kill .kill) .kill) .kill) .kill)))) (.node 0 .kill .kill)) .kill) (.node 0 .kill .kill))))) (.node 0 .kill .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill))) (.node 0 .kill .kill)) .kill) .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)

private def k15FareyCertC7 : FareyTree :=
  (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 1 .kill (.node 2 (.node 2 (.node 0 .kill .kill) (.node 1 (.node 8 (.node 1 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill)))))))) (.node 1 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 2 (.node 1 (.node 0 .kill .kill) (.node 1 .kill (.node 1 (.node 0 .kill .kill) (.node 2 (.node 1 (.node 0 .kill .kill) (.node 2 (.node 0 .kill .kill) (.node 1 (.node 1 (.node 3 (.node 1 (.node 0 .kill .kill) (.node 1 .kill (.node 1 .kill (.node 1 .kill (.node 1 .kill (.node 1 .kill (.node 2 (.node 1 .kill (.node 1 .kill (.node 2 (.node 0 .kill .kill) (.node 1 (.node 1 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 4 (.node 1 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 1 .kill (.node 3 (.node 1 .kill (.node 1 .kill (.node 1 .kill (.node 3 (.node 0 .kill (.node 0 .kill .kill)) (.node 1 (.node 1 (.node 1 (.node 1 (.node 1 (.node 2 (.node 1 .kill (.node 0 .kill .kill)) (.node 1 (.node 5 (.node 1 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill))))) (.node 1 (.node 0 (.node 0 (.node 0 k15FareyCertC6 .kill) .kill) .kill) .kill)) (.node 0 .kill .kill))) .kill) .kill) .kill) .kill) (.node 0 .kill .kill)))))) (.node 1 (.node 0 .kill .kill) (.node 0 .kill .kill))))))))))))) (.node 1 (.node 0 (.node 0 (.node 0 .kill .kill) .kill) .kill) .kill))) (.node 0 .kill .kill)) .kill) (.node 0 .kill .kill))))) (.node 1 (.node 0 .kill .kill) .kill)))))))) (.node 0 (.node 0 .kill .kill) .kill)) .kill) (.node 0 .kill .kill)))) (.node 1 (.node 0 .kill .kill) .kill))))) (.node 0 .kill .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)) (.node 0 .kill .kill))) (.node 1 (.node 0 .kill .kill) (.node 0 .kill .kill))))))))))))))))))))))))

private def k15FareyCertC8 : FareyTree :=
  (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 2 (.node 1 (.node 0 .kill .kill) (.node 1 .kill (.node 1 (.node 0 .kill .kill) (.node 1 (.node 2 (.node 0 .kill (.node 0 .kill .kill)) (.node 1 (.node 1 (.node 1 (.node 2 (.node 0 .kill .kill) (.node 1 (.node 3 (.node 1 .kill (.node 0 .kill .kill)) (.node 1 (.node 1 (.node 1 (.node 2 (.node 1 (.node 0 .kill .kill) (.node 4 (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill))) (.node 1 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 1 (.node 3 (.node 1 (.node 0 .kill .kill) (.node 1 .kill (.node 1 .kill (.node 1 .kill (.node 1 .kill (.node 2 (.node 0 .kill .kill) (.node 1 (.node 1 (.node 2 (.node 0 .kill .kill) (.node 1 (.node 3 (.node 1 .kill (.node 0 .kill (.node 0 .kill .kill))) (.node 1 (.node 1 (.node 1 (.node 1 (.node 1 (.node 4 (.node 1 (.node 0 .kill .kill) (.node 0 .kill (.node 0 .kill .kill))) (.node 1 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 1 (.node 2 (.node 1 .kill (.node 0 .kill .kill)) (.node 1 (.node 2 (.node 0 .kill (.node 0 .kill .kill)) (.node 1 (.node 1 (.node 3 (.node 1 .kill (.node 0 .kill (.node 0 .kill .kill))) (.node 1 (.node 0 (.node 0 (.node 0 (.node 1 (.node 1 (.node 2 (.node 1 (.node 0 .kill .kill) (.node 1 .kill (.node 2 (.node 0 .kill .kill) (.node 1 (.node 1 (.node 2 (.node 0 .kill .kill) (.node 1 (.node 2 (.node 0 .kill .kill) (.node 1 (.node 5 (.node 1 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill))))) (.node 1 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 2 (.node 1 (.node 0 .kill .kill) (.node 1 .kill (.node 2 (.node 0 .kill .kill) (.node 1 (.node 7 (.node 1 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill k15FareyCertC7))))))) (.node 1 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 .kill .kill) .kill) .kill) .kill) .kill) .kill)) (.node 0 .kill .kill))))) (.node 0 .kill .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)) (.node 0 .kill .kill))) (.node 0 .kill .kill))) (.node 0 .kill .kill)) (.node 0 .kill .kill))))) (.node 0 .kill .kill)) .kill) .kill) .kill) .kill) .kill) .kill)) (.node 0 .kill .kill)) (.node 0 .kill .kill))) (.node 0 .kill .kill))) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)) .kill) .kill) .kill) .kill) .kill)) (.node 0 .kill .kill))) (.node 0 .kill .kill)) (.node 0 .kill .kill)))))))) (.node 0 (.node 0 .kill .kill) .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill))) (.node 0 .kill .kill)) .kill) .kill) .kill)) (.node 0 .kill .kill))) (.node 0 .kill .kill)) .kill) .kill)) (.node 0 .kill .kill))))) (.node 0 .kill .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)

private def k15FareyCertC9 : FareyTree :=
  (.node 1 (.node 0 .kill .kill) (.node 11 (.node 1 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 4 (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill))) (.node 1 (.node 1 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 1 (.node 3 (.node 1 (.node 0 .kill .kill) (.node 1 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 1 .kill (.node 2 (.node 0 .kill .kill) (.node 1 (.node 1 (.node 1 (.node 2 (.node 1 .kill (.node 0 .kill .kill)) (.node 1 (.node 1 (.node 1 (.node 7 (.node 1 (.node 0 .kill .kill) (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill))))))) (.node 1 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 k15FareyCertC8 .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)) .kill) .kill) .kill)) .kill) .kill) (.node 0 .kill .kill))))))))) (.node 0 (.node 0 .kill .kill) .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) (.node 0 .kill .kill))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (.node 1 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 .kill .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)))

private def k15FareyCertC10 : FareyTree :=
  (.node 1 (.node 5 (.node 1 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill))))) (.node 1 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 1 (.node 2 (.node 1 (.node 0 .kill .kill) (.node 0 .kill .kill)) (.node 1 (.node 1 (.node 1 (.node 2 (.node 1 .kill .kill) (.node 1 (.node 3 (.node 1 .kill (.node 0 .kill (.node 0 .kill .kill))) (.node 1 (.node 1 (.node 1 (.node 1 (.node 1 (.node 2 (.node 1 (.node 0 .kill .kill) (.node 1 .kill (.node 1 .kill (.node 5 (.node 1 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 2 (.node 0 .kill .kill) (.node 1 (.node 1 (.node 1 (.node 1 (.node 2 (.node 1 .kill (.node 0 .kill .kill)) (.node 1 (.node 1 (.node 2 (.node 1 .kill (.node 0 .kill .kill)) (.node 1 (.node 1 (.node 2 (.node 1 (.node 0 .kill .kill) (.node 3 (.node 0 .kill (.node 0 .kill .kill)) (.node 1 (.node 1 (.node 1 (.node 1 (.node 2 (.node 1 (.node 0 .kill .kill) (.node 3 (.node 0 .kill (.node 0 .kill .kill)) (.node 1 (.node 1 (.node 1 (.node 1 (.node 1 (.node 2 (.node 1 (.node 0 .kill .kill) (.node 1 (.node 0 .kill .kill) (.node 1 (.node 2 (.node 0 .kill .kill) (.node 1 (.node 3 (.node 1 .kill (.node 0 .kill .kill)) (.node 1 (.node 1 (.node 1 (.node 1 (.node 2 (.node 1 (.node 0 .kill .kill) (.node 2 (.node 0 .kill .kill) (.node 1 (.node 3 (.node 1 .kill (.node 0 .kill .kill)) (.node 1 (.node 1 (.node 1 (.node 1 (.node 1 (.node 4 (.node 1 (.node 0 .kill .kill) (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill)))) (.node 1 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 2 (.node 1 (.node 0 .kill .kill) (.node 1 .kill (.node 1 .kill (.node 2 (.node 0 .kill .kill) (.node 1 (.node 2 k15FareyCertC9 (.node 0 .kill .kill)) (.node 0 .kill .kill)))))) (.node 0 .kill .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)) .kill) .kill) .kill) .kill) .kill)) (.node 0 .kill .kill)))) (.node 0 .kill .kill)) .kill) .kill) .kill) .kill)) (.node 0 .kill .kill))) (.node 0 .kill .kill)))) (.node 0 .kill .kill)) .kill) .kill) .kill) .kill) .kill))) (.node 0 .kill .kill)) .kill) .kill) .kill) .kill))) (.node 0 .kill .kill)) .kill) .kill)) (.node 0 .kill .kill)) .kill)) .kill) .kill) .kill) (.node 0 .kill .kill)))))))))))))))))))) (.node 1 (.node 0 (.node 0 (.node 0 (.node 0 .kill .kill) .kill) .kill) .kill) .kill))))) (.node 0 .kill .kill)) .kill) .kill) .kill) .kill) .kill)) (.node 0 .kill .kill))) (.node 0 .kill .kill)) .kill) .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)) (.node 0 .kill .kill))

private def k15FareyCertC11 : FareyTree :=
  (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 2 (.node 0 .kill .kill) (.node 1 (.node 1 (.node 1 (.node 3 (.node 1 (.node 0 .kill .kill) (.node 1 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 1 .kill (.node 2 (.node 0 .kill .kill) (.node 1 (.node 2 (.node 1 (.node 0 .kill .kill) (.node 1 (.node 0 .kill .kill) (.node 3 (.node 1 .kill (.node 1 .kill (.node 1 .kill (.node 1 .kill (.node 1 .kill (.node 6 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill))))) (.node 1 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 4 (.node 1 (.node 0 .kill .kill) (.node 1 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 1 .kill (.node 3 (.node 1 .kill (.node 1 .kill (.node 1 .kill (.node 1 .kill (.node 1 .kill (.node 3 (.node 1 .kill (.node 1 .kill (.node 0 .kill (.node 1 .kill (.node 1 .kill (.node 2 (.node 0 .kill .kill) (.node 1 (.node 1 (.node 2 (.node 0 .kill .kill) (.node 1 (.node 4 (.node 1 .kill (.node 0 .kill (.node 0 .kill .kill))) (.node 1 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 2 (.node 1 (.node 0 .kill .kill) (.node 2 (.node 0 .kill .kill) (.node 1 (.node 6 (.node 1 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 2 (.node 0 .kill .kill) (.node 1 (.node 1 (.node 2 (.node 1 (.node 0 .kill .kill) (.node 2 (.node 0 .kill .kill) k15FareyCertC10)) (.node 0 .kill .kill)) .kill) (.node 0 .kill .kill))))))))))))))))))))))) (.node 1 (.node 0 (.node 0 (.node 0 (.node 0 .kill .kill) .kill) .kill) .kill) .kill)) (.node 0 .kill .kill)))) (.node 0 .kill .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)) (.node 0 .kill .kill))) (.node 0 .kill .kill)) (.node 0 .kill .kill)))))))) (.node 1 (.node 0 (.node 0 .kill .kill) .kill) (.node 0 .kill .kill)))))))) (.node 1 (.node 0 (.node 0 .kill .kill) .kill) (.node 0 .kill .kill)))))))))))) (.node 0 (.node 0 (.node 0 .kill .kill) .kill) .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) (.node 0 .kill .kill)))))))) (.node 1 (.node 0 (.node 0 .kill .kill) .kill) .kill)))) (.node 0 .kill .kill)) (.node 0 .kill .kill))))))))) (.node 0 (.node 0 .kill .kill) .kill)) .kill) .kill) (.node 0 .kill .kill)))))))))))

private def k15FareyCertC12 : FareyTree :=
  (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 3 (.node 1 .kill (.node 1 .kill (.node 1 .kill (.node 1 .kill (.node 1 .kill (.node 13 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill k15FareyCertC11)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (.node 1 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 .kill .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) (.node 0 .kill .kill)))))))) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)

def k15FareyCert : FareyTree :=
  (.node 1 .kill (.node 1 .kill (.node 6 .kill (.node 1 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 k15FareyCertC12 .kill) .kill) .kill) .kill) .kill) .kill) .kill))))

set_option maxRecDepth 400000 in
set_option maxHeartbeats 40000000 in
-- Kernel-only certificate check (`decide +kernel`, no `native_decide`):
-- evaluates the 4173-node Farey descent tree (depth 1547, hence the
-- `maxRecDepth` bump), including 945 exact 15th-power candidate
-- refutations on integers up to ~6022 bits (hence the `maxHeartbeats`
-- bump).  The `+kernel` variant bypasses the elaborator evaluator, whose
-- fixed C stack cannot hold the deep recursion of this tree; the proof
-- term and axioms are identical to plain `decide`.
theorem k15FareyCert_check :
    fareyCheck 4 97 1 13 2217 (11 * 10 ^ 120) k15EqRefuted 1 1 11 10 k15FareyCert =
      true := by
  decide +kernel

/--
**No `k = 15`, `N = 4` gap solution with `221 ≤ d < 10^120`** (extended
range; the headline `10^60` statement is
`no_gap_solution_four_fifteen_below`).  Composes the banked ratio window and
row-1 quotient confinement with the centered-Thue descent certificate.
-/
theorem no_gap_solution_four_fifteen_below_ext {n d : ℕ}
    (hd : 221 ≤ d) (hB : d < 10 ^ 120) :
    blockProduct 15 (n + d) ≠ 4 * blockProduct 15 n := by
  intro heq
  obtain ⟨hup, hlo⟩ := ratio_window_four_nat heq
  have hqd : 10 * d ≤ n + 1 := row_base_lower_k15 hd hup
  have hqd' : n + 1 < 11 * d := row_base_upper_k15 hlo
  have hn : 2209 ≤ n := by omega
  have hsol : K15CenteredEq (n + d + 8) (n + 8) := k15_centered_of_eq heq
  have hbl := k15_scaled_lower hn hlo
  have hbu := k15_scaled_upper hn hup
  have hYlo : 2217 ≤ n + 8 := by omega
  have hYmax : n + 8 ≤ 11 * 10 ^ 120 := by
    generalize hP : (10 : ℕ) ^ 120 = P at hB ⊢
    omega
  have hlow : (n + 8) * 1 + 1 ≤ (n + d + 8) * 1 := by omega
  have hhigh : (n + d + 8) * 10 + 1 ≤ (n + 8) * 11 := by omega
  exact fareyCheck_sound
    (Sol := fun X Y => K15CenteredEq X Y ∧
      109651 * Y < 100000 * X ∧ 100000 * X < 109714 * Y)
    (fun X Y h hS => k15EqRefuted_sound X Y h hS.1)
    (fun X Y hS h1 _h2 => k15_thue_window hS.1 hS.2.1 hS.2.2 h1)
    ⟨hsol, hbl, hbu⟩ hYlo hYmax (by omega)
    k15FareyCert 1 1 11 10 (by norm_num) k15FareyCert_check hlow hhigh

/--
**No `k = 15`, `N = 4` gap solution with `221 ≤ d < 10^60`.**  Together with
the banked `d ≤ 220` small-core certificate this closes `k = 15` up to the
tail `NoLargeGapSolutionFour 15 (10^60)`
(see `no_gap_solution_four_fifteen_of_tail`).
-/
theorem no_gap_solution_four_fifteen_below {n d : ℕ}
    (hd : 221 ≤ d) (hB : d < 10 ^ 60) :
    blockProduct 15 (n + d) ≠ 4 * blockProduct 15 n :=
  no_gap_solution_four_fifteen_below_ext hd
    (lt_of_lt_of_le hB (Nat.pow_le_pow_right (by norm_num) (by norm_num)))

/--
Conditional closure for `k = 15`, `d ≥ 221`: the certified strip
`221 ≤ d < 10^60` plus the tail hypothesis `NoLargeGapSolutionFour 15 (10^60)`
refute every gap solution with `d ≥ 221`.
-/
theorem no_gap_solution_four_fifteen_of_tail
    (htail : NoLargeGapSolutionFour 15 (10 ^ 60)) {n d : ℕ} (hd : 221 ≤ d) :
    blockProduct 15 (n + d) ≠ 4 * blockProduct 15 n := by
  rcases Nat.lt_or_ge d (10 ^ 60) with h | h
  · exact no_gap_solution_four_fifteen_below hd h
  · exact htail n d h

/-- Variant of `no_gap_solution_four_fifteen_of_tail` from the weaker tail at
`10^120` (the full certified range). -/
theorem no_gap_solution_four_fifteen_of_tail_ext
    (htail : NoLargeGapSolutionFour 15 (10 ^ 120)) {n d : ℕ} (hd : 221 ≤ d) :
    blockProduct 15 (n + d) ≠ 4 * blockProduct 15 n := by
  rcases Nat.lt_or_ge d (10 ^ 120) with h | h
  · exact no_gap_solution_four_fifteen_below_ext hd h
  · exact htail n d h

end Erdos686Variant

end Erdos686
