/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686ConvergentMachinery

/-!
# Erdős 686, k = 9: centered-Thue/convergent certificate

Instance of the Farey/Stern–Brocot descent machinery
(`Erdos686ConvergentMachinery`) for `k = 9`, `N = 4`, closing the gap
equation `(n+d+1)⋯(n+d+9) = 4·(n+1)⋯(n+9)` for all `221 ≤ d < 10^120`
(headline statement at `10^60`, matching the campaign tail interface).
Mathematics: `compute/theory/oddk_9/note.md` and
`compute/theory/odd_k_thue_synthesis.md`; certificate generated and
pre-verified by `compute/erdos686_thue_gen_lean.py` (cross-checked against
`compute/artifacts/thue_convergents_k9.json`).

The chain, entirely in integer arithmetic:

1. **Centering** (`k9_centered_of_eq`): with `X = n+d+5`, `Y = n+5` the
   equation is exactly `P₉(X) = 4·P₉(Y)` for
   `P₉(T) = T⁹ − 30T⁷ + 273T⁵ − 820T³ + 576T`,
   stated ℕ-safely (`K9CenteredEq`) as
   `X⁹ + 273X⁵ + 576X + 120Y⁷ + 3280Y³`
   `= 4Y⁹ + 1092Y⁵ + 2304Y + 30X⁷ + 820X³`.
2. **Ratio bracket** (`k9_scaled_lower/upper`): unlike the `k = 5` module
   (which extracted the bracket from the equation via a monotone scaled
   polynomial), here the bracket comes from the *banked ratio window*
   `4(n+1)⁹ ≤ (n+d+1)⁹`, `(n+d+9)⁹ ≤ 4(n+9)⁹` and the
   9th-power bracket facts `116652⁹ < 4·10^45 < 116653⁹`; the
   centered offsets are absorbed by `omega` using `Y ≥ 1109`, giving
   `116591·Y < 10⁵·X < 116714·Y`.
3. **Thue window** (`k9_thue_window`): `5·|X⁹ − 4Y⁹| ≤ 162·Y⁷`
   (constant `32.4`; certified sup over the bracket `≈ 32.143`, true
   value `≈ 31.82`).
4. **Handoff from the banked window**: `ratio_window_four_nat` +
   `row_base_lower_k9`/`row_base_upper_k9` give `5d ≤ n+1 < 7d` for
   `d ≥ 221`, hence `1109 ≤ Y ≤ 7·10^120` for `221 ≤ d < 10^120`.
   The `d = 1` telescope `P₉(8) = 4·P₉(7)` (i.e. `(n,d) = (2,1)`)
   solves the raw centered equation but has `Y = 7 < Ylo = 1109`, so it
   is skipped by the `Ylo` guard of every equality candidate (and
   `d = 1` is banked in the `d ≤ 220` branch anyway).
5. **Descent certificate** (`k9FareyCert`, `k9FareyCert_check`): a
   5341-node Farey tree rooted at `1/1 < 4^(1/9) < 6/5`; one kernel
   `decide` checks every side certificate, mediant multiple bound, and
   the 556 exact candidate refutations (`Y` up to `7·10^120`,
   ~3611-bit integers).  No `native_decide`.
-/

namespace Erdos686

namespace Erdos686Variant

/--
The exact centered equation for `k = 9`, `N = 4` in ℕ-safe form:
`X⁹ + 273X⁵ + 576X + 120Y⁷ + 3280Y³`
`= 4Y⁹ + 1092Y⁵ + 2304Y + 30X⁷ + 820X³`
⟺ `P₉(X) = 4·P₉(Y)` with
`P₉(T) = T⁹ − 30T⁷ + 273T⁵ − 820T³ + 576T`,
at `X = n+d+5`, `Y = n+5`.
-/
def K9CenteredEq (X Y : ℕ) : Prop :=
  X ^ 9 + 273 * X ^ 5 + 576 * X + 120 * Y ^ 7 + 3280 * Y ^ 3 =
    4 * Y ^ 9 + 1092 * Y ^ 5 + 2304 * Y + 30 * X ^ 7 + 820 * X ^ 3

/-- Boolean refuter for the exact centered equation (kernel-decidable). -/
def k9EqRefuted (X Y : ℕ) : Bool :=
  decide (X ^ 9 + 273 * X ^ 5 + 576 * X + 120 * Y ^ 7 + 3280 * Y ^ 3 ≠
    4 * Y ^ 9 + 1092 * Y ^ 5 + 2304 * Y + 30 * X ^ 7 + 820 * X ^ 3)

lemma k9EqRefuted_sound (X Y : ℕ) (h : k9EqRefuted X Y = true) :
    ¬ K9CenteredEq X Y := by
  intro hc
  exact (of_decide_eq_true h) hc

/-! ## Centering -/

private lemma blockProduct_nine_prod (x : ℕ) :
    blockProduct 9 x =
      (x + 1) * (x + 2) * (x + 3) * (x + 4) * (x + 5) * (x + 6) * (x + 7) * (x + 8) * (x + 9) := by
  norm_num [blockProduct, Finset.prod_Icc_succ_top, Finset.Icc_self,
    Finset.prod_singleton]

/-- The centered identity `∏_{i=1}^{9}(m+i) = P₉(m+5)` in additive ℕ form. -/
private lemma blockProduct_nine_centered (m : ℕ) :
    blockProduct 9 m + 30 * (m + 5) ^ 7 + 820 * (m + 5) ^ 3 =
      (m + 5) ^ 9 + 273 * (m + 5) ^ 5 + 576 * (m + 5) := by
  rw [blockProduct_nine_prod]; ring

/-- A gap solution satisfies the exact centered equation. -/
lemma k9_centered_of_eq {n d : ℕ}
    (heq : blockProduct 9 (n + d) = 4 * blockProduct 9 n) :
    K9CenteredEq (n + d + 5) (n + 5) := by
  have h1 := blockProduct_nine_centered (n + d)
  have h2 := blockProduct_nine_centered n
  unfold K9CenteredEq
  linarith

/-! ## Ratio bracket `116591/10⁵ < X/Y < 116714/10⁵` from the banked window

The banked window inequalities compare `k`-th powers at the row bases
`n+1` and `n+9`; a rational bracket of `4^(1/9)` at scale `10⁵`
(`116652⁹ < 4·10^45 < 116653⁹`) linearizes them, and `omega` absorbs
the centered-coordinate offsets using `Y = n+5 ≥ 1109` (banked confinement
for `d ≥ 221`). -/

/-- Scaled lower bracket from the banked lower window. -/
lemma k9_scaled_lower {n d : ℕ} (hn : 1104 ≤ n)
    (hlo : 4 * (n + 1) ^ 9 ≤ (n + d + 1) ^ 9) :
    116591 * (n + 5) < 100000 * (n + d + 5) := by
  have hAB : 116652 * (n + 1) < 100000 * (n + d + 1) := by
    by_contra hnot
    have hnot' : 100000 * (n + d + 1) ≤ 116652 * (n + 1) := Nat.le_of_not_lt hnot
    have hp : (100000 * (n + d + 1)) ^ 9 ≤ (116652 * (n + 1)) ^ 9 :=
      Nat.pow_le_pow_left hnot' 9
    rw [mul_pow, mul_pow] at hp
    have h1 : 4 * 100000 ^ 9 * (n + 1) ^ 9 ≤ 116652 ^ 9 * (n + 1) ^ 9 :=
      calc 4 * 100000 ^ 9 * (n + 1) ^ 9
          = 100000 ^ 9 * (4 * (n + 1) ^ 9) := by ring
        _ ≤ 100000 ^ 9 * (n + d + 1) ^ 9 := Nat.mul_le_mul (le_refl _) hlo
        _ ≤ 116652 ^ 9 * (n + 1) ^ 9 := hp
    have h2 : 0 < (n + 1) ^ 9 := pow_pos (by omega) 9
    exact absurd (Nat.le_of_mul_le_mul_right h1 h2) (by norm_num)
  omega

/-- Scaled upper bracket from the banked upper window. -/
lemma k9_scaled_upper {n d : ℕ} (hn : 1104 ≤ n)
    (hup : (n + d + 9) ^ 9 ≤ 4 * (n + 9) ^ 9) :
    100000 * (n + d + 5) < 116714 * (n + 5) := by
  have hCD : 100000 * (n + d + 9) < 116653 * (n + 9) := by
    by_contra hnot
    have hnot' : 116653 * (n + 9) ≤ 100000 * (n + d + 9) := Nat.le_of_not_lt hnot
    have hp : (116653 * (n + 9)) ^ 9 ≤ (100000 * (n + d + 9)) ^ 9 :=
      Nat.pow_le_pow_left hnot' 9
    rw [mul_pow, mul_pow] at hp
    have h1 : 116653 ^ 9 * (n + 9) ^ 9 ≤ 4 * 100000 ^ 9 * (n + 9) ^ 9 :=
      calc 116653 ^ 9 * (n + 9) ^ 9
          ≤ 100000 ^ 9 * (n + d + 9) ^ 9 := hp
        _ ≤ 100000 ^ 9 * (4 * (n + 9) ^ 9) := Nat.mul_le_mul (le_refl _) hup
        _ = 4 * 100000 ^ 9 * (n + 9) ^ 9 := by ring
    have h2 : 0 < (n + 9) ^ 9 := pow_pos (by omega) 9
    exact absurd (Nat.le_of_mul_le_mul_right h1 h2) (by norm_num)
  omega

/-! ## The Thue window `5·|X⁹ − 4Y⁹| ≤ 162·Y⁷` -/

set_option maxHeartbeats 4000000 in
-- The `nlinarith` bracket-power expansions (degree 7 products of 6-digit
-- scaled brackets) and the two ~21-fact `linarith` calls exceed the
-- default limit at this degree.
/--
Two-sided Thue window in the exact shape consumed by `fareyCheck_sound`
(`N = 4`, `cnum = 162`, `cden = 5`, `e = 7`): for any solution inside
the scaled bracket with `Y ≥ 1109`, `5·(4Y⁹) ≤ 5·X⁹ + 162·Y⁷` and
`5·X⁹ ≤ 5·(4Y⁹) + 162·Y⁷`.
-/
lemma k9_thue_window {X Y : ℕ} (hsol : K9CenteredEq X Y)
    (hbl : 116591 * Y < 100000 * X) (hbu : 100000 * X < 116714 * Y)
    (hY : 1109 ≤ Y) :
    5 * (4 * Y ^ 9) ≤ 5 * X ^ 9 + 162 * Y ^ 7 ∧
      5 * X ^ 9 ≤ 5 * (4 * Y ^ 9) + 162 * Y ^ 7 := by
  have hz :  (X : ℤ) ^ 9 + 273 * (X : ℤ) ^ 5 + 576 * (X : ℤ) + 120 * (Y : ℤ) ^ 7 + 3280 * (Y :
      ℤ) ^ 3 = 4 * (Y : ℤ) ^ 9 + 1092 * (Y : ℤ) ^ 5 + 2304 * (Y : ℤ) + 30 * (X : ℤ) ^ 7 + 820 *
      (X : ℤ) ^ 3 := by
    exact_mod_cast hsol
  have hblz : (116591 : ℤ) * Y ≤ 100000 * X := by exact_mod_cast hbl.le
  have hbuz : (100000 : ℤ) * X ≤ 116714 * Y := by exact_mod_cast hbu.le
  have hYz : (1109 : ℤ) ≤ (Y : ℤ) := by exact_mod_cast hY
  have hY0 : (0 : ℤ) ≤ (Y : ℤ) := Int.natCast_nonneg Y
  -- odd powers of the scaled bracket
  have hlo3 :
      (1584875244213071 : ℤ) * (Y : ℤ) ^ 3 ≤
        1000000000000000 * (X : ℤ) ^ 3 := by
    nlinarith [pow_le_pow_left₀ (by positivity : (0 : ℤ) ≤ 116591 * (Y : ℤ))
      hblz 3]
  have hhi3 :
      (1000000000000000 : ℤ) * (X : ℤ) ^ 3 ≤
        1589896525002344 * (Y : ℤ) ^ 3 := by
    nlinarith [pow_le_pow_left₀ (by positivity : (0 : ℤ) ≤ 100000 * (X : ℤ))
      hbuz 3]
  have hlo5 :
      (21543940267425799952603951 : ℤ) * (Y : ℤ) ^ 5 ≤
        10000000000000000000000000 * (X : ℤ) ^ 5 := by
    nlinarith [pow_le_pow_left₀ (by positivity : (0 : ℤ) ≤ 116591 * (Y : ℤ))
      hblz 5]
  have hhi5 :
      (10000000000000000000000000 : ℤ) * (X : ℤ) ^ 5 ≤
        21657821342893989237873824 * (Y : ℤ) ^ 5 := by
    nlinarith [pow_le_pow_left₀ (by positivity : (0 : ℤ) ≤ 100000 * (X : ℤ))
      hbuz 5]
  have hlo7 :
      (292856717865429397196173443046121231 : ℤ) * (Y : ℤ) ^ 7 ≤
        100000000000000000000000000000000000 * (X : ℤ) ^ 7 := by
    nlinarith [pow_le_pow_left₀ (by positivity : (0 : ℤ) ≤ 116591 * (Y : ℤ))
      hblz 7]
  have hhi7 :
      (100000000000000000000000000000000000 : ℤ) * (X : ℤ) ^ 7 ≤
        295026259850478544698243010065931904 * (Y : ℤ) ^ 7 := by
    nlinarith [pow_le_pow_left₀ (by positivity : (0 : ℤ) ≤ 100000 * (X : ℤ))
      hbuz 7]
  -- lower-degree absorption at `Y ≥ 1109`
  have hab1 :
      (1860326946952404841 : ℤ) * (Y : ℤ) ≤ (Y : ℤ) ^ 7 := by
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℤ) ≤ 1109) hYz 6,
      pow_nonneg hY0 1]
  have hab3 :
      (1512607274161 : ℤ) * (Y : ℤ) ^ 3 ≤ (Y : ℤ) ^ 7 := by
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℤ) ≤ 1109) hYz 4,
      pow_nonneg hY0 3]
  have hab5 :
      (1229881 : ℤ) * (Y : ℤ) ^ 5 ≤ (Y : ℤ) ^ 7 := by
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℤ) ≤ 1109) hYz 2,
      pow_nonneg hY0 5]
  have hpos1 : (0 : ℤ) ≤ (Y : ℤ) ^ 1 := by positivity
  have hpos3 : (0 : ℤ) ≤ (Y : ℤ) ^ 3 := by positivity
  have hpos5 : (0 : ℤ) ≤ (Y : ℤ) ^ 5 := by positivity
  have hpos7 : (0 : ℤ) ≤ (Y : ℤ) ^ 7 := by positivity
  constructor
  · have hgoal : 5 * (4 * (Y : ℤ) ^ 9) ≤
        5 * (X : ℤ) ^ 9 + 162 * (Y : ℤ) ^ 7 := by
      linarith [hz, hlo3, hhi3, hlo5, hhi5, hlo7, hhi7, hab1, hab3, hab5, hpos1, hpos3, hpos5,
        hpos7, hblz, hbuz]
    exact_mod_cast hgoal
  · have hgoal : 5 * (X : ℤ) ^ 9 ≤
        5 * (4 * (Y : ℤ) ^ 9) + 162 * (Y : ℤ) ^ 7 := by
      linarith [hz, hlo3, hhi3, hlo5, hhi5, hlo7, hhi7, hab1, hab3, hab5, hpos1, hpos3, hpos5,
        hpos7, hblz, hbuz]
    exact_mod_cast hgoal

/-! ## The descent certificate

Generated by `compute/erdos686_thue_gen_lean.py 120 9` (deterministic,
byte-stable); root Farey pair `1/1 < 4^(1/9) < 6/5`, `Ylo = 1109`,
`Ymax = 7·10^120`.  5341 nodes: 2670 mediant splits, 2669 side-certificate
kills, 2 `Ymax`-exits; 556 candidate pairs refuted by the exact equation.
Every convergent of `cf(4^(1/9))` with denominator `≤ 7·10^120` (233 of the
341 rows of `compute/artifacts/thue_convergents_k9.json`) occurs among the
mediants; determinants, straddle signs, and sign alternation are re-verified
by the generator before emission. -/

/- AUTOGENERATED by compute/erdos686_thue_gen_lean.py (YMAX_EXP=120).
   Farey/Stern-Brocot descent certificate for k = 9, N = 4:
   root pair 1/1 < 4^(1/9) < 6/5, Thue window 5*|X^9-4Y^9| <= 162*Y^7,
   Ylo = 1109, Ymax = 7 * 10^120.  Do not edit by hand. -/

-- generated single-line tree literals (repo precedent: Erdos154.lean)
set_option linter.style.longLine false

private def k9FareyCertC0 : FareyTree :=
  (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 1 (.node 1 .kill (.node 10 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 2 (.node 0 .kill .kill) (.node 1 (.node 0 (.node 0 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 1 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 1 (.node 1 .kill (.node 3 (.node 0 .kill .high) (.node 0 .high .kill))) (.node 0 .kill .kill))) .kill) .kill)) .kill) .kill) .kill) (.node 0 .kill .kill))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 .kill .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill))) (.node 0 .kill .kill)))))

private def k9FareyCertC1 : FareyTree :=
  (.node 0 (.node 0 (.node 0 (.node 1 (.node 2 (.node 0 .kill (.node 0 .kill .kill)) (.node 1 (.node 1 (.node 2 (.node 1 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 1 (.node 2 (.node 1 .kill (.node 0 .kill (.node 1 .kill (.node 5 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 2 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 2 (.node 0 .kill .kill) (.node 1 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 1 (.node 1 (.node 0 .kill .kill) (.node 2 (.node 1 .kill (.node 0 .kill (.node 1 .kill (.node 6 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 3 (.node 0 .kill (.node 0 .kill .kill)) (.node 1 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 2 (.node 1 (.node 0 .kill .kill) (.node 0 .kill k9FareyCertC0)) (.node 0 .kill .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) (.node 0 .kill .kill)))))))))))))))))))))))))))))))))))))))))))) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 .kill .kill) .kill) .kill) .kill) .kill) .kill))))) (.node 0 .kill .kill))) (.node 0 .kill .kill))) .kill) .kill) .kill) .kill) .kill) .kill)))))) (.node 0 (.node 0 .kill .kill) .kill))))))))))))))))))))))))) (.node 0 (.node 0 (.node 0 (.node 0 .kill .kill) .kill) .kill) .kill))))) (.node 0 .kill .kill)) (.node 0 .kill .kill))))))) (.node 0 .kill .kill)) .kill) .kill)) .kill) .kill) .kill) .kill)

private def k9FareyCertC2 : FareyTree :=
  (.node 0 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 2 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 3 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 4 (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill))) (.node 1 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 2 (.node 0 .kill (.node 0 .kill .kill)) (.node 0 (.node 0 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 1 (.node 4 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill)))) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 1 (.node 1 (.node 0 .kill .kill) (.node 3 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 2 (.node 1 .kill (.node 1 .kill (.node 3 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 1 (.node 5 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill)))) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 k9FareyCertC1 .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)) (.node 0 .kill .kill))))))))))) (.node 0 (.node 0 (.node 0 .kill .kill) .kill) .kill)))) (.node 0 .kill .kill))))))))))))))) (.node 0 (.node 0 (.node 0 .kill .kill) .kill) .kill))) (.node 0 .kill .kill))) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)) .kill)) .kill) .kill) .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)))))))))) (.node 0 (.node 0 (.node 0 .kill .kill) .kill) .kill))))))))) (.node 0 (.node 0 .kill .kill) .kill))) .kill) .kill)

private def k9FareyCertC3 : FareyTree :=
  (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 2 (.node 0 .kill (.node 0 .kill .kill)) (.node 0 (.node 0 (.node 1 (.node 2 (.node 0 .kill .kill) (.node 1 (.node 1 (.node 2 (.node 1 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 1 (.node 1 .kill (.node 1 (.node 0 .kill .kill) (.node 1 (.node 1 (.node 1 (.node 1 .kill (.node 1 .kill (.node 5 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 2 (.node 0 .kill .kill) (.node 1 (.node 0 (.node 0 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 1 (.node 1 (.node 1 .kill (.node 1 .kill (.node 3 (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill))) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 1 (.node 2 (.node 0 .kill .kill) (.node 1 (.node 1 (.node 1 (.node 1 .kill (.node 1 .kill (.node 2 (.node 0 .kill .kill) (.node 1 (.node 0 (.node 0 k9FareyCertC2 .kill) .kill) .kill)))) (.node 0 .kill .kill)) .kill) .kill)) .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)))) (.node 0 .kill .kill)) .kill)) .kill) .kill) .kill) (.node 0 .kill .kill)))))))))))))))))))))))))) (.node 0 (.node 0 (.node 0 (.node 0 .kill .kill) .kill) .kill) .kill)))) (.node 0 .kill .kill)) .kill) .kill))) (.node 0 .kill .kill)))))) (.node 0 .kill .kill)) .kill) .kill)) .kill) .kill) .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)

private def k9FareyCertC4 : FareyTree :=
  (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 3 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 1 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 1 (.node 3 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 1 (.node 1 (.node 0 .kill .kill) (.node 1 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 1 (.node 1 .kill (.node 2 (.node 0 .kill .kill) (.node 1 (.node 1 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 1 (.node 1 (.node 0 .kill .kill) (.node 1 (.node 9 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill)))))))) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 k9FareyCertC3 .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)) .kill)) (.node 0 .kill .kill))) .kill) .kill) .kill))) (.node 0 .kill .kill))) .kill) .kill)) (.node 0 .kill .kill))))))))))) (.node 0 (.node 0 .kill .kill) .kill)) .kill)) .kill) (.node 0 .kill .kill)))))))))))) (.node 0 (.node 0 (.node 0 .kill .kill) .kill) .kill))))))))))))))))))))))))))))))))))))))))

private def k9FareyCertC5 : FareyTree :=
  (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 3 (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill))) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 11 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill k9FareyCertC4))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 .kill .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)

private def k9FareyCertC6 : FareyTree :=
  (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 1 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 1 (.node 1 .kill (.node 3 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 1 (.node 1 (.node 10 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill))))))))) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 k9FareyCertC5 .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)) .kill) (.node 0 .kill .kill))))))))))) (.node 0 (.node 0 .kill .kill) .kill))) (.node 0 .kill .kill))) .kill) (.node 0 .kill .kill))))))))))))))))))))))))

private def k9FareyCertC7 : FareyTree :=
  (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 2 (.node 0 .kill (.node 0 .kill .kill)) (.node 0 (.node 0 (.node 1 (.node 5 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 1 (.node 1 .kill (.node 1 .kill (.node 1 (.node 1 .kill (.node 1 (.node 0 .kill .kill) (.node 1 (.node 1 (.node 3 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 1 (.node 1 .kill (.node 1 (.node 0 .kill .kill) (.node 1 (.node 1 (.node 8 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill k9FareyCertC6))))))))))))))))))))))))))))))))))))))))))))))))))))) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 .kill .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)) .kill) .kill))) (.node 0 .kill .kill))))))))))))))) (.node 0 (.node 0 (.node 0 .kill .kill) .kill) .kill)) .kill) .kill))) (.node 0 .kill .kill)))) (.node 0 .kill .kill))))))))))))))))))))))))))))) (.node 0 (.node 0 (.node 0 (.node 0 .kill .kill) .kill) .kill) .kill)) .kill) .kill) .kill)) .kill) .kill) .kill) .kill) .kill) .kill)

private def k9FareyCertC8 : FareyTree :=
  (.node 1 .kill (.node 1 (.node 1 (.node 1 .kill (.node 3 (.node 0 .kill (.node 0 .kill .kill)) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 2 (.node 1 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 1 (.node 1 (.node 0 .kill .kill) (.node 1 (.node 1 (.node 1 .kill (.node 1 .kill (.node 1 (.node 0 .kill .kill) (.node 1 (.node 1 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 3 (.node 0 .kill (.node 0 .kill .kill)) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 2 (.node 1 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 1 (.node 2 (.node 0 .kill .kill) (.node 1 (.node 1 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 1 (.node 2 (.node 0 .kill .kill) (.node 1 (.node 1 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 1 (.node 1 .kill (.node 3 (.node 0 .kill (.node 0 .kill .kill)) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 2 (.node 1 (.node 0 .kill .kill) (.node 1 .kill (.node 1 .kill (.node 5 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 5 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill)))) (.node 1 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 k9FareyCertC7 .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)))))))))))))))))))))))))) (.node 0 (.node 0 (.node 0 (.node 0 .kill .kill) .kill) .kill) .kill))))) (.node 0 .kill .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill))) (.node 0 .kill .kill))) .kill) .kill) .kill)) .kill)) .kill) .kill) .kill)) (.node 0 .kill .kill)))))))) (.node 0 .kill .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill))) .kill) .kill) .kill)))) (.node 0 .kill .kill)) .kill)) (.node 0 .kill .kill)))))))) (.node 0 .kill .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill))) (.node 0 .kill .kill)) (.node 0 .kill .kill)))

private def k9FareyCertC9 : FareyTree :=
  (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 1 .kill (.node 1 (.node 1 .kill (.node 3 (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill))) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 2 (.node 0 .kill (.node 0 .kill .kill)) (.node 0 (.node 1 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 3 (.node 0 .kill (.node 0 .kill .kill)) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 1 (.node 3 (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill))) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 1 (.node 1 (.node 0 .kill .kill) (.node 1 (.node 1 .kill (.node 6 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 2 (.node 0 .kill .kill) (.node 1 (.node 1 (.node 1 (.node 2 (.node 0 .kill (.node 0 .kill .kill)) (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 2 (.node 0 .kill (.node 0 .kill .kill)) (.node 0 (.node 0 (.node 0 (.node 1 (.node 2 (.node 1 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill k9FareyCertC8))))) (.node 0 .kill .kill)) .kill) .kill) .kill) .kill)) .kill) .kill) .kill) .kill) .kill)) .kill) .kill) (.node 0 .kill .kill))))))))))))))))))))))))))))))))))))))))) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 .kill .kill) .kill) .kill) .kill) .kill) .kill))) (.node 0 .kill .kill))) (.node 0 .kill .kill))) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)) .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill))) .kill) .kill) .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill))) (.node 0 .kill .kill)))) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)

private def k9FareyCertC10 : FareyTree :=
  (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 1 (.node 1 (.node 0 .kill .kill) (.node 1 (.node 2 (.node 0 .kill .kill) (.node 0 (.node 0 (.node 0 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 1 (.node 1 (.node 0 .kill .kill) (.node 1 (.node 3 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 4 (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill))) (.node 1 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 2 (.node 1 .kill (.node 1 .kill (.node 1 .kill (.node 1 (.node 2 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 1 (.node 1 (.node 1 .kill (.node 1 (.node 0 .kill .kill) (.node 1 (.node 1 (.node 5 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill)))) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 4 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill)))) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 3 (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill))) k9FareyCertC9) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)) .kill) .kill))) (.node 0 .kill .kill)) (.node 0 .kill .kill))))))) (.node 0 .kill .kill)) (.node 0 .kill .kill))))) (.node 0 .kill .kill))) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill))))))))))) (.node 0 (.node 0 .kill .kill) .kill)) .kill)) (.node 0 .kill .kill))) .kill) .kill) .kill) .kill)) .kill)) .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)

private def k9FareyCertC11 : FareyTree :=
  (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 6 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 9 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill)))))))) (.node 1 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 k9FareyCertC10 .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill))))))))))))))))))))))))))))))))))) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 .kill .kill) .kill) .kill) .kill) .kill) .kill)))))))))

private def k9FareyCertC12 : FareyTree :=
  (.node 1 (.node 0 .kill .kill) (.node 1 (.node 6 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill))))) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 2 (.node 0 .kill (.node 0 .kill .kill)) (.node 0 (.node 0 (.node 0 (.node 1 (.node 6 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill)))))) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 2 (.node 0 .kill (.node 0 .kill .kill)) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 3 (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill))) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 2 (.node 0 .kill (.node 0 .kill .kill)) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 1 (.node 4 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill k9FareyCertC11)))))))))) (.node 0 (.node 0 (.node 0 .kill .kill) .kill) .kill)) .kill)) .kill) .kill) .kill) .kill) .kill) .kill))) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)) .kill) .kill) .kill) .kill) .kill) .kill))) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)) .kill) .kill) .kill) .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)) .kill))

private def k9FareyCertC13 : FareyTree :=
  (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 3 (.node 0 .kill (.node 0 .kill .kill)) (.node 1 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 1 (.node 0 .kill .kill) (.node 1 (.node 1 k9FareyCertC12 .kill) .kill))) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) (.node 0 .kill .kill))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private def k9FareyCertC14 : FareyTree :=
  (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 2 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 1 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 14 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill k9FareyCertC13))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 .kill .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill))) (.node 0 .kill .kill)) (.node 0 .kill .kill))))))) (.node 0 .kill .kill))) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)

private def k9FareyCertC15 : FareyTree :=
  (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 k9FareyCertC14 .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)

private def k9FareyCertC16 : FareyTree :=
  (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 k9FareyCertC15 .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)

private def k9FareyCertC17 : FareyTree :=
  (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 1 (.node 1 .kill (.node 19 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill)))))))))))))))))) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 k9FareyCertC16 .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill))) (.node 0 .kill .kill)))))))))))))))))

private def k9FareyCertC18 : FareyTree :=
  (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill k9FareyCertC17)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

def k9FareyCert : FareyTree :=
  (.node 14 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill k9FareyCertC18))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) .kill)

set_option maxRecDepth 400000 in
set_option maxHeartbeats 40000000 in
-- Kernel-only certificate check (`decide +kernel`, no `native_decide`):
-- evaluates the 5341-node Farey descent tree (depth 2327, hence the
-- `maxRecDepth` bump), including 556 exact 9th-power candidate
-- refutations on integers up to ~3611 bits (hence the `maxHeartbeats`
-- bump).  The `+kernel` variant bypasses the elaborator evaluator, whose
-- fixed C stack cannot hold the deep recursion of this tree; the proof
-- term and axioms are identical to plain `decide`.
theorem k9FareyCert_check :
    fareyCheck 4 162 5 7 1109 (7 * 10 ^ 120) k9EqRefuted 1 1 6 5 k9FareyCert =
      true := by
  decide +kernel

/--
**No `k = 9`, `N = 4` gap solution with `221 ≤ d < 10^120`** (extended
range; the headline `10^60` statement is
`no_gap_solution_four_nine_below`).  Composes the banked ratio window and
row-1 quotient confinement with the centered-Thue descent certificate.
-/
theorem no_gap_solution_four_nine_below_ext {n d : ℕ}
    (hd : 221 ≤ d) (hB : d < 10 ^ 120) :
    blockProduct 9 (n + d) ≠ 4 * blockProduct 9 n := by
  intro heq
  obtain ⟨hup, hlo⟩ := ratio_window_four_nat heq
  have hqd : 5 * d ≤ n + 1 := row_base_lower_k9 hd hup
  have hqd' : n + 1 < 7 * d := row_base_upper_k9 hlo
  have hn : 1104 ≤ n := by omega
  have hsol : K9CenteredEq (n + d + 5) (n + 5) := k9_centered_of_eq heq
  have hbl := k9_scaled_lower hn hlo
  have hbu := k9_scaled_upper hn hup
  have hYlo : 1109 ≤ n + 5 := by omega
  have hYmax : n + 5 ≤ 7 * 10 ^ 120 := by
    generalize hP : (10 : ℕ) ^ 120 = P at hB ⊢
    omega
  have hlow : (n + 5) * 1 + 1 ≤ (n + d + 5) * 1 := by omega
  have hhigh : (n + d + 5) * 5 + 1 ≤ (n + 5) * 6 := by omega
  exact fareyCheck_sound
    (Sol := fun X Y => K9CenteredEq X Y ∧
      116591 * Y < 100000 * X ∧ 100000 * X < 116714 * Y)
    (fun X Y h hS => k9EqRefuted_sound X Y h hS.1)
    (fun X Y hS h1 _h2 => k9_thue_window hS.1 hS.2.1 hS.2.2 h1)
    ⟨hsol, hbl, hbu⟩ hYlo hYmax (by omega)
    k9FareyCert 1 1 6 5 (by norm_num) k9FareyCert_check hlow hhigh

/--
**No `k = 9`, `N = 4` gap solution with `221 ≤ d < 10^60`.**  Together with
the banked `d ≤ 220` small-core certificate this closes `k = 9` up to the
tail `NoLargeGapSolutionFour 9 (10^60)`
(see `no_gap_solution_four_nine_of_tail`).
-/
theorem no_gap_solution_four_nine_below {n d : ℕ}
    (hd : 221 ≤ d) (hB : d < 10 ^ 60) :
    blockProduct 9 (n + d) ≠ 4 * blockProduct 9 n :=
  no_gap_solution_four_nine_below_ext hd
    (lt_of_lt_of_le hB (Nat.pow_le_pow_right (by norm_num) (by norm_num)))

/--
Conditional closure for `k = 9`, `d ≥ 221`: the certified strip
`221 ≤ d < 10^60` plus the tail hypothesis `NoLargeGapSolutionFour 9 (10^60)`
refute every gap solution with `d ≥ 221`.
-/
theorem no_gap_solution_four_nine_of_tail
    (htail : NoLargeGapSolutionFour 9 (10 ^ 60)) {n d : ℕ} (hd : 221 ≤ d) :
    blockProduct 9 (n + d) ≠ 4 * blockProduct 9 n := by
  rcases Nat.lt_or_ge d (10 ^ 60) with h | h
  · exact no_gap_solution_four_nine_below hd h
  · exact htail n d h

/-- Variant of `no_gap_solution_four_nine_of_tail` from the weaker tail at
`10^120` (the full certified range). -/
theorem no_gap_solution_four_nine_of_tail_ext
    (htail : NoLargeGapSolutionFour 9 (10 ^ 120)) {n d : ℕ} (hd : 221 ≤ d) :
    blockProduct 9 (n + d) ≠ 4 * blockProduct 9 n := by
  rcases Nat.lt_or_ge d (10 ^ 120) with h | h
  · exact no_gap_solution_four_nine_below_ext hd h
  · exact htail n d h

end Erdos686Variant

end Erdos686
