/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686ConvergentMachinery

/-!
# Erdős 686, k = 7: centered-Thue/convergent certificate

Instance of the Farey/Stern–Brocot descent machinery
(`Erdos686ConvergentMachinery`) for `k = 7`, `N = 4`, closing the gap
equation `(n+d+1)⋯(n+d+7) = 4·(n+1)⋯(n+7)` for all `221 ≤ d < 10^120`
(headline statement at `10^60`, matching the campaign tail interface).
Mathematics: `compute/theory/oddk_7/note.md` and
`compute/theory/odd_k_thue_synthesis.md`; certificate generated and
pre-verified by `compute/erdos686_thue_gen_lean.py` (cross-checked against
`compute/artifacts/thue_convergents_k7.json`).

The chain, entirely in integer arithmetic:

1. **Centering** (`k7_centered_of_eq`): with `X = n+d+4`, `Y = n+4` the
   equation is exactly `P₇(X) = 4·P₇(Y)` for
   `P₇(T) = T⁷ − 14T⁵ + 49T³ − 36T`, stated ℕ-safely as
   `X⁷ + 49X³ + 56Y⁵ + 144Y = 4Y⁷ + 196Y³ + 14X⁵ + 36X` (`K7CenteredEq`).
2. **Ratio bracket** (`k7_scaled_lower/upper`): unlike the `k = 5` module
   (which extracted the bracket from the equation via a monotone scaled
   polynomial), here the bracket comes from the *banked ratio window*
   `4(n+1)⁷ ≤ (n+d+1)⁷`, `(n+d+7)⁷ ≤ 4(n+7)⁷` and the 7th-power bracket
   facts `121901⁷ < 4·10^35 < 121902⁷`; the centered offsets are absorbed
   by `omega` using `Y ≥ 887`, giving
   `121826·Y < 10⁵·X < 121977·Y`.
3. **Thue window** (`k7_thue_window`): `5·|X⁷ − 4Y⁷| ≤ 93·Y⁵`
   (constant `18.6`; certified sup over the bracket `≈ 18.432`, true
   value `≈ 18.32`).
4. **Handoff from the banked window**: `ratio_window_four_nat` +
   `row_base_lower_k7`/`row_base_upper_k7` give `4d ≤ n+1 < 5d` for
   `d ≥ 221`, hence `887 ≤ Y ≤ 5·10^120` for `221 ≤ d < 10^120`.
5. **Descent certificate** (`k7FareyCert`, `k7FareyCert_check`): a
   7307-node Farey tree rooted at `1/1 < 4^(1/7) < 5/4`; one kernel
   `decide` checks every side certificate, mediant multiple bound, and
   the 445 exact candidate refutations (`Y` up to `5·10^120`,
   ~2800-bit integers).  No `native_decide`.
-/

namespace Erdos686

namespace Erdos686Variant

/--
The exact centered equation for `k = 7`, `N = 4` in ℕ-safe form:
`X⁷ + 49X³ + 56Y⁵ + 144Y = 4Y⁷ + 196Y³ + 14X⁵ + 36X` ⟺ `P₇(X) = 4·P₇(Y)`
with `P₇(T) = T⁷ − 14T⁵ + 49T³ − 36T`, at `X = n+d+4`, `Y = n+4`.
-/
def K7CenteredEq (X Y : ℕ) : Prop :=
  X ^ 7 + 49 * X ^ 3 + 56 * Y ^ 5 + 144 * Y =
    4 * Y ^ 7 + 196 * Y ^ 3 + 14 * X ^ 5 + 36 * X

/-- Boolean refuter for the exact centered equation (kernel-decidable). -/
def k7EqRefuted (X Y : ℕ) : Bool :=
  decide (X ^ 7 + 49 * X ^ 3 + 56 * Y ^ 5 + 144 * Y ≠
    4 * Y ^ 7 + 196 * Y ^ 3 + 14 * X ^ 5 + 36 * X)

lemma k7EqRefuted_sound (X Y : ℕ) (h : k7EqRefuted X Y = true) :
    ¬ K7CenteredEq X Y := by
  intro hc
  exact (of_decide_eq_true h) hc

/-! ## Centering -/

private lemma blockProduct_seven_prod (x : ℕ) :
    blockProduct 7 x =
      (x + 1) * (x + 2) * (x + 3) * (x + 4) * (x + 5) * (x + 6) * (x + 7) := by
  norm_num [blockProduct, Finset.prod_Icc_succ_top, Finset.Icc_self,
    Finset.prod_singleton]

/-- The centered identity `∏_{i=1}^{7}(m+i) = P₇(m+4)` in additive ℕ form. -/
private lemma blockProduct_seven_centered (m : ℕ) :
    blockProduct 7 m + 14 * (m + 4) ^ 5 + 36 * (m + 4) =
      (m + 4) ^ 7 + 49 * (m + 4) ^ 3 := by
  rw [blockProduct_seven_prod]; ring

/-- A gap solution satisfies the exact centered equation. -/
lemma k7_centered_of_eq {n d : ℕ}
    (heq : blockProduct 7 (n + d) = 4 * blockProduct 7 n) :
    K7CenteredEq (n + d + 4) (n + 4) := by
  have h1 := blockProduct_seven_centered (n + d)
  have h2 := blockProduct_seven_centered n
  unfold K7CenteredEq
  linarith

/-! ## Ratio bracket `121826/10⁵ < X/Y < 121977/10⁵` from the banked window

The banked window inequalities compare `k`-th powers at the row bases
`n+1` and `n+7`; a rational bracket of `4^(1/7)` at scale `10⁵`
(`121901⁷ < 4·10^35 < 121902⁷`) linearizes them, and `omega` absorbs the
centered-coordinate offsets using `Y = n+4 ≥ 887` (banked confinement for
`d ≥ 221`). -/

/-- Scaled lower bracket from the banked lower window. -/
lemma k7_scaled_lower {n d : ℕ} (hn : 883 ≤ n)
    (hlo : 4 * (n + 1) ^ 7 ≤ (n + d + 1) ^ 7) :
    121826 * (n + 4) < 100000 * (n + d + 4) := by
  have hAB : 121901 * (n + 1) < 100000 * (n + d + 1) := by
    by_contra hnot
    have hnot' : 100000 * (n + d + 1) ≤ 121901 * (n + 1) := Nat.le_of_not_lt hnot
    have hp : (100000 * (n + d + 1)) ^ 7 ≤ (121901 * (n + 1)) ^ 7 :=
      Nat.pow_le_pow_left hnot' 7
    rw [mul_pow, mul_pow] at hp
    have h1 : 4 * 100000 ^ 7 * (n + 1) ^ 7 ≤ 121901 ^ 7 * (n + 1) ^ 7 :=
      calc 4 * 100000 ^ 7 * (n + 1) ^ 7
          = 100000 ^ 7 * (4 * (n + 1) ^ 7) := by ring
        _ ≤ 100000 ^ 7 * (n + d + 1) ^ 7 := Nat.mul_le_mul (le_refl _) hlo
        _ ≤ 121901 ^ 7 * (n + 1) ^ 7 := hp
    have h2 : 0 < (n + 1) ^ 7 := pow_pos (by omega) 7
    exact absurd (Nat.le_of_mul_le_mul_right h1 h2) (by norm_num)
  omega

/-- Scaled upper bracket from the banked upper window. -/
lemma k7_scaled_upper {n d : ℕ} (hn : 883 ≤ n)
    (hup : (n + d + 7) ^ 7 ≤ 4 * (n + 7) ^ 7) :
    100000 * (n + d + 4) < 121977 * (n + 4) := by
  have hCD : 100000 * (n + d + 7) < 121902 * (n + 7) := by
    by_contra hnot
    have hnot' : 121902 * (n + 7) ≤ 100000 * (n + d + 7) := Nat.le_of_not_lt hnot
    have hp : (121902 * (n + 7)) ^ 7 ≤ (100000 * (n + d + 7)) ^ 7 :=
      Nat.pow_le_pow_left hnot' 7
    rw [mul_pow, mul_pow] at hp
    have h1 : 121902 ^ 7 * (n + 7) ^ 7 ≤ 4 * 100000 ^ 7 * (n + 7) ^ 7 :=
      calc 121902 ^ 7 * (n + 7) ^ 7
          ≤ 100000 ^ 7 * (n + d + 7) ^ 7 := hp
        _ ≤ 100000 ^ 7 * (4 * (n + 7) ^ 7) := Nat.mul_le_mul (le_refl _) hup
        _ = 4 * 100000 ^ 7 * (n + 7) ^ 7 := by ring
    have h2 : 0 < (n + 7) ^ 7 := pow_pos (by omega) 7
    exact absurd (Nat.le_of_mul_le_mul_right h1 h2) (by norm_num)
  omega

/-! ## The Thue window `5·|X⁷ − 4Y⁷| ≤ 93·Y⁵` -/

/--
Two-sided Thue window in the exact shape consumed by `fareyCheck_sound`
(`N = 4`, `cnum = 93`, `cden = 5`, `e = 5`): for any solution inside the
scaled bracket with `Y ≥ 887`, `5·(4Y⁷) ≤ 5X⁷ + 93Y⁵` and
`5X⁷ ≤ 5·(4Y⁷) + 93Y⁵`.
-/
lemma k7_thue_window {X Y : ℕ} (hsol : K7CenteredEq X Y)
    (hbl : 121826 * Y < 100000 * X) (hbu : 100000 * X < 121977 * Y)
    (hY : 887 ≤ Y) :
    5 * (4 * Y ^ 7) ≤ 5 * X ^ 7 + 93 * Y ^ 5 ∧
      5 * X ^ 7 ≤ 5 * (4 * Y ^ 7) + 93 * Y ^ 5 := by
  have hz : (X : ℤ) ^ 7 + 49 * (X : ℤ) ^ 3 + 56 * (Y : ℤ) ^ 5 + 144 * Y =
      4 * (Y : ℤ) ^ 7 + 196 * (Y : ℤ) ^ 3 + 14 * (X : ℤ) ^ 5 + 36 * X := by
    exact_mod_cast hsol
  have hblz : (121826 : ℤ) * Y ≤ 100000 * X := by exact_mod_cast hbl.le
  have hbuz : (100000 : ℤ) * X ≤ 121977 * Y := by exact_mod_cast hbu.le
  have hYz : (887 : ℤ) ≤ (Y : ℤ) := by exact_mod_cast hY
  have hY0 : (0 : ℤ) ≤ (Y : ℤ) := Int.natCast_nonneg Y
  -- odd powers of the scaled bracket
  have hlo3 : (1808089627747976 : ℤ) * (Y : ℤ) ^ 3 ≤
      1000000000000000 * (X : ℤ) ^ 3 := by
    nlinarith [pow_le_pow_left₀ (by positivity : (0 : ℤ) ≤ 121826 * (Y : ℤ))
      hblz 3]
  have hhi3 : (1000000000000000 : ℤ) * (X : ℤ) ^ 3 ≤
      1814821197601833 * (Y : ℤ) ^ 3 := by
    nlinarith [pow_le_pow_left₀ (by positivity : (0 : ℤ) ≤ 100000 * (X : ℤ))
      hbuz 3]
  have hlo5 : (26834896507886776412665376 : ℤ) * (Y : ℤ) ^ 5 ≤
      10000000000000000000000000 * (X : ℤ) ^ 5 := by
    nlinarith [pow_le_pow_left₀ (by positivity : (0 : ℤ) ≤ 121826 * (Y : ℤ))
      hblz 5]
  have hhi5 : (10000000000000000000000000 : ℤ) * (X : ℤ) ^ 5 ≤
      27001614888585154416573657 * (Y : ℤ) ^ 5 := by
    nlinarith [pow_le_pow_left₀ (by positivity : (0 : ℤ) ≤ 100000 * (X : ℤ))
      hbuz 5]
  -- lower-degree absorption at `Y ≥ 887`
  have hab1 : (619005459361 : ℤ) * (Y : ℤ) ≤ (Y : ℤ) ^ 5 := by
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℤ) ≤ 887) hYz 4,
      pow_nonneg hY0 1]
  have hab3 : (786769 : ℤ) * (Y : ℤ) ^ 3 ≤ (Y : ℤ) ^ 5 := by
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℤ) ≤ 887) hYz 2,
      pow_nonneg hY0 3]
  have hpos1 : (0 : ℤ) ≤ (Y : ℤ) ^ 1 := by positivity
  have hpos3 : (0 : ℤ) ≤ (Y : ℤ) ^ 3 := by positivity
  have hpos5 : (0 : ℤ) ≤ (Y : ℤ) ^ 5 := by positivity
  constructor
  · have hgoal : 5 * (4 * (Y : ℤ) ^ 7) ≤ 5 * (X : ℤ) ^ 7 + 93 * (Y : ℤ) ^ 5 := by
      linarith [hz, hhi3, hlo5, hblz, hab1, hab3, hpos1, hpos3, hpos5]
    exact_mod_cast hgoal
  · have hgoal : 5 * (X : ℤ) ^ 7 ≤ 5 * (4 * (Y : ℤ) ^ 7) + 93 * (Y : ℤ) ^ 5 := by
      linarith [hz, hhi5, hlo3, hbuz, hab1, hab3, hpos1, hpos3, hpos5]
    exact_mod_cast hgoal

/-! ## The descent certificate

Generated by `compute/erdos686_thue_gen_lean.py 120 7` (deterministic,
byte-stable); root Farey pair `1/1 < 4^(1/7) < 5/4`, `Ylo = 887`,
`Ymax = 5\u00b710^120`.  7307 nodes: 3653 mediant splits, 3651 side-certificate
kills, 3 `Ymax`-exits; 445 candidate pairs refuted by the exact equation.
Every convergent of `cf(4^(1/7))` with denominator `\u2264 5\u00b710^120` (227 of the
341 rows of `compute/artifacts/thue_convergents_k7.json`) occurs among the
mediants; determinants, straddle signs, and sign alternation are re-verified
by the generator before emission. -/

/- AUTOGENERATED by compute/erdos686_thue_gen_lean.py (YMAX_EXP=120).
   Farey/Stern-Brocot descent certificate for k = 7, N = 4:
   root pair 1/1 < 4^(1/7) < 5/4, Thue window 5*|X^7-4Y^7| <= 93*Y^5,
   Ylo = 887, Ymax = 5 * 10^120.  Do not edit by hand. -/

-- generated single-line tree literals (repo precedent: Erdos154.lean)
set_option linter.style.longLine false

private def k7FareyCertC0 : FareyTree :=
  (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 1 (.node 0 .kill .kill) (.node 0 (.node 1 (.node 3 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 2 (.node 0 .kill .kill) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 1 (.node 1 .kill (.node 1 .kill (.node 1 (.node 1 (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 1 (.node 0 .kill (.node 1 .kill (.node 1 (.node 2 (.node 0 .kill .kill) (.node 0 (.node 0 (.node 0 (.node 1 (.node 1 .kill (.node 1 .kill (.node 1 (.node 3 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 1 (.node 3 (.node 0 .kill (.node 0 .kill .kill)) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 0 (.node 0 (.node 1 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 0 (.node 0 (.node 1 (.node 1 .kill (.node 1 .kill (.node 1 (.node 1 (.node 0 .kill .kill) (.node 0 (.node 0 (.node 1 (.node 0 .kill (.node 0 .kill (.node 1 .high (.node 12 .high .high)))) (.node 0 .kill .kill)) .kill) .kill)) .kill))) .kill) .kill) .kill))))) (.node 0 .kill .kill)) .kill) .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)) (.node 0 .kill .kill)))))))))))))))))))) (.node 0 (.node 0 (.node 0 .kill .kill) .kill) .kill)) .kill))) .kill) .kill) .kill) .kill)) .kill))) (.node 0 .kill .kill))))) (.node 0 .kill .kill)) .kill))) (.node 0 .kill .kill))) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)))))))))))))))))) (.node 0 (.node 0 (.node 0 .kill .kill) .kill) .kill)) .kill) .kill))) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)

private def k7FareyCertC1 : FareyTree :=
  (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 1 (.node 1 (.node 3 (.node 0 .kill (.node 0 .kill .kill)) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 3 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 1 (.node 1 (.node 1 .kill (.node 1 (.node 0 .kill (.node 1 .kill (.node 1 (.node 1 .kill (.node 4 (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill))) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 2 (.node 0 .kill (.node 0 .kill .kill)) (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 2 (.node 0 .kill (.node 0 .kill .kill)) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 3 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 4 (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill))) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 k7FareyCertC0 .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)))))))))))))) (.node 0 (.node 0 .kill .kill) .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill)) .kill) .kill) .kill) .kill) .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill))) (.node 0 .kill .kill)))) (.node 0 .kill .kill))) .kill) (.node 0 .kill .kill))))))))))))))) (.node 0 (.node 0 .kill .kill) .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)) .kill) (.node 0 .kill .kill))))))))))))))))))))))

private def k7FareyCertC2 : FareyTree :=
  (.node 0 .kill (.node 2 (.node 0 .kill .kill) (.node 0 (.node 0 (.node 0 (.node 1 (.node 2 (.node 0 .kill (.node 0 .kill .kill)) (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 1 .kill (.node 1 .kill (.node 3 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 1 (.node 1 (.node 0 .kill .kill) (.node 1 (.node 1 (.node 1 .kill (.node 1 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 1 (.node 1 (.node 5 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 7 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill k7FareyCertC1))))))))))))))))))))))))))))))))))))))))))) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 .kill .kill) .kill) .kill) .kill) .kill) .kill) .kill))))))))))))))))))))))))))))))))))))))) (.node 0 (.node 0 (.node 0 (.node 0 .kill .kill) .kill) .kill) .kill)) .kill) .kill))))) (.node 0 .kill .kill))) .kill) .kill)) (.node 0 .kill .kill)))))))))))) (.node 0 (.node 0 .kill .kill) .kill)))) .kill) .kill) .kill) .kill) .kill)) .kill) .kill) .kill) .kill)))

private def k7FareyCertC3 : FareyTree :=
  (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 1 (.node 1 .kill (.node 1 (.node 1 .kill (.node 3 (.node 0 .kill (.node 0 .kill .kill)) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 4 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill)))) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 1 .kill (.node 0 .kill (.node 0 .kill (.node 2 (.node 0 .kill .kill) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 1 (.node 0 .kill .kill) (.node 0 (.node 1 (.node 3 (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill))) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 4 (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill))) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 1 (.node 1 .kill (.node 2 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill k7FareyCertC2))))))) (.node 0 (.node 0 .kill .kill) .kill))) (.node 0 .kill .kill)))))) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill))) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)) .kill) .kill))) .kill) .kill) .kill) .kill) .kill) .kill))))) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill))) (.node 0 .kill .kill))) (.node 0 .kill .kill))))))

private def k7FareyCertC4 : FareyTree :=
  (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 1 (.node 0 (.node 0 (.node 1 (.node 1 .kill (.node 1 (.node 0 .kill .kill) (.node 0 (.node 1 (.node 2 (.node 0 .kill (.node 0 .kill .kill)) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 1 (.node 0 .kill .kill) (.node 1 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 1 (.node 2 (.node 0 .kill k7FareyCertC3) (.node 0 .kill .kill)) .kill)) .kill) .kill))) .kill) .kill) .kill) .kill) .kill) .kill) .kill)) .kill) .kill))) .kill) .kill) .kill) (.node 0 .kill .kill)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private def k7FareyCertC5 : FareyTree :=
  (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill k7FareyCertC4)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private def k7FareyCertC6 : FareyTree :=
  (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill k7FareyCertC5)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private def k7FareyCertC7 : FareyTree :=
  (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill k7FareyCertC6)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private def k7FareyCertC8 : FareyTree :=
  (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill k7FareyCertC7)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private def k7FareyCertC9 : FareyTree :=
  (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill k7FareyCertC8)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private def k7FareyCertC10 : FareyTree :=
  (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill k7FareyCertC9)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private def k7FareyCertC11 : FareyTree :=
  (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill k7FareyCertC10)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private def k7FareyCertC12 : FareyTree :=
  (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill k7FareyCertC11)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private def k7FareyCertC13 : FareyTree :=
  (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill k7FareyCertC12)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private def k7FareyCertC14 : FareyTree :=
  (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill k7FareyCertC13)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private def k7FareyCertC15 : FareyTree :=
  (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill k7FareyCertC14)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private def k7FareyCertC16 : FareyTree :=
  (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill k7FareyCertC15)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private def k7FareyCertC17 : FareyTree :=
  (.node 0 .kill (.node 1 .kill (.node 36 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill k7FareyCertC16)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 .kill .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill))))

private def k7FareyCertC18 : FareyTree :=
  (.node 1 .kill (.node 1 (.node 1 (.node 0 .kill .kill) (.node 1 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 1 (.node 1 .kill (.node 6 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 2 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 1 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 1 (.node 2 (.node 0 .kill .kill) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 2 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 1 (.node 0 .kill (.node 1 .kill (.node 1 (.node 1 .kill (.node 2 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 3 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 2 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 0 (.node 0 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 1 (.node 1 (.node 0 .kill k7FareyCertC17) (.node 0 .kill .kill)) .kill)) .kill) .kill) .kill))))) (.node 0 .kill .kill)))))))))))))) (.node 0 (.node 0 (.node 0 .kill .kill) .kill) .kill)))))))) (.node 0 (.node 0 .kill .kill) .kill))) (.node 0 .kill .kill)))) (.node 0 .kill .kill))))))) (.node 0 .kill .kill)) .kill) .kill) .kill) .kill) .kill)) .kill)) .kill) .kill))))) (.node 0 (.node 0 .kill .kill) .kill)))))))))))))))))))))))))))))))))))))))))))))))))))))) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 .kill .kill) .kill) .kill) .kill) .kill) .kill))) (.node 0 .kill .kill))) .kill) .kill)) (.node 0 .kill .kill)))

private def k7FareyCertC19 : FareyTree :=
  (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 2 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 1 (.node 4 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 1 (.node 0 (.node 0 (.node 1 (.node 1 .kill (.node 1 (.node 0 .kill .kill) (.node 0 (.node 0 (.node 0 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 3 (.node 0 .kill (.node 0 .kill .kill)) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 2 (.node 0 .kill (.node 0 .kill .kill)) (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 4 (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill))) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 2 (.node 0 .kill (.node 0 .kill .kill)) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 1 .kill (.node 1 .kill (.node 1 (.node 0 .kill (.node 0 .kill k7FareyCertC18)) (.node 0 .kill .kill)))) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill))) .kill) .kill) .kill) .kill) .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill))) .kill) .kill) .kill) .kill))) .kill) .kill) .kill) .kill))))))))))))))))))))))))))))) (.node 0 (.node 0 (.node 0 (.node 0 .kill .kill) .kill) .kill) .kill)) (.node 0 .kill .kill)))))))) (.node 0 .kill .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)

private def k7FareyCertC20 : FareyTree :=
  (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 2 (.node 0 .kill (.node 0 .kill .kill)) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 5 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill))))) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 k7FareyCertC19 .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)) .kill) .kill) .kill) .kill) .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)

private def k7FareyCertC21 : FareyTree :=
  (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 1 (.node 2 (.node 0 .kill (.node 0 .kill .kill)) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 1 .kill (.node 1 (.node 0 .kill (.node 1 .kill (.node 1 (.node 1 .kill (.node 1 (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 1 (.node 4 (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill))) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 2 (.node 0 .kill (.node 0 .kill .kill)) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 10 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill)))))))))) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 k7FareyCertC20 .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill))) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)) (.node 0 .kill .kill))))) (.node 0 .kill .kill))) (.node 0 .kill .kill)))) (.node 0 .kill .kill)))) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)) (.node 0 .kill .kill)))))))))))))

private def k7FareyCertC22 : FareyTree :=
  (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 3 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 1 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 1 (.node 6 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill k7FareyCertC21))))))))))))))))))))))))))))))))))))))))) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 .kill .kill) .kill) .kill) .kill) .kill)) .kill)) .kill) (.node 0 .kill .kill)))))))))))))) (.node 0 (.node 0 (.node 0 .kill .kill) .kill) .kill))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private def k7FareyCertC23 : FareyTree :=
  (.node 1 .kill (.node 3 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 1 (.node 1 (.node 1 .kill (.node 3 (.node 0 .kill (.node 0 .kill .kill)) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 1 .kill (.node 1 (.node 10 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill k7FareyCertC22)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 .kill .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)) .kill))) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill))) .kill) (.node 0 .kill .kill)))))))))))) (.node 0 (.node 0 .kill .kill) .kill)))

private def k7FareyCertC24 : FareyTree :=
  (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 3 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 7 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill)))))) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 0 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 1 (.node 1 (.node 0 .kill .kill) (.node 1 (.node 2 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 1 (.node 1 .kill (.node 2 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill k7FareyCertC23)))) (.node 0 .kill .kill))) (.node 0 .kill .kill))))))) (.node 0 .kill .kill)) .kill)) .kill)) .kill) .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill))))))))))))))))) (.node 0 (.node 0 .kill .kill) .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)

private def k7FareyCertC25 : FareyTree :=
  (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 k7FareyCertC24 .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)

private def k7FareyCertC26 : FareyTree :=
  (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 1 (.node 5 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 1 (.node 2 (.node 0 .kill .kill) (.node 0 (.node 0 (.node 0 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 12 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill)))))))))))) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 k7FareyCertC25 .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill))) .kill) .kill) .kill) .kill)) (.node 0 .kill .kill)))))))))))))))))))))))))))))))))))) (.node 0 (.node 0 (.node 0 (.node 0 .kill .kill) .kill) .kill) .kill)) (.node 0 .kill .kill))))))))))))))

private def k7FareyCertC27 : FareyTree :=
  (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 2 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 2 (.node 0 .kill .kill) (.node 0 (.node 0 (.node 0 (.node 0 (.node 6 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 1 (.node 1 .kill (.node 1 (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 2 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 1 (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 1 (.node 1 (.node 2 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 4 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill k7FareyCertC26)))))))))))) (.node 0 (.node 0 (.node 0 (.node 0 .kill .kill) .kill) .kill) .kill)))))))))) (.node 0 (.node 0 .kill .kill) .kill)) .kill) .kill)))) (.node 0 .kill .kill)))))) (.node 0 .kill .kill))))) (.node 0 .kill .kill))) (.node 0 .kill .kill))))))))))))))))))))))))))))))))))))))))))))))))) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 .kill .kill) .kill) .kill) .kill) .kill)) .kill) .kill) .kill) .kill))))))))) (.node 0 (.node 0 .kill .kill) .kill))) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)

def k7FareyCert : FareyTree :=
  (.node 1 .kill (.node 1 (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 0 (.node 0 (.node 1 (.node 1 .kill (.node 1 .kill (.node 1 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 0 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 0 (.node 0 (.node 1 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 1 (.node 1 .kill (.node 4 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill)))) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 k7FareyCertC27 .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill))) (.node 0 .kill .kill)))))) (.node 0 .kill .kill)) .kill) .kill)) .kill) .kill)) .kill) .kill))) .kill) .kill) .kill)))) .kill))

set_option maxRecDepth 400000 in
set_option maxHeartbeats 40000000 in
-- Kernel-only certificate check (`decide`, no `native_decide`): evaluates
-- the 7307-node Farey descent tree (depth 3367, hence the `maxRecDepth`
-- bump), including 445 exact 7th-power candidate refutations on integers
-- up to ~2800 bits (hence the `maxHeartbeats` bump).
theorem k7FareyCert_check :
    fareyCheck 4 93 5 5 887 (5 * 10 ^ 120) k7EqRefuted 1 1 5 4 k7FareyCert =
      true := by
  decide

/--
**No `k = 7`, `N = 4` gap solution with `221 ≤ d < 10^120`** (extended
range; the headline `10^60` statement is
`no_gap_solution_four_seven_below`).  Composes the banked ratio window and
row-1 quotient confinement with the centered-Thue descent certificate.
-/
theorem no_gap_solution_four_seven_below_ext {n d : ℕ}
    (hd : 221 ≤ d) (hB : d < 10 ^ 120) :
    blockProduct 7 (n + d) ≠ 4 * blockProduct 7 n := by
  intro heq
  obtain ⟨hup, hlo⟩ := ratio_window_four_nat heq
  have h4d : 4 * d ≤ n + 1 := row_base_lower_k7 hd hup
  have h5d : n + 1 < 5 * d := row_base_upper_k7 hlo
  have hn : 883 ≤ n := by omega
  have hsol : K7CenteredEq (n + d + 4) (n + 4) := k7_centered_of_eq heq
  have hbl := k7_scaled_lower hn hlo
  have hbu := k7_scaled_upper hn hup
  have hYlo : 887 ≤ n + 4 := by omega
  have hYmax : n + 4 ≤ 5 * 10 ^ 120 := by
    generalize hP : (10 : ℕ) ^ 120 = P at hB ⊢
    omega
  have hlow : (n + 4) * 1 + 1 ≤ (n + d + 4) * 1 := by omega
  have hhigh : (n + d + 4) * 4 + 1 ≤ (n + 4) * 5 := by omega
  exact fareyCheck_sound
    (Sol := fun X Y => K7CenteredEq X Y ∧
      121826 * Y < 100000 * X ∧ 100000 * X < 121977 * Y)
    (fun X Y h hS => k7EqRefuted_sound X Y h hS.1)
    (fun X Y hS h1 _h2 => k7_thue_window hS.1 hS.2.1 hS.2.2 h1)
    ⟨hsol, hbl, hbu⟩ hYlo hYmax (by omega)
    k7FareyCert 1 1 5 4 (by norm_num) k7FareyCert_check hlow hhigh

/--
**No `k = 7`, `N = 4` gap solution with `221 ≤ d < 10^60`.**  Together with
the banked `d ≤ 220` small-core certificate this closes `k = 7` up to the
tail `NoLargeGapSolutionFour 7 (10^60)`
(see `no_gap_solution_four_seven_of_tail`).
-/
theorem no_gap_solution_four_seven_below {n d : ℕ}
    (hd : 221 ≤ d) (hB : d < 10 ^ 60) :
    blockProduct 7 (n + d) ≠ 4 * blockProduct 7 n :=
  no_gap_solution_four_seven_below_ext hd
    (lt_of_lt_of_le hB (Nat.pow_le_pow_right (by norm_num) (by norm_num)))

/--
Conditional closure for `k = 7`, `d ≥ 221`: the certified strip
`221 ≤ d < 10^60` plus the tail hypothesis `NoLargeGapSolutionFour 7 (10^60)`
refute every gap solution with `d ≥ 221`.
-/
theorem no_gap_solution_four_seven_of_tail
    (htail : NoLargeGapSolutionFour 7 (10 ^ 60)) {n d : ℕ} (hd : 221 ≤ d) :
    blockProduct 7 (n + d) ≠ 4 * blockProduct 7 n := by
  rcases Nat.lt_or_ge d (10 ^ 60) with h | h
  · exact no_gap_solution_four_seven_below hd h
  · exact htail n d h

/-- Variant of `no_gap_solution_four_seven_of_tail` from the weaker tail at
`10^120` (the full certified range). -/
theorem no_gap_solution_four_seven_of_tail_ext
    (htail : NoLargeGapSolutionFour 7 (10 ^ 120)) {n d : ℕ} (hd : 221 ≤ d) :
    blockProduct 7 (n + d) ≠ 4 * blockProduct 7 n := by
  rcases Nat.lt_or_ge d (10 ^ 120) with h | h
  · exact no_gap_solution_four_seven_below_ext hd h
  · exact htail n d h

end Erdos686Variant

end Erdos686
