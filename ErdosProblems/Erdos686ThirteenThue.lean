/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686ConvergentMachinery

/-!
# Erdős 686, k = 13: centered-Thue/convergent certificate

Instance of the Farey/Stern–Brocot descent machinery
(`Erdos686ConvergentMachinery`) for `k = 13`, `N = 4`, closing the gap
equation `(n+d+1)⋯(n+d+13) = 4·(n+1)⋯(n+13)` for all `221 ≤ d < 10^120`
(headline statement at `10^60`, matching the campaign tail interface).
Mathematics: `compute/theory/oddk_13/note.md` and
`compute/theory/odd_k_thue_synthesis.md`; certificate generated and
pre-verified by `compute/erdos686_thue_gen_lean.py` (cross-checked against
`compute/artifacts/thue_convergents_k13.json`).

The chain, entirely in integer arithmetic:

1. **Centering** (`k13_centered_of_eq`): with `X = n+d+7`, `Y = n+7` the
   equation is exactly `P₁₃(X) = 4·P₁₃(Y)` for
   `P₁₃(T) = T¹³ − 91T¹¹ + 3003T⁹ − 44473T⁷ + 296296T⁵ − 773136T³ + 518400T`,
   stated ℕ-safely (`K13CenteredEq`) as
   `X¹³ + 3003X⁹ + 296296X⁵ + 518400X + 364Y¹¹ + 177892Y⁷ + 3092544Y³`
   `= 4Y¹³ + 12012Y⁹ + 1185184Y⁵ + 2073600Y + 91X¹¹ + 44473X⁷ + 773136X³`.
2. **Ratio bracket** (`k13_scaled_lower/upper`): unlike the `k = 5` module
   (which extracted the bracket from the equation via a monotone scaled
   polynomial), here the bracket comes from the *banked ratio window*
   `4(n+1)¹³ ≤ (n+d+1)¹³`, `(n+d+13)¹³ ≤ 4(n+13)¹³` and the
   13th-power bracket facts `111253¹³ < 4·10^65 < 111254¹³`; the
   centered offsets are absorbed by `omega` using `Y ≥ 1774`, giving
   `111214·Y < 10⁵·X < 111293·Y`.
3. **Thue window** (`k13_thue_window`): `1·|X¹³ − 4Y¹³| ≤ 72·Y¹¹`
   (constant `72`; certified sup over the bracket `≈ 71.049`, true
   value `≈ 70.02`).
4. **Handoff from the banked window**: `ratio_window_four_nat` +
   `row_base_lower_k13`/`row_base_upper_k13` give `8d ≤ n+1 < 9d` for
   `d ≥ 221`, hence `1774 ≤ Y ≤ 9·10^120` for `221 ≤ d < 10^120`.
5. **Descent certificate** (`k13FareyCert`, `k13FareyCert_check`): a
   4497-node Farey tree rooted at `1/1 < 4^(1/13) < 8/7`; one kernel
   `decide` checks every side certificate, mediant multiple bound, and
   the 790 exact candidate refutations (`Y` up to `9·10^120`,
   ~5225-bit integers).  No `native_decide`.
-/

namespace Erdos686

namespace Erdos686Variant

/--
The exact centered equation for `k = 13`, `N = 4` in ℕ-safe form:
`X¹³ + 3003X⁹ + 296296X⁵ + 518400X + 364Y¹¹ + 177892Y⁷ + 3092544Y³`
`= 4Y¹³ + 12012Y⁹ + 1185184Y⁵ + 2073600Y + 91X¹¹ + 44473X⁷ + 773136X³`
⟺ `P₁₃(X) = 4·P₁₃(Y)` with
`P₁₃(T) = T¹³ − 91T¹¹ + 3003T⁹ − 44473T⁷ + 296296T⁵ − 773136T³ + 518400T`,
at `X = n+d+7`, `Y = n+7`.
-/
def K13CenteredEq (X Y : ℕ) : Prop :=
  X ^ 13 + 3003 * X ^ 9 + 296296 * X ^ 5 + 518400 * X + 364 * Y ^ 11 + 177892 * Y ^ 7 + 3092544
      * Y ^ 3 =
    4 * Y ^ 13 + 12012 * Y ^ 9 + 1185184 * Y ^ 5 + 2073600 * Y + 91 * X ^ 11 + 44473 * X ^ 7 +
      773136 * X ^ 3

/-- Boolean refuter for the exact centered equation (kernel-decidable). -/
def k13EqRefuted (X Y : ℕ) : Bool :=
  decide (X ^ 13 + 3003 * X ^ 9 + 296296 * X ^ 5 + 518400 * X + 364 * Y ^ 11 + 177892 * Y ^ 7 +
      3092544 * Y ^ 3 ≠
    4 * Y ^ 13 + 12012 * Y ^ 9 + 1185184 * Y ^ 5 + 2073600 * Y + 91 * X ^ 11 + 44473 * X ^ 7 +
      773136 * X ^ 3)

lemma k13EqRefuted_sound (X Y : ℕ) (h : k13EqRefuted X Y = true) :
    ¬ K13CenteredEq X Y := by
  intro hc
  exact (of_decide_eq_true h) hc

/-! ## Centering -/

private lemma blockProduct_thirteen_prod (x : ℕ) :
    blockProduct 13 x =
      (x + 1) * (x + 2) * (x + 3) * (x + 4) * (x + 5) * (x + 6) * (x + 7) * (x + 8) * (x + 9) *
        (x + 10) * (x + 11) * (x + 12) * (x + 13) := by
  norm_num [blockProduct, Finset.prod_Icc_succ_top, Finset.Icc_self,
    Finset.prod_singleton]

/-- The centered identity `∏_{i=1}^{13}(m+i) = P₁₃(m+7)` in additive ℕ form. -/
private lemma blockProduct_thirteen_centered (m : ℕ) :
    blockProduct 13 m + 91 * (m + 7) ^ 11 + 44473 * (m + 7) ^ 7 + 773136 * (m + 7) ^ 3 =
      (m + 7) ^ 13 + 3003 * (m + 7) ^ 9 + 296296 * (m + 7) ^ 5 + 518400 * (m + 7) := by
  rw [blockProduct_thirteen_prod]; ring

/-- A gap solution satisfies the exact centered equation. -/
lemma k13_centered_of_eq {n d : ℕ}
    (heq : blockProduct 13 (n + d) = 4 * blockProduct 13 n) :
    K13CenteredEq (n + d + 7) (n + 7) := by
  have h1 := blockProduct_thirteen_centered (n + d)
  have h2 := blockProduct_thirteen_centered n
  unfold K13CenteredEq
  linarith

/-! ## Ratio bracket `111214/10⁵ < X/Y < 111293/10⁵` from the banked window

The banked window inequalities compare `k`-th powers at the row bases
`n+1` and `n+13`; a rational bracket of `4^(1/13)` at scale `10⁵`
(`111253¹³ < 4·10^65 < 111254¹³`) linearizes them, and `omega` absorbs
the centered-coordinate offsets using `Y = n+7 ≥ 1774` (banked confinement
for `d ≥ 221`). -/

/-- Scaled lower bracket from the banked lower window. -/
lemma k13_scaled_lower {n d : ℕ} (hn : 1767 ≤ n)
    (hlo : 4 * (n + 1) ^ 13 ≤ (n + d + 1) ^ 13) :
    111214 * (n + 7) < 100000 * (n + d + 7) := by
  have hAB : 111253 * (n + 1) < 100000 * (n + d + 1) := by
    by_contra hnot
    have hnot' : 100000 * (n + d + 1) ≤ 111253 * (n + 1) := Nat.le_of_not_lt hnot
    have hp : (100000 * (n + d + 1)) ^ 13 ≤ (111253 * (n + 1)) ^ 13 :=
      Nat.pow_le_pow_left hnot' 13
    rw [mul_pow, mul_pow] at hp
    have h1 : 4 * 100000 ^ 13 * (n + 1) ^ 13 ≤ 111253 ^ 13 * (n + 1) ^ 13 :=
      calc 4 * 100000 ^ 13 * (n + 1) ^ 13
          = 100000 ^ 13 * (4 * (n + 1) ^ 13) := by ring
        _ ≤ 100000 ^ 13 * (n + d + 1) ^ 13 := Nat.mul_le_mul (le_refl _) hlo
        _ ≤ 111253 ^ 13 * (n + 1) ^ 13 := hp
    have h2 : 0 < (n + 1) ^ 13 := pow_pos (by omega) 13
    exact absurd (Nat.le_of_mul_le_mul_right h1 h2) (by norm_num)
  omega

/-- Scaled upper bracket from the banked upper window. -/
lemma k13_scaled_upper {n d : ℕ} (hn : 1767 ≤ n)
    (hup : (n + d + 13) ^ 13 ≤ 4 * (n + 13) ^ 13) :
    100000 * (n + d + 7) < 111293 * (n + 7) := by
  have hCD : 100000 * (n + d + 13) < 111254 * (n + 13) := by
    by_contra hnot
    have hnot' : 111254 * (n + 13) ≤ 100000 * (n + d + 13) := Nat.le_of_not_lt hnot
    have hp : (111254 * (n + 13)) ^ 13 ≤ (100000 * (n + d + 13)) ^ 13 :=
      Nat.pow_le_pow_left hnot' 13
    rw [mul_pow, mul_pow] at hp
    have h1 : 111254 ^ 13 * (n + 13) ^ 13 ≤ 4 * 100000 ^ 13 * (n + 13) ^ 13 :=
      calc 111254 ^ 13 * (n + 13) ^ 13
          ≤ 100000 ^ 13 * (n + d + 13) ^ 13 := hp
        _ ≤ 100000 ^ 13 * (4 * (n + 13) ^ 13) := Nat.mul_le_mul (le_refl _) hup
        _ = 4 * 100000 ^ 13 * (n + 13) ^ 13 := by ring
    have h2 : 0 < (n + 13) ^ 13 := pow_pos (by omega) 13
    exact absurd (Nat.le_of_mul_le_mul_right h1 h2) (by norm_num)
  omega

/-! ## The Thue window `1·|X¹³ − 4Y¹³| ≤ 72·Y¹¹` -/

set_option maxHeartbeats 4000000 in
-- The `nlinarith` bracket-power expansions (degree 11 products of 6-digit
-- scaled brackets) and the two ~29-fact `linarith` calls exceed the
-- default limit at this degree.
/--
Two-sided Thue window in the exact shape consumed by `fareyCheck_sound`
(`N = 4`, `cnum = 72`, `cden = 1`, `e = 11`): for any solution inside
the scaled bracket with `Y ≥ 1774`, `1·(4Y¹³) ≤ 1·X¹³ + 72·Y¹¹` and
`1·X¹³ ≤ 1·(4Y¹³) + 72·Y¹¹`.
-/
lemma k13_thue_window {X Y : ℕ} (hsol : K13CenteredEq X Y)
    (hbl : 111214 * Y < 100000 * X) (hbu : 100000 * X < 111293 * Y)
    (hY : 1774 ≤ Y) :
    1 * (4 * Y ^ 13) ≤ 1 * X ^ 13 + 72 * Y ^ 11 ∧
      1 * X ^ 13 ≤ 1 * (4 * Y ^ 13) + 72 * Y ^ 11 := by
  have hz :  (X : ℤ) ^ 13 + 3003 * (X : ℤ) ^ 9 + 296296 * (X : ℤ) ^ 5 + 518400 * (X : ℤ) + 364 *
      (Y : ℤ) ^ 11 + 177892 * (Y : ℤ) ^ 7 + 3092544 * (Y : ℤ) ^ 3 = 4 * (Y : ℤ) ^ 13 + 12012 *
      (Y : ℤ) ^ 9 + 1185184 * (Y : ℤ) ^ 5 + 2073600 * (Y : ℤ) + 91 * (X : ℤ) ^ 11 + 44473 * (X :
      ℤ) ^ 7 + 773136 * (X : ℤ) ^ 3 := by
    exact_mod_cast hsol
  have hblz : (111214 : ℤ) * Y ≤ 100000 * X := by exact_mod_cast hbl.le
  have hbuz : (100000 : ℤ) * X ≤ 111293 * Y := by exact_mod_cast hbu.le
  have hYz : (1774 : ℤ) ≤ (Y : ℤ) := by exact_mod_cast hY
  have hY0 : (0 : ℤ) ≤ (Y : ℤ) := Int.natCast_nonneg Y
  -- odd powers of the scaled bracket
  have hlo3 :
      (1375556341868344 : ℤ) * (Y : ℤ) ^ 3 ≤
        1000000000000000 * (X : ℤ) ^ 3 := by
    nlinarith [pow_le_pow_left₀ (by positivity : (0 : ℤ) ≤ 111214 * (Y : ℤ))
      hblz 3]
  have hhi3 :
      (1000000000000000 : ℤ) * (X : ℤ) ^ 3 ≤
        1378489771870757 * (Y : ℤ) ^ 3 := by
    nlinarith [pow_le_pow_left₀ (by positivity : (0 : ℤ) ≤ 100000 * (X : ℤ))
      hbuz 3]
  have hlo5 :
      (17013642613827579913433824 : ℤ) * (Y : ℤ) ^ 5 ≤
        10000000000000000000000000 * (X : ℤ) ^ 5 := by
    nlinarith [pow_le_pow_left₀ (by positivity : (0 : ℤ) ≤ 111214 * (Y : ℤ))
      hblz 5]
  have hhi5 :
      (10000000000000000000000000 : ℤ) * (X : ℤ) ^ 5 ≤
        17074156066889127589439693 * (Y : ℤ) ^ 5 := by
    nlinarith [pow_le_pow_left₀ (by positivity : (0 : ℤ) ≤ 100000 * (X : ℤ))
      hbuz 5]
  have hlo7 :
      (210434153935044475627795275229995904 : ℤ) * (Y : ℤ) ^ 7 ≤
        100000000000000000000000000000000000 * (X : ℤ) ^ 7 := by
    nlinarith [pow_le_pow_left₀ (by positivity : (0 : ℤ) ≤ 111214 * (Y : ℤ))
      hblz 7]
  have hhi7 :
      (100000000000000000000000000000000000 : ℤ) * (X : ℤ) ^ 7 ≤
        211482748254891997587383577532082357 * (Y : ℤ) ^ 7 := by
    nlinarith [pow_le_pow_left₀ (by positivity : (0 : ℤ) ≤ 100000 * (X : ℤ))
      hbuz 7]
  have hlo9 :
      (2602766153461342686454996734556830611483651584 : ℤ) * (Y : ℤ) ^ 9 ≤
        1000000000000000000000000000000000000000000000 * (X : ℤ) ^ 9 := by
    nlinarith [pow_le_pow_left₀ (by positivity : (0 : ℤ) ≤ 111214 * (Y : ℤ))
      hblz 9]
  have hhi9 :
      (1000000000000000000000000000000000000000000000 : ℤ) * (X : ℤ) ^ 9 ≤
        2619453203673966941372322890249686101328688093 * (Y : ℤ) ^ 9 := by
    nlinarith [pow_le_pow_left₀ (by positivity : (0 : ℤ) ≤ 100000 * (X : ℤ))
      hbuz 9]
  have hlo11 :
      (32192453187494608623809787644370491637395119991224612864 : ℤ) * (Y : ℤ) ^ 11 ≤
        10000000000000000000000000000000000000000000000000000000 * (X : ℤ) ^ 11 := by
    nlinarith [pow_le_pow_left₀ (by positivity : (0 : ℤ) ≤ 111214 * (Y : ℤ))
      hblz 11]
  have hhi11 :
      (10000000000000000000000000000000000000000000000000000000 : ℤ) * (X : ℤ) ^ 11 ≤
        32444892752991205744704844318033368581919904806094373957 * (Y : ℤ) ^ 11 := by
    nlinarith [pow_le_pow_left₀ (by positivity : (0 : ℤ) ≤ 100000 * (X : ℤ))
      hbuz 11]
  -- lower-degree absorption at `Y ≥ 1774`
  have hab1 :
      (308699662703995575300080214885376 : ℤ) * (Y : ℤ) ≤ (Y : ℤ) ^ 11 := by
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℤ) ≤ 1774) hYz 10,
      pow_nonneg hY0 1]
  have hab3 :
      (98090946231992991367250176 : ℤ) * (Y : ℤ) ^ 3 ≤ (Y : ℤ) ^ 11 := by
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℤ) ≤ 1774) hYz 8,
      pow_nonneg hY0 3]
  have hab5 :
      (31168915600383654976 : ℤ) * (Y : ℤ) ^ 5 ≤ (Y : ℤ) ^ 11 := by
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℤ) ≤ 1774) hYz 6,
      pow_nonneg hY0 5]
  have hab7 :
      (9904087349776 : ℤ) * (Y : ℤ) ^ 7 ≤ (Y : ℤ) ^ 11 := by
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℤ) ≤ 1774) hYz 4,
      pow_nonneg hY0 7]
  have hab9 :
      (3147076 : ℤ) * (Y : ℤ) ^ 9 ≤ (Y : ℤ) ^ 11 := by
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℤ) ≤ 1774) hYz 2,
      pow_nonneg hY0 9]
  have hpos1 : (0 : ℤ) ≤ (Y : ℤ) ^ 1 := by positivity
  have hpos3 : (0 : ℤ) ≤ (Y : ℤ) ^ 3 := by positivity
  have hpos5 : (0 : ℤ) ≤ (Y : ℤ) ^ 5 := by positivity
  have hpos7 : (0 : ℤ) ≤ (Y : ℤ) ^ 7 := by positivity
  have hpos9 : (0 : ℤ) ≤ (Y : ℤ) ^ 9 := by positivity
  have hpos11 : (0 : ℤ) ≤ (Y : ℤ) ^ 11 := by positivity
  constructor
  · have hgoal : 1 * (4 * (Y : ℤ) ^ 13) ≤
        1 * (X : ℤ) ^ 13 + 72 * (Y : ℤ) ^ 11 := by
      linarith [hz, hlo3, hhi3, hlo5, hhi5, hlo7, hhi7, hlo9, hhi9, hlo11, hhi11, hab1, hab3,
        hab5, hab7, hab9, hpos1, hpos3, hpos5, hpos7, hpos9, hpos11, hblz, hbuz]
    exact_mod_cast hgoal
  · have hgoal : 1 * (X : ℤ) ^ 13 ≤
        1 * (4 * (Y : ℤ) ^ 13) + 72 * (Y : ℤ) ^ 11 := by
      linarith [hz, hlo3, hhi3, hlo5, hhi5, hlo7, hhi7, hlo9, hhi9, hlo11, hhi11, hab1, hab3,
        hab5, hab7, hab9, hpos1, hpos3, hpos5, hpos7, hpos9, hpos11, hblz, hbuz]
    exact_mod_cast hgoal

/-! ## The descent certificate

Generated by `compute/erdos686_thue_gen_lean.py 120 13` (deterministic,
byte-stable); root Farey pair `1/1 < 4^(1/13) < 8/7`, `Ylo = 1774`,
`Ymax = 9·10^120`.  4497 nodes: 2248 mediant splits, 2240 side-certificate
kills, 9 `Ymax`-exits; 790 candidate pairs refuted by the exact equation.
Every convergent of `cf(4^(1/13))` with denominator `≤ 9·10^120` (225 of the
341 rows of `compute/artifacts/thue_convergents_k13.json`) occurs among the
mediants; determinants, straddle signs, and sign alternation are re-verified
by the generator before emission. -/

/- AUTOGENERATED by compute/erdos686_thue_gen_lean.py (YMAX_EXP=120).
   Farey/Stern-Brocot descent certificate for k = 13, N = 4:
   root pair 1/1 < 4^(1/13) < 8/7, Thue window 1*|X^13-4Y^13| <= 72*Y^11,
   Ylo = 1774, Ymax = 9 * 10^120.  Do not edit by hand. -/

-- generated single-line tree literals (repo precedent: Erdos154.lean)
set_option linter.style.longLine false

private def k13FareyCertC0 : FareyTree :=
  (.node 1 (.node 3 (.node 1 (.node 0 .kill .kill) (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 4 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 5 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill)))) (.node 1 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 7 (.node 1 (.node 0 .kill .kill) (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill))))))) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 2 (.node 1 (.node 0 .kill .kill) (.node 1 (.node 0 .kill .kill) (.node 1 (.node 2 (.node 0 .kill .kill) (.node 1 (.node 2 (.node 1 (.node 0 .kill .kill) (.node 1 (.node 0 .kill .kill) (.node 1 (.node 1 (.node 0 .kill .kill) (.node 3 (.node 1 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 1 .kill (.node 3 (.node 0 .kill (.node 0 .kill .kill)) (.node 1 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 1 (.node 2 (.node 1 .kill (.node 0 .kill .kill)) (.node 1 (.node 8 (.node 1 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .high (.node 0 .high (.node 0 .high (.node 0 .high (.node 0 .high (.node 0 .high (.node 0 .high (.node 0 .high .high)))))))))))))))) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 .kill .kill) .kill) .kill) .kill) .kill) .kill) .kill)) (.node 0 .kill .kill))) .kill) .kill) .kill) .kill) .kill) .kill) .kill) (.node 0 .kill .kill)))))))) (.node 0 (.node 0 .kill .kill) .kill))) (.node 0 .kill .kill)))) (.node 0 .kill .kill)) (.node 0 .kill .kill))) (.node 0 .kill .kill)))) (.node 0 .kill .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) (.node 0 .kill .kill)))))))))))) (.node 1 (.node 0 (.node 0 (.node 0 .kill .kill) .kill) .kill) (.node 0 .kill .kill)))))))))))) (.node 0 (.node 0 .kill .kill) .kill)) .kill)

private def k13FareyCertC1 : FareyTree :=
  (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 6 (.node 1 (.node 0 .kill .kill) (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill)))))) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 3 (.node 1 (.node 0 .kill .kill) (.node 0 .kill (.node 0 .kill .kill))) (.node 1 (.node 0 (.node 0 (.node 0 (.node 1 (.node 1 (.node 6 (.node 1 (.node 0 .kill .kill) (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill)))))) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 k13FareyCertC0 .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)) .kill) .kill) .kill) .kill) .kill) .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)

private def k13FareyCertC2 : FareyTree :=
  (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 2 (.node 1 (.node 0 .kill .kill) (.node 0 .kill .kill)) (.node 1 (.node 1 (.node 2 (.node 0 .kill .kill) (.node 1 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 7 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill)))))) (.node 1 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 2 (.node 0 .kill .kill) (.node 1 (.node 1 (.node 2 (.node 0 .kill .kill) (.node 1 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 1 (.node 1 (.node 0 .kill .kill) (.node 1 (.node 2 (.node 0 .kill .kill) (.node 1 (.node 2 (.node 1 .kill (.node 1 .kill (.node 1 .kill (.node 3 (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill))) (.node 1 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 3 (.node 1 (.node 0 .kill .kill) (.node 1 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 1 .kill (.node 1 (.node 3 (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill))) (.node 1 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 1 (.node 2 (.node 1 .kill (.node 0 .kill .kill)) (.node 1 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 1 (.node 2 (.node 0 .kill (.node 0 .kill .kill)) (.node 1 (.node 1 (.node 2 (.node 1 (.node 0 .kill .kill) (.node 1 .kill (.node 10 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill))))))))) (.node 1 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 k13FareyCertC1 .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)))) (.node 0 .kill .kill)) .kill) .kill)) (.node 0 .kill .kill))) (.node 0 .kill .kill)) .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill)) (.node 0 .kill .kill)))))))) (.node 0 (.node 0 .kill .kill) .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) (.node 0 .kill .kill)))))) (.node 0 (.node 0 .kill .kill) .kill)) (.node 0 .kill .kill))) (.node 0 .kill .kill))) (.node 0 .kill .kill))) (.node 0 .kill .kill)) .kill)) (.node 0 .kill .kill)) (.node 0 .kill .kill)))) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill))) (.node 0 .kill .kill)) .kill)) .kill) .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)

private def k13FareyCertC3 : FareyTree :=
  (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 3 (.node 1 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 2 (.node 0 .kill .kill) (.node 1 (.node 1 (.node 1 (.node 1 (.node 3 (.node 1 .kill (.node 0 .kill (.node 0 .kill .kill))) (.node 1 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 6 (.node 1 (.node 0 .kill .kill) (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 1 .kill (.node 1 (.node 2 (.node 0 .kill (.node 0 .kill .kill)) (.node 1 (.node 1 (.node 1 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 5 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill))))) (.node 1 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 2 (.node 1 (.node 0 .kill .kill) (.node 1 .kill (.node 1 (.node 0 .kill .kill) (.node 1 (.node 4 (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill))) (.node 1 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 2 (.node 1 (.node 0 .kill .kill) (.node 1 .kill (.node 1 .kill (.node 2 (.node 1 .kill (.node 1 .kill (.node 5 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill))))) (.node 1 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 k13FareyCertC2 .kill) .kill) .kill) .kill) .kill) .kill) .kill)))) (.node 0 (.node 0 .kill .kill) .kill))))) (.node 0 .kill .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)) (.node 0 .kill .kill))))) (.node 0 .kill .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill))) (.node 0 .kill .kill)) .kill) .kill) .kill)) (.node 1 .kill .kill)))))))))))))))))))))))))))))))) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 .kill .kill) .kill) .kill) .kill) .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)) .kill) .kill) .kill) (.node 0 .kill .kill)))))))))) (.node 1 (.node 0 (.node 0 .kill .kill) .kill) (.node 0 .kill .kill)))))))))))

private def k13FareyCertC4 : FareyTree :=
  (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 2 (.node 1 (.node 0 .kill .kill) (.node 1 .kill (.node 3 (.node 0 .kill (.node 0 .kill .kill)) (.node 1 (.node 0 (.node 0 (.node 0 (.node 1 (.node 1 (.node 2 (.node 0 .kill (.node 0 .kill .kill)) (.node 1 (.node 3 (.node 1 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 4 (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill))) (.node 1 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 4 (.node 1 (.node 0 .kill .kill) (.node 0 .kill (.node 0 .kill k13FareyCertC3))) (.node 0 (.node 0 (.node 0 .kill .kill) .kill) .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) (.node 0 .kill .kill)))))))))) (.node 0 (.node 0 .kill .kill) .kill)) (.node 0 .kill .kill))) .kill) .kill) .kill) .kill) .kill) .kill)))) (.node 0 .kill .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)

private def k13FareyCertC5 : FareyTree :=
  (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 2 (.node 0 .kill .kill) (.node 1 (.node 1 (.node 1 (.node 1 (.node 17 (.node 1 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill)))))))))))))))) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 k13FareyCertC4 .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)) .kill) .kill) .kill) (.node 0 .kill .kill)))))))))

private def k13FareyCertC6 : FareyTree :=
  (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 4 (.node 1 (.node 0 .kill .kill) (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 1 .kill (.node 2 (.node 1 (.node 0 .kill .kill) (.node 4 (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill))) (.node 1 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 8 (.node 1 (.node 0 .kill .kill) (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill k13FareyCertC5))))))))))))))))))))))))))))))))))))))) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 .kill .kill) .kill) .kill) .kill) .kill) .kill) .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill))) (.node 1 (.node 0 .kill .kill) .kill)))))))))))))) (.node 0 (.node 0 (.node 0 .kill .kill) .kill) .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)

private def k13FareyCertC7 : FareyTree :=
  (.node 1 (.node 0 .kill .kill) (.node 1 (.node 1 (.node 0 .kill .kill) (.node 1 (.node 3 (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill))) (.node 1 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 1 (.node 2 (.node 1 .kill (.node 0 .kill .kill)) (.node 1 (.node 1 (.node 15 (.node 1 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill))))))))))))))) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 k13FareyCertC6 .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)) .kill) .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill)) (.node 0 .kill .kill))) (.node 0 .kill .kill)))

private def k13FareyCertC8 : FareyTree :=
  (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 2 (.node 1 (.node 0 .kill .kill) (.node 1 .kill (.node 3 (.node 0 .kill (.node 0 .kill .kill)) (.node 1 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 2 (.node 1 (.node 0 .kill .kill) (.node 1 .kill (.node 1 .kill (.node 1 .kill (.node 2 (.node 1 .kill (.node 1 .kill (.node 6 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 1 .kill (.node 1 k13FareyCertC7 (.node 1 .kill (.node 0 .kill .kill))))))))))))))))))))))))))))))))) (.node 1 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 .kill .kill) .kill) .kill) .kill) .kill) .kill)))) (.node 0 (.node 0 .kill .kill) .kill)))))) (.node 0 .kill .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill)))) (.node 0 .kill .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)

private def k13FareyCertC9 : FareyTree :=
  (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 1 .kill (.node 1 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 3 (.node 1 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 1 .kill (.node 11 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill))))))))))) (.node 1 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 k13FareyCertC8 .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) (.node 0 .kill .kill)))))))) (.node 0 (.node 0 .kill .kill) .kill))) (.node 0 .kill .kill)) (.node 0 .kill .kill)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private def k13FareyCertC10 : FareyTree :=
  (.node 1 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 1 .kill (.node 1 (.node 17 (.node 1 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill k13FareyCertC9))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (.node 1 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 .kill .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)) (.node 0 .kill .kill))))))))))))

private def k13FareyCertC11 : FareyTree :=
  (.node 1 (.node 0 .kill .kill) (.node 1 (.node 2 (.node 0 .kill (.node 0 .kill .kill)) (.node 1 (.node 1 (.node 2 (.node 1 (.node 0 .kill .kill) (.node 1 .kill (.node 1 .kill (.node 2 (.node 1 .kill (.node 1 .kill (.node 1 .kill (.node 6 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 3 (.node 1 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 1 .kill (.node 2 (.node 1 .kill (.node 1 .kill (.node 2 (.node 0 .kill .kill) (.node 1 (.node 1 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 1 (.node 2 (.node 0 .kill (.node 0 .kill .kill)) (.node 1 (.node 1 (.node 2 (.node 1 (.node 0 .kill .kill) (.node 1 .kill (.node 2 (.node 0 .kill .kill) (.node 1 (.node 1 (.node 1 (.node 2 (.node 0 .kill (.node 0 .kill .kill)) (.node 1 (.node 1 (.node 1 (.node 2 (.node 0 .kill .kill) (.node 1 (.node 4 (.node 1 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill)))) (.node 1 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 2 (.node 1 (.node 0 .kill .kill) (.node 1 .kill (.node 1 .kill (.node 1 .kill (.node 2 (.node 1 .kill (.node 1 .kill (.node 1 (.node 0 .kill .kill) (.node 1 (.node 3 (.node 1 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 1 .kill (.node 2 (.node 1 (.node 0 .kill .kill) (.node 3 (.node 1 .kill (.node 1 .kill (.node 1 .kill (.node 1 .kill (.node 2 (.node 0 .kill .kill) (.node 1 (.node 1 (.node 2 (.node 0 .kill (.node 0 .kill .kill)) (.node 1 (.node 1 (.node 1 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 4 k13FareyCertC10 (.node 0 (.node 0 (.node 0 .kill .kill) .kill) .kill))) (.node 0 .kill .kill)) .kill) .kill) .kill)) (.node 0 .kill .kill)) (.node 0 .kill .kill))))))) (.node 0 (.node 0 .kill .kill) .kill))) (.node 0 .kill .kill)))))))) (.node 0 (.node 0 .kill .kill) .kill)) (.node 0 .kill .kill))))) (.node 1 (.node 0 .kill .kill) .kill)))))) (.node 0 .kill .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)) (.node 0 .kill .kill))) .kill) .kill) .kill)) .kill) .kill) (.node 0 .kill .kill))))) (.node 0 .kill .kill)) .kill) .kill)) (.node 0 .kill .kill))) (.node 0 .kill .kill)) .kill) (.node 0 .kill .kill))))) (.node 1 (.node 0 .kill .kill) .kill))))))) (.node 1 (.node 0 (.node 0 .kill .kill) .kill) (.node 0 .kill .kill)))))))))))))))))))))))))) (.node 1 (.node 0 (.node 0 (.node 0 (.node 0 .kill .kill) .kill) .kill) .kill) .kill))))) (.node 0 (.node 0 .kill .kill) .kill))))) (.node 0 .kill .kill)) .kill) .kill)) (.node 0 .kill .kill)))

private def k13FareyCertC12 : FareyTree :=
  (.node 3 (.node 0 .kill (.node 0 .kill .kill)) (.node 1 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 4 (.node 1 (.node 0 .kill .kill) (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 1 .kill (.node 2 (.node 1 .kill (.node 1 .kill (.node 1 .kill (.node 6 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill))))) (.node 1 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 2 (.node 1 (.node 0 .kill .kill) (.node 0 .kill .kill)) (.node 1 (.node 1 (.node 1 (.node 4 (.node 1 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill)))) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 2 (.node 1 (.node 0 .kill .kill) (.node 0 .kill .kill)) (.node 1 (.node 1 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 2 (.node 0 .kill (.node 0 .kill .kill)) (.node 1 (.node 1 (.node 1 (.node 1 (.node 5 (.node 1 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill)))) (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 2 (.node 0 .kill (.node 0 .kill .kill)) (.node 1 (.node 1 (.node 1 (.node 2 (.node 1 (.node 0 .kill .kill) (.node 1 .kill (.node 1 .kill (.node 1 .kill (.node 1 (.node 1 (.node 0 .kill .kill) (.node 1 (.node 2 (.node 0 .kill .kill) (.node 1 (.node 1 (.node 2 (.node 0 .kill .kill) (.node 1 (.node 2 (.node 1 (.node 0 .kill .kill) k13FareyCertC11) (.node 0 .kill .kill)) .kill)) (.node 0 .kill .kill)) .kill)) (.node 0 .kill .kill))) (.node 0 .kill .kill)))))) (.node 0 .kill .kill)) .kill) .kill) .kill))) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)) .kill) .kill) .kill) .kill))) (.node 0 .kill .kill)) .kill) .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)) .kill) .kill) .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill))))) (.node 1 (.node 0 .kill .kill) (.node 0 .kill .kill)))))))))))))) (.node 0 (.node 0 (.node 0 .kill .kill) .kill) .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) (.node 0 .kill .kill)))

private def k13FareyCertC13 : FareyTree :=
  (.node 0 .kill (.node 1 .kill (.node 1 .kill (.node 2 (.node 1 (.node 0 .kill .kill) (.node 2 (.node 1 .kill (.node 1 .kill (.node 2 (.node 0 .kill (.node 0 .kill .kill)) (.node 1 (.node 1 (.node 1 (.node 1 (.node 3 (.node 1 .kill (.node 0 .kill (.node 0 .kill .kill))) (.node 1 (.node 0 (.node 0 (.node 0 (.node 1 (.node 2 (.node 1 (.node 0 .kill .kill) (.node 1 .kill (.node 4 (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill))) (.node 1 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 2 (.node 0 .kill .kill) (.node 1 (.node 1 (.node 3 (.node 1 (.node 0 .kill .kill) (.node 1 .kill (.node 0 .kill (.node 1 .kill (.node 1 .kill (.node 4 (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill))) (.node 1 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 2 (.node 1 (.node 0 .kill .kill) (.node 0 .kill .kill)) (.node 1 (.node 1 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 6 (.node 1 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 4 (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill))) (.node 1 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 2 (.node 0 .kill .kill) (.node 1 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 3 (.node 0 .kill (.node 0 .kill .kill)) (.node 1 (.node 1 (.node 0 (.node 1 (.node 1 (.node 3 (.node 1 (.node 0 .kill .kill) (.node 1 .kill (.node 0 .kill (.node 1 .kill (.node 1 .kill k13FareyCertC12))))) (.node 0 (.node 0 .kill .kill) .kill)) .kill) .kill) .kill) .kill) .kill))) (.node 0 .kill .kill)) (.node 0 .kill .kill)))) (.node 0 .kill .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) (.node 0 .kill .kill))))))))))))))))))))))))))) (.node 1 (.node 0 (.node 0 (.node 0 (.node 0 .kill .kill) .kill) .kill) .kill) .kill))) (.node 0 .kill .kill)) .kill) .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) (.node 0 .kill .kill)))))))) (.node 0 (.node 0 .kill .kill) .kill)) .kill) .kill))) (.node 0 .kill .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill)))) (.node 0 .kill .kill)) .kill) .kill) .kill) .kill) .kill)) .kill) .kill) .kill) (.node 0 .kill .kill))))) (.node 0 (.node 0 .kill .kill) .kill))) (.node 1 .kill .kill)))))

def k13FareyCert : FareyTree :=
  (.node 1 (.node 3 .kill (.node 1 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 1 (.node 2 .kill (.node 1 (.node 1 (.node 1 (.node 4 (.node 1 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 5 (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill)))) (.node 1 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 1 (.node 0 .kill .kill) (.node 1 (.node 3 (.node 0 .kill (.node 0 .kill (.node 0 .kill .kill))) (.node 1 (.node 0 (.node 0 (.node 0 (.node 0 (.node 1 (.node 1 (.node 2 (.node 1 .kill (.node 0 .kill .kill)) (.node 1 (.node 1 (.node 1 (.node 1 (.node 0 .kill .kill) (.node 2 (.node 0 .kill (.node 0 .kill .kill)) (.node 1 (.node 1 (.node 1 (.node 1 (.node 2 (.node 1 (.node 0 .kill .kill) (.node 1 (.node 0 .kill .kill) (.node 1 (.node 2 (.node 0 .kill .kill) (.node 1 (.node 1 (.node 5 (.node 1 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 1 .kill (.node 2 (.node 0 .kill .kill) (.node 1 (.node 1 (.node 1 (.node 1 (.node 5 (.node 1 (.node 0 .kill .kill) (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill (.node 0 .kill k13FareyCertC13))))))))))))) (.node 0 (.node 0 (.node 0 (.node 0 .kill .kill) .kill) .kill) .kill)) .kill) .kill) .kill) (.node 0 .kill .kill))))))))))))))))))))) (.node 0 (.node 0 (.node 0 (.node 0 .kill .kill) .kill) .kill) .kill)) .kill) .kill)) (.node 0 .kill .kill)))) (.node 0 .kill .kill)) .kill) .kill) .kill) .kill))) (.node 0 .kill .kill)) .kill) .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill)) (.node 0 .kill .kill)))) (.node 0 .kill .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) .kill) (.node 0 .kill .kill))))))))))))))) .kill) .kill) .kill) .kill)) .kill) .kill) .kill) .kill) .kill) .kill) .kill)) .kill)

set_option maxRecDepth 400000 in
set_option maxHeartbeats 40000000 in
-- Kernel-only certificate check (`decide +kernel`, no `native_decide`):
-- evaluates the 4497-node Farey descent tree (depth 1771, hence the
-- `maxRecDepth` bump), including 790 exact 13th-power candidate
-- refutations on integers up to ~5225 bits (hence the `maxHeartbeats`
-- bump).  The `+kernel` variant bypasses the elaborator evaluator, whose
-- fixed C stack cannot hold the deep recursion of this tree; the proof
-- term and axioms are identical to plain `decide`.
theorem k13FareyCert_check :
    fareyCheck 4 72 1 11 1774 (9 * 10 ^ 120) k13EqRefuted 1 1 8 7 k13FareyCert =
      true := by
  decide +kernel

/--
**No `k = 13`, `N = 4` gap solution with `221 ≤ d < 10^120`** (extended
range; the headline `10^60` statement is
`no_gap_solution_four_thirteen_below`).  Composes the banked ratio window and
row-1 quotient confinement with the centered-Thue descent certificate.
-/
theorem no_gap_solution_four_thirteen_below_ext {n d : ℕ}
    (hd : 221 ≤ d) (hB : d < 10 ^ 120) :
    blockProduct 13 (n + d) ≠ 4 * blockProduct 13 n := by
  intro heq
  obtain ⟨hup, hlo⟩ := ratio_window_four_nat heq
  have hqd : 8 * d ≤ n + 1 := row_base_lower_k13 hd hup
  have hqd' : n + 1 < 9 * d := row_base_upper_k13 hlo
  have hn : 1767 ≤ n := by omega
  have hsol : K13CenteredEq (n + d + 7) (n + 7) := k13_centered_of_eq heq
  have hbl := k13_scaled_lower hn hlo
  have hbu := k13_scaled_upper hn hup
  have hYlo : 1774 ≤ n + 7 := by omega
  have hYmax : n + 7 ≤ 9 * 10 ^ 120 := by
    generalize hP : (10 : ℕ) ^ 120 = P at hB ⊢
    omega
  have hlow : (n + 7) * 1 + 1 ≤ (n + d + 7) * 1 := by omega
  have hhigh : (n + d + 7) * 7 + 1 ≤ (n + 7) * 8 := by omega
  exact fareyCheck_sound
    (Sol := fun X Y => K13CenteredEq X Y ∧
      111214 * Y < 100000 * X ∧ 100000 * X < 111293 * Y)
    (fun X Y h hS => k13EqRefuted_sound X Y h hS.1)
    (fun X Y hS h1 _h2 => k13_thue_window hS.1 hS.2.1 hS.2.2 h1)
    ⟨hsol, hbl, hbu⟩ hYlo hYmax (by omega)
    k13FareyCert 1 1 8 7 (by norm_num) k13FareyCert_check hlow hhigh

/--
**No `k = 13`, `N = 4` gap solution with `221 ≤ d < 10^60`.**  Together with
the banked `d ≤ 220` small-core certificate this closes `k = 13` up to the
tail `NoLargeGapSolutionFour 13 (10^60)`
(see `no_gap_solution_four_thirteen_of_tail`).
-/
theorem no_gap_solution_four_thirteen_below {n d : ℕ}
    (hd : 221 ≤ d) (hB : d < 10 ^ 60) :
    blockProduct 13 (n + d) ≠ 4 * blockProduct 13 n :=
  no_gap_solution_four_thirteen_below_ext hd
    (lt_of_lt_of_le hB (Nat.pow_le_pow_right (by norm_num) (by norm_num)))

/--
Conditional closure for `k = 13`, `d ≥ 221`: the certified strip
`221 ≤ d < 10^60` plus the tail hypothesis `NoLargeGapSolutionFour 13 (10^60)`
refute every gap solution with `d ≥ 221`.
-/
theorem no_gap_solution_four_thirteen_of_tail
    (htail : NoLargeGapSolutionFour 13 (10 ^ 60)) {n d : ℕ} (hd : 221 ≤ d) :
    blockProduct 13 (n + d) ≠ 4 * blockProduct 13 n := by
  rcases Nat.lt_or_ge d (10 ^ 60) with h | h
  · exact no_gap_solution_four_thirteen_below hd h
  · exact htail n d h

/-- Variant of `no_gap_solution_four_thirteen_of_tail` from the weaker tail at
`10^120` (the full certified range). -/
theorem no_gap_solution_four_thirteen_of_tail_ext
    (htail : NoLargeGapSolutionFour 13 (10 ^ 120)) {n d : ℕ} (hd : 221 ≤ d) :
    blockProduct 13 (n + d) ≠ 4 * blockProduct 13 n := by
  rcases Nat.lt_or_ge d (10 ^ 120) with h | h
  · exact no_gap_solution_four_thirteen_below_ext hd h
  · exact htail n d h

end Erdos686Variant

end Erdos686
