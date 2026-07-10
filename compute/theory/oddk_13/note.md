# Erdős 686, k=13, N=4: centered Thue reduction and quasi-convergent confinement

*compute/theory/oddk_13, 2026-07-09.  Template: `../k5_third_row_note.md`,
Sections 5–6 (k=5 case).  Every numerical claim is backed by exact-arithmetic
scripts in this directory; every PROVED tag was verified symbolically (sympy
over ℚ, Sturm sequences) or by exact integer computation.  Floats appear only
in display strings and in one documented conservative pre-filter; no decision
is floating-point.*

Scripts:
- `derivation.py` — 22 exact checks: centered identity, expansion of P₁₃,
  ratio bracket (Sturm + shift certificates), exact Thue constant, pinning
  constant C₁₃ = 3/2, asymptotic identity, window/confinement translation,
  grid validation.
- `cf_scan.py` — 9 exact checks: cf(4^(1/13)) to 330 terms by the
  polynomial Taylor-shift method (integer sign logic only), convergent
  verification, Worley-family enumeration to Y ≤ 10^100, exact equation scan,
  brute cross-scan Y ≤ 10^6, unconditional closure Y ≤ 2100.

---

## 0. Executive summary

Setting: `n ≥ 1`, `d ≥ 1`, `(n+d+1)⋯(n+d+13) = 4·(n+1)⋯(n+13)`.  The Lean
bank closes `d ≤ 220` (small-core row-escape certificates); `k = 13` is one of
the seven odd `ConstantCaseBoundHypothesisOdd14` pairs, box `(13, 8)`.

1. **Centered identity (PROVED).**  With `X = n+d+7`, `Y = n+7` the equation
   is exactly `P(X) = 4P(Y)`,
   `P(T) = T(T²−1)(T²−4)(T²−9)(T²−16)(T²−25)(T²−36)
        = T¹³ − 91T¹¹ + 3003T⁹ − 44473T⁷ + 296296T⁵ − 773136T³ + 518400T`.

2. **Exact Thue inequality (PROVED).**  For any solution with `Y ≥ 600`:
   `(89/80)Y < X < (9/8)Y` (from the equation itself, Sturm-certified;
   exact thresholds 219 and 6), and then
   `|X¹³ − 4Y¹³| ≤ (3501/50)·Y¹¹` with `X¹³ < 4Y¹³` (one-sided).

3. **Pinning (PROVED).**  Hence, with `q = 4^{1/13}`:
   **`0 < q − X/Y ≤ (3/2)/Y²`** for `Y ≥ 600`.  `C₁₃ = 3/2` exactly;
   the asymptotically sharp constant is `7(q − 1/q) = 1.4957635203…`
   (identity `91(4−q¹¹)/(13q¹²) = 7(q−1/q)` verified mod `q¹³ = 4`).
   General odd k: `C_k^asy = (k²−1)/24 · (4^{1/k} − 4^{−1/k})` — for k=5 this
   is `0.5616496…`, matching the banked k=5 note.

4. **Confinement (classical, Worley class).**  `C₁₃ = 3/2` is above both the
   Legendre threshold `1/2` and the Fatou threshold `1`: k=13 lands in the
   genuine **quasi-convergent (Worley) class**, `rs < 2C = 3`.  Writing
   `X/Y = g·(a/b)` in lowest terms:
   - `g ≥ 2`: `C/g² ≤ 3/8 < 1/2` → Legendre → `b = q_m` and
     `g² < (3/2)(a_{m+1}+2)`; with `a_max = 192` below `10^{102}` this gives
     `g ≤ 18` (blanket `g ≤ 50` used in the scan);
   - `g = 1`: Worley (1981) → `(a,b) = (r·p_{m+1} ± s·p_m, r·q_{m+1} ± s·q_m)`
     with `(r,s) ∈ {(1,0), (0,1), (1,1), (1,2), (2,1)}` (`rs ≤ 2`).
   Exact finite candidate family per CF index m:
   `Y ∈ {g·q_m (g ≤ 18)} ∪ {q_{m+1} ± q_m, q_{m+1} ± 2q_m, 2q_{m+1} ± q_m}`.

5. **Exact CF + scan (PROVED computation).**  cf(4^{1/13}) computed to 330
   terms with *every* partial quotient certified by integer sign evaluations
   of an exact integer polynomial (Taylor-shift/reversal; the polynomial has a
   unique real root at every step, so signs decide floors unambiguously).
   `q_m > 10^{100}` first at `m = 189`.  Family below `10^{100}`:
   **14 118 Y-values, 70 525 (X,Y) pairs — none satisfies `P(X) = 4P(Y)`.**
   Cross-checks: 34 brute-scan candidates in `Y ≤ 10^6` all fall inside the
   family (empirical Worley validation); `Y ≤ 2100` closed unconditionally by
   direct sweep; all 190 convergent pairs pass the Thue filter (the
   confinement is a genuine near-miss family, not vacuous).

**Corollary (conditional only on steps 2–4, all elementary/classical):**

> There is no k=13, N=4 solution with `n + 7 ≤ 10^{100}`; combined with the
> banked `d ≤ 220` certificates and the window `Y ≤ cd + 6`
> (`c = 1/(q−1) ∈ (8.88573, 8.88652)`): **no solution with `d ≤ 1.125·10^{99}`.**

---

## 1. Centered identity and expansion (PROVED, Lean: `ring`)

`∏_{i=1}^{13}(x+i) = P(x+7)` where `P(T) = T·∏_{j=1}^{6}(T²−j²)`.  The
elementary symmetric functions of `{1, 4, 9, 16, 25, 36}` are
`(91, 3003, 44473, 296296, 773136, 518400)`, giving the explicit odd
polynomial above.  Subtracting the leading parts,

```
P(X) = 4P(Y)   ⟺   X¹³ − 4Y¹³ = G(X,Y)
G := 91(X¹¹−4Y¹¹) − 3003(X⁹−4Y⁹) + 44473(X⁷−4Y⁷)
     − 296296(X⁵−4Y⁵) + 773136(X³−4Y³) − 518400(X−4Y)
```

(polynomial identity, PASS 5).  The degree drop 13 → 11 is the whole game:
`|X¹³ − 4Y¹³| = O(Y¹¹)` sits exactly at the borderline Thue exponent, as in
the k=5 case.

## 2. Ratio bracket from the equation (PROVED, Lean: nlinarith-ready)

`P` is strictly increasing on `[7, ∞)` (P′ has no real root ≥ 6; Sturm,
PASS 9).  Exact rational bracket for `q = 4^{1/13}`:
`89¹³ < 4·80¹³` and `4·8¹³ < 9¹³`, so `89/80 < q < 9/8`.

- `4P(Y) − P((89/80)Y) > 0` for all `Y ≥ 219` (Sturm; PASS 10), so by
  monotonicity any solution has `X > (89/80)Y`.
- `P((9/8)Y) − 4P(Y) > 0` for all `Y ≥ 6` (PASS 11), so `X < (9/8)Y`.
- **Shift certificates**: after `Y → 600 + u` both cleared polynomials have
  *all* coefficients positive (PASS 12) — in Lean each bracket inequality is
  a `nlinarith`/`positivity` one-liner on `u = Y − 600 ≥ 0`.

## 3. Exact Thue inequality (PROVED)

For odd `j`, `(X^j − A^j)/(X − A)` has nonnegative coefficients (PASS 13), so
the bracket gives `(89/80)^j Y^j ≤ X^j ≤ (9/8)^j Y^j`, and since
`(9/8)¹¹ < 4` every difference `X^j − 4Y^j` (odd `j ≤ 11`) is negative with
`|X^j − 4Y^j| ≤ t_j Y^j`, `t_j = 4 − (89/80)^j`.  Assembling `G` with
`Y ≥ Y₀ = 600`:

```
|X¹³ − 4Y¹³| ≤ [91·t₁₁ + 3003·t₉/Y₀² + 44473·t₇/Y₀⁴ + 296296·t₅/Y₀⁶
                + 773136·t₃/Y₀⁸ + 518400·t₁/Y₀¹⁰] · Y¹¹
             = C₁′·Y¹¹,   C₁′ = 70.01546605…  (exact rational, PASS 14)
             ≤ (3501/50)·Y¹¹ .
```

Moreover `G < 0` under the bracket (PASS 15), so `X < qY` strictly: the
approximation is one-sided, `X/Y ↗ q` from below.

## 4. Pinning constant C₁₃ = 3/2 (PROVED)

`X¹³ − 4Y¹³ = (X − qY)·Φ`, `Φ = Σ_{i=0}^{12} X^i (qY)^{12−i}` (verified mod
`q¹³ = 4`, PASS 16).  Each of the 13 terms of Φ exceeds `((89/80)Y)¹²`, so

```
0 < q − X/Y ≤ C₁/(13·(89/80)¹²) / Y²  with  C₁ = 3501/50,
C₁/(13·(89/80)¹²) = 4811737761054720000000000/3210875246348407823945773
                  = 1.49857512… ≤ 3/2                       (PASS 17)
```

**`0 < q − X/Y ≤ (3/2)/Y²` for every solution with `Y ≥ 600`.**  The
Lean-checkable 13th-power form (no irrational q):
`X¹³ < 4Y¹³` and `4(2Y²)¹³ < (2XY + 3)¹³`.

Exact asymptotic: `lim Y²(q − X/Y) = 91(4−q¹¹)/(13q¹²) = 7(q − 1/q) =
1.4957635203…` (PASS 18) — so 3/2 is within 0.3% of optimal; no choice of
rational bracket can push C₁₃ below ~1.496.  (Prompt heuristic 0.08k ≈ 1.04
underestimates: the true growth law is `C_k ≈ (ln 4)/12 · k ≈ 0.1155·k`.)

## 5. Small-Y bridge (banked machinery)

Window (banked): `4(n+1)¹³ ≤ (n+d+1)¹³` and `(n+d+13)¹³ ≤ 4(n+13)¹³`, i.e.
`n+1 ≤ cd ≤ n+13`, `c = 1/(q−1)`.  Exact bracket
`111253¹³ < 4·100000¹³ < 111254¹³` gives `8.88573 < c < 8.88652` (PASS 19).
So `d ≥ 221 ⟹ n ≥ ⌈221c⌉ − 13 ≥ 1951 ⟹ Y ≥ 1958 ≥ 600` (PASS 20): the
`Y₀ = 600` hypothesis is *free* once `d ≤ 220` is banked.  Conversely
`d ≤ 1.125·10^{99} ⟹ Y ≤ cd + 6 < 10^{100}` (PASS 21), which converts the
scan bound to a d-bound.

## 6. Exact continued fraction of 4^(1/13) (PROVED computation)

Method (`cf_scan.py`): maintain an integer polynomial with a *unique* real
root equal to the current complete quotient (start `z¹³ − 4`; the 12
conjugates are complex and stay complex under the Möbius steps).  Each
partial quotient is the integer where the sign of the polynomial flips —
located by exact sign bisection; then Taylor-shift by `a`, reverse
coefficients, reduce content.  No floating point anywhere in the extraction.

```
cf(4^(1/13)) = [1; 8, 1, 7, 1, 4, 13, 17, 2, 1, 1, 7, 1, 3, 2, 5, 2, 1, 1, 3,
               19, 5, 16, 1, 1, 1, 3, 4, 1, 6, 3, 12, 2, 3, 6, 13, 1, 3, 1, 1, …]
```

330 terms; advisory cross-check against a 1500-digit mpmath expansion agrees
on all 330.  Exact verification: unimodularity
`p_m q_{m−1} − p_{m−1} q_m = (−1)^{m−1}` and alternation
`sign(p_m¹³ − 4q_m¹³) = (−1)^{m+1}` for all m (PASS 2–3), and the classical
quality floor `|q − p_m/q_m| > 1/((a_{m+1}+2)q_m²)` checked exactly for all
`m ≤ 193` (PASS 4 — this is what bounds the Legendre multiplier g).
`q_m > 10^{100}` first at `m = 189`; `a_max = 192` (at one index; next
largest ~19), giving `g ≤ ⌊√(1.5·194)⌋ = 18`.

## 7. Scan results (PROVED computation)

Family enumerated with blanket `g ≤ 50` on convergents plus mediant classes
`(1,1), (1,2), (2,1)` with margin multiples `g ≤ 8`, both signs:

| quantity | value |
|---|---|
| distinct Y candidates ≤ 10^100 | 14 118 |
| (X,Y) pairs checked exactly (`X ∈ iroot13(4Y¹³) ± 2`) | 70 525 |
| pairs passing the Thue filter `|X¹³−4Y¹³| ≤ (3501/50)Y¹¹` | 662 |
| … of which true convergent denominators `Y = q_m` | 188 (all 189 with `8 ≤ q_m ≤ 10^100` pass: positive control) |
| pairs satisfying `P(X) = 4P(Y)` exactly | **0** |

The 662 Thue-passers (convergents, small multiples at large `a_{m+1}`,
mediants) are the honest near-miss family — every one with `Y ≥ 600` also
satisfies the exact pinning form `(2XY−3)¹³ < 4(2Y²)¹³ < (2XY+3)¹³`, and
every one fails the exact equation.  None is exceptional beyond that: the
smallest relative residuals behave like `1/q_m`, exactly the heuristic rate.

Cross-validations:
- brute scan of *all* `8 ≤ Y ≤ 10^6` for `|q − X/Y| < (3/2)/Y²` (float
  pre-filter with proven 1e-6 slack ≫ 8e-10 error bound, exact 13th-power
  confirmation): 34 candidates, all inside the enumerated family, none
  solves the equation;
- unconditional monotone sweep `8 ≤ Y ≤ 2100` (no approximation input):
  no solution — this independently covers the range below the confinement
  floor `Y ≥ 1958`.

**Verified bound: no k=13, N=4 solution with `d ≤ 1.125·10^{99}`** (given
banked `d ≤ 220` + the PROVED steps 2–4 + Worley).  Each extra order of
magnitude costs ~2 CF terms; `10^{1000}` is minutes of computation.

## 8. Lean formalization plan (Mathlib v4.29.1 inventory verified in-repo)

**What Mathlib has** (checked in `.lake/packages/mathlib`, rev v4.29.1):
- `Mathlib/NumberTheory/DiophantineApproximation/Basic.lean`:
  `Real.convergent : ℝ → ℕ → ℚ` (recursive floor/fract definition),
  `Real.convergent_zero/succ`, and **Legendre's theorem**
  `Real.exists_rat_eq_convergent : |ξ − q| < 1/(2·q.den²) → ∃ n, q = ξ.convergent n`
  (plus the sharpened induction form `exists_rat_eq_convergent'` via
  `ContfracLegendre.Ass`).
- `Mathlib/NumberTheory/DiophantineApproximation/ContinuedFractions.lean`:
  `Real.convs_eq_convergent`, `Real.exists_convs_eq_rat` (Legendre in
  `GenContFract` language).
- `Mathlib/Algebra/ContinuedFractions/*`: `GenContFract.of`, convergence
  (`of_convergence_epsilon`), fib lower bounds on denominators
  (`succ_nth_fib_le_of_nth_den`), `abs_sub_convs_le`
  (`|v − convs| ≤ 1/(b·B_n·B_{n+1})`), `GenContFract.determinant`
  (unimodularity), `of_den_mono`.
- `Mathlib/NumberTheory/Real/Irrational.lean`: `irrational_nrt_of_notint_nrt`
  (irrationality of `4^{1/13}` from `x¹³ = 4` with no integer root — ROUTINE).

**What Mathlib does NOT have**: Worley/quasi-convergent theory in any form —
no Fatou (`C < 1`), no mediants, no `|ξ − p/q| < C/q²` classification for
`C ≥ 1/2`, and no lower bound `|ξ − p_m/q_m| > 1/((a_{m+1}+2)q_m²)`
(the latter is derivable from `abs_sub_convs_le`-adjacent material plus
determinant identities, MEDIUM-EASY).

Difficulty ledger:

| step | status | Lean route |
|---|---|---|
| centered identity, G-identity | ROUTINE | `ring` |
| P strictly monotone on [7,∞) | ROUTINE | `nlinarith` on P(b)−P(a) = (b−a)(…) or factored derivative certificate |
| bracket (Sturm thresholds) | ROUTINE | shift certificates: all-positive coefficients in `u = Y−600` → `positivity`/`nlinarith` |
| Thue chain `|X¹³−4Y¹³| ≤ (3501/50)Y¹¹` | ROUTINE | per-power `pow_le_pow_left` + `linarith` over explicit rationals |
| pinning `0 < q − X/Y ≤ (3/2)/Y²` | ROUTINE-MEDIUM | `q := (4:ℝ)^((1:ℝ)/13)` via `rpow`, factor Φ, 13-term lower bound; or stay in the 13th-power integer form throughout |
| `g ≥ 2` case → Legendre | AVAILABLE | `Real.exists_rat_eq_convergent` directly (`C/g² ≤ 3/8 < 1/2`) |
| `g = 1` case → **Worley, C = 3/2** | **HARD (build from scratch)** | ~800–1500 lines: locate `q_m ≤ Y < q_{m+1}`, expand `(X,Y)` in the unimodular basis `((p_{m+1},q_{m+1}),(p_m,q_m))`, bound the coefficients by `rs < 3`; Stoll's `ContfracLegendre.Ass` induction is the closest template but is hardwired to `1/2`; best-approximation machinery must be built |
| CF certificate for 4^{1/13} (≈190 terms) | ROUTINE, heavy | per-term floor certificates: `a_m ≤ α_m < a_m+1` unfolds to two sign checks of integer 13th-power forms (~380 `norm_num` goals on ≤1300-digit literals); kernel-checked, no `native_decide` (repo axiom gate) |
| 70 525 candidate checks | ROUTINE, heavy | `decide`/`norm_num` on bignum identities, sliceable like the existing banked certificates; only the 662 Thue-passers actually need the full equation check if the Thue filter is formalized first |

Recommended banking order: (1) identity + bracket + Thue chain (small,
self-contained); (2) pinning in 13th-power form; (3) the Worley lemma
specialized to `C = 3/2` (the one genuinely new piece — reusable verbatim
for k=5 (C=0.61 needs only Fatou, a sub-case) and every other odd k);
(4) CF + candidate certificates to whatever d-bound the campaign needs.

## 9. Obstructions / open core

- **Worley step is the formalization bottleneck** — classical but absent
  from Mathlib; everything else is certificate engineering.
- **The full k=13 problem stays open for the same reason as k=5**: Hurwitz
  guarantees infinitely many `Y` with `‖qY‖ < 0.45/Y`, while a solution only
  needs `≈ 1.496/Y` — approximation quality alone can never finish it.  What
  must be excluded is the exact integer coincidence `P(X) = 4P(Y)` along the
  CF family: Thue-equation territory (Baker / hypergeometric).  Note Bennett
  (2001) gives effective irrationality measures for `4^{1/k}` only for
  `k = 6, 12` and prime `k ∈ [17, 347]` — **k = 13 is prime but below
  Bennett's range**; the borderline degree `|X¹³ − 4Y¹³| ~ Y¹¹` sits exactly
  at the Roth exponent for degree 13.
- Heuristic tail: a solution at convergent index m needs a relative
  coincidence `~1/q_m`; `Σ_{q_m > 10^{100}} 1/q_m < 10^{−99}` (HEURISTIC —
  the standard reason to believe the statement, localized to the explicit
  sparse family).
