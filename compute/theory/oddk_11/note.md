# Erdős 686, k=11, N=4: the centered Thue reduction, two-sided pinning, and the quasi-convergent scan

*compute/theory/oddk_11, 2026-07-09.  Template: `../k5_third_row_note.md`,
Sections 5–6 (the k=5 convergent-pinning reduction).  Every numerical claim is
backed by exact arithmetic in the two scripts here; every PROVED tag was
verified symbolically (sympy over ℚ, Sturm/Descartes certificates) or by exact
integer computation.  Status tags:* **PROVED** *(verified here, elementary),*
**CLASSICAL** *(literature theorem with elementary proof, to be formalized),*
**ROUTINE** *(standard Lean work, no mathematical risk),* **OPEN**.

Scripts:
- `derivation.py` — 31 exact checks: centered identity, monotonicity, ratio
  bracket, the exact Thue inequality with rational constants, two-sided pin,
  Lean-readiness (positivity-grade) certificates, numeric grid echo.
- `cf_scan.py` — pure-integer (no floating point anywhere) continued fraction
  of 4^(1/11) to 340 certified terms; Worley candidate family to Y ≤ 10^100;
  95 813 exact equation checks; unconditional brute scan Y ≤ 2·10^5;
  empirical validation of the Worley confinement.

---

## 0. Executive summary

Setting: `n ≥ 1`, `d ≥ 1`, `(n+d+1)⋯(n+d+11) = 4·(n+1)⋯(n+11)`.  Lean bank
closes `d ≤ 220` (small-core certificate); for `d ≥ 221` the banked row-1
quotient confinement for k=11 gives quotient `q = 7` and `n ≥ 7·221 − 1 = 1546`.

In centered variables `X := n+d+6`, `Y := n+6` the equation is exactly
`P₁₁(X) = 4·P₁₁(Y)` with

```
P₁₁(T) = T(T²−1)(T²−4)(T²−9)(T²−16)(T²−25)
       = T¹¹ − 55T⁹ + 1023T⁷ − 7645T⁵ + 21076T³ − 14400T .
```

Main results (all PROVED here unless tagged):

1. **Two-sided pin.**  Every solution with `Y ≥ 100` satisfies
   `1134·Y < 1000·X < 1135·Y` and, with `α := 4^{1/11}`,

   ```
   6/5 · 1/Y²  <  α − X/Y  <  13/10 · 1/Y²          (so C₁₁ = 13/10)
   ```

   integer form `(10XY+12)¹¹ < 4·(10Y²)¹¹ < (10XY+13)¹¹`; in particular
   `X = ⌊αY⌋`.  Exact intermediate constants: `|X¹¹−4Y¹¹| ≤ B·Y⁹` with
   `B = 19375581326722967338249563/390625000000000000000000 ≈ 49.6015`, lower
   bound `4Y¹¹−X¹¹ > 40Y⁹` (so `X/Y` approaches α strictly from below); exact
   pin constants `C ≈ 1.282246 ≤ 13/10` and `c ≈ 1.227853 ≥ 6/5`; asymptotic
   `Y·(αY−X) → 55(4−4^{9/11})/(11·4^{10/11}) = 1.263606335997…`.  The k=5
   analogue was one-sided with `C₅ = 0.61`; at k=11 the constant crosses BOTH
   the Legendre threshold 1/2 and the Fatou threshold 1 — this is the
   structural novelty of the case.

2. **Quasi-convergent confinement (CLASSICAL: Worley 1981 / Dujella 2004).**
   `|α − X/Y| < C/Y²` with `C = 13/10` forces, with `g := gcd(X,Y)`:
   - `g ≥ 2`: `|α − x/y| < 13/(10g²y²) ≤ 13/40 < 1/2`, so Legendre applies:
     `Y = g·q_m` with `g² < (13/10)(a_{m+1}+2)`;
   - `g = 1`: `(X,Y) = (r·p_{m+1} ± s·p_m, r·q_{m+1} ± s·q_m)` with
     `r,s ≥ 0`, `rs < 2C = 13/5`, i.e. `rs ≤ 2`:
     `(r,s) ∈ {(1,0),(0,1),(1,1),(1,2),(2,1)}`.
   Refinement from the two-sided pin: pure convergents are impossible in the
   `g = 1` branch, since `Y²·|α − p_m/q_m| < q_m/q_{m+1} < 1 < 6/5`.  Confirmed
   empirically: none of the scan survivors is a bare `q_m`.

3. **Scan (PROVED computation, `cf_scan.py`).**  cf(4^{1/11}) =
   `[1; 7, 2, 4, 13, 1, 5, 2, 1, 1, 1, 4, 7, 2, 6, 3, 1, 1, 1, 2, 2, 1, 3, 7,
   2, 5, 7, 11, 5, 1, 5, 1, 12, 1, 799, …]`, 340 terms, every floor certified
   by two integer sign checks against x¹¹−4 (no floating point anywhere in the
   file).  `q_k > 10^100` at k = 209; partial quotients ≥ 100 below there:
   a₃₄ = 799, a₆₄ = 103, a₁₁₉ = 2589, a₁₈₂ = 114, a₂₀₉ = 442.
   Candidate family (generous superset): 15 973 values of Y ≤ 10^100,
   95 813 (X,Y) pairs — **none satisfies the equation**.  Exactly **16**
   candidates pass the two-sided pin filter (the only (X,Y) a solution could
   inhabit); all 16 lie in the strict Worley family and all fail the equation.
   Unconditional cross-check: exact monotone bisection over ALL `Y ≤ 2·10^5`
   finds no solution; and all 18 values in `[100, 2·10^5]` satisfying the
   Worley hypothesis `|α − X/Y| < 13/(10Y²)` lie in the strict theoretical
   family (0 strays — the confinement theory validated end-to-end).

4. **Corollary (conditional only on 1–2, both elementary/classical):**

   > There is no k=11, N=4 solution with `Y = n+6 ≤ 10^100`; hence (via the
   > bracket `d = X−Y > 0.134·Y` and the banked `d ≤ 220` + confinement
   > `Y ≥ 1552` inputs) **no solution with `d ≤ 10^99`**.

   Each additional order of magnitude costs ~2 CF terms.

---

## 1. Centering identity (PROVED, Lean: `ring`)

With `m = (k−1)/2 = 5`, `(k+1)/2 = 6`:

```
∏_{i=1..11}(x+i) = P₁₁(x+6),   P₁₁(T) = T·∏_{j=1..5}(T²−j²)
```

verified by symbolic expansion; coefficients as in §0.  Equivalently
`P₁₁(T) = ∏_{j=−5..5}(T−j)` — eleven increasing factors, all positive for
`T > 5`; this factored form makes strict monotonicity of `P₁₁` on `[5,∞)`
trivial (also verified via Sturm: `P₁₁'` has no root in `[5,∞)`).
Rearrangement identity on the solution set (`L := P₁₁(T) − T¹¹`):

```
X¹¹ − 4Y¹¹ = 4L(Y) − L(X)
           = −55(4Y⁹−X⁹) + 1023(4Y⁷−X⁷) − 7645(4Y⁵−X⁵)
             + 21076(4Y³−X³) − 14400(4Y−X).
```

## 2. The exact Thue inequality (PROVED)

Fix `Y₀ = 100`, `r_lo = 1134/1000`, `r_hi = 1135/1000`.  Integer checks:
`1134¹¹ < 4·1000¹¹ < 1135¹¹` (so `r_lo < α < r_hi`) and `1135⁹ < 4·1000⁹`.

**Bracket (from the equation + monotonicity).**  For `Y ≥ Y₀`:
`P₁₁(r_hi·Y) − 4P₁₁(Y) > 0` and `4P₁₁(Y) − P₁₁(r_lo·Y) > 0` on `[Y₀, ∞)`
(Sturm: no roots ≥ Y₀; largest real roots 4.20 and 63.65).  Since
`X = Y+d > Y ≥ 100 > 5` sits in the monotone region, `P₁₁(X) = 4P₁₁(Y)` forces
`r_lo·Y < X < r_hi·Y`.

**Termwise bounds.**  For odd `j ≤ 9`, `r_hi^j < 4`, so each block above
satisfies `0 < (4−r_hi^j)Y^j < 4Y^j − X^j < (4−r_lo^j)Y^j`.  Triangle
inequality and folding the lower-degree terms into the `Y⁹` term at `Y = Y₀`
(fold certificate: quartic `H(S)` with `H(10⁴) = 0`, Descartes signs
`(+,−,−,−,−)`, and the exact factorization `H(S) = (S−10⁴)·(positive cubic)`):

```
40·Y⁹ < ℓ·Y⁹ ≤ 4Y¹¹ − X¹¹ ≤ B·Y⁹,   B ≈ 49.6015,  ℓ ≈ 47.9179   (exact ℚ).
```

**Pin.**  `4Y¹¹ − X¹¹ = (αY − X)·Φ`, `Φ = Σ_{i=0}^{10} X^i(αY)^{10−i}`, and
`11·r_lo¹⁰·Y¹⁰ < Φ < 11·r_hi¹⁰·Y¹⁰`.  Division gives the two-sided pin of §0
with exact rational constants

```
C₁₁ = B/(11·r_lo¹⁰) = 5382105924089713149513767500/4197403928429317550068356771
    ≈ 1.282246 ≤ 13/10
c₁₁ = ℓ/(11·r_hi¹⁰) ≈ 1.227853 ≥ 6/5 .
```

Grid echo (mpmath, redundant): on 99 log-spaced points `Y ∈ [100, 10⁹]` the
real solution branch `X*(Y)` gives `Y²(α − X*/Y) ∈ [1.263606, 1.264554]` —
inside `(6/5, 13/10)` and converging to κ = 1.2636… from above.

**Small-Y translation.**  `d ≤ 220` is banked; `d ≥ 221` gives (banked
confinement, k=11, q=7) `n ≥ 1546`, i.e. `Y ≥ 1552 > Y₀`.  So `Y ≥ Y₀` is
automatic in the open branch, with a 15× margin.

## 3. Confinement class

`C₁₁ = 13/10` exceeds both `1/2` (Legendre) and `1` (Fatou): the k=11 case is
in the **Worley/Dujella quasi-convergent class** `rs < 2C = 13/5`.  Candidate
family per CF index m (complete list):

```
Y ∈ {g·q_m : g² < (13/10)(a_{m+1}+2)}                        [g ≥ 2 via Legendre]
  ∪ {q_{m+1} ± q_m,  q_{m+1} ± 2q_m,  2q_{m+1} ± q_m}        [g = 1, rs ≤ 2]
```

(pure convergents excluded by the 6/5 lower bound, see §0.2).  Max multiplier
over the scanned range: `g ≤ 59` (attained near a₁₁₉ = 2589; the three
survivors `56,57,58·q₁₁₈` sit exactly under this bound — `58² = 3364 <
(13/10)·2591 = 3368.3`).

## 4. Scan results (`cf_scan.py`, all exact)

- Family scanned: 15 973 Y-values ≤ 10^100 (superset margins: blanket `g ≤ 64`,
  quasi range `a ∈ 1..3, b ∈ −3..3`, multiples ≤ 8 of `q_k ± q_{k−1}`);
  95 813 (X,Y) pairs with `X ∈ ⌊(4Y¹¹)^{1/11}⌋ + [−2..3]`: **0 solutions**.
- **16 two-sided-pin survivors** (digits, first-found form):
  15 `q₂₈−q₂₇`; 21 `q₃₅+2q₃₄`; 29 `3q₅₄+q₅₃`; 48 `3q₉₂+q₉₁`;
  61,61,61 `56,57,58·q₁₁₈`; 66 `5·q₁₂₈`; 68 `3q₁₃₀+2q₁₂₉`; 74 `2·q₁₄₆`;
  80 `2·q₁₆₀`; 82 `q₁₆₆−q₁₆₅`; 83 `4·q₁₇₀`; 90 `q₁₈₃+2q₁₈₂`; 91 `q₁₈₅+2q₁₈₄`;
  97 `q₂₀₁+2q₂₀₀`.  All 16 verified members of the **strict** Worley family;
  all fail the exact equation.  (Forms with `rs > 2` are first-found scan
  labels; the strict `rs ≤ 2` or `g·q_m` representation exists at a
  neighbouring index — verified by set membership.)
- Loose-window `Y·(αY−X) ∈ [1, 3/2]` survivors: 107 (density echo of κ).
- Unconditional: integer bisection over all `Y ∈ [7, 2·10⁵]`: 0 solutions.
- Worley validation: all 18 pin-hypothesis passers in `[100, 2·10⁵]` lie in
  the strict theoretical family; 0 strays, 0 pass the two-sided filter.

**Verified d-bound: no k=11, N=4 solution with `d ≤ 10^99`** (conservative;
the scan actually gives `d > 1.34·10^99`), conditional only on §2 (PROVED,
elementary) and Worley's theorem (CLASSICAL).

## 5. Lean formalization plan (Mathlib v4.29.1, checked against this repo's checkout)

**Available in Mathlib:**

- `Real.exists_rat_eq_convergent`
  (`Mathlib/NumberTheory/DiophantineApproximation/Basic.lean`): **Legendre's
  theorem** — `|ξ − q| < 1/(2·q.den²) → ∃ n, q = ξ.convergent n`; also the
  `GenContFract` version `Real.exists_convs_eq_rat`
  (`…/DiophantineApproximation/ContinuedFractions.lean`) and the technical
  induction form `exists_rat_eq_convergent'` with `ContfracLegendre.Ass`.
- `Real.convergent` (recursive ℚ-valued convergents), `Real.convs_eq_convergent`.
- `GenContFract.abs_sub_convs_le` (`|v − Aₙ/Bₙ| ≤ 1/(Bₙ·Bₙ₊₁)`),
  `of_convergence`, determinant identity, continuant recurrences, Fibonacci
  lower bound `succ_nth_fib_le_of_nth_den`.

**Missing from Mathlib (must be built):**

- **Worley/Dujella quasi-convergent theorem** — no statement of the form
  `|α − a/b| < c/b² → (a,b) = (r·p_{m+1} ± s·p_m, r·q_{m+1} ± s·q_m), rs < 2c`
  exists in any form.  THE hard step.  The `ContfracLegendre.Ass`
  strong-induction proof (~260 lines for Legendre) is the natural template;
  estimate 600–1200 lines including the numerator/denominator sequence API
  for `Real.convergent` that it needs.  MEDIUM-HARD, elementary throughout.
- Best-approximation **lower** bound `|α − p_m/q_m| > 1/(q_m(q_{m+1}+q_m))`
  (needed for the multiplier bound `g² < C(a_{m+1}+2)`): short derivation
  from the determinant identity + alternation, ~100 lines.  EASY-MEDIUM.

**ROUTINE steps (no mathematical risk):**

1. Centering + rearrangement identities: `ring` (ℤ-valued, after the banked
   blockProduct bridge `X = n+d+6`, `Y = n+6`).
2. Monotonicity: factored form `∏_{j=−5..5}(T−j)`, positive increasing factors.
3. Bracket inequalities: after `Y = 100 + t` the cleared-denominator
   polynomials have **all coefficients ≥ 0** (verified exactly:
   `derivation.py` "Lean cert" checks) → `positivity`/`nlinarith`-trivial.
4. Fold: `H(S) = (S−10⁴)·(cubic with positive coefficients)`, likewise the
   lower-bound fold `G` — explicit factor certificates, `nlinarith`-ready.
5. Final pin in pure-ℤ form `(10XY+12)¹¹ < 4(10Y²)¹¹ < (10XY+13)¹¹`; the
   bridge to `|α − X/Y| < 13/(10Y²)` for feeding Legendre/Worley uses only
   strict monotonicity of `t ↦ t¹¹` on ℝ (odd power, exists in Mathlib).
6. CF certificate for 4^{1/11}: the homographic floor method is directly
   formalizable — `sign(A·α + B) = sign(4A¹¹ + B¹¹)` (one small lemma from
   odd-power monotonicity), then each of the 210 needed partial quotients is
   two `norm_num` goals on ≤ 2000-digit integers (420 goals total; kernel
   handles GMP-sized literals; NO native_decide, consistent with the axiom
   gate).  Same certified data gives `(4^{1/11}).convergent m = p_m/q_m`.
7. Candidate elimination: per family Y (15 973): floor certificate
   `X₀¹¹ ≤ 4Y¹¹ < (X₀+1)¹¹` (2 comparisons) + pin-window failure
   (2 comparisons), and for the 16 survivors one equation-failure check —
   ≈ 64k bignum comparisons on ≤ 2300-digit integers, band-sliced into ~50
   certificate files (the banked `k_five_gap_*` decide idiom).  ROUTINE,
   heavy kernel time.
8. Assembly: banked `d ≤ 220` small core + k=11 quotient confinement
   (`Y ≥ 1552`) + pin + Worley + scan certificates ⇒ `d ≤ 10^99` theorem.

**Effort estimate:** machinery ~1.5–2.5 kloc (dominated by Worley) + ~50
generated certificate files.  Everything except Worley is mechanical.

## 6. What remains OPEN

Identical in shape to the k=5 open core, now localized to k=11: rule out the
exact equation along the sparse family itself.  Pure approximation quality
cannot do it (solutions need `Y·‖αY‖ ∈ (6/5, 13/10)` while quasi-convergents
provide `Y·‖αY‖ < 1.3` infinitely often — the 16 survivors show the window is
hit); what must be excluded is the integer coincidence at each index.  That is
effective-Thue territory: `|X¹¹ − 4Y¹¹| ≍ Y⁹` sits exactly at the Roth
exponent for degree 11.  Note Bennett's effective irrationality measures for
`4^{1/k}` cover k=6, k=12 and prime k ∈ [17, 347] — **k=11 is not covered**
(prime but below 17), so no off-the-shelf effective bound exists.  Heuristic
tail: `Σ_{q_k > 10^100} 1/q_k < 10^{−99}`.

Asymptotic constant for the whole odd-k program:
`κ_k = e₁(k)·(4 − 4^{(k−2)/k})/(k·4^{(k−1)/k})`, `e₁(k) = Σ_{j≤(k−1)/2} j²`,
growing ≈ `(ln 4/12)·k ≈ 0.1155·k`: k=5 → κ ≈ 0.5616, k=13 → κ ≈ 1.4958
(rs ≤ 3), k=15 → κ ≈ 1.7276 (rs ≤ 3).  The Worley machinery built once for k=11 covers
every remaining odd k with only the constant changing.
