# Erdős 686, k=15, N=4: centered Thue reduction, the largest constant, and the widened quasi-convergent scan

*compute/theory/oddk_15, 2026-07-10.  Template: `../oddk_7/note.md` /
`../k5_third_row_note.md` Sections 5–6.  Every numerical claim is backed by
exact-arithmetic scripts in this directory; every PROVED tag is verified
symbolically (sympy over ℚ, shift/Sturm certificates) or by exact integer
computation.  Floats appear only in display strings and one documented
conservative pre-filter (slack 0.7 ≫ 10⁻⁹ float error; every accepted
candidate is confirmed by an exact 15th-power window test); no decision is
floating-point.  Status tags:* **PROVED**, **CLASSICAL** *(cited cross-check
only)*, **ROUTINE/MEDIUM/HARD** *(Lean effort)*, **OPEN**.

Scripts:
- `derivation.py` — 13 exact checks: centered identity and expansion,
  15th-power brackets, the crude all-Y bracket (self-contained `Y₀`),
  monotonicity, tight ratio bracket, the **two-sided** Thue band, the exact
  constant `C₁₅ = 1729/1000`, end-to-end grid validation.
- `cf_scan.py` — 10 exact checks: pure-integer cf(4^(1/15)) (336 terms, 670
  straddle certificates), brute window scan `Y ≤ 10^6`, banked-region
  catalog `d ≤ 220`, unconditional sweep `Y ≤ 10^6`, Worley-superset family
  to `Y ≤ 10^100`, **self-contained confinement family** (Section 3), exact
  equation checks throughout, verified d-bound.

---

## 0. Executive summary

Setting: `n ≥ 0`, `d ≥ 1`, `(n+d+1)⋯(n+d+15) = 4·(n+1)⋯(n+15)`.  In
centered variables `X = n+d+8`, `Y = n+8` the equation is exactly

```
P(X) = 4·P(Y),   P(T) = T·∏_{j=1..7}(T²−j²)
     = T¹⁵ − 140T¹³ + 7462T¹¹ − 191620T⁹ + 2475473T⁷ − 15291640T⁵
       + 38402064T³ − 25401600T                                      (*)
```

**The k=15 telescope.**  `d = 1` collapses the ratio to `(n+16)/(n+1) = 4`,
solved by `n = 4`: `P(13) = 4·P(12)`, i.e. `6·7⋯20 = 4·(5·6⋯19)` —
overlapping blocks (`d = 1 < k = 15`), outside the problem domain
`m ≥ n + k`, closed by the banked `d ≤ 220` machinery.  Every scan below
finds exactly this coincidence and nothing else.

**Self-contained small-Y bridge (PROVED — no banked input needed).**  The
crude bracket `P(X) > (X−7)¹⁵`, `P(Y) < (Y+7)¹⁵` etc. gives, for *every*
solution, `(ρ_lo−1)Y − 7ρ_lo < d < (ρ_hi−1)Y + 7ρ_hi + 7` with
`ρ_lo = 109682397/10⁸ < 4^(1/15) < 109682598/10⁸ = ρ_hi` (15th-power sign
checks).  Hence `d ≥ 221 ⇒ Y ≥ Y₀ = 2131` — independently of the banked
(15,10) confinement, which would give the slightly stronger `Y ≥ 2217`.

**Thue band (PROVED, two-sided).**  For every solution with `Y ≥ 2131`,
with `R(T) := T¹⁵ − P(T)` (so `X¹⁵ − 4Y¹⁵ = R(X) − 4R(Y)` on solutions),
shift-certificates give the **band**

```
−C_A·Y¹³ ≤ X¹⁵ − 4Y¹⁵ ≤ −C_B·Y¹³
C_A = 140(4 − ρ_lo¹³) + 1/100 ≈ 94.522349     (exact ℚ in constants.json)
C_B = 140(4 − ρ_hi¹³) − 1/200 ≈ 94.496259     (exact ℚ, width ≈ 0.026)
```

— in particular `X¹⁵ < 4Y¹⁵` strictly (one-sided approach from below), and
via `a¹⁵−b¹⁵ = (a−b)Σaⁱb^(14−i)` with all 15 terms `> (ρ_lo·Y)¹⁴`:

```
0 < 4^(1/15) − X/Y ≤ C₁₅/Y²,   C₁₅ = 1729/1000
                               [C_A/(15ρ_lo¹⁴) = 1.727930158… ≤ C₁₅, exact]
```

`C₁₅` is the **largest constant in the odd-k program** and is within
3·10⁻⁴ of the asymptotic optimum `κ₁₅ = 140(4−q¹³)/(15q¹⁴) =
(28/3)(q − 1/q) = 1.7276232506…`: k=15 sits far past both the Legendre
(1/2) and Fatou (1) thresholds, and past the `rs ≤ 2` Worley regime of
k=9/11/13 — `2C₁₅ = 3.458 ∈ (3,4]` puts it in the **`rs ≤ 3` class**, the
widest of the six odd k.

**Confinement.**  Section 3 instantiates the exact self-contained
confinement theorem (proved in `../oddk_9/note.md` §3 — any `C`, no
classical black box): with margin constant `C = 9/5 ≥ C₁₅` the tight family
below `10^100` has **1 012 members**.  The classical Worley route
(`rs < 2C₁₅`, i.e. `rs ≤ 3`: shapes `(1,1),(1,2),(2,1),(1,3),(3,1)`) is kept
as a CLASSICAL cross-check; the generous superset scan (21 001 Y-values)
covers both with wide margins.

**Scan (PROVED computation).**  cf(4^(1/15)) to 336 terms, every partial
quotient pinned by two integer sign checks (670 straddle certificates).
Exact equation checks: tight family (6 032 pairs) — only the telescope;
superset (125 970 pairs) — only the telescope; unconditional sweep
`Y ≤ 10^6` — only the telescope; per-d banked-region catalog `d ≤ 220`
(50 489 window checks) — only the telescope.  **No k=15, N=4 solution with
`d ≥ 15` and `Y = n+8 ≤ 10^100`.**

**Corollary (conditional only on the PROVED chain + §3):** any solution with
`Y > 10^100` has `d > (ρ_lo−1)·10^100 − 7ρ_lo`; with the banked `d ≤ 220`
branch: **no solution with `d ≤ 9.6824·10^98`.**  Each additional order of
magnitude costs ~2 CF terms.

## 1. Centered identity (PROVED, Lean: `ring`)

With `(k+1)/2 = 8`: `∏_{i=1..15}(x+i) = P(x+8)`, `P(T) = T·∏_{j=1..7}
(T²−j²) = ∏_{j=−7..7}(T+j)`.  The elementary symmetric functions of
`{1,4,9,16,25,36,49}` give `e₁…e₇ = 140, 7462, 191620, 2475473, 15291640,
38402064, 25401600` (and `P(8) = 15!` as a sanity anchor).  Both `P` and
`R = T¹⁵ − P` are strictly increasing on `[8,∞)`: `P` as a product of 15
increasing positive factors; `R′ > 0` by the explicit pairing certificate
`11e₂/13e₁, 7e₄/9e₃, 3e₆/5e₅ < 64 = 8²` (all exact ℚ; Sturm double-check).

## 2. The exact Thue band (PROVED)

Fix `Y₀ = 2131` (§0 bridge).  All certificates are the shift
`Y = 2131 + v` with **all coefficients nonnegative** (Lean
`positivity`-grade; printed by `derivation.py`).

- **Ratio bracket.** `4P(Y) − P(ρ_lo·Y) > 0` and `P(ρ_hi·Y) − 4P(Y) > 0` on
  `[Y₀,∞)`; with `P` monotone and `X > Y ≥ Y₀ > 8`:
  `ρ_lo·Y < X < ρ_hi·Y`.
- **Band.**  `R` monotone on the bracket plus three shift-certificates
  (`F1, F2, F3` in the script) squeeze `X¹⁵ − 4Y¹⁵ = R(X) − 4R(Y)` into
  `[−C_A·Y¹³, −C_B·Y¹³]`.  The band has *relative width 2.8·10⁻⁴* — the
  narrowest two-sided pin in the odd-k program — and doubles as a powerful
  scan filter: below `10^100` exactly **one** candidate pair survives it
  (a `2q₁₇+q₁₆` quasi-convergent at `Y ≈ 10^12`, which then misses the
  equation by `|P(X)−4P(Y)|/Y¹³ ≈ 0.0143`, against a generic scale of 94.5).
- **Pin.**  Dividing by `Φ = Σ_{i<15} Xⁱ(qY)^{14−i} > 15(ρ_lo Y)¹⁴` gives
  `0 < q − X/Y ≤ C₁₅/Y²` for `Y ≥ 2131`, `C₁₅ = 1729/1000` (exact chain
  `C_A/(15ρ_lo¹⁴) ≤ C₁₅` checked in ℚ).  Legendre-branch sanity:
  `C₁₅/4 = 0.43225 < 1/2`, so `g ≥ 2` multiples still reduce to Legendre.

Validation (never decides): the five certificates re-verified exactly at 13
grid points `Y ∈ [2131, 10^15]`; 147 convergent-quality pairs `(g·p_m,
g·q_m)` pushed end-to-end through the implication (Thue band ⇒ pin) against
a 10⁻⁴⁰ rational sandwich of `q`; 2000 random probes found 0 equation hits
and 0 band intrusions (expected ≈ 1 — the band is that narrow).

## 3. Confinement: the widened quasi-convergent class at `rs ≤ 3`

`C₁₅ = 1729/1000` is past every classical threshold; the k=9 note (§3)
proves the **self-contained confinement theorem** used here verbatim: for
`|αY − X| ≤ C/Y` with `q_m ≤ Y < q_{m+1}`, the unimodular expansion
`(X,Y) = (r·p_{m+1} + s·p_m, r·q_{m+1} + s·q_m)` lands in exactly one of

```
(i)   Y = g·q_m,            g²·q_m < C(q_m+q_{m+1})   [⇒ g² < C(a_{m+1}+2)]
(ii)  Y = r·q_{m+1} − t·q_m, 1 ≤ r ≤ t,  t·Y < C(q_m+q_{m+1})
(iii) Y = s·q_m − r·q_{m+1}, 1 ≤ r < s,  s·Y < C(q_m+q_{m+1})
```

with at most one `r` per `t` (resp. `s`) — only ingredients: the exact
identity `q_{m+1}θ_m + q_mθ_{m+1} = 1` and sign alternation.  Instantiated
with the margin constant `C = 9/5 ≥ C₁₅`: **1 012 candidates below
`10^100`** (5 of them outside the generous Worley superset — classes (ii)
and (iii) at large `t`, `s`).

CLASSICAL cross-check (Worley 1981 / Dujella 2004): `rs < 2C₁₅ = 3.458`,
i.e. `rs ≤ 3`, shapes `(r,s) ∈ {(1,0),(0,1),(1,1),(1,2),(2,1),(1,3),(3,1)}`
with per-index multiple bound `g² < C(q_{m+1}+q_m)/q_m` on convergents.  The
scan enumerates the superset (blanket `g ≤ max(60, per-index)`, both signs,
margin multiples `g ≤ 8` on quasi-convergents): 21 001 Y-values, and every
brute-scan window survivor `Y ≤ 10^6` (42 pairs, exact 15th-power window
`|αY − X| < (9/5)/Y`) lies in **both** families; the `g ≥ 2` reduced parts
are all pure convergents, exactly as the Legendre branch predicts.

## 4. cf(4^(1/15)) and scan results (PROVED computation)

Extraction: exact rational sandwich of `4^(1/15)` at 10⁻⁴⁸⁰ from an integer
15th root; CF of both endpoints; common prefix (336 terms).
**Certification by straddle:** each `a_{m+1}` pinned by two integer sign
evaluations of `u¹⁵ − 4v¹⁵` at the semiconvergents `s_a` (far side — it *is*
the (m+1)-convergent) and `s_{a+1}` (across): **670 certificates**, plus
`1¹⁵ < 4 < 2¹⁵` for `a₀`.  Convergents re-verified by sign alternation of
`p¹⁵ − 4q¹⁵` and the determinant identity.

```
cf(4^(1/15)) = [1; 10, 3, 20, 5, 1, 109, 4, 7, 2, 2, 1, 6, 21, 9, 1, 5, 1,
                6, 2, 1, 1, 1, 9, 2, 2, 21, 3, 2, 1, 1, 18, 1, 3, 1, 1, 1,
                6, 3, 1, …]
q_m > 10^100 first at m = 207 (q₂₀₇ ≈ 4.9·10^100);
max a_m for m ≤ 208: 109 (at m = 6);  max a_m for m ≤ 335: 506 (at m = 311).
```

Results (all decisions exact):

| check | scope | equation hits |
|---|---|---|
| unconditional monotone sweep | all `Y ∈ [8, 10^6]` | only `(12,13)` (d=1) |
| banked-region catalog, per-d crude-bracket windows | all `d ∈ [1,220]`, 50 489 checks | only `(12,13)` |
| brute window scan `|αY−X| < 1.8/Y` | all `Y ∈ [9, 10^6]`, 42 pairs | none |
| tight self-contained family (§3) | 1 012 Y ≤ 10^100, 6 032 pairs | only `(12,13)` |
| Worley superset | 21 001 Y ≤ 10^100, 125 970 pairs | only `(12,13)` |

Filter cascade on the superset: 775 pairs pass the one-sided Thue filter
`|X¹⁵−4Y¹⁵| ≤ C_A·Y¹³` (the honest near-miss family: convergents and
variants — positive control); exactly **1** survives the two-sided band and
then fails the equation by 4 orders of magnitude below the generic residual
scale.  Zero near-misses anywhere.

**Corollary.**  No k=15, N=4 solution with `d ≥ 15` and `Y = n+8 ≤ 10^100`;
hence (crude bracket `d > (ρ_lo−1)Y − 7ρ_lo`, banked `d ≤ 220`): **no
solution with `d ≤ 9.6824·10^98`** — conditional only on §2 + §3, with the
classical Worley route as an independent second witness.

**OPEN core (k=15).**  Rule out the exact coincidence `P(X) = 4P(Y)` along
the CF family.  `|X¹⁵ − 4Y¹⁵| ~ 94.5·Y¹³` sits exactly at the Roth exponent
for degree 15; Bennett (2001) covers `k = 6, 12` and prime `k ∈ [17,347]` —
**k=15 is composite and uncovered**, so no off-the-shelf effective
irrationality measure exists.  Heuristic tail: `Σ_{q_m>10^100} 1/q_m <
10^{−99}`.

## 5. Lean formalization plan (Mathlib v4.29.1; inventory as in ../oddk_7 note)

1. **ROUTINE.**  Centered identity, `R`-split, monotonicity (factored form
   `∏_{j=−7..7}(T+j)`; pairing certificate for `R′`), crude bracket (pure
   15th-power `norm_num` on ≤ 130-digit integers), ratio bracket and the
   three band certificates — all-nonneg shift polynomials at `Y = 2131 + v`
   (the script prints them; `positivity`-grade).  The banked `d ≤ 220` +
   telescope branch already exists; the self-contained `Y₀ = 2131` bridge
   removes any dependence on the (15,10) confinement lemma.
2. **MEDIUM (shared, build once).**  The §3 confinement theorem — same
   ~300–500-line build as detailed in the k=9 plan; k=15 only changes the
   constant to `9/5` and the caps to `t·Y < (9/5)(q_m+q_{m+1})`.
3. **ROUTINE-heavy.**  670 straddle `norm_num` goals (≤ 2700-digit
   integers; 2×208 needed below 10^100); 1 012-member family ⇒ ~6k
   disequalities `P(X) ≠ 4P(Y)` on ≤ 1600-digit integers, sliceable per the
   banked manifest/audit idiom; no `native_decide` (repo axiom gate).
4. Assembly: crude bracket ⇒ `Y ≥ 2131`; band ⇒ pin; confinement ⇒ family;
   certificates ⇒ `d ≤ 9.68·10^98`.

The two-sided band (unique among the six odd k in narrowness) also gives the
formalizer a luxury: the final candidate elimination can use the band filter
(2 comparisons each) to discharge all but 1 of the 775 Thue-passers without
touching the full equation.
