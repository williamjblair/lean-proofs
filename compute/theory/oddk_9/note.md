# Erdős 686, k=9, N=4: the centered Thue reduction past the Fatou threshold

*compute/theory/oddk_9, 2026-07-10.  Template: `../oddk_7/note.md` /
`../k5_third_row_note.md` Sections 5–6.  Every numerical claim is backed by
exact-arithmetic scripts in this directory; every PROVED tag is verified
symbolically (sympy over ℚ, shift/Sturm certificates) or by exact integer
computation.  Floats appear only in display strings and one documented
conservative seed; no decision is floating-point.  Status tags:* **PROVED**
*(verified here, elementary),* **CLASSICAL** *(literature theorem, cited as a
cross-check only — the headline no longer depends on it),* **ROUTINE /
MEDIUM / HARD** *(Lean effort estimates),* **OPEN** *(genuinely open).*

Scripts:
- `derivation.py` — 26 exact checks: centered identity, monotonicity, ratio
  bracket, the two-round Thue chain, the exact constant `C₉`, banked handoff,
  numeric grid validation (mpmath validates, never decides).
- `cf_scan.py` — pure-integer cf(4^(1/9)) (320 terms, 638 semiconvergent
  straddle certificates), exhaustive `Y ≤ 10^6` sweep, Worley-superset family
  scan to `Y ≤ 10^100`, **self-contained confinement family** (Section 3)
  with exact equation checks, empirical confinement validation.

---

## 0. Executive summary

Setting: `n ≥ 0`, `d ≥ 1`, `(n+d+1)⋯(n+d+9) = 4·(n+1)⋯(n+9)`.  In centered
variables `X = n+d+5`, `Y = n+5` the equation is exactly

```
P9(X) = 4·P9(Y),   P9(T) = T(T²−1)(T²−4)(T²−9)(T²−16)
                        = T⁹ − 30T⁷ + 273T⁵ − 820T³ + 576T          (*)
```

**The k=9 telescope.**  For `d = 1` the ratio collapses to
`(n+k+1)/(n+1) = 4`, solvable in integers iff `3 | k` (`n = k/3 − 1`); among
odd `k ∈ {5,…,15}` only `k = 9, 15` qualify.  Here `n = 2`:
`P9(8) = 4·P9(7)`, i.e. `4·5⋯12 = 4·(3·4⋯11)`.  This is an *overlapping*
pair (`d = 1 < k = 9`), outside the problem domain `m ≥ n + k` of
`ErdosProblems/Erdos686Reduction.lean`, and is the banked "k=9 exceptional
branch".  Every scan below finds exactly this coincidence and nothing else.

**Thue chain (PROVED, two rounds).**  For every solution with `Y ≥ 1330`
(forced by `d ≥ 221` via the banked (k,q) = (9,6) confinement; `d ≤ 220` is
banked), with `q := 4^(1/9)`:

```
0 < q − X/Y ≤ C₉/Y²,    C₉ = 1031/1000 = 1.031          (one-sided!)
```

with the exact round-2 constant
`C_b = 995535003783116941037651543036514369195704840308053168599900000000 /
965631239433694934260778407689252758184402619600102578277063581849
≈ 1.0309681 ≤ C₉`, within `2·10⁻⁵` of the asymptotic optimum
`κ₉ = (10/3)(q − 1/q) = 1.03095018907681…` (minimal polynomial
`6561x⁹ + 656100x⁷ + 21870000x⁵ + 270000000x³ + 900000000x − 1250000000`).

**The structural novelty of k=9:** `κ₉ > 1` — k=9 is the *first* odd k whose
pinning constant is past not only Legendre (`1/2`) but also **Fatou (`1`)**.
No constant-tightening can help (`C₉` is 2·10⁻⁵ from optimal): the
convergent/mediant family of the k=5 and k=7 notes provably does not suffice,
and a *widened quasi-convergent class* is required.  Section 3 derives it
**exactly and self-contained** (no Worley/Fatou/Legendre black box): for any
`C`, `|α − X/Y| ≤ C/Y²` confines `Y` to an explicit finite per-index family
(≈ `3C(a_{m+1}+2)` members per CF index).  With `C = C₉` the family below
`10^100` has just **575 members**.

**Scan (PROVED computation).**  cf(4^(1/9)) computed to 320 terms, every
partial quotient certified by two integer sign checks (638 straddle
certificates, no floating point anywhere in the decision path).  Exact
equation checks: 575-member self-contained family (3 429 pairs) — zero
solutions; 21 839-member classical Worley superset (131 010 pairs) — zero
solutions with `d ≥ 9`; unconditional sweep of all `Y ≤ 10^6` — only the
telescope.  **No k=9, N=4 solution with `d ≥ 9` and `Y = n+5 ≤ 10^100`.**

**Corollary (conditional only on §2 + §3, all PROVED-elementary):**
any solution with `d ≥ 221` has `X/Y > ρ₂`, so `d > (ρ₂−1)Y > 1.665283·10^99`
once `Y > 10^100`; with banked `d ≤ 220`: **no solution with
`d ≤ 1.665·10^99`.**  Each additional order of magnitude costs ~2 CF terms.

## 1. Centered identity (PROVED, Lean: `ring`)

```
∏_{i=1..9}(x+i) = P9(x+5),  P9(T) = T⁹ − 30T⁷ + 273T⁵ − 820T³ + 576T
                                  = T(T²−1)(T²−4)(T²−9)(T²−16).
```

Coefficients `30, 273, 820, 576`: elementary symmetric functions of
`{1,4,9,16}` (central factorial pattern).  Splitting the leading term,
`P9(T) = T⁹ − u(T)` with `u(T) = 30T⁷ − 273T⁵ + 820T³ − 576T`, so on
solutions

```
X⁹ − 4Y⁹ = u(X) − 4u(Y)        (degree drop 9 → 7: the whole game).
```

`P9` is strictly increasing on `[4,∞)` and `u` on `[3,∞)` (shifted
derivatives have all-nonnegative coefficients — `positivity`-grade
certificates, printed by `derivation.py`).

## 2. The exact Thue inequality (PROVED, two rounds)

All single-variable positivity claims below are certified by the shift
`Y = Y₀ + z` with **all polynomial coefficients nonnegative** (the
Lean-friendly shape; no `nlinarith` search), with an exact Sturm fallback
that was never needed.

**Round 1 (`Y ≥ 60`).**  Rational bracket `r_lo = 29/25 < q < 59/50 = r_hi`
(integer 9th-power checks).  From the equation and monotonicity:
- A1: `4·P9(Y) − P9(r_lo·Y) > 0` for `Y ≥ 60` ⇒ `X > r_lo·Y`;
- A2: `P9(r_hi·Y) − 4·P9(Y) > 0` for `Y ≥ 60` ⇒ `X < r_hi·Y`;
- B1: `4u(Y) − u(r_hi·Y) > 0` for `Y ≥ 60` ⇒ `X⁹ < 4Y⁹`, i.e. `X/Y < q` —
  the approximation is **one-sided** (X/Y approaches q strictly from below);
- B2: `4u(Y) − u(r_lo·Y) ≤ c₇ₐ·Y⁷` for `Y ≥ 2`,
  `c₇ₐ = 120 − 30·(29/25)⁷ = 42985117146/1220703125 ≈ 35.2134`.

Factoring `4Y⁹ − X⁹ = (qY − X)·Φ`, `Φ = Σ_{i=0}^{8} Xⁱ(qY)^{8−i} >
9(r_lo·Y)⁸`:

```
0 < q − X/Y ≤ C_a/Y²,   C_a = c₇ₐ/(9·r_lo⁸) = 1791046547750/1500739238883
                            ≈ 1.19344  < 6/5        (round-1 constant).
```

**Round 2 (`Y ≥ 1330`, bootstrap).**  Banked handoff: `d ≤ 220` is closed by
the banked small-core certificates; for `d ≥ 221` the banked (9,6)
constant-quotient confinement gives `n+1 ≥ 6d`, so `Y = n+5 ≥ 6·221+4 =
1330 =: Y₀`.  Feed `C_a` back in: `X/Y > q − C_a/1330² ≥ ρ₂`, with

```
ρ₂ = 11665283/10⁷,   certified by  (ρ₂ + C_a/1330²)⁹ < 4  (exact).
```

Rerunning B2 with the tight bracket (folding the positive `Y³` term at
`Y₀ = 1330`): `4u(Y) − u(ρ₂Y) ≤ c₇ᵦ·Y⁷` for `Y ≥ 1330` with
`c₇ᵦ = 120 − 30ρ₂⁷ + (3280 − 820ρ₂³)/1330⁴ ≈ 31.8163216` (exact rational in
`constants.json`), whence for **every solution with `Y ≥ 1330`**:

```
0 < q − X/Y ≤ C_b/Y² ≤ C₉/Y²,   C₉ = 1031/1000,   C_b ≈ 1.03096810 (exact ℚ).
```

Numeric echo (mpmath, redundant): along the real solution branch `X*(Y)`,
`Y²(q − X*/Y) ∈ (1.0309, 1.03096]` on a grid `Y ∈ [1330, 10^15]`, converging
to `κ₉ = 1.030950189…` from above — `C₉` cannot be improved below `κ₉ > 1`.

## 3. Confinement past Fatou: the exact widened quasi-convergent class

`C₉ > 1`: Legendre (`< 1/(2Y²)` ⇒ convergent) and Fatou (`< 1/Y²` ⇒
convergent or mediant) both fail to apply.  The classical patch is
**Worley's theorem** (Worley 1981, J. Austral. Math. Soc. 32; Dujella 2004):
`|α − a/b| < C/b²`, gcd(a,b)=1 ⇒ `(a,b) = (r·p_{m+1} ± s·p_m,
r·q_{m+1} ± s·q_m)` with `r,s ≥ 0`, `rs < 2C`; here `2C₉ = 1031/500 = 2.062`,
so `rs ≤ 2`.  We keep it only as a CLASSICAL cross-check.  The headline
instead uses the following **self-contained theorem, PROVED here**, which
handles any `C` (in particular `C < 2` as posed, but nothing below uses
`C < 2`) with two elementary continued-fraction facts.

**Ingredients.**  Let `δ_m := q_m·α − p_m`, `θ_m := |δ_m|` (`p_{−1} = 1,
q_{−1} = 0`).  Then:
- **F1 (alternation):** `sign(δ_m) = (−1)^m`;
- **F2 (exact identity):** `q_{m+1}θ_m + q_m θ_{m+1} = 1` — multiply the
  determinant identity `q_{m+1}δ_m − q_m δ_{m+1} = (−1)^m` by `(−1)^m` and
  use F1;
- **F3 (two-sided quality):** `1/(q_m+q_{m+1}) < θ_m < 1/q_{m+1}` — upper
  bound from F2 and `θ_{m+1} > 0`; lower bound from F2 and
  `θ_{m+1} < 1/q_{m+2} ≤ 1/(q_{m+1}+q_m)` (F2 at level m+1).

**Theorem (self-contained confinement).**  *Let `α` be irrational, `C > 0`,
and `X, Y ∈ ℤ`, `Y ≥ 1`, with `|αY − X| ≤ C/Y`.  Choose the (unique) index
`m` with `q_m ≤ Y < q_{m+1}` and set `r := (−1)^m(Xq_m − Yp_m)`,
`s := (−1)^{m+1}(Xq_{m+1} − Yp_{m+1})`, so that `X = r·p_{m+1} + s·p_m`,
`Y = r·q_{m+1} + s·q_m` (unimodular basis).  Then `s ≠ 0`, and exactly one
of:*

1. *`r = 0`: `Y = g·q_m` with `g = s ≥ 1`, and `g²·q_m < C(q_m + q_{m+1})`
   (hence `g² < C(a_{m+1}+2)`);*
2. *`r ≥ 1`: `s = −t` with `1 ≤ r ≤ t`, `Y = r·q_{m+1} − t·q_m`, and
   `t·Y < C(q_m + q_{m+1})`;*
3. *`r ≤ −1`: `s ≥ 2`, `Y = s·q_m − |r|·q_{m+1}` with `1 ≤ |r| ≤ s−1`, and
   `s·Y < C(q_m + q_{m+1})`.*

*Moreover, for fixed `t` (resp. `s`) the window `q_m ≤ Y < q_{m+1}` admits
at most one `r`, so the family has at most `≈ 3C(a_{m+1}+2)` members per
index.*

**Proof.**  The expansion follows from the determinant identity (both stated
combinations reproduce `X` and `Y`; the 2×2 system is unimodular).
`δ := αY − X = r·δ_{m+1} + s·δ_m`.
*`s = 0`* would give `Xq_{m+1} = Yp_{m+1}`, so `q_{m+1} | Y`
(gcd(p_{m+1},q_{m+1}) = 1 by the determinant identity), contradicting
`Y < q_{m+1}`.
*Case `r = 0`:* `Y = s·q_m > 0` forces `g := s ≥ 1`; `|δ| = g·θ_m`, so by F3
`g²q_m/(q_m+q_{m+1}) < g²q_m·θ_m = Y|δ| ≤ C`; and `q_{m+1} < (a_{m+1}+1)q_m`
gives `g² < C(a_{m+1}+2)`.
*Case `r ≥ 1`:* `s·q_m = Y − r·q_{m+1} < (1−r)q_{m+1} ≤ 0` forces
`s = −t ≤ −1`.  By F1, `r·δ_{m+1}` and `−t·δ_m` share the sign `(−1)^{m+1}`,
so `|δ| = r·θ_{m+1} + t·θ_m > t·θ_m > t/(q_m+q_{m+1})` (F3), giving
`t·Y < C(q_m+q_{m+1})`.  From `Y < q_{m+1}` and `q_m < q_{m+1}`:
`r·q_{m+1} = Y + t·q_m < (1+t)·q_{m+1}`, so `r ≤ t`.
*Case `r ≤ −1`:* `s·q_m = Y + |r|q_{m+1} ≥ q_m + q_{m+1} > 2q_m` forces
`s ≥ 2`.  Both `s·δ_m` and `−|r|·δ_{m+1}` have sign `(−1)^m`, so
`|δ| = s·θ_m + |r|·θ_{m+1} > s·θ_m > s/(q_m+q_{m+1})`, giving
`s·Y < C(q_m+q_{m+1})`; and `|r|·q_{m+1} = s·q_m − Y ≤ (s−1)q_m <
(s−1)q_{m+1}` gives `|r| ≤ s−1`.
Uniqueness of `r`: `q_m ≤ r·q_{m+1} − t·q_m < q_{m+1}` pins `r` to a
half-open interval of length `1 − q_m/q_{m+1} < 1` (similarly in case 3).  ∎

**Remarks.**  (a) Class 2 with `(r,t) = (1,1)` is the Fatou mediant
`q_{m+1} − q_m`; class 1 with `g = 1` is the convergent itself — the theorem
degenerates to Legendre/Fatou families for `C < 1`.  (b) Worley's `rs < 2C`
is a sharper *shape* constraint; our per-candidate filter
`t·Y < C(q_m+q_{m+1})` is what the enumeration uses — both are exact integer
tests.  (c) Everything in the proof is two-line CF algebra on top of the
determinant identity — no induction on approximations (contrast Legendre's
proof); this is the Lean-friendliest confinement statement we know of (§5).

**Instantiation for k=9** (`C = C₉ = 1031/1000`, applied with `X = ⌊qY⌋`
since the approximation is one-sided): candidate family per index `m`

```
Y ∈ {g·q_m : g²·q_m < C₉(q_m+q_{m+1})}                       [g ≤ 20 always]
  ∪ {r·q_{m+1} − t·q_m : t·Y < C₉(q_m+q_{m+1}), r unique}
  ∪ {s·q_m − r·q_{m+1} : s·Y < C₉(q_m+q_{m+1}), r unique}.
```

Below `10^100` (CF indices m ≤ 191) this is **575 values of Y** — the tight
family.  The scan *additionally* runs the classical Worley superset
(convergent multiples `g ≤ max(50, per-index bound)`, quasi-convergents
`r·q_{m+1} ± s·q_m` with `rs ≤ 4` and margin multiples `g ≤ 8`): 21 839
values — 38× the tight family, for cross-validation and margin.  All 21
brute-scan Thue survivors (`Y ≤ 2·10^5`) lie in **both** families (empirical
completeness of the theorem and of Worley's).

## 4. cf(4^(1/9)) and scan results (PROVED computation)

Extraction is pure integer arithmetic: exact rational sandwich
`r/10^500 < q < (r+1)/10^500` from an integer 9th root, interval-floor
agreement for 320 terms.  **Certification** is by straddle: each partial
quotient `a_{m+1}` is pinned by two integer sign evaluations of `u⁹ − 4v⁹`
at the semiconvergents `s_a, s_{a+1}` (`s_a` on the far side — it *is* the
(m+1)-convergent — and `s_{a+1}` across `q`): **638 certificates for terms
a₁…a₃₁₉**, plus the floor bracket `1⁹ < 4 < 2⁹` for a₀.  Convergents
re-verified independently by sign alternation of `p⁹ − 4q⁹` and the
determinant identity.

```
cf(4^(1/9)) = [1; 6, 201, 1, 2, 352, 1, 1, 5, 2, 1, 1, 199, 11, 2, 2, 1, 1,
               1, 33, 1, 4, 1, 37, 2, 6, 1, 10, 2, 6, 1, 2, 17, 1, 34, 93, …]
max a_m (m < 320) = 352 (at m = 5);  q_m > 10^100 at m = 191;
320 terms reach q_m ~ 10^164.
```

Results (all decisions exact):

- **Unconditional sweep:** all `5 ≤ Y ≤ 10^6` by monotone integer bisection:
  the only `(Y,X)` with `P9(X) = 4·P9(Y)` is the telescope `(7, 8)` — `d = 1`,
  outside the `d ≥ 9` problem domain.  No CF theory used; covers all `d`.
- **Self-contained family (tight):** 575 Y ≤ 10^100, 3 429 (X,Y) pairs with
  `X ∈ iroot9(4Y⁹) ± 2`: **zero equation hits** (the telescope's `Y = 7`
  does not even satisfy the Thue hypothesis — `|q·7 − 8| = 0.166 > C₉/7`).
- **Worley superset:** 21 839 Y ≤ 10^100, 131 010 pairs: zero hits with
  `d ≥ 9`; the telescope appears (via `Y = 7 = q_1 + q_0`) and is the *only*
  coincidence.  239 pairs pass the exact Thue filter
  `(X₀ + C₉/Y)⁹ ≥ 4Y⁹` — the honest near-miss family (even-index convergents
  and variants); every one fails the equation.
- **Empirical confinement validation:** all 21 values `Y ≤ 2·10^5` passing
  the Thue filter are classified inside the family (convergent multiples
  `g·q_m` with `g² ≤ C₉(a_{m+1}+2)` — 18 of them are `g·q₄` (g = 2…19),
  riding the spike `a₅ = 352` — plus `r·q_{m+1} ± s·q_m` forms, `rs ≤ 2`).

**Corollary.**  No k=9, N=4 solution with `d ≥ 9` and `Y = n+5 ≤ 10^100`;
hence (via `d > (ρ₂−1)Y` for `d ≥ 221`, banked `d ≤ 220`): **no solution
with `d ≤ 1.665283·10^99`** — conditional only on §2 (PROVED) and §3
(PROVED).  Unlike k=5/7/11/13, *no classical black box remains* in the k=9
chain.

**OPEN core (k=9).**  Same shape as k=5/7: rule out the exact integer
coincidence `P9(X) = 4·P9(Y)` along the sparse CF family itself.
`|X⁹ − 4Y⁹| ~ 31.8·Y⁷` sits exactly at the Roth exponent for degree 9; no
effective irrationality measure for `4^(1/9)` exists (Bennett 2001 covers
`k = 6, 12` and prime `k ∈ [17, 347]`; 9 is neither).  Heuristic tail:
`Σ_{q_m > 10^100} 1/q_m < 10^{−99}`.

## 5. Lean formalization plan (Mathlib v4.29.1 inventory as per ../oddk_7 note)

Available: Legendre (`Real.exists_rat_eq_convergent`), `Real.convergent`
recursion, `GenContFract` determinant/approximation API, irrationality via
`irrational_nrt_of_n_not_dvd_multiplicity` (x⁹ = 4, p = 2, 9 ∤ 2).
Missing: any confinement past Legendre; convergent-distance lower bound;
CF certificates for algebraic numbers (see the k=7 note's inventory — grep
re-verified there).

Difficulty ledger (deltas from the k=7 plan):

1. **ROUTINE.**  Centered identity + `u`-split: `ring`.  Bracket + two-round
   chain (A1, A2, B1, B2, B2′): all-nonneg-coefficient shift certificates at
   `Y = 60 + z` / `Y = 1330 + z` (printed); 9th-power bracket facts are
   `norm_num` on ≤ 50-digit integers.  ρ₂-bootstrap: one more `norm_num`
   goal `(ρ₂·1330² + C_a·…)⁹ < 4·(…)⁹` on ~90-digit integers.  Handoff:
   banked (9,6) confinement + banked `d ≤ 220` + banked exceptional-branch
   telescope.  Integer pinning form (no real q needed):
   `X⁹ < 4Y⁹` and `4(10⁷Y²)⁹ < (10⁷XY + C₉·10⁴·Y·…)⁹`-style two-sided
   9th-power comparisons.
2. **MEDIUM — the payoff of §3.**  The self-contained confinement theorem
   needs only: convergent recurrences, determinant identity (in Mathlib),
   alternation F1, the exact identity F2 (2 lines from determinant), F3
   (2 lines from F2), and the case analysis (±20 lines of `omega`/`nlinarith`
   arithmetic).  Estimate **300–500 lines total** — versus 600–1500 for
   Worley in the k=11/k=13 plans.  It immediately supersedes the Fatou step
   in the k=5/k=7 plans and the Worley step in the k=11/13/15 plans: **build
   once, close the confinement step for all six odd k.**
3. **ROUTINE-heavy.**  CF certificate: the 638 straddle sign checks
   formalize as `norm_num` goals on ≤ 1000-digit integers (the semiconvergent
   monotonicity lemma is small); 2×191 needed below 10^100.  Kernel-only,
   no `native_decide` (repo axiom gate).
4. **ROUTINE-heavy.**  Candidate elimination: 575 tight-family Y-values,
   ~3.4k disequalities `P9(X) ≠ 4·P9(Y)` on ≤ 900-digit integers, sliceable
   per the banked manifest/audit idiom.

Banking order: (1) integer lemmas file `OddK9Pinning.lean`; (2) the §3
confinement theorem (shared infrastructure — highest campaign value);
(3) CF straddle certificates; (4) family disequalities ⇒ verified
`d ≤ 1.665·10^99` with the open core isolated as the CF-family statement.
