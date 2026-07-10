# Erdős 686, k=5, N=4: third row, tight-window pinning, and the convergent reduction

*compute/theory, 2026-07-09.  All numerical claims in this note are backed by
exact-arithmetic scripts in this directory; every PROVED tag has been verified
symbolically (sympy over ℤ) or by exact integer computation.  Status tags:*
**PROVED** *(verified here, elementary),* **ROUTINE** *(standard Lean work, no
mathematical risk),* **HEURISTIC** *(probabilistic reasoning, not a proof),*
**OPEN** *(genuinely open).*

Scripts:
- `k5_third_row_derivation.py` — 39 exact checks: (s,t) re-derivation, rows 3–5, identities, resultants, constants.
- `k5_bracket_constants.py` — exact rational brackets for c, σ, α (Sturm-verified unique roots).
- `k5_tight_scan.c` / `k5_tight_scan_check.py` — tight-window scanner (validated against exact Python brute force) + results in `scan_out/`.
- `k5_cone_scan.c` — scanner for the banked (loose-cone) reduced problem.
- `k5_framework_check.py` — F-congruence framework and survivor structure mining.
- `k5_convergent_reduction.py` — the full-equation convergent-pinning reduction, checked to Y = 10^130.

---

## 0. Executive summary

Setting: `n ≥ 1`, `d ≥ 5`, `(n+d+1)⋯(n+d+5) = 4·(n+1)⋯(n+5)`.  Lean bank
(ErdosProblems/Erdos686.lean) closes `d < 44291`; the community lists k=5
as open for unbounded d.

Three results, in increasing strength:

1. **Third row banked-form extension (the assigned task).**  The (s,t)
   reduction extends row-by-row: with `M = 24s+t`, all five rows become
   `M+j−1 | T_j(t)` for the *single* quintic family `T_j(t) = T_1(t−95(j−1))`,
   `T_1(t) = t(t+72)(t+144)(t+216)(t+288)`.  In particular
   `T_3(t) = (t−190)(t−118)(t−46)(t+26)(t+98)`.  PROVED, Lean-ready
   (Section 2).

2. **Tight-window pinning.**  The banked cone `4s < 37t ∧ 9t < s+832` throws
   away almost all of the ratio window.  The exact window is
   **`A ≤ c·d ≤ A+4`** where `A = n+1`, `c = 1/(4^{1/5}−1) = 3.129812960…`:
   for every d there are exactly **4 candidate values of A** (Section 3).
   In (s,t) coordinates: `0 ≤ σt − s ≤ 839.05`, σ = 9.0766125506… .
   This converts the reduced problem from a 2-parameter cone into a
   1-parameter family, and the scan cost from quadratic to linear.
   PROVED, Lean-ready.

3. **Convergent-pinning reduction (the real prize, full-equation route).**
   In centered variables `X = n+d+3`, `Y = n+3` the equation is exactly
   `X⁵−5X³+4X = 4(Y⁵−5Y³+4Y)`, whence `|X⁵−4Y⁵| ≈ 8.51·Y³` — a *borderline
   Thue inequality*.  It forces `|4^{1/5} − X/Y| < 0.58/Y²` `(Y ≥ 40)`,
   which is inside the Legendre–Fatou threshold `1/Y²`.  Hence **Y must be a
   convergent denominator of cf(4^{1/5}), a bounded multiple, or a mediant
   neighbour** — an exponentially sparse explicit family.  Checking
   "no solution with `Y ≤ 10^N`" costs `O(N)` exact integer checks.
   Verified here: **no solution with `n+3 ≤ 10^120`** (75 790 candidate pairs
   checked exactly), conditional only on the two PROVED/classical steps
   (pinning inequality + Fatou), both formalizable.  (Section 6.)

Scan headlines (Section 4): in the tight window the two-row system dies at
**d = 117** and the three-row system at **d = 18**; no four- or five-row
survivor exists at all.  Verified for all `d < 10^11` (≈ t < 1.43·10^9,
far beyond the 10^7 target).  In the banked cone, by contrast, two-row
solutions keep appearing (8 hits for t < 10^6) — the cone version can never
be closed; the window was the missing rigidity, exactly as suspected.

---

## 1. Validated re-derivation of the banked (s,t) reduction

Variables (all validated against Erdos686.lean, lines ~8770–8800, 10302,
11343):

| symbol | meaning | banked form |
|---|---|---|
| `A = n+1` | window variable | `A = 3d+s = 24s+t`, `s ≥ 13` |
| `s = A − 3d` | first reduction | `13 ≤ s` for `d ≥ 125` |
| `t = A − 24s = 72d − 23A` | second reduction | `3d = 23s+t`, so `3 | 23s+t` |
| `M = 24s+t = A` | modulus | rows: `M+j−1 | R_j(d)` |

Rows of the divisor skeleton: `R_j(d) = ∏_{i=1..5}(d+i−j)`, i.e.
`n+j | R_j(d)` (`individual_divisor_skeleton_four`).  Note `R_j(d) = R_1(d−j+1)`.

**Key congruence (PROVED, polynomial identity in ℤ[d,A]):** modulo `A+j−1`,
`24s ≡ −(t+j−1)` gives `72d = 23·24s + 24t ≡ t − 23(j−1)`, hence

```
T_j(t) − 72⁵·R_j(d)  ≡  0   (mod A+j−1),      T_j(t) := ∏_{i=1..5} (t − 23(j−1) + 72(i−j))
```

as an identity in ℤ[d,A] after substituting `t = 72d−23A` (checked by exact
polynomial division, `k5_third_row_derivation.py`).  Consequently

> `A+j−1 | R_j(d)` **implies** `A+j−1 | T_j(t)` — with *no* coprimality or
> 72⁵-slack needed in this direction, because `T_j(t) − 72⁵R_j(d)` is itself a
> multiple of `A+j−1`.

(The task prompt's "72⁵-relaxed" caution is thus unnecessary for the forward
direction; the banked Lean rows 1–2 already exploit this.)

The five quintics are shifts of a single one, `T_j(t) = T_1(t − 95(j−1))`:

```
T_1(t) = t(t+72)(t+144)(t+216)(t+288)            [banked: kFiveExactRowOneTProduct]
T_2(t) = (t−95)(t−23)(t+49)(t+121)(t+193)        [banked: kFiveExactRowTwoTProduct]
T_3(t) = (t−190)(t−118)(t−46)(t+26)(t+98)        [NEW: third row]
T_4(t) = (t−285)(t−213)(t−141)(t−69)(t+3)        [NEW: fourth row]
T_5(t) = (t−380)(t−308)(t−236)(t−164)(t−92)      [NEW: fifth row]
```

Banked cone window re-derived and confirmed:
`651(23s+t) − 624(24s+t) = 27t − 3s` gives `9t < s + 832`;
`892(23s+t) − 855(24s+t) = 37t − 4s` gives `4s < 37t`; hence
`217t − 19968 < M < 223t`.  These come from the linear brackets
`651/208 < c < 892/285`, which are *convergent-level* approximations
(651/208 is literally a convergent of c) — but they open the window from
width 4 (exact) to width `0.25t + 832` in s.  That is the entire reason the
banked reduced problem still has solutions (Section 4).

## 2. The third row, banked form (Lean-ready)

Everything mirrors rows 1–2 (`k_five_row_one/two_t_product_dvd`,
lines 10040–10262).  Proposed definitions and statements:

```lean
/-- Exact third row product in (s,t) coordinates; d = (23s+t)/3. -/
def kFiveExactRowThreeST (s t : ℕ) : ℕ :=
  let d := (23 * s + t) / 3
  (d - 2) * (d - 1) * d * (d + 1) * (d + 2)

/-- Third exact reduced row as a product depending only on t (t ≥ 190). -/
def kFiveExactRowThreeTProduct (t : ℕ) : ℕ :=
  (t - 190) * (t - 118) * (t - 46) * (t + 26) * (t + 98)

theorem k_five_row_three_t_product_dvd {s t : ℕ}
    (hs13 : 13 ≤ s) (ht190 : 190 ≤ t)
    (hdiv3 : 3 ∣ 23 * s + t)
    (hrow3 : 24 * s + t + 2 ∣ kFiveExactRowThreeST s t) :
    24 * s + t + 2 ∣ kFiveExactRowThreeTProduct t
```

*Proof skeleton (ROUTINE):* identical to the banked row-2 proof: from
`3d = 23s+t`, `72d ≡ t − 46 (mod 24s+t+2)`; multiply the five factors of
`kFiveExactRowThreeST` by 72 each; the ℕ-subtractions are guarded by
`ht190` (and `d ≥ 2` from `hs13`).  For `t < 190` extend the existing decide
certificates (the banked cone already forces `t < 204` when `s < 1000`, so
the small-t band is covered by the same slices; in the tight window t < 190
corresponds to d ≤ 13270).

Combined escape form (extends `no_solution_four_five_of_combined_t_product_escape`,
line 11343): the hypothesis set gains
`24*s+t+2 ∣ kFiveExactRowThreeTProduct t` and the conclusion gains the factor
`(24s+t+2)`, dividing `T_1·T_2·T_3`.  ROUTINE.

Resultant data (PROVED, `k5_third_row_derivation.py`): the T_j are pairwise
coprime as polynomials; `Res(T_i,T_j)` depends only on `|i−j|`:

```
|i−j|=1: −5⁵·7⁶·11⁴·19⁵·23⁴·167⁴·193·239³·311²·383          (≈ −2.8·10^50)
|i−j|=2:  2²⁵·5⁵·7⁴·13²·19⁵·23³·29²·59⁴·131⁴·167³·239        (≈ 4.3·10^54)
|i−j|=3:  3²⁵·5⁵·7⁴·11³·13³·17⁴·19⁵·23²·47³·71⁴·167²·191     (≈ 2.9·10^58)
|i−j|=4: −2⁵⁰·5⁵·7⁴·11⁴·19⁵·23·41²·59³·113⁴·131³·149²·167    (≈ −3.3·10^63)
```

so `gcd(T_i(t), T_j(t))` divides a fixed integer for every t.  (These were
computed for the cascade attack of Section 5; they are not needed for the
banked extension.)

## 3. Tight-window pinning (NEW, Lean-ready)

**Lemma A (window).**  For any solution, with `A = n+1`
(from `ratio_window_four_nat`, already banked):

```
4A⁵ ≤ (A+d)⁵          -- i.e.  A ≤ c·d      (exact ⁵√ direction)
(A+d+4)⁵ ≤ 4(A+4)⁵    -- i.e.  c·d ≤ A+4
```

Since `x ↦ x⁵` is strictly monotone these are *equivalent* to
`A ≤ cd ≤ A+4`, `c = 1/(4^{1/5}−1)`.  As `c` is irrational, for each d the
candidate set is exactly the 4 integers `⌈cd⌉−4 … ⌊cd⌋`.

**Lemma B (pinning, PROVED here / ROUTINE in Lean).**
For `d, A, B : ℕ` with `d ≥ 1`, `A, B ≥ 1`:
`4A⁵ ≤ (A+d)⁵  →  (B+d+4)⁵ ≤ 4(B+4)⁵  →  A ≤ B+4.`
*Proof.*  If `B+4 < A` then `(B+4+d)·A − (A+d)·(B+4) = d(A−B−4) > 0`, so
`((B+4+d)A)⁵ > ((A+d)(B+4))⁵ ≥ 4A⁵(B+4)⁵`, giving `(B+4+d)⁵ > 4(B+4)⁵`,
contradicting the second hypothesis.  ∎  (nlinarith-friendly; no real
numbers, no 5th roots.)

**Bracket forms for certificates (PROVED, `k5_bracket_constants.py`).**
With `c_lo = 3129812960126`, `c_hi = 3129812960127` (denominator 10^12):
`c_lo/10^12 < c < c_hi/10^12`, verified by the sign of `(p+q)⁵ − 4p⁵`; in
Lean each is one `norm_num` goal on ~65-digit integers.  Then any window
candidate satisfies `−d ≤ c_lo·d − 10^12·A ≤ 4·10^12`, which pins A to an
explicitly enumerable strip for decide-certificates.

**(s,t) form.**  `σ := (c−3)/(72−23c) = 9.0766125506557153668…`, minimal
polynomial `1861153x⁵ − 16581140x⁴ − 2810720x³ − 177280x² − 4960x − 52`
(unique real root in [9,10], Sturm-verified).  Exact identity:
`σt − s = (1+23σ)(cd − A)`, hence

```
0 ≤ σt − s ≤ 4(1+23σ) = 839.0483547…
```

Lean-ready integer form, with `σ`-brackets `90766125506/10^10 < σ <
90766125507/10^10` (each a quintic sign check):

```
10^10 · s ≤ 90766125507 · t
90766125506 · t ≤ 10^10 · s + 8390483546644
```

**(M,t) form.**  `α := M/t-slope = c/(72−23c) = 24σ+1 = 1/(72·4^{1/5}−95)
= 218.8387012157371688…`, minimal polynomial
`1861153x⁵ − 407253125x⁴ − 8573750x³ − 90250x² − 475x − 1`.
`0 ≤ αt − M ≤ 4+92α = 20137.16…`; bracket `2188387012157/10^10 < α <
2188387012158/10^10` gives

```
10^10 · M ≤ 2188387012158 · t
2188387012157 · t ≤ 10^10 · M + 201371605118536
```

Compare with the banked cone `217t − 19968 < M < 223t`: width `6t + 19968`
versus constant width `20137`.  Structural explanation: the continued
fraction of c is `[3; 7, 1, 2, 2, 1, 2, 4, 56, 1, 14, 2, …]` with
convergents `3, 22/7, 25/8, 72/23, …, 651/208, 2845/909, 159971/51112, …` —
both `72/23` (the reduction matrix) and `651/208` (the banked linear bound)
are convergents of c.  The banked reduction stopped one convergent short.

**Certificate economics.**  In (d,A) coordinates a slice `d < D` costs
`4D` divisibility checks (4 candidates per d, ~90-bit products).  The
existing (s,t) cone certificates cost `Θ(D²)`-equivalent work.  Extending
the verified bound 44291 → 10^6 costs 4·10^6 kernel checks — about 20× the
existing `s<2250` certificate, sliceable into ~40 files.  ROUTINE (heavy).

## 4. Scan results

### 4.1 Tight window (scanner `k5_tight_scan.c`, validated against exact
Python brute force on d < 3·10^5 — bit-for-bit identical hit lists)

For every d, all 4 window candidates A are tested for rows 1–5
(`L_k` = rows 1..k all hold; upper rows recorded for hits too).

**Complete list of L≥2 survivors for `5 ≤ d < 10^11`:**

| d | A | rows (lower) | level |
|---|---|---|---|
| 5 | 14 | 1,2 | 2 |
| 5 | 15 | 1,2,4 | 2 |
| 6 | 15 | 1,2,4 | 2 |
| 7 | 20 | 1,2,5 | 2 |
| **9** | **26** | **1,2,3** | **3** |
| 12 | 35 | 1,2 | 2 |
| 13 | 39 | 1,2,4 | 2 |
| **18** | **55** | **1,2,3** | **3** |
| 18 | 56 | 1,2,5 | 2 |
| 19 | 56 | 1,2,5 | 2 |
| 21 | 63 | 1,2,4 | 2 |
| 22 | 65 | 1,2 | 2 |
| 45 | 140 | 1,2 | 2 |
| 46 | 140 | 1,2,5 | 2 |
| 90 | 279 | 1,2 | 2 |
| 117 | 363 | 1,2 | 2 |

- Last two-row survivor: **d = 117**.  Last three-row survivor: **d = 18**.
- **No** L4 or L5 survivor exists anywhere in the range (not even at small d).
- None satisfies the full equation (checked exactly).
- All survivors lie far below the Lean-verified bound 44291.
- Every survivor has `d < 125`, i.e. `s = A − 3d ≤ 12`: **in the banked
  branch (`s ≥ 13`, equivalently `d ≥ 125`) the tight-window two-row system
  has no solutions at all for `d < 10^11`.**  The sharpest row-route open
  lemma is therefore: *no `(d, A)` with `d ≥ 125`, `A ≤ cd ≤ A+4`,
  `A | R_1(d)`, `A+1 | R_2(d)`.*

Row-1-only hits (window + `A | R_1(d)`) keep occurring forever, per decade:

| decade | 10^0.. | 10^2.. | 10^3.. | 10^4.. | 10^5.. | 10^6.. | 10^7.. | [10^8, 8.4·10^9) |
|---|---|---|---|---|---|---|---|---|
| L1 hits | 136 | 123 | 176 | 344 | 925 | 1620 | 1319 | 3866 |

consistent with the divisor-density heuristic `Σ_d polylog(d)/d` per decade
(HEURISTIC).  The expected number of L2 hits with `d > D` scales like
`Σ_{d>D} polylog(d)/d²` — convergent, hence a *last* two-row solution exists;
empirically it is d = 117.  For L3 the tail is `Σ polylog/d³`.

### 4.2 Banked cone, for contrast (`k5_cone_scan.c`)

Exact hypothesis set of the banked reduced problem
(`13 ≤ s`, `t ≥ 95`, `4s < 37t`, `9t < s+832`, `3 | 23s+t`,
`M | T_1(t)`, `M+1 | T_2(t)`), t < 10^6:

```
(t, s, M):  (103, 97, 2431)  (171, 813, 19683)  (1035, 9525, 229635)
            (1107, 9522, 229635)  (171392, 1542320, 37187072)
            (188856, 1726422, 41622984)  (307544, 2842439, 68526080)
            (459392, 4153928, 100153664)
```

Two-row cone solutions persist at all scales (log-divergent expected count,
HEURISTIC) — **the cone version of the two-row problem can never be closed.**
Adding the third row: **zero** cone L3 solutions in `95 ≤ t < 10^6`.  So even
in the loose cone, the third row (empirically) suffices; but only the tight
window turns the heuristic tail convergent *and* makes scanning linear.

## 5. Proof attempts on the reduced (rows + window) problem

### 5.1 The cofactor-cascade identities are vacuous (PROVED no-go)

Define `f_j = R_j(d)/(A+j−1)` (integers, given the rows).  The task's
proposed identities hold and were verified symbolically, e.g.

```
f_j f_{j+1} = C_j·((d−j) f_j − (d+5−j) f_{j+1}),   C_j = shared 4-factor core,
e_1 e_2   = T_2 e_1 − T_1 e_2                      (t-form, e_j = T_j/(M+j−1)),
2 e_1 e_3 = T_3 e_1 − T_1 e_3.
```

**No-go lemma.**  Each such identity is *equivalent to* `(M+1) − M = 1`
after substituting the definitions of the cofactors: it holds for every
`(M,t)` satisfying the two divisibilities and contains no further
information.  Consequently: coprime-part extraction (`a | T_1`, `b | T_2`
after dividing by `g = gcd(e_1,e_2)`) reproduces facts already implied by
`e_j | T_j`.  The "two linear forms in divisors" analogy with Chan's k=3
gap principle fails here because both forms live at *different* moduli
(M and M+1) — in Chan's argument one modulus divides two independent
linear forms.  PROVED (verification in `k5_third_row_derivation.py`).

### 5.2 The F-congruence framework (PROVED, but reconstructive)

`F := (A+d)⁵ − 4A⁵` satisfies (validated, `k5_framework_check.py`):

- window ⇒ `0 ≤ F ≤ 4[(A+4)⁵−A⁵] − [(D+4)⁵−D⁵] ≤ 80(A+4)⁴`
  (refined constant `80 − 20·4^{4/5} = 19.371…`),
- pure algebra: `F ≡ (d−j)⁵ + 4j⁵ (mod A+j)` and
  `F ≡ −j⁵ + 4(d+j)⁵ (mod D+j)`, `D = A+d`, `j = 0..4`,
- rows ⇒ `F ≡ 4j⁵ − W(d−j) (mod A+j)`, `W(x) = 10x⁴+35x³+50x²+24x`
  (`R_1(x) = x⁵ + W(x)`), and upper rows ⇒
  `F ≡ −j⁵ + 4W̃(d+j) (mod D+j)`, `W̃(x) = 10x⁴−35x³+50x²−24x`.

So a solution forces one O(d⁴)-sized integer F into ten explicit residue
classes with CRT modulus ~d^10.  This *repackages* rows+window into "small
integer with prescribed residues", but cannot refute: F exists by
construction, and each congruence is a consequence, never a constraint on
consistency.  Useful as a certificate compressor, not as a contradiction
engine.

### 5.3 Size-ledger obstruction (HEURISTIC meta-result, honest assessment)

Any elementary contradiction of the "integer strictly between K and K+1"
type needs a forced integer with uncertainty window smaller than 1 (or
smaller than its modulus).  Inventory: window uncertainty in A is 4;
every forced integer built from k rows (cofactors f_j, pair-quotients
`Π_{6}/(A(A+1))`, triple-quotients `Π₇/(A(A+1)(A+2))`, F itself) has value
~d⁴ and A-window-induced uncertainty `≳ 4k·d^{k−1}/c ≫ d ≫ 1` for k ≥ 2.
No ℤ[d]-combination of the available forced integers has o(1) uncertainty:
the identities of 5.1 show all discovered relations reduce to CRT
tautologies.  **Conclusion: rows + window alone, treated by elementary
integer-pinching, cannot close the problem; the divisor conditions are
genuinely Hooley-type.**  This is why Section 6 switches to the full
equation.

### 5.4 Splitting-pattern rigidity (PROVED fragments; the salvage)

For `p ≥ 5`, `p^e ∥ A` and `A | R_1(d)` force `p^e | d+i` for a *single* i
(consecutive factors differ by ≤ 4).  Hence `A = 2^{a}3^{b}·u_0u_1u_2u_3u_4`
with pairwise-coprime `u_i | d+i`.  Consequences:

- every prime power in A is `≤ d+4 < A/3` (so e.g. `A+2` prime kills row 3
  instantly — visible throughout the survivor table: A+2 ∈ {17, 37, 41, 67,
  281} for the two-row-only survivors);
- **two-support uniqueness (PROVED):** if `A = u_0u_1` with `u_i | d+i`
  (co-divisors `m_i = (d+i)/u_i`), the window forces
  `m_0 m_1 ∈ [d(d+1)/(cd), d(d+1)/(cd−4)]`, an interval of length
  `4/c² + O(1/d) = 0.408… + O(1/d)` — i.e. `m_0m_1` is pinned to (at most)
  **one** admissible integer per d.  Analogous statements hold for each
  2-element support pattern.  This is the strongest elementary rigidity in
  the row problem, and the right starting point if someone attacks the
  reduced problem again;
- for ≥3-support patterns the corresponding window contains Θ(d) integers —
  no pinch (part of the 5.3 ledger).

### 5.5 What remains OPEN in the reduced problem

"No `(d, A)` with `d ≥ 118`, `A ≤ cd ≤ A+4`, `A | R_1(d)`, `A+1 | R_2(d)`"
(two rows; empirically true to 10^11) — and its three-row weakening for
`d ≥ 19`.  Both are divisor-equidistribution statements (Hooley class);
no elementary route was found, and 5.1/5.3 delimit *why*.  The scan bound
means any future Lean certificate in (d,A) coordinates immediately certifies
whatever range it covers.

## 6. The convergent-pinning reduction (full equation) — the main new result

The relaxation to rows is lossy: it forgets that the *same* cofactors must
multiply back to 4.  Keep the full equation instead.

**Centering (PROVED, identity).**  With `X := n+d+3`, `Y := n+3`
(so `X,Y ≥ 4`, `X = Y+d`):
`z(z+1)(z+2)(z+3)(z+4) = w⁵ − 5w³ + 4w` at `w = z+2`, so the equation is

```
X⁵ − 5X³ + 4X = 4(Y⁵ − 5Y³ + 4Y)          (*)
⇔  X⁵ − 4Y⁵ = 5X³ − 4X − 20Y³ + 16Y
```

**Step 1 — approximation forcing (PROVED numerics; ROUTINE to formalize).**
From (*), for `Y ≥ 40`: `1.31Y < X < 1.322Y`, hence
`|5X³ − 4X − 20Y³ + 16Y| ≤ 8.8·Y³`, while
`X⁵ − 4Y⁵ = (X − qY)·Φ`, `q := 4^{1/5}`, with
`Φ = X⁴ + X³(qY) + … + (qY)⁴ ≥ 14.5·Y⁴`.  Therefore

```
|q − X/Y| ≤ 0.61/Y²  <  1/Y²        (Y ≥ 40),
asymptotically  Y·|qY − X| → (4−q³)/q⁴ = 0.5616496275… .
```

All constants are crude and improvable; only `< 1/Y²` matters.  The
inequality chain is polynomial (no real 5th roots needed in Lean: compare
5th powers).

**Step 2 — Legendre/Fatou (classical).**  If `|q − X/Y| < 1/Y²` with
`X/Y = g·(a/b)` in lowest terms, then: if `g ≥ 2`, `|q − a/b| < 1/(4b²)`,
so by Legendre `a/b` is a convergent `p_k/q_k` and `g ≤ √(a_{k+1}+2)`;
if `g = 1`, by Fatou `a/b` is a convergent or a mediant neighbour
`(p_{k+1} ± p_k)/(q_{k+1} ± q_k)`.  **Hence every solution has**

```
Y ∈ { g·q_k (g² ≤ a_{k+1}+2) }  ∪  { q_{k+1} ± q_k },
```

where `q_k` are the continued-fraction denominators of `4^{1/5}` — a family
with exponentially growing gaps.  (Lean status: Legendre's theorem needs
formalizing if absent from Mathlib — MEDIUM; everything else is integer
arithmetic.)

**Step 3 — exact check along the family (PROVED computation,
`k5_convergent_reduction.py`).**

- cf(4^{1/5}) = `[1; 3, 7, 1, 2, 2, 1, 2, 4, 56, 1, 14, 2, 1, 1, 3, 5, 6, …]`,
  first 320 terms verified exactly (each convergent checked by the sign of
  `p⁵ − 4q⁵`, alternating);  max partial quotient among the first 260: 92
  (so `g ≤ 50` is a valid superset bound; the scan used g ≤ 50 plus mediant
  multiples g ≤ 8 for margin);
- `q_k > 10^120` at k = 244; family below 10^130: 15 158 Y-values,
  75 790 (X,Y) pairs — **none satisfies (*)**;
- independent cross-check: brute enumeration of *all* `Y ≤ 2·10^6` with
  `‖qY‖ < 0.9/Y` found exactly 21 candidates — every one a convergent
  denominator, small multiple, or mediant (validating Step 2 empirically),
  and none within 3 000 of satisfying (*) (residuals in the table in the
  script output).

**Corollary (conditional only on Steps 1–2, both elementary/classical):**

> There is no k=5, N=4 solution with `n + 3 ≤ 10^120` (hence none with
> `d ≤ 3.19·10^119`).

and the OPEN core of Erdős 686 (k=5, N=4) is reduced to:

> **Open Core (smallest checkable form).**  Only finitely many (conjecturally
> zero) convergent denominators `q_k` of `4^{1/5}` admit `g, X` with
> `Y = g·q_k` (or a mediant) satisfying `X⁵−5X³+4X = 4(Y⁵−5Y³+4Y)`.

Each additional order of magnitude in the verified bound costs ~2 CF terms;
pushing to `10^1000` is minutes of computation.  A full proof must rule out
the equation along the CF family itself: pure approximation quality can
never do it (Hurwitz guarantees `‖qY‖ < 0.45/Y` infinitely often, and our
solutions only need `0.56/Y`), so what must be excluded is the *exact*
integer coincidence at each convergent.  That is Thue-equation territory —
Baker linear-forms-in-logs or hypergeometric effective methods are the
plausible source (OPEN, outside elementary scope; note the borderline
degree: `|X⁵−4Y⁵| ~ Y³` sits exactly at the Roth exponent for degree 5,
which is why this case of Erdős 686 is the hard one).

Heuristic tail: a solution at convergent k requires an integer coincidence of
relative size `~1/q_k`; `Σ_{q_k > 10^120} 1/q_k < 10^{−119}` (HEURISTIC —
the standard reason to believe the problem is *true*, now localized to an
explicit sparse family).

## 7. Recommended banking order for the campaign

1. **Lemma B (window pinning)** + bracket constants (Section 3): small,
   self-contained, immediately upgrades every future certificate.  ROUTINE.
2. **Third-row t-product machinery** (Section 2) + extended escape theorem:
   completes the assigned banked-form task.  ROUTINE.
3. **(d,A)-coordinate decide-certificates**: extend `d < 44291` to `d < 10^6`
   in ~40 slices (4 checks per d).  ROUTINE, heavy kernel time.
4. **Convergent reduction** (Section 6): centering identity + Step-1
   inequality (ROUTINE); Legendre/Fatou (MEDIUM, check Mathlib); CF
   certificate for `4^{1/5}` via exact recurrences + alternating quintic
   signs (ROUTINE); final candidate checks (decide on big literals).
   Outcome: verified bound `~10^120`, i.e. beyond any conceivable scan,
   with the open core isolated as the CF-family statement above.

---

*Scan totals for `5 ≤ d < 10^11` (12-way parallel, `scan_out/`): L1 = 11 598,
L2 = 16 (last at d = 117), L3 = 2 (d = 9, 18), L4 = L5 = 0.  Runtime ≈ 45 min
wall on M-series.  Per-chunk logs preserved in `scan_out/chunk_*.log`.*

*Lemma B is not just ROUTINE-claimed: `compute/theory/K5WindowPin.lean`
compiles clean against this repo's Mathlib (checked via `lake env lean`),
proving `k_five_window_pin` and `k_five_window_width` with `omega`/`nlinarith`
only.  It is kept outside the build graph pending banking.*
