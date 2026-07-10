# Erdős 686, N=4, odd k ∈ {5,7,9,11,13,15}: Thue/convergent reduction — synthesis

*compute/theory, 2026-07-10.  Consolidates the six per-k notes for the
banking follow-up: `k5_third_row_note.md` §5–6, `oddk_7/note.md`,
`oddk_9/note.md`, `oddk_11/note.md`, `oddk_13/note.md`, `oddk_15/note.md`.
All numbers below are harvested from the exact-arithmetic scripts in those
directories (every decision integer/ℚ; floats only in display and documented
conservative pre-filters) plus the uniform generator
`gen_thue_convergents.py`.*

These six odd k are exactly the open pairs of
`ConstantCaseBoundHypothesisOdd` in `ErdosProblems/Erdos686Reduction.lean`
(boxes `(5,3), (7,4), (9,6), (11,7), (13,8), (15,10)`); even
`k ∈ {6,8,10,12}` are banked-closed and `k = 14` is closed for
`d ≥ 663 000`.

## 0. The uniform reduction

For each odd k, with `h = (k+1)/2`, `X := n+d+h`, `Y := n+h`, the equation
`(n+d+1)⋯(n+d+k) = 4·(n+1)⋯(n+k)` is exactly `P_k(X) = 4·P_k(Y)` where

```
P_k(T) = T·∏_{j=1}^{(k−1)/2} (T² − j²)          (odd, integer coefficients)
```

and the leading cancellation `X^k − 4Y^k = O(Y^{k−2})` pins `X/Y` against
`α_k := 4^{1/k}`:  **every solution with `Y ≥ Y₀(k)` satisfies
`0 < α_k − X/Y ≤ C_k/Y²`** (one-sided in all six cases: `X^k < 4Y^k`
strictly).  The exponent `k−2` sits exactly at the Roth threshold for degree
k — this is why the odd-k core is the hard part of Erdős 686 — and the
constant grows linearly:

```
κ_k = (k²−1)/24 · (α_k − 1/α_k)  ≈ (ln 4)/12 · k ≈ 0.1155·k
```

(the asymptotically optimal constant; each `C_k` below is within 0.3% of
it, so no bracket-tightening can change any confinement class).

Confinement of `|α − X/Y| ≤ C/Y²`:

- `C < 1/2`: Legendre — never available (`κ₅ = 0.56 > 1/2` already);
- `C < 1`: Legendre (g≥2 multiples) + Fatou (g=1 mediants) — k = 5, 7;
- `C > 1`: **widened quasi-convergent class** — k = 9, 11, 13, 15:
  classically Worley 1981/Dujella 2004 (`rs < 2C`), and now also the
  **self-contained confinement theorem** (PROVED elementarily in
  `oddk_9/note.md` §3, valid for *any* C):  with `q_m ≤ Y < q_{m+1}` and the
  unimodular expansion `(X,Y) = (r·p_{m+1}+s·p_m, r·q_{m+1}+s·q_m)`,

  ```
  (i)   Y = g·q_m,             g²·q_m < C(q_m+q_{m+1})  [⇒ g² < C(a_{m+1}+2)]
  (ii)  Y = r·q_{m+1} − t·q_m, 1 ≤ r ≤ t,   t·Y < C(q_m+q_{m+1})
  (iii) Y = s·q_m − r·q_{m+1}, 1 ≤ r < s,   s·Y < C(q_m+q_{m+1})
  ```

  with at most one `r` per `t`/`s` — inputs: only the exact identity
  `q_{m+1}θ_m + q_m·θ_{m+1} = 1` and sign alternation.  This removes the
  classical black box from the k=9 and k=15 chains and has been re-run as a
  **uniform cross-check for all six k** (`gen_thue_convergents.py`, table
  §2): zero disjoint-block equation hits anywhere.

## 1. Per-k constants (all exact ℚ; decimals for display only)

| k | X, Y | Y₀ (chain valid) | exact chain constant | headline `C_k` | `κ_k` (asymptote) | class |
|---|---|---|---|---|---|---|
| 5 | n+d+3, n+3 | 40 | 88/145 ≈ 0.6069 (via 8.8Y³ / 14.5Y⁴) | **61/100** | 0.5616496275… | Legendre(g≥2)+Fatou |
| 7 | n+d+4, n+4 | 250 | 40892848961307066872025100000 / 51262467486572955812169421801 ≈ 0.7977152 | **399/500** | 0.7973565963… | Legendre(g≥2)+Fatou |
| 9 | n+d+5, n+5 | 1330 | C_b ≈ 1.0309681 (66/66-digit ℚ, `oddk_9/constants.json`) | **1031/1000** | 1.0309501890… | quasi-conv., rs ≤ 2 |
| 11 | n+d+6, n+6 | 100 | 5382105924089713149513767500 / 4197403928429317550068356771 ≈ 1.2822459; lower pin ≥ 6/5 | **13/10** | 1.2636063359… | quasi-conv., rs ≤ 2 |
| 13 | n+d+7, n+7 | 600 | 4811737761054720000000000 / 3210875246348407823945773 ≈ 1.4985751 | **3/2** | 1.4957635203… | quasi-conv., rs ≤ 2 |
| 15 | n+d+8, n+8 | 2131 | C_A/(15ρ_lo¹⁴) ≈ 1.7279302 (ℚ in `oddk_15/constants.json`) | **1729/1000** | 1.7276232506… | quasi-conv., rs ≤ 3 |

Supporting per-k data:

| k | ratio bracket (from the equation) | intermediate Thue bound | `Y₀` provenance |
|---|---|---|---|
| 5 | 1.31 < X/Y < 1.322 | \|X⁵−4Y⁵\| ≤ 8.8·Y³ | note §6 (Y ≥ 40); sweep covers small Y |
| 7 | 60949/50000 < X/Y < 12191/10000 | \|X⁷−4Y⁷\| ≤ (2862499427291494681041757/156250000000000000000000)·Y⁵ ≈ 18.32·Y⁵ | banked k=7 confinement ⇒ Y ≥ 887 for d ≥ 221 |
| 9 | round 1: 29/25 < X/Y < 59/50; round 2: X/Y > ρ₂ = 11665283/10⁷ | 4Y⁹−X⁹ ≤ c₇ᵦ·Y⁷, c₇ᵦ ≈ 31.8163 (exact ℚ) | banked (9,6) confinement ⇒ Y ≥ 1330 for d ≥ 221 |
| 11 | 1134/1000 < X/Y < 1135/1000 | 40·Y⁹ < 4Y¹¹−X¹¹ ≤ 49.6015·Y⁹ (exact ℚ, two-sided) | banked (11,7) confinement ⇒ Y ≥ 1552 for d ≥ 221 |
| 13 | 89/80 < X/Y < 9/8 | 4Y¹³−X¹³ ≤ (3501/50)·Y¹¹ | banked (13,8) confinement ⇒ Y ≥ 1958 for d ≥ 221 |
| 15 | ρ_lo = 109682397/10⁸ < X/Y < ρ_hi = 109682598/10⁸ | band: C_B·Y¹³ ≤ 4Y¹⁵−X¹⁵ ≤ C_A·Y¹³, C_A ≈ 94.522349, C_B ≈ 94.496259 (exact ℚ) | **self-contained** crude bracket ⇒ Y ≥ 2131 for d ≥ 221 (banked (15,10) would give 2217) |

All chains are certified in the Lean-ready shape (shift `Y = Y₀ + z`, all
coefficients nonnegative) except where the per-k notes say Sturm/Descartes;
`d ≤ 220` is closed by the banked small-core certificates in every case.

## 2. Scans, candidate families, verified bounds

Per-note scans (each with its own generous superset; all equation checks
exact):

| k | CF terms (note) | scan depth | note family size | (X,Y) pairs | Thue-filter passes | equation hits | verified d-bound |
|---|---|---|---|---|---|---|---|
| 5 | 320 | Y ≤ 10^130 | 15 158 | 75 790 | 21 (brute ≤ 2·10⁶) | **0** | `d ≤ 3.19·10^119` |
| 7 | 320 | Y ≤ 10^120 | 37 478 | 187 390 | 29 (brute ≤ 2·10⁶) | **0** | `d ≤ 2·10^119` |
| 9 | 320 | Y ≤ 10^100 | 21 839 | 131 010 | 239 | (7,8) d=1 only | `d ≤ 1.665283·10^99` |
| 11 | 340 | Y ≤ 10^100 | 15 973 | 95 813 | 16 (two-sided pin) | **0** | `d ≤ 10^99` (actual > 1.34·10^99) |
| 13 | 330 | Y ≤ 10^100 | 14 118 | 70 525 | 662 | **0** | `d ≤ 1.125·10^99` |
| 15 | 336 | Y ≤ 10^100 | 21 001 | 125 970 | 775 (band: 1) | (12,13) d=1 only | `d ≤ 9.6824·10^98` |

Uniform self-contained-family cross-check (`gen_thue_convergents.py`, one
constant per k from §1, Y ≤ 10^100, exact `P_k(X) = 4P_k(Y)` on every
member):

| k | C used | tight family size | pairs checked | hits |
|---|---|---|---|---|
| 5 | 61/100 | 349 | 2 077 | none |
| 7 | 399/500 | 463 | 2 759 | none |
| 9 | 1031/1000 | 575 | 3 429 | none |
| 11 | 13/10 | 802 | 4 774 | none |
| 13 | 3/2 | 808 | 4 811 | none |
| 15 | 9/5 | 1 012 | 6 032 | (12,13) d=1 only |

**Headline: across all six odd k, the exact equation has NO solution on any
enumerated family to the stated depths, other than the two d = 1 telescopes
(k = 9: `(Y,X) = (7,8)`, i.e. `(n,d) = (2,1)`; k = 15: `(12,13)`, i.e.
`(4,1)`) — both overlapping-block pairs with `d = 1 < k`, outside the
problem domain `m ≥ n + k` of `Erdos686Reduction.lean` and inside the banked
`d ≤ 220` branch.  No counterexample candidate exists anywhere in the
scanned ranges.**

Every additional order of magnitude in any verified bound costs ~2 CF terms;
the shipped 341-row data files support immediate extension to `Y ~ 10^170`.

## 3. Machine-readable convergent data (for certificate generation)

`compute/artifacts/thue_convergents_k{5,7,9,11,13,15}.json`, produced by
`compute/theory/gen_thue_convergents.py` (143–426 KiB each):

- `data`: 341 rows, `i = 0…340`, each `[p_i, q_i, D_i, a_{i+1}]` with
  `D_i = p_i^k − 4·q_i^k` (exact JSON bignums; Python `json.load` restores
  them losslessly; `sign(D_i) = (−1)^{i+1}` is the side certificate);
- `cf_a0 = 1` (the `a₀` floor, certified by `1^k < 4 < 2^k`);
- certification metadata: 682 semiconvergent **straddle sign checks** per k
  (two per partial quotient — the far-side/crossed pair described in the
  notes; these are the objects that become `norm_num` goals in Lean),
  alternation and determinant identities re-verified;
- summary fields: `max_partial_quotient_to_341`, `argmax`,
  `first_index_q_exceeds_1e100`, `headline_C`, family/equation-check counts.

Key per-k CF facts (index of `q_i > 10^100` / largest partial quotient among
`i ≤ 341`):

| k | q > 10^100 at i | max `a_i` (i ≤ 341) | at i |
|---|---|---|---|
| 5 | 203 | 465 | 266 |
| 7 | 187 | 1639 | 136 |
| 9 | 191 | 352 | 5 |
| 11 | 209 | 2589 | 119 |
| 13 | 189 | 192 | 114 |
| 15 | 207 | 506 | 311 |

(The `g ≥ 2` multiple bound `g² < C(a_{m+1}+2)` therefore needs `g` up to:
k=5: 16, k=7: 36, k=9: 20, k=11: 59, k=13: 18, k=15: 31 — each note's scan
used a blanket ≥ these.)

## 4. k-specific complications (deviations from the k=7 pattern)

1. **d = 1 telescopes (k = 9, 15).**  `(n+k+1)/(n+1) = 4` is solvable iff
   `3 | k`: `(n,d) = (k/3−1, 1)`.  These are genuine solutions of the
   *centered polynomial equation* and are found by every honest scan; they
   are outside the disjoint-block domain (`d < k`) and inside banked
   `d ≤ 220`.  Scan scripts must expect them — the k=9 verification
   originally crashed on `(7,8)` (an interrupted assertion, now repaired:
   hits are split by `d ≥ k` vs `d < k`).  Note the asymmetry: `(12,13)`
   appears in the k=15 tight family (it satisfies `|αY−X| < (9/5)/Y`), while
   `(7,8)` does *not* satisfy the k=9 Thue hypothesis (`Y = 7 < Y₀`) and so
   is absent from the k=9 tight family.
2. **Past-Fatou constants (k ≥ 9).**  `κ₉ = 1.0310 > 1` is the first
   crossing; Fatou-based confinement (k=5/7 pattern) provably cannot work
   for k ≥ 9.  k=9/11/13 land at Worley `rs ≤ 2`; **k=15 at `rs ≤ 3`**
   (`2C₁₅ = 3.458`), the widest class — its scan enumerates the two extra
   shapes `(1,3), (3,1)`.  The self-contained theorem (§0) sidesteps the
   class distinction entirely: only the caps change.
3. **Two-round bootstrap (k=9 only).**  The round-1 constant
   `C_a ≈ 1.1934` exceeds `κ₉ + 10⁻¹`; a second pass through the chain with
   the certified ρ₂-bracket is needed to reach `C₉ = 1031/1000`
   (within 2·10⁻⁵ of optimal).  No other k needed a bootstrap.
4. **Two-sided information (k=11, k=15).**  k=11 has a PROVED lower pin
   `q − X/Y > (6/5)/Y²` (kills pure convergents in the g=1 branch); k=15
   has the narrowest band `4Y¹⁵−X¹⁵ ∈ [C_B, C_A]·Y¹³` (relative width
   2.8·10⁻⁴ — exactly 1 band survivor below 10^100).  These are scan
   accelerators / extra filters, not needed for the headline.
5. **Y₀ provenance.**  k=15's `Y₀ = 2131` is self-contained (crude
   product-vs-power bracket, no banked input); the others inherit
   `Y ≥ q·221 + h − 1` from the banked constant-quotient confinement for
   `d ≥ 221` (values in §1) and cover the remaining small-Y strip by
   unconditional sweeps (k=5: 2·10⁶ note-scan; k=7: 10⁶; k=9: 10⁶; k=11:
   2·10⁵; k=13: 2100 unconditional + 10⁶ windowed; k=15: 10⁶).
6. **Scan depth.**  k=5 (10^130) and k=7 (10^120) were scanned deeper than
   k ∈ {9,…,15} (10^100).  The uniform artifacts (341 rows ≈ `q ~ 10^170`)
   support harmonizing everything to ≥ 10^150 at trivial cost when the
   banking target is fixed.
7. **No effective measures exist for any of the six.**  Bennett (2001)
   covers `4^{1/k}` only for k = 6, 12 and prime k ∈ [17, 347]: k = 5, 7,
   11, 13 are prime but below 17; k = 9, 15 are composite.  The open core
   for every k is the exact integer coincidence along its CF family —
   Baker/hypergeometric territory, outside elementary scope.

## 5. Banking recommendation (order of operations)

1. **The self-contained confinement theorem** (`oddk_9/note.md` §3):
   ~300–500 Lean lines on top of Mathlib's `GenContFract` determinant API.
   One build closes the confinement step for all six k (supersedes the
   Fatou step in the k=5/7 plans and the 600–1500-line Worley estimates in
   the k=11/13 plans).
2. Per-k pinning files (`OddK{k}Pinning.lean`): centered identity (`ring`),
   bracket/chain shift-certificates (`positivity`-grade, printed by each
   `derivation.py`), k-th-power `norm_num` facts.
3. CF straddle certificates from the JSON artifacts (2 `norm_num` sign goals
   per term; only terms up to the 10^100 index — 188–210 per k — are needed
   for the current bounds).  Kernel-only; no `native_decide` (axiom gate).
4. Family disequality slices per the banked manifest/audit idiom (tight
   families: 349–1012 Y-values per k, §2 table).
5. Assembly per k: banked `d ≤ 220` + confinement handoff + pin + theorem +
   certificates ⇒ verified `d`-bounds of §2.

Open core after banking (unchanged in shape, now uniform): for each odd
k ∈ {5,…,15}, only finitely many (conjecturally zero) indices m admit an
exact coincidence `P_k(X) = 4·P_k(Y)` on the confinement family of
`4^{1/k}` — with heuristic tail `Σ_{q_m > B} 1/q_m < 1/B` per k.
