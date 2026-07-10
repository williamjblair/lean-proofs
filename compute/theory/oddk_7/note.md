# Erdős 686, k=7, N=4: the convergent-pinning reduction

*compute/theory/oddk_7, 2026-07-09.  Template: `../k5_third_row_note.md`
Section 5–6.  All numerical claims are backed by exact-arithmetic scripts in
this directory; every PROVED tag is verified symbolically (sympy over ℤ,
exact real-root isolation) or by exact integer computation.  Status tags:*
**PROVED** *(verified here, elementary),* **ROUTINE** *(standard Lean work),*
**MEDIUM/HARD** *(Lean effort estimates),* **OPEN** *(genuinely open).*

Scripts:
- `derivation.py` — 12 exact lemmas: centered identity, monotonicity, ratio
  bracket, the Thue inequality chain, the exact constant `C_7`, banked
  handoff, numeric grid validation, Lean shift certificates.
- `cf_scan.py` — pure-integer cf(4^(1/7)) (320 terms, 638 straddle
  certificates), exhaustive `Y ≤ 10^6` check, brute `‖qY‖`-window scan to
  `2·10^6` with family classification, candidate-family scan to `Y ≤ 10^120`.

---

## 0. Executive summary

Setting: `n ≥ 0`, `d ≥ 1`, `(n+d+1)⋯(n+d+7) = 4·(n+1)⋯(n+7)`.  In centered
variables `X = n+d+4`, `Y = n+4` the equation is exactly

```
P7(X) = 4·P7(Y),      P7(T) = T(T²−1)(T²−4)(T²−9) = T⁷ − 14T⁵ + 49T³ − 36T   (*)
```

and the leading cancellation `|X⁷ − 4Y⁷| ≤ C₁·Y⁵` (`C₁ = 56 − 14·r⁵`,
`r = 60949/50000`) forces, for every solution with `Y ≥ 250`,

```
|4^(1/7) − X/Y| ≤ C₇/Y²,     C₇ = 2(4 − r⁵)/r⁶
                                = 40892848961307066872025100000/51262467486572955812169421801
                                ≈ 0.7977152  <  399/500  <  1.
```

`C₇ < 1` puts `X/Y` inside the **Fatou threshold** `1/Y²`: `X/Y` is confined
to convergents, bounded multiples of convergents, and mediant neighbours of
cf(4^(1/7)) — an exponentially sparse explicit family.  Checked exactly:
**no solution with `Y = n+4 ≤ 10^120`** (37 478 family denominators, 187 390
(X,Y) pairs), plus an unconditional exhaustive check for `Y ≤ 10^6`.  Via the
banked confinement `4d ≤ n+1 < 5d` (`d ≥ 221`) and the banked `d ≤ 220`
certificate this gives: **no k=7, N=4 solution with `d ≤ 2·10^119`**,
conditional only on the PROVED pinning chain and classical Legendre/Fatou.

The asymptotic constant is `κ₇ = 2(4 − q⁵)/q⁶ = 0.79735659639…`
(`q = 4^(1/7)`); since `κ₇ > 1/2`, no tightening of brackets can ever reach
the Legendre threshold `1/(2Y²)` — the Fatou step is *unavoidable* for k=7,
exactly as for k=5 (`κ₅ = 0.5617 > 1/2`).

## 1. Centered identity (PROVED, Lean: `ring`)

```
∏_{i=1..7}(x+i) = P7(x+4),   P7(T) = T⁷ − 14T⁵ + 49T³ − 36T = T(T²−1)(T²−4)(T²−9).
```

Coefficients `1, −14, 49, −36`: elementary symmetric functions of `{1,4,9}`
(central factorial pattern; k=5 analogue was `T⁵ − 5T³ + 4T`).  So (*) holds
with `X = n+d+4`, `Y = n+4`, and `X⁷ − 4Y⁷ = G(X,Y)` on solutions, where

```
G(X,Y) = 14X⁵ − 49X³ + 36X − 56Y⁵ + 196Y³ − 144Y        (identity L2).
```

## 2. The exact Thue inequality (PROVED)

All lemmas verified in `derivation.py` by exact sign checks; every
single-variable positivity below has an integer shift point at which *all*
polynomial coefficients are nonnegative (printed by the script), so the Lean
proofs are coefficient-wise — no `nlinarith` search.

- **L3 (monotonicity).** `P7'(3+s)` has coefficients
  `[7, 126, 875, 2940, 4872, 3528, 720]`, all `> 0` ⇒ `P7` strictly
  increasing on `[3, ∞)`.  Likewise `∂G/∂X` at `X = 2+s`:
  `[70, 560, 1533, 1652, 568]`.
- **L4 (bracket sanity).** `60949⁷ < 4·50000⁷` and `4·10000⁷ < 12191⁷`, i.e.
  `r_lo = 60949/50000 < 4^(1/7) < r_hi = 12191/10000`.
- **L5/L6 (ratio bracket from the equation).**  For any solution with
  `Y ≥ Y₀ = 250`:  `r_lo < X/Y < r_hi`.  Proof: if `50000·X ≤ 60949·Y`,
  monotonicity gives `P7(X) ≤ P7(r_lo Y)`, and
  `N_lo(Y) = 4·50000⁷·P7(Y) − 50000⁷·P7(r_lo Y) > 0` for `Y ≥ 250`
  (largest real root in `(153.933, 153.934]`; all-nonneg shift at `Y = 154`),
  contradicting (*); symmetrically for `N_hi` (largest root `≈ 2.17`,
  shift `Y = 3`).  `X > Y` since `4P7(Y) > P7(Y) > 0` for `Y ≥ 4`.
- **L7/L8 (the Thue bound).**  `G` is increasing in `X` on the bracket and
  `G(r_hi Y, Y) < 0` for `Y ≥ 250` (largest root `≈ 2.17`), so
  `X⁷ − 4Y⁷ = G(X,Y) < 0`; and
  `G(r_lo Y, Y) + C₁Y⁵ = (c₃Y³ − c₁Y)/50000⁵ ≥ 0` for `Y ≥ 1`
  (`c₃ = 33514510050832247500000000 ≥ c₁ = 31286475000000000000000000 > 0`).
  Hence, **for every solution with `Y ≥ 250`:**

  ```
  |X⁷ − 4Y⁷| ≤ C₁·Y⁵,    C₁ = 56 − 14·r_lo⁵ = 2862499427291494681041757/156250000000000000000000
                              ≈ 18.319996        (no lower-order terms needed).
  ```
- **L9 (pinning).**  `X⁷ − 4Y⁷ = (X − qY)·Φ`, `Φ = Σ_{i=0}^{6} Xⁱ(qY)^{6−i}
  > 7(r_lo Y)⁶` on the bracket, so

  ```
  |4^(1/7) − X/Y| ≤ C₁/(7 r_lo⁶ Y²) = C₇/Y²,   C₇ = 2(4 − r_lo⁵)/r_lo⁶ < 399/500.
  ```

  Exact value above; asymptote `κ₇ = 0.797356… < C₇` (certified via the
  7th-power bracket `q < 121901366/10⁸`).  Numeric grid validation on 258
  `Y`-values in `[250, 10^24]`: max `Y²`-deviation `0.797393`, all chain
  inequalities hold at the real solution ray (L11).

**Handoff (L10).**  Banked `row_base_lower_k7`
(`Erdos686QuotientConfinement.lean`, bracket `4·9⁷ < 11⁷`) gives `4d ≤ n+1`
for `d ≥ 221`, so `Y = n+4 ≥ 887 ≥ Y₀ = 250`; the upper confinement
(`6⁷ < 4·5⁷`) pins the floor, `n+1 < 5d`, so `d > (Y−3)/5`.  `d ≤ 220` is
closed by the banked small-core row-escape certificate.  (Independently,
`cf_scan.py` checks `Y ≤ 10^6` exhaustively, so even the strip
`250 ≤ Y < 887` never carries conditional weight.)

## 3. Confinement: Fatou class (classical), exact candidate family

`C₇ ≈ 0.7977 ∈ (1/2, 1)` — same class as k=5.  Write `X/Y = g·(a/b)` in
lowest terms:

- **`g ≥ 2` (Legendre).**  `|q − a/b| < C₇/(g²b²) ≤ C₇/4·b⁻² < 1/(2b²)`, so
  `a/b` is a convergent `p_i/q_i`; the classical lower bound
  `|q − p_i/q_i| > 1/((a_{i+1}+2)q_i²)` forces `g² ≤ C₇(a_{i+1}+2) <
  a_{i+1}+2`, i.e. **`g² ≤ a_{i+1}+1`**.
- **`g = 1` (Fatou 1904).**  `|q − a/b| < 1/b²` ⇒ `a/b` is a convergent or a
  mediant neighbour `(p_{i+1} ± p_i)/(q_{i+1} ± q_i)`.

**Candidate family per CF index i:**

```
Y ∈ {g·q_i : g = 1 or g² ≤ a_{i+1}+1}  ∪  {q_{i+1} + q_i, q_{i+1} − q_i}.
```

Over the scanned range the tight family has ~948 members (`≤ 10^120`).  The
scan uses a strict superset — `{g·q_i : g ≤ 50}` (valid since
`max a_{i+1} = 1639`, `√1640 ≈ 40.5 ≤ 50`) plus **all** semiconvergents
`a·q_i + q_{i−1}` (`1 ≤ a ≤ a_{i+1}+1`) with margin multiples `g ≤ 8` — so
the scan also covers the weaker, easier-to-formalize statement "`< 1/b²` ⇒
semiconvergent" (both Fatou mediants are the `a = a_{i+1} ∓ 1`… `+1`
semiconvergents).

## 4. cf(4^(1/7)) and scan results (PROVED computation)

Generation is pure integer arithmetic: each partial quotient `a_{i+1}` is
pinned by the **straddle certificate** — two sign checks
`u⁷ ≶ 4v⁷` at the semiconvergents `s_a, s_{a+1}` (`s_a` on the far side,
`s_{a+1}` across) — 638 certificates for 320 terms; no floating point in any
decision.  Cross-checked against 1500-digit mpmath and the alternation law
`sign(p_i⁷ − 4q_i⁷) = (−1)^{i+1}`.

```
cf(4^(1/7)) = [1; 4, 1, 1, 3, 3, 2, 2, 1, 2, 1, 3, 4, 1, 2, 26, 1, 1, 8, 5,
               47, 1, 1, 1, 3, 1, 4, 1, 3, 3, 8, 1, 24, 2, 34, 1, 1, 4, 2, 200, …]
max a_i (1 ≤ i < 320) = 1639  (at i = 136);  q_i > 10^100 at i = 187;
q_i > 10^120 at i = 228.
```

Results (all exact):

- **Exhaustive:** no solution of (*) with `4 ≤ Y ≤ 10^6` (monotone integer
  bisection; unconditional, covers all d).
- **Brute window scan:** 29 values `Y ≤ 2·10^6` with `‖qY‖ < 0.95/Y`; every
  one is a convergent multiple or semiconvergent of cf(4^(1/7)) (empirical
  Fatou validation — the largest is `5·q_14 = 851020`); none is remotely
  close to satisfying (*) (smallest scaled residual at `Y = 9`).
- **Family scan:** 37 478 candidate `Y ≤ 10^120` (34 215 ≤ 10^100),
  187 390 (X,Y) pairs with `X ∈ iroot7(4Y⁷) ± 2`: **zero solutions, zero
  near-misses** (`|P7(X) − 4P7(Y)| < Y⁴` never occurs).

**Corollary (conditional only on §2 + classical Legendre/Fatou).**
No k=7, N=4 solution with `n+4 ≤ 10^120`; hence none with `d ≤ 2·10^119`
(combining `d > (Y−3)/5` for `d ≥ 221` with the banked `d ≤ 220` closure).
Each additional order of magnitude costs ~2 CF terms.

**OPEN core (k=7).**  Same shape as k=5: only finitely many (conjecturally
zero) convergent denominators of `4^(1/7)` admit the exact integer
coincidence (*).  `|X⁷ − 4Y⁷| ~ 18.3·Y⁵` sits exactly at the Roth exponent
for degree 7; no effective irrationality measure for `4^(1/7)` exists
(Bennett 2001 covers prime `k ∈ [17, 347]` only), so unbounded closure is
Baker/hypergeometric territory.

## 5. Lean formalization plan (Mathlib v4.29.1 inventory verified locally)

### What exists in Mathlib (checked in `.lake/packages/mathlib`)

| item | name | file |
|---|---|---|
| **Legendre's theorem** (`< 1/(2·den²)` ⇒ convergent) | `Real.exists_rat_eq_convergent` | `Mathlib/NumberTheory/DiophantineApproximation/Basic.lean` |
| Legendre, `GenContFract.convs` form | `Real.exists_convs_eq_rat` | `…/DiophantineApproximation/ContinuedFractions.lean` |
| Legendre induction engine (hyp. `< 1/(v(2v−1))`) | `ContfracLegendre.Ass`, `Real.exists_rat_eq_convergent'` | same as Basic |
| simple convergent recursion | `Real.convergent`, `convergent_zero/succ` | same |
| bridge to CF machinery | `Real.convs_eq_convergent` | `…/ContinuedFractions.lean` |
| `|v − Aₙ/Bₙ| ≤ 1/(BₙBₙ₊₁)` | `GenContFract.abs_sub_convs_le` | `…/Computation/Approximations.lean` |
| exact difference formula | `GenContFract.sub_convs_eq` | same |
| determinant identity | `GenContFract.determinant` | `…/ContinuedFractions/Determinant.lean` |
| CF convergence | `GenContFract.of_convergence` | `…/Computation/ApproximationCorollaries.lean` |
| irrationality of 4^(1/7) | `irrational_nrt_of_n_not_dvd_multiplicity` (x⁷=4, p=2, 7∤2) | `Mathlib/NumberTheory/Real/Irrational.lean` |

### What is MISSING (grep-verified: no hits)

1. **Fatou's theorem** (`< 1/q²` ⇒ convergent or mediant) — absent in any
   form; no `mediant`, no `semiconvergent` API anywhere in Mathlib.
2. **Convergent-distance lower bound** `|ξ − p_i/q_i| > 1/((a_{i+1}+2)q_i²)`
   (needed for the multiple bound `g² ≤ a_{i+1}+1`) — only *upper* bounds
   exist (`abs_sub_convs_le`, `abs_sub_convergents_le'`).
3. **Explicit CF certificates for algebraic numbers** — nothing computes or
   certifies `GenContFract.of ξ` / `Real.convergent ξ i` for irrational
   algebraic `ξ`.

### Plan, by difficulty

**ROUTINE (banked idioms, hours–days):**
1. Centered identity + `X⁷−4Y⁷ = G` (§1): `ring` in ℤ (cast from ℕ as in the
   banked window lemmas).
2. Bracket + chain (L3–L8): each is `0 < Σ cᵢ zⁱ` with literal nonneg
   coefficients after the printed shifts (`N_lo` at `Y = 154+z`, `N_hi`,
   `−G_hi` at `Y = 3+z`) — `positivity`/`nlinarith []` with the shift
   substitution; mirrors `K5WindowPin.lean`.  The 7th-power bracket facts
   (L4) are single `norm_num` goals on ≤ 40-digit integers.
3. Handoff: `row_base_lower_k7` + `row_base_quotient_confined_of_window`
   already banked; `d ≤ 220` banked.
4. Real-number packaging of L9 (`q := (4:ℝ)^((1:ℝ)/7)`, `q⁷ = 4` via
   `Real.rpow_inv_natCast_pow`; `r_lo < q < r_hi` from L4 by strict mono of
   `x ↦ x⁷`): ROUTINE-plus.
5. Final candidate checks: certify the **tight** family (~950 Y-values to
   10^120, ~5 X's each ⇒ ~4 700 `decide`/`norm_num` disequalities
   `P7(X) ≠ 4·P7(Y)` on ≤ 900-digit integers — kernel GMP Nat arithmetic;
   sliceable per the repo's manifest/audit idiom; **no native_decide
   needed**).  ROUTINE, heavy kernel time.

**MEDIUM (days):**
6. Irrationality of `4^(1/7)`: instantiate
   `irrational_nrt_of_n_not_dvd_multiplicity` (m = 4, p = 2, n = 7).
7. `g ≥ 2` branch: `Real.exists_rat_eq_convergent` applies as-is
   (`C₇/4 < 1/2`).  The multiple bound needs missing item 2 — build from
   `GenContFract.sub_convs_eq` + `determinant` (~200–400 lines).

**HARD (the two genuinely new pieces, shared with k=5 and all odd k):**
8. **Fatou step (g = 1).**  Two viable targets: (a) Fatou proper, by
   adapting Mathlib's own Legendre induction (`ContfracLegendre.Ass`:
   weaken the hypothesis to `< 1/v²`, widen the conclusion to
   {convergent, two mediants}; est. 500–900 lines); or (b) the weaker
   "semiconvergent" conclusion — the scan already covers the full
   semiconvergent superset (all `a ≤ a_{i+1}+1`, multiples `g ≤ 8`), so
   either suffices.  Build once, reuse for every k.
9. **CF certificate machinery.**  A lemma turning the 638 straddle sign
   checks into `Real.convergent q i = pᵢ/qᵢ` for the explicit 120-digit
   convergents (induction on complete quotients; floor pinned by the two
   integer 7th-power comparisons per term).  ~300–600 lines of plumbing +
   2×229 kernel checks.  New infrastructure: "explicit continued fractions
   of algebraic numbers", reusable across the campaign.

### Banking order

1. L1–L8 integer lemmas (ROUTINE, self-contained file `OddK7Pinning.lean`).
2. Real packaging + Legendre `g ≥ 2` branch (MEDIUM).
3. CF certificate machinery + the 229-term certificate (HARD-plumbing).
4. Fatou (HARD-math, shared).  Outcome: verified bound `d ≤ 2·10^119`
   for k=7, with the open core isolated as the CF-family statement.
