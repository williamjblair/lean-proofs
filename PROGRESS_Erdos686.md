# PROGRESS.md - Erdős Problem #686

Date: 2026-07-10 (full-solution campaign, day 2)
Formal lane: refute the universal positive statement by proving `N = 4` has no
quotient representation. Previous plan archived in
`PROGRESS_Erdos686_gptpro_archive.md`.

Status tags: `[R]` banked in Lean (axiom-clean, kernel-verified) · `[E]` exact
computational evidence · `[C]` conjectural/open · `[X]` refuted by exact
counterexample.

---

## 0. Executive status

[R] The refutation of Erdős #686 is now machine-checked down to exactly two
open hypotheses. In `ErdosProblems/Erdos686SmallBranch.lean`:

```lean
theorem erdos686_false_of_constant_bound_and_large_escape
    (hbound : ConstantCaseBoundHypothesis)
    (hlarge : LargeKEscapeHypothesis) :
    ¬ ∀ N : ℕ, 2 ≤ N → ∃ k n m : ℕ, 2 ≤ k ∧ m ≥ n + k ∧
      (N : ℚ) = (∏ i ∈ Finset.Icc 1 k, ((m + i : ℕ) : ℚ)) /
                (∏ i ∈ Finset.Icc 1 k, ((n + i : ℕ) : ℚ))
```

[R] CI gate: 458 manifest-tracked theorems (419 for problem 686), 458
regenerated attestations, and 884 headline theorem surfaces with axioms
contained in `[propext, Classical.choice, Quot.sound]`.  Every new module also
passed its standalone build, exact reproduction, and independent hostile
audit.

[R] **All pure prime-power odd tails are closed.**  The p-adic lift module
now proves that for every prime `p`, exponent `e`, and
`k ∈ {5,7,9,11,13,15}`, the equation has no solution when
`d=p^e≥10^120`.  For `p≥k` this is the clean localized square lift; for
`p<k`, a maximum-valuation factor loses at most
`1+v_p((k-1)!)`, and the exact residual bound is dominated by
`14! * 35 * 13^30 < 10^120`.  This removes the entire one-prime-support
regime but does not close mixed-prime gaps.

[R] **The whole gap square lands in one residual progression.**  Put
`X_i=3(n+i)-d`.  The exact equation is

```text
product_i (X_i+4d) = 4 product_i (X_i+d).
```

The constant terms differ by three, the linear terms cancel, and every
higher coefficient `4^r-4` is divisible by three.  Lean therefore proves
unconditionally that `d^2 | product_i X_i`, plus a positive natural-number
wrapper in the live range.  This removes the derivative-coefficient loss
before any new primewise concentration; it is a proper consequence, not yet
a mixed-prime closure.

[R] **Every two-distinct-prime gap is closed.**  The global square lift now
cleans each `p^e|d` into a component `h` with `h|d`, `h|n+i`, and
`h^2|3(n+i)-d`.  The exact loss is at most `64` for `p≠3` and `59049` for
`p=3`; the latter is proved by removing the common three from the whole
residual progression.  For `d=p^e q^f`, same-owner components multiply as
coprime squares.  Distinct owners satisfy the cleaned Pell relation and
second local obstructions; simultaneous reflected zeros are repaired by the
third local lift with exact coefficient `20`.  The fully composed Lean
theorem gives `d<10^120` for all distinct primes `p,q`, including `2,3`,
without a base-size hypothesis.  Any surviving odd tail therefore has at
least three distinct prime divisors.

[R] **Three cleaned buckets have exact second/third restrictions, but no
closure.**  For `d=gPQR` and three step-three square residuals, Lean proves
`P|3(C_iabc-12D_ig^2(i-j)(i-l))` and the companion square divisibility
`P^2|-3O_i+180E_ig^2(i-j)(i-l)d`, cyclically.  Exact arithmetic checks all
1,035 index triples and 5,216 signed fixtures.  A 121-digit CRT construction
satisfies this congruence package and both global moments but is explicitly
not an equation solution and exceeds the verified short window.  The live
three-bucket gap is the quantified short-CRT lemma, not a claimed resultant.

[R] **Two global cubic moment combinations.**  Expanding at the evaluation
ratio `2^2=4` cancels every term through degree two after explicit constant
and linear corrections.  Lean proves `d^3` divides the resulting
combinations for both residual progressions `n+i-d` and `3(n+i)+d`.  The
exact solution `(k,n,d)=(1,0,3)` shows why the correction is load-bearing:
neither raw residual product is divisible by `27`.

[R] **Large-k maximum-valuation owners compress to one lcm.**  For every
exact equation with `k>=1` and `d>=k`,

```text
B(k,n) | (k-1)! * lcm(d-k+1,...,d+k-1).
```

The row skeleton alone gives the same statement with two factorial
allowances.  In the large branch the exact ratio also sharpens to `kd<5n`,
forcing `(kd)^k < 5^k (k-1)! C(k,d)`.  Both named deep row-prefix fixtures
and the `d=1` telescopes pass the hostile audit.  The result is a proper
compression, not a closure: generic lcm mass still has `2k-1` possible hosts
and grows with degree `2k-1` in `d`.

[X] **The former large-branch target is falsified.** The fixed-prefix
statement `RowSixteenBoundaryHypothesis` (rows 1..15 divide ⟹ row 16 fails)
is FALSE: the exact-window point `(k, n, d) = (984, 3177026, 4480)` passes
rows 1..16; only row 17 fails (`n+17 = 439·7237`, and 7237 exceeds the row-17
interval maximum 5447). Banked as `row_sixteen_boundary_hypothesis_false`
(kernel-verified witness). Deep survivor clusters (n = 48502 fails first at
row 16; n = 3177026 at row 17) show fixed-prefix caps cannot work; the
repaired open target is the unrestricted escape.

[R] **k = 14 closed entirely** (all d ≥ 221): the Runge trap confines
`m = T₁₄(w) − 2T₁₄(v)` to 834 candidates, all killed by a 31-prime
mod-p set cover (`Erdos686FourteenStrip.lean`).  All even
`k ∈ {6, 8, 10, 12, 14}` are unconditional.

[R] **Equation-level prime obstruction** (`Erdos686PrimeObstruction.lean`):
a prime `q ≥ d + k` dividing any block element refutes the equation in
five lines.  Hence any solution has both blocks entirely
`(d+k)`-smooth; the large-`k` core is now `LargeKSmoothHypothesis`.

[R] **The Thue route (odd k)**: centered variables `X = n+d+(k+1)/2`,
`Y = n+(k+1)/2` turn the equation into `P_k(X) = 4·P_k(Y)` with `P_k`
odd; the leading cancellation forces `|4^{1/k} − X/Y| ≤ C_k/Y²`
(C₅ = 61/100, C₇ = 399/500, C₉ = 1031/1000, C₁₁ = 13/10, C₁₃ = 3/2,
C₁₅ = 1729/1000 — all exact, proved chains).  A C-agnostic
Stern–Brocot descent certificate (`Erdos686ConvergentMachinery.lean`,
no reals, no Mathlib CF, kernel decide ~1s) confines and refutes every
candidate.  **k = 5 is banked closed for 221 ≤ d < 10^120**
(`Erdos686FiveThue.lean`) — the community had k = 5 open;
k ∈ {7, 9, 11, 13, 15} are also banked to the same `10^120` threshold.
Telescope caveat: k = 9, 15 have d = 1
polynomial identities (`P₉(8) = 4·P₉(7)`), excluded by the domain.

[C] The open hypotheses (the entire remaining mathematical content):

```lean
-- per odd k: no equation solution at astronomical heights
def NoLargeGapSolutionFour (k B : ℕ) : Prop :=
  ∀ n d : ℕ, B ≤ d → blockProduct k (n + d) ≠ 4 * blockProduct k n
-- six tails: NoLargeGapSolutionFour k (10^120-ish), k ∈ {5,7,9,11,13,15}

def LargeKSmoothHypothesis : Prop :=                 -- large-k core
  ∀ k n d : ℕ, 16 ≤ k → k ≤ d →
    blockProduct k (n + d) = 4 * blockProduct k n →
    (∀ i, i ∈ Finset.Icc 1 k → ∀ q, q.Prime → q ∣ n + i → q < d + k) →
    False
```

[R] **The terminal reduction is banked**
(`Erdos686FinalReduction.lean`):

```lean
theorem erdos686_false_of_thue_tails_and_smooth
    (htails : OddThueTailHypothesis)     -- six tails at d ≥ 10^120
    (hsmooth : LargeKSmoothHypothesis) : -- k ≥ 16 double smoothness
    ¬ (universal Erdős 686 statement)
```

with the UNCONDITIONAL `no_gap_solution_four_small_k_below`: for every
`5 ≤ k ≤ 15` and `221 ≤ d < 10^120` the `N = 4` equation is
impossible.  All five odd-k Thue modules reached full 10^120 depth.
Every intermediate conditional reduction remains banked and audited.

---

## 1. Architecture (revised from the earlier GPT Pro plan)

The earlier 13-tuple quotient-confinement plan collapsed to something much
simpler once the row→residual reduction was proved parametrization-only:

[R] `residual_dvd_of_row_dvd` (Erdos686ConstantQuotient.lean) needs only
`n + 1 = (q+1)·d − u`, NOT that `q` is each row's true quotient. The per-factor
identity is exact in ℤ: `q·(d + (1+s) − (t+1)) − M = q·s − R_t` where
`M = n+1+t`, `R_t = d−u+(q+1)t`. Consequently:

- only the **row-1 quotient** `(n+1)/d` needs confining (banked:
  `row_base_quotient_confined_of_window`, one value per k, two for k = 9);
- the k = 13 exceptional tuple (8,8,8,9) is absorbed by the (13,8) constant
  case;
- the single exceptional branch (9, quotient 5) is a finite box
  (`u ∈ [1,6], d ≤ 1421`), banked closed (`k_nine_quotient_five_row_escape`).

[R] The **u = d top edge** (`n+1 = q·d`, missed by all earlier scans because
they used `u < d`) is window-feasible only for (9,6), d ≤ 1613, passes the
t = 0 residual trivially (`residualRowPoly 9 6 0 = 0`), and is banked closed
(`constant_u_eq_d_no_prefix_three`).

Small-k pipeline (all banked; `Erdos686SmallBranch.lean` assembles):
`d ≤ 220` finite core → else confinement → (9,5)-box / constant case →
deficiency `u` → residuals t = 0..3 → [OPEN bound] → survivor membership →
row-4 escape → contradiction.

---

## 2. Banked modules (this session)

| Module | Content |
|---|---|
| `Erdos686ConstantQuotient.lean` | residualRowPoly, affine/lifted polynomials, exact lifted identity, primitive criterion (saturation + fixed (q+1)^k correction), prime-witness escape, row→residual reduction, deficiency parametrization |
| `Erdos686QuotientConfinement.lean` | `row_base_quotient_confined_of_window` (5 ≤ k ≤ 15, d ≥ 221), `window_n_upper_bound_of_d_le`; two-digit rational brackets, all norm_num |
| `Erdos686ExceptionalNine.lean` | k = 9, quotient-5 branch closed; exact box + Fin 1201 × Fin 6 kernel decide |
| `Erdos686SmallCore.lean` | `row_full_escape_small_k_d_le_220`: 5 ≤ k ≤ 15, k ≤ d ≤ 220, window ⟹ some row j ≤ 5 fails; banded certs, 23,730 grid points; `window_n_bound_small_k` (n < 2287) |
| `Erdos686ConstantSurvivors.lean` | the 45 prefix-three survivors + 6 band shadows; row-4 escape decide; banded membership certs for all 11 (k,q); u = d edge |
| `Erdos686SmallBranch.lean` | assembly, the two open Props, conditional reductions, boundary falsification |

---

## 3. The 11 constant cases and the bound table

```text
(k,q): (5,3) (6,3) (7,4) (8,5) (9,6) (10,6) (11,7) (12,8) (13,8) (14,9) (15,10)
bound:  220   220   220   220   220   266    7029   2695   4467   2811   2915
```

[E] Evidence for `ConstantCaseBoundHypothesis` (exact scans, q-relaxed
residual form = the form used in Lean):

```text
k = 5..9:   d ≤ 1e8,  zero three-row survivors with d ≥ 221
k = 10:     d ≤ 3e8,  3 survivors, max d 266
k = 11:     d ≤ 1e9,  7 survivors, max d 7029
k = 12:     d ≤ 3e8,  5 survivors, max d 2695
k = 13:     d ≤ 1e9,  7 survivors, max d 4467
k = 14:     d ≤ 3e8, 10 survivors, max d 2811
k = 15:     d ≤ 3e8, 13 survivors, max d 2915
```

All 45 survivors fail the row-4 residual (banked). Two-row survivors continue
to appear at all scales but thin out; three-row survivors stop.

---

## 4. Literature status (verified 2026-07-09)

- erdosproblems.com/686 is OPEN; community results for N = 4: k = 2 (Tao),
  k = 3 (vilc, via Bennett's effective irrationality measures + Chan's gap
  principle), k = 4 (reduction to k = 2), k = 6 (Kovač sketch). k = 5 is
  explicitly open. The banked corpus already exceeds this.
- Fixed-k finiteness of `∏(m+i) = 4·∏(n+i)` IS known:
  Beukers–Shorey–Tijdeman 1999 (via Rakaczki 2003, Thm B) — but
  Siegel-ineffective; no bound exists to cite or formalize.
- No congruence obstruction exists for (N,k) = (4,5) (MalekZ): admissible
  congruential solutions exist for every modulus. Archimedean window input is
  unavoidable.
- Effective irrationality measures for 4^{1/k}: only k = 6 (2.45, Bennett),
  k = 12 (≤ 4.9), prime k ∈ [17,347] (Bennett 2001 Thm 7.1). Nothing for odd
  k ∈ {5,7,9,11,13,15}.
- Uniform-in-k finiteness (our large branch) is a special case of the open
  Erdős conjecture behind problem #388. Strongest citable effective input:
  Laishram–Shorey `P(∆(x,k)) > 1.95k` (elementary + explicit prime bounds).

---

## 5. Even k: the Kovač/Runge route (mathematics verified, Lean in progress)

For even k set `w = 2m+k+1`, `v = 2n+k+1` (odd); the equation becomes
`S_k(w) = 4·S_k(v)` with `S_k(W) = ∏_{l odd < k} (W² − l²)`.

- k ≡ 2 (mod 4): the polynomial part P of √S has 2-power denominators;
  `2^{e}·P` is odd-valued at odd arguments while the doubled side is even —
  a mod-2 gap of 2^{−v(k)} survives for all k ≡ 2 (mod 4) (verified k ≤ 60).
  Kills k = 6, 10, 14 outside an explicit finite region.
- k ≡ 0 (mod 4): P is integer-valued; the equation forces `P(w) = 2P(v)`
  AND `R(w) = 4R(v)` exactly (R = S − P², deg R ≤ k/2−2) for w beyond an
  explicit threshold. For k = 8: `R = −4096·W²`, so w = 2v — parity
  contradiction. For k = 12: the system's resultant is nonzero with no
  integer roots. Kills k = 8, 12.
- In all five cases the sub-threshold region satisfies d ≤ 220 (via the
  banked confinement lower bounds), already closed by the finite core.

[C] A uniform even-k statement (all even k ≥ 16) would need the 2-adic
coefficient pattern as a general lemma; per-k it is mechanical.

---

## 6. Large branch: what is actually known

[X] Fixed-prefix boundary (rows 1..15 ⟹ row 16 fails): FALSE at
(984, 3177026, 4480). Both known deep clusters die by the same mechanism —
a single prime `p | n+j` with no multiple of p in the row-j interval
`[d+1−j, d+k−j]` — but at different rows j (16 resp. 17).

[C] Open target: `LargeKEscapeHypothesis` (some row j ≤ k fails). The banked
mechanisms (`row_escape_of_large_prime_in_n_add`, transition package,
smoothness lemmas) remain usable per-row. Gross log-mass counting does not
suffice (supply ≈ 2k·log d exceeds demand ≈ k·log(0.72kd) always); the
rigidity is finer, Grimm-problem-adjacent.

[E] All rows-1..15-passing points with k ≤ 3000, n ≤ 10^7: exactly two
clusters (n = 48502, k ∈ [244,260]; n = 3177026, k ∈ [984,1050]); every point
fails some row j ≤ 17.

---

## 7. Refuted targets (do not revisit)

- [X] `RowSixteenBoundaryHypothesis` — see §0.
- [X] Bare residual obstruction without the window ((k,q,d,r) = (7,4,339,162)).
- [X] Affine-saturation-only route (k=7, d=302, u=135).
- [X] Polynomial prefixes a ≤ 14 and row prefixes j ≤ 15 (survivor clusters).
- [X] Pure congruence obstruction for (4,5) (admissible for every modulus).

---

## 8. Current proof obligations, ordered

1. [in flight] Even-k Runge theorems (k = 6,8,10,12,14) — restricts the open
   small-k core to odd k.
2. [open, highest mathematical value] `ConstantCaseBoundHypothesis` for odd
   k; sharpest attack: the k = 5 third-row (s,t)-elimination with the tight
   window pinning `s = σ·t + O(1)`, σ = (c−3)/(72−23c), plus the
   divisor-cascade identities of the form `e₁e₂ = 72⁵(T₂e₁ − T₁e₂)`.
3. [open] `LargeKEscapeHypothesis`: needs a genuinely new idea; the failing
   row is unbounded. Candidate frame: for every window point some `n + j`
   (j ≤ k) has a prime power with no multiple in its row interval.
4. Housekeeping: PR the conditional reduction toward formal-conjectures
   (`erdos_686.variants.four` is open there with `answer(sorry)`).

---

## 9. Terminal assessment: what blocks the full solve (2026-07-10)

The two open hypotheses are research problems, not formalization gaps:

**The six odd tails** (`OddThueTailHypothesis`, d ≥ 10^120).  Any
concrete bound is cheap (each decade of d costs ~2 CF terms in the
descent certificate; 10^1000 is minutes of work).  Unbounded closure
needs one of:
- an effective irrationality measure < k for `4^{1/k}` at odd
  k ∈ {5..15} — none exists; the hypergeometric method structurally
  fails at these k (verified);
- Baker–Feldman — effective on paper but with bounds ~10^(10^500),
  unreachable by certificate, and linear forms in logarithms have
  never been formalized in any proof assistant;
- structure in cf(4^{1/k}) — none known.
Beukers–Shorey–Tijdeman prove the tails are finite via Siegel —
fundamentally ineffective.  Watch the Calegari–Dimitrov–Tang holonomy
program (arXiv:2510.04156), which announces effective measures for
high-order roots: if explicit constants materialize for 4^{1/k}, the
tails become finishable on paper and then formalizable.

**Large-k double smoothness** (`LargeKSmoothHypothesis`).  A special
case of the open conjecture behind Erdős #388 (uniform-in-k
finiteness); needs Grimm-strength control of smooth numbers in sliding
windows.  Census evidence: no candidate in 145+ billion window points
(k ≤ 6500, n ≤ 3·10^7).

**Standing.**  Unconditional k ≤ 15 to d < 10^120 exceeds the
literature (community: k ≤ 4 plus a k = 6 sketch; k = 5 was open).
Natural next steps: upstream PR toward formal-conjectures
(`erdos_686.variants.four`), a note on the erdosproblems.com/686
forum, and monitoring the holonomy program.
