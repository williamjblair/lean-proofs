# Erdős #1212 — structural results and a reduction to a single lemma

**DRAFT — awaiting Will's approval. Nothing posted without it.**
Intended venue: erdosproblems.com forum thread for #1212.
AI-assistance disclosure is mandatory and is included below.

---

## Summary

We do not solve #1212. We report unconditional structural results about the
graph, and a chain of reductions showing that a YES answer follows from a
single, precisely stated lemma about the geometry of blocked edges. Selected
results are formalized in Lean 4 (Mathlib), kernel-checked, axioms
`[propext, Classical.choice, Quot.sound]`.

Notation. `G` has vertices `{(x,y) : gcd(x,y) = 1, min(x,y) > 1, x or y
composite}`, edges joining points differing by 1 in one coordinate. Passing to
odd-odd *hubs* (both coordinates odd, not both prime), each hub-to-hub move is
two steps and the horizontal move `(a,b) → (a±2,b)` is available exactly when
`gcd(b, a(a+1)(a+2)) = 1`. Every intermediate vertex is automatically
admissible, so the composite condition collapses to "not both prime" at hubs.

## 1. Unconditional results

**(1.1) Move parity.** A horizontal step forces the row odd; a vertical step
forces the column odd. Rows divisible by 3 admit no horizontal move (one of
`a, a+1, a+2` is divisible by 3), but are freely climbable.

**(1.2) Elevator shafts.** If `a` is composite with `p⁻(a) > H`, the entire
segment `{(a,s) : 2 ≤ s ≤ H}` is admissible and connected: `a` is composite so
the composite condition holds at every height, and coprimality is automatic
below `p⁻(a)`. Consequently *vertical motion is never the obstruction*: a
component of horizontal extent `[u,v]` at heights `< H` contains the full shaft
of every composite `a ∈ [u,v]` with `p⁻(a) > H`.

**(1.3) Composite-palette wall.** Let `S` be any finite set of composite rows,
all at most `Y`. Every composite `r ≤ Y` has a prime factor `≤ √Y`, so a single
congruence `a ≡ -1 (mod ∏_{p ≤ √Y} p)` blocks the horizontal step on *every*
row of `S` at once. Such columns recur with period `exp((1+o(1))√Y)`.

This is sharper than the naive wall bound (which uses one prime per row) and it
is decisive for architecture design: any strategy confining its rows to a band
of height `Y` fails once `exp(√Y) < x`, i.e. for bands of height `o(log²x)`.
Bands of height `log^{5}x` and above are unaffected.

**(1.4) Rough-supply theorem.** For `z ≥ z₀`, every interval of length `z⁵`
contains at least `z⁵/(10 log z)` odd `z`-rough composites, two of them within
`12 log z` of each other, uniformly in the position of the interval.
(Lower linear sieve for the rough count; Brun–Titchmarsh to subtract primes;
pigeonhole for the close pair. Explicit constants available.)

**(1.5) Pointwise tameness and a universal climbing lemma.** Fix a vertical span
`σ` and set `R = R(σ) = 2·10⁴ σ log Y`. A climb column that is `R`-rough is
automatically coprime to every prime `≤ R`, so only primes `> R` dividing the
swept range can obstruct it; since any `m ≤ 3Y⁵` has at most `log m/log R` such
prime factors, the obstruction mass of *every* band satisfies
`K(B) ≤ 1/(3900 log R)`, pointwise and with no averaging.
Combined with (1.4) this gives: **every vertical span `σ` has a dockable
composite climb column in every horizontal interval of length `R(σ)⁵`.**

**(1.6) Cubic climb latency.** Using Iwaniec's uniform Jacobsthal bound
`j(n) ≪ ω(n)² log²(2ω(n))` in place of (1.4), the interval length in (1.5)
improves from quintic to essentially cubic in the span: every prescribed pair of
rows at distance `≤ Y^{1/3}/(log Y)⁶` has a dockable climb inside *every* window
of length `Y/30`.

**(1.7) A factor-disjoint reservoir.** There is a set of `≫ Y^{5/2-η}/log Y`
rows in the band, each a semiprime `pq` with both factors `≥ Y^{5/2-η}`, lying
in one interval of length `Y^{5/2-η}/4`; distinct rows have *disjoint* prime
supports. Each such row has at most six blocked columns per window of
`Y^{5/2-η}` columns, and in any window of length `Y/30` a `1 - O(Y^{-1/2+η})`
fraction of the reservoir consists of rows with no block at all.

## 2. The reduction

Let `u < v` be consecutive columns carrying full-height shafts. Say a *guarded
window* is a horizontal interval of length `Y/30` with guards of width
`2R(4d)⁵`. The results above yield: shafts exist and attach (1.2, 1.4); no
column blocks more than a vanishing fraction of reservoir rows (1.7); every
short-range handoff inside a window is available (1.6); no band is untame (1.5);
and the scale ratchet and seam bookkeeping go through.

What does *not* follow is that the component crosses from `u` to `v`. The gap is
exactly this:

> **Arithmetic Staircase Exclusion (ASE).** There is no sequence of reservoir
> row-packets `P₁, …, P_K` ordered by height, together with nondecreasing
> columns `c₁ ≤ … ≤ c_K`, such that (i) every row of `P_i` has a block event
> near `c_i`, (ii) the packets respect the per-window capacity bound, and (iii)
> for each `i`, the horizontal slab from `c_i` to `c_{i+1}` contains no dockable
> climb across the vertical gap between `P_i` and `P_{i+1}`.

ASE implies that the reachable set survives every guarded window, hence
shaft-to-shaft crossing, hence horizontal extent doubling, hence — by (1.2) and
König — an infinite path. **ASE ⟹ the answer to #1212 is YES.**

## 3. Why ASE resists counting

Marginal estimates cannot prove it, and we can say precisely why. The graph is
static: a blocked edge stays blocked, so a dual separator pays for each row once
and for each interface once. Its total cost is therefore comparable to the
number of rows it cuts, which is well inside every budget we can prove — the
window log-mass bound, the per-row block-event cap, and the per-column blocked
fraction are all satisfied by a hypothetical "staircase" cut. What must be
excluded is a *phase* coincidence: that the block residues of the reservoir rows
(modulo their own large prime factors) can be aligned, packet by packet, with
the gaps between dockable climb columns. That is a joint correlation statement
about two arithmetically unrelated CRT structures, and it is the whole
remaining difficulty.

## 4. Formalization

`ErdosProblems/Erdos1212.lean` (Lean 4, Mathlib) kernel-checks: move parity, the
blocking criterion, dead rows mod 3, elevator shafts (1.2), the composite-palette
wall (1.3) including the `√Y` modulus, the six-events-per-window cap for
two-large-factor rows (1.7), and the prime-counting core of (1.5). Axioms:
`[propext, Classical.choice, Quot.sound]`; no `sorry`.

## 5. Provenance and AI disclosure

These results were produced in a two-day machine-assisted campaign. The informal
mathematics was developed by Claude (Anthropic) in an agentic setting, with
adversarial refereeing across ten rounds by GPT-5 Pro (OpenAI), which refuted
four earlier proposed architectures and supplied several of the corrections and
explicit constants recorded above; the Lean formalization is Claude's. Numerical
verification (rough-supply constants, killer-sum averages, palette-wall
thresholds, component percolation data) is reproducible from the scripts in the
campaign repository. All errors are ours; the ten-round record of refuted
approaches is included in the repository because it maps the methods that
provably cannot work.
