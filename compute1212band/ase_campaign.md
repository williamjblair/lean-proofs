# ASE campaign — the phase-correlation attack (opened 2026-07-31)

Target: **Arithmetic Staircase Exclusion** (statement in `erdos1212_proof.md`
§19 and `writeup_1212_DRAFT.md` §2). ASE ⟹ #1212 is YES via the certified chain.

## Hard constraints from the 10-round record (do not re-derive)

1. **No counting/marginal arguments.** Window log-mass, per-row event caps, and
   per-column blocked fractions are all *satisfied* by a hypothetical staircase.
   Any argument whose only inputs are cardinalities is dead on arrival.
2. **The graph is static.** A separator pays once per row and once per interface;
   there is no "re-suppression" cost. Any argument charging the adversary
   repeatedly over horizontal position is wrong (this killed round 10).
3. **Position must be treated as space, not time.** The reachable-set language is
   convenient but the object is a min-cut in a fixed graph.

## The live idea: phase incompatibility

A staircase needs, at each interface `i`, that the slab `[c_i, c_{i+1}]` contains
no dockable climb across the gap between packets `P_i` and `P_{i+1}`. Two CRT
structures must therefore align:

* **Block times** of reservoir rows: `a ≡ 0, -1, -2 (mod ℓ)` for `ℓ | r`, with
  `ℓ ≥ Z = Y^{5/2-η}`. Each row contributes ≤ 6 residues mod its own two primes,
  and the primes are *distinct across rows* (factor-disjointness, §1.7).
* **Climb columns** for a gap `I`: integers `a` that are `R`-rough and coprime to
  `∏_{m ∈ I} m`. This is a sieve set defined by the primes dividing the *rows*
  in the gap, i.e. by a different, disjoint set of primes.

The disjointness in §1.7 is the asset nobody has used: the primes defining where
a packet is *cut* are disjoint from the primes defining where the neighbouring
gap is *climbable*. Two candidate formalizations:

**(A) Exponential sums / equidistribution.** Show the climb-column set is
equidistributed in residue classes modulo the reservoir primes `ℓ ≥ Z`, with
error beating the number of interfaces. Since climb columns are a sieve set with
level `R = Y^{o(1)}` and the moduli are `≥ Y^{5/2-η}`, this is a
large-modulus/short-set equidistribution question — likely needs a bilinear or
Bombieri–Vinogradov-type input, but the modulus is *fixed per interface* and only
`K ≈ Y^{1/2-η}` interfaces exist, so even a weak individual bound may suffice
after a union.

**(B) Second-moment / energy.** Count pairs (interface, alignment) with a second
moment over the packet structure; the disjoint supports make the relevant
correlation sums factor, which is exactly what defeated the first-moment
arguments. Target: show the number of interfaces admitting a climb-free slab is
`< K`, so some interface is crossable — that alone breaks every staircase.

**(C) Constructive dodge (weakest sufficient form).** Do not exclude all
staircases; show the *specific* reachable component can choose packets whose
interfaces are provably crossable — e.g. by selecting the reservoir subfamily
adaptively at the left shaft (free choice of starting height) so that the chosen
interfaces have climb columns at prescribed positions. This trades a global
theorem for a selection argument, and selection is where the campaign has
repeatedly found room.

## First concrete tasks

1. Numerics: build a surrogate reservoir at small `Y`, compute the joint
   distribution of (block residues, climb-column positions) per interface, and
   measure whether climb-free slabs at interfaces are as rare as (B) needs.
   Falsification target: if climb-free interfaces are *common* in the surrogate,
   ASE may be false and the whole tier architecture needs rethinking.
2. Literature probe: equidistribution of sieve sets in progressions to large
   moduli (Bombieri–Vinogradov for sifted sequences, Iwaniec's linear sieve in
   APs, Green–Tao-type transference for the specific level `R = Y^{o(1)}`).
3. If (A) or (B) yields a bound, restate ASE with explicit constants and referee.

## Status

Opened. No results yet. Prior probability of success unclear — this is the first
attack aimed at the actual difficulty rather than around it.

## MEASUREMENT RESULTS (2026-07-31) — ASE strongly supported; route (B) sharpened

Surrogate: semiprime reservoir rows (both factors >= Z) in a height window of
length Z at height ~1e9, exact block sets, exact dockable-climb sets, exact
reachability DP over the dual-staircase condition. Boundary convention generous
to the adversary. Columns [1e7, 1.4e7].

  Z     K    q_mean   q_max   mean climb-free gap  median p   log E[#staircases]
  300   27   0.0166   0.121   12.3                 4889       -1489
  600   23   0.0078   0.032   13.2                 5930       -1477
  1200  39   0.0082   0.032   14.1                 5345       -2241
  2400  59   0.0060   0.031   16.0                 6911       -5779
  4800  83   0.0045   0.021   18.5                 12603      -10712

Findings:
1. Direct DP: staircases die at depth 2 of up to 83 rows. No staircase exists
   at any tested parameter.
2. The per-interface survival probability obeys the predicted law
   q ~ (mean climb-free gap) * 6 / p_min, measured within a factor <= 2 of
   prediction at every Z. MECHANISM CONFIRMED.
3. Scaling is decisive: log E[#staircases] = log|B_1| + sum_i log q_i grows more
   negative with Z (-1489 -> -10712). At true scale p >= Z = Y^{5/2-eta} while
   climb-free gaps stay polylog, and K ~ Z/log Y, so the first moment is
   super-exponentially small.

**Why this is not another dead resource count.** Rounds 6/8/10 refuted arguments
that charge the adversary's *resources* (mass, prime occurrences, events). This
is a first moment over the *configuration space of staircases*, a different
object. Its key input is that consecutive reservoir rows have COPRIME moduli
(factor-disjointness), so the continuation condition at each interface is a
pair-correlation between two AP families with coprime moduli:

  #continuable pairs = #{(c,c'): c = block of row i, c' = block of row i+1,
                         |c - c'| <= |climb-free interval|}
                     ~ L * (6/p_i)(6/p_{i+1}) * 2G  by CRT,

giving q_i ~ 12G/p_{i+1} << 1 — elementary lattice-point counting, no sieve
multiplicity, no resource charging.

**Remaining ingredients for a proof (the sharpest the campaign has been):**
(i) Replace the fixed G by the actual climb-free interval lengths: need
    sum_J |J|^2 over climb-free intervals J, i.e. a SECOND MOMENT on
    climb-free gaps. The certified desert-counting theorem (Thm 3) is exactly
    the tool for this; block-sparsity gives |B ∩ J| <= 6|J|/Z + 6.
(ii) Make the CRT pair count uniform over interfaces and rigorous with the
    O(1) endpoint terms.
(iii) Sum over the K interfaces and conclude E[#staircases] < 1, hence NO
    staircase, hence ASE, hence #1212 = YES.

Next action: attempt (i) — the second-moment bound on climb-free gaps — using
the certified desert machinery. This is the first ASE route whose every
ingredient is either already certified or a standard sieve second moment.
