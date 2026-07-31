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

## Ingredient (i) — climb-free gap tail: ESSENTIALLY CLOSED

**Parameter check.** Need density of climb-free gaps > D to be <= 1/(6 delta p),
p >= Z = Y^{5/2-eta}. Certified desert-counting Thm 3 gives density
<= (1/D)(C log z/D)^k with z ~ (vertical gap) ~ log Y, valid when
log X >= Ck(log 2T + log_2 3z)log(3kz). CRITICAL: X is the column MAGNITUDE
~ e^{Y/2}, not the shaft-gap length; so log X = Y/2 while the requirement is
~ C log Y log log Y. Needed k ~ (5/2)log Y/log log Y. Verified:
  Y=1e6: log X = 5e5 vs condition 5.8e3 — SATISFIED, margin 86x
  Y=1e8: log X = 5e7 vs condition 7.0e3 — SATISFIED, margin 7194x
Margin grows like Y/(log Y log log Y). Ingredient (i) is available from
already-certified machinery.

**Surrogate confirmation** (3.4M gaps over 38 interfaces, Z=1200): mean gap
14.1 (delta=0.071); P(gap>D) tracks exp(-delta D) within 0.7-1.2x out to
D=140, with the expected Jacobsthal heavy tail appearing at the far end
(4.2x at D=200) — precisely why the polynomial-of-arbitrary-order form of
Thm 3 is needed rather than a geometric model. At the surrogate's own
required D=122, observed P=2e-4 vs required 4.3e-4: satisfied, 2x margin
(the surrogate has Z/G ~ 10 vs Y^{5/2}/polylog at true scale, so this is the
hardest possible case).

## Ingredient (iii) — assembly: BLOCKED, and the blocker is sharp

Per-interface the count works: pairs (c,c') with c in B_i, c' in B_{i+1},
|c-c'| <= D is a CRT lattice count over coprime moduli, ~ 72DL/(p_i p_{i+1}),
giving q_i ~ 12D/p_{i+1} << 1 — provided L >= p_i p_{i+1} ~ Y^{5-2eta} (true
for long shaft gaps; short gaps must be handled separately, and have few
blocks anyway).

The chain does NOT assemble by iterating this. Two failed routes, both
recorded so they are not re-attempted:
* **l1 contraction fails.** sum_{c'} v_{i+1}(c') = sum_c v_i(c)|B_{i+1} n J(c)|
  needs the MAX continuation count, not the average; the weight v_i can
  concentrate on the few c with continuations.
* **Crude drift bound fails.** Treating the chain as congruence conditions on
  c_1 with drift <= jD makes the j-th condition a window of size ~2jD mod
  p_{j+1}; these go vacuous once jD > Z, i.e. after j ~ Z/D steps, while the
  chain has K ~ Z/log Y > Z/D rows. The product of densities then exceeds 1
  (it behaves like (2D/(e log Y))^K).

**The residual analytic statement** is therefore: the chain positions
equidistribute modulo the successive row primes. Precisely — for the chain
c_1 -> ... -> c_j determined by primes p_1..p_j, the value c_j mod p_{j+1}
should be equidistributed (p_{j+1} being a distinct prime, coprime to all
data defining c_j except through the climb sets). This is a multi-dimensional
equidistribution / exponential-sum statement over a drifting chain, NOT a
resource count and NOT a single-modulus equidistribution.

Status: the first-moment route is now reduced to exactly this one statement,
with ingredient (i) supplied by certified machinery and the per-interface
count elementary. This is the sharpest the problem has been, but it is not a
proof, and the residual statement is genuinely hard.

## 2026-07-31 (later): quadratic climb latency + the pursuit-game reduction

**Quadratic climb lemma (NEW, improves certified cubic; to referee).** The
climb condition "gcd(a, prod_{m in [r,r+h]} m) = 1" is ONE forbidden residue
(0) per prime: all p <= h (each divides some m), plus <= 5h log Y/log h big
primes with <= 1 multiple each per window. Linear sieve at level h^2 on a
window of length T: count >= T/(2 log h) - h^2 - 10h log Y/log h > 0 for
T >= C h^2 log h. Columns at scale x = e^{Y/2} are prime with density 2/Y --
negligible; 2 | product forces oddness free. So EVERY window of length
C h^2 log h contains an odd composite dockable climb column: latency h^2
polylog, vs the certified cubic (which paid an extra factor for compositeness
via the ell*n trick -- unnecessary since primes are density 1/log x at column
scale, GPT Pro's own round-9 S5.1 observation). VERIFIED numerically:
density 0.12-0.14 ~ 1/log h; max gaps 90-130 at h=12..48, far below h^2 log h.

**The pursuit-game reduction (final structural picture).** Crossing a shaft
gap is a pursuit game: the component (holding all reachable rails, mobile
within radius Lambda(w) = (w Y/30)^{1/kappa} after w windows of patience at
latency exponent kappa) vs a moving blocked frontier of thickness Theta
(refreshed under the 6-events-per-rail-per-Z budget, forcing frontier
velocity >= Theta/6 per window). Path beats frontiers with Theta^kappa < Y/C;
adversary needs Theta >= (Y/C)^{1/kappa}. THE BUDGET IS SCALE-FREE: sweep
cost = (duration)(events/window) = (6E/Theta)(Theta/10 log Y) ~ E/log Y ~
budget, INDEPENDENT of Theta and kappa: no exponent improvement (even
kappa = 1) breaks the draw; homogeneity extends it to multi-reservoir play.
CONCLUSION: the game is critical -- decided by constants and by
phase-realizability of coordinated frontiers, not by any counting or latency
exponent. This is the precise, apparently irreducible core of #1212:
* the answer is YES iff the actual prime multiples cannot realize a
  constant-factor-perfect sweeping frontier;
* every counting resource (mass, events, capacity) is EXACTLY balanced at
  every scale -- explaining both why the problem is hard and why every
  plausible-looking argument on both sides has failed;
* a proof requires either winning the pursuit constants (sharpen 6-events,
  frontier refresh, and latency constants jointly until the draw breaks) or
  a phase/equidistribution input about multiples of the reservoir primes.

This supersedes ASE as the sharpest formulation: ASE-with-constants IS the
pursuit game.
