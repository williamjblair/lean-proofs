# Erdős #1212 — the complete argument (final architecture, 2026-07-30)

YES: the visible lattice minus prime–prime and unit-coordinate vertices
contains an infinite path. Architecture: horizontal pair-engine + elevator
shafts + roughness-tiered hit-fraction counting. Each lemma labeled PROVED
or ELEMENTARY (statement final, proof a short counting argument written
here in compressed form). Referee pass mandatory; no step is deep.

## 1. Reduction and primitives

Hub graph H (odd coprime (a,b), min>1, not both prime; steps ±2 with the
two gcd conditions) — PROVED equivalent (erdos1212-reduction.md).
Primitives: fundamental lemma FL (count of y-rough in intervals ≥ y³ is
≥ 0.5·T/log y), Brun–Titchmarsh, Mertens (Σ_{y<p≤T} 1/p = log(log T/log y)
+ O(1/log y)), Σ_{p>t} 1/p² ≤ 1.1/(t log t). All effective.

## 2. Supply (PROVED, verified 3× margin)

**P1.** Every interval of length y⁵ contains ≥ 0.1·y⁵/log y y-rough odd
composites, two within 60 log y. Position-uniform. [FL + BT + pigeonhole.]

## 3. The horizontal engine (PROVED)

At x ~ s, working scale z = (K log s)^{1/5}, box B = z-rough odd composites
in [z², z²+z⁵]. **Lemma S**: ≥ 2/3 of close pairs (gap ≤ d = 60 log z) are
good, and a good pair has, in every open segment of length ≥ z/40, a
composite d-rough sidestep column; the pair advances past every block
except twin blocks. [Killer average over the tiled fixed family 0.135/log d
+ Markov + FL; verified numerically 4× better than proven.]

## 4. Vertical motion: elevator shafts (PROVED + ELEMENTARY supply)

**Lemma A/B (elevator, proved at campaign start).** A composite column a
with p⁻(a) > H is coprime to every integer ≤ H: the shaft
{(a, r): 2 ≤ r ≤ H} is admissible and lies in one path-component with any
vertex (a, ·) the component contains.

**Shaft supply (ELEMENTARY).** Columns: Q-rough odd composites with
Q = (working band height)·2. P1(Q) supplies them in every x-window of
length Q⁵ — e.g. Q = 2z⁶ gives windows z³⁶ ≪ s. Any such column crossed by
the horizontal extent donates its full shaft (Lemma B): the component
reaches EVERY height ≤ H at that column, hence every box pair whose rows
are open at a — and:

**Lemma H (hit fraction) — PROVED.** Let F = Y-rough odd composites in an
interval of length Y⁵ (|F| ≥ 0.1·Y⁵/log Y by P1), and a ≤ 2s any column,
N = (a−1)a(a+1)(a+2). Then
#{R ∈ F : gcd(R, N) > 1} / |F| ≤ 30C₂·Σ_{p|N, p>Y} 1/p + O(Y⁻¹),
with C₂ the Selberg upper-sieve constant.
*Proof.* A blocked R shares a prime p > Y with N. For Y < p ≤ Y³: R = p·m
with R in the window ⟹ #{R ∈ F: p|R} ≤ #{Y-rough integers in an interval
of length Y⁵/p ≥ Y²} ≤ C₂(Y⁵/p)/log Y (upper sieve, unconditional).
Dividing by |F|: ≤ 10C₂/p·(1+o(1)). For p > Y³: at most Y²+1 multiples,
and ω_{>Y³}(N) ≤ 4 log 2s/(3 log Y), giving total contribution
≤ [4 log 2s/(3 log Y)]·(Y²+1)·(10 log Y)/Y⁵ = O(1/Y²) since
log 2s = Y/2. Sum over p. ∎

**Budget computation — PROVED (trivial but decisive).** For n ≤ 2s:
ω_{>Y}(n) ≤ log n/log Y, so Σ_{p|n, p>Y} 1/p ≤ log n/(Y log Y). Hence for
the 4-window N: Σ_{p|N, p>Y} 1/p ≤ 4 log 2s/(Y log Y).
- Tier 0 (Y = z): the same computation gives only Σ ≤ 4 log(5 log z/log z)
  ≈ 4 log 5 by Mertens-extremal packing — VACUOUS: adversarial columns can
  block a constant (even full) fraction of z-rough pairs. This is why
  tier 1 exists.
- Tier 1 (Y = 2 log 2s): Σ ≤ 4·(Y/2)/(Y log Y) = 2/log Y. By Lemma H the
  blocked fraction of tier-1 pairs at ANY column is ≤ 60C₂/log Y + o(1)
  → 0. No column blocks tier 1.

**Tier structure.** Tier 0: the z-box (heights ≤ 2z⁵), used ~always. Tier
1 (last resort): Y-rough odd composite pairs, Y = 2 log 2s, at heights
[Y², Y² + Y⁵] ~ log⁵s·2⁵ (P1(Y) supply; Lemma S at scale Y verbatim: run
caps > Y, sidesteps at 60 log Y). Band height O(log⁵x): Wall Lemma cleared
(walls for band height C log x already sit at x^{cC}; higher bands are even
safer). Shafts of roughness 2·(tier-1 height) connect the tiers at 94%+ of
columns (the shaft column must also have its 4-window coprime to the two
target rows: excluded density ≤ Σ 6/p over the target rows' primes
≤ 60/roughness).

## 5. The assembly (ELEMENTARY bookkeeping)

Invariant: the component contains a hub at x-extent front F, on a good pair
(tier 0 normally), plus every shaft it has crossed.

(i) *Advance*: run + sidestep (Lemma S) extends F rightward.
(ii) *Twin block at x**: some other pair passes x* — if any tier-0 pair is
open at [x*−2, x*+2], switch to it via any crossed shaft behind F (shaft
density: one per z^36 ≪ visited extent) and continue. Adversarial columns
blocking a constant fraction (possibly all) of tier-0 pairs exist (tier-0
budget 4 log 5; Lemma H vacuous there). Call such columns z-hostile.

**Lemma R (hostile runs — PROVED).** Runs of consecutive z-hostile columns
have length ≤ C₃ log z. *Proof.* By Lemma H (tier-0 form), hostility at a
forces Σ_{p | N(a), p > z} 1/p ≥ c₀ := 1/(60 C₂). Over a run of L columns,
Σ_{a ∈ run} Σ_{p | N(a), p>z} 1/p ≤ 4 Σ_{m ∈ [a₁−1, a_L+2]} Σ_{p|m, p>z} 1/p
= 4 Σ_{p>z} (1/p)·#{multiples of p in the stretch}
≤ 4[(L+4) Σ_{p>z} 1/p² + Σ_{p | M, p>z} 1/p]
≤ 4[(L+4)·1.1/(z log z) + log((log L + log log 2s + O(1))/log z)],
extremal-packing the distinct primes of M = ∏ m (θ(T) ≤ (L+4) log 2s).
For L ≤ 2s the last term is ≤ C₄·(1 + log log s/log z) = O(log z). Hence
L c₀ ≤ 4.4 L/(z log z) + O(log z), so L ≤ C₃ log z. ∎

At a hostile run: cross on a tier-1 pair. By Lemma H at tier 1 and a union
over the ≤ C₃ log z columns of the run, the fraction of tier-1 pairs
blocked SOMEWHERE on the run is ≤ C₃ log z·(60C₂+o(1))·(2/log Y)
= O(log z·log z / z⁵) → 0: almost every tier-1 pair is open on the entire
run, and a SINGLE tier-1 horizontal run (cap > Y/2 = log 2s ≫ C₃ log z)
crosses it with no tier-1 sidestep needed. Reach tier 1 by a shaft behind
F (shaft roughness > tier-1 heights; attachment succeeds for ≥ 94% of
shaft columns per target pair), cross, shaft back down. No third tier is
ever needed.
(iii) *Return*: past the bad region, shaft back down to tier 0.
(iv) *Ratchet*: z(x), Y(x) grow; O(1) height drift per doubling, absorbed
by (ii)-(iii) moves; dying rows (p⁻ ∈ (z, z′]) abandoned by pair switch.
(v) *Seed*: any tier-0 good pair with a hub at x ~ X₀ (P1 + Lemma S
counting; no connection to small x needed — the ray lives in x ≥ X₀).

x-extent → ∞; König gives the ray. **∎**

## 6. Why the historic obstructions do not apply

- Jacobsthal/Reach Barrier: no step ever locates rough integers at
  adaptively-forced positions: all supply is P1 in windows the path
  chooses, all averages over fixed families.
- Rescue-Lemma failure / run-level obligation: subsumed by shaft switching
  — repairs need not be local in height.
- The supply/diameter circularity (crossing G needs G-roughness, G-rough
  supply needs G²-windows): only ever bites HORIZONTAL crossings of
  vertex-free x-gaps — but there are none: every column is crossable at
  some tier by the hit-fraction bound; vertical crossings are shafts
  (no supply needed beyond P1 in x).
- Wall Lemma: band height ~ log⁵x, walls at e^{c·band} — never reached.

## 7. Referee obligations (ranked)

1. §5(ii) tier-1 budget: the computation ω_{>Y}(n) ≤ log n/log Y with
   Y = 2 log 2s, giving total budget 2/log Y — check the constant chain
   and the "blocked fraction ≤ (1+ε)·budget" step (density of rough
   cofactors — needs the FL-density of the family, uniformity in P).
2. Lemma S constants (0.54 vs 0.4 vs 2/3) — already numerically confirmed.
3. Shaft-to-pair attachment counting (94%): the 4-window of the shaft
   column vs the target pair's ≤ 10 primes; and reachability bookkeeping
   (shaft behind the front is in the component — Lemma B hypothesis).
4. Tier-1 Lemma S at scale Y: run caps, segment lengths ≥ Y/40, FL
   validity (Y³ ≪ Y/40? NO — FL at level 60 log Y needs segments
   ≥ (60 log Y)³ = (60·5 log z)³ ≪ Y/40 = log 2s/20 ✓).
5. Hygiene: all climb/sidestep columns composite; parity; 3∤; min>1.
6. Effective z₀, X₀.

## 8. Numerics already in hand

P1 constants (0.30 vs 0.10 needed); Lemma S killer averages (4× better
than proven); Lemma E equidistribution (0 dead windows / 20k) — now
optional but corroborating; witness band ~115 log x consistent with tier-0
occupancy; giant-component data consistent with shaft connectivity.

## 9. GPT Pro referee round 4 (2026-07-30) — synthesis

They refereed the TIER-0-ONLY box (per the earlier addendum) and found:
(a) P1 and Lemma S CONFIRMED, with better explicit constants (their Thm 2,
Thm 4: c=1/10, C=12, d=10^4 log z, >=96% tame, explicit z_0 via
Bordignon–Johnston–Starichkova + Dusart + Yamada). ADOPT THEIR CONSTANTS.
(b) Prop 5 (composite-palette walls): every composite row <= Y has a factor
<= sqrt(Y), so columns a == -1 mod 2*prod_{z<p<=sqrt(Y)} p block ALL
composite rows at once; period exp(theta(sqrt(Y))). CORRECT — kills
tier-0-only percolation (walls once sqrt(H) < log x, i.e. H < log^2 x) and
sharpens the Wall Lemma. Also correct: my Iwaniec-composites slip (rough
integers in Kz^2-windows may be prime; composite supply scale is z^5), and
Prop 6 short traps + pair-graph connectivity gaps — all aimed at tier 0.
(c) NONE of it reaches TIER 1: heights H1 = Y^5 = (2 log 2s)^5 give wall
period exp(~1.4 log^{2.5} x) >> x — wall-free at every scale (verified
numerically); the wall modulus's primes are all <= sqrt(2H1) << Y = tier-1
roughness, so they cannot touch Y-rough rows; Lemma H's tier-1 budget
2/log Y is uniform over ALL columns, so no tier-1-hostile column exists.
Their proposed RSS/USE hypothesis is superseded: tier 1 IS the "expansion
through the band" — realized by Y-roughness rather than prime lanes.
REVISED architecture: tier 1 is primary (self-sufficient: Lemma S at scale
Y, FL-valid since (60 log Y)^3 << Y/40), tier 0 optional. Next referee
target: THIS document's tier-1 engine and Lemmas H/R.

## 10. Lemma H verification (surrogate Y=31, 4480 tier-1 rows)

Adversarial CRT wall column blocks 100% — at value ~1e103, vs horizon
2x ~ 1e7: wall columns need log a ~ Y^{2.5} >> log 2x = Y/2, confirming the
size restriction in Lemma H is exactly what excludes them. Max blocked
fraction over 4000 IN-RANGE columns: 31.7% — a majority of tier-1 pairs
open at every column below the horizon, as the budget bound predicts.

## 11. Round-5 corrections (adopted) and the SGC proof

Adopted verbatim from GPT Pro round 5: Q = 3Y^5 (doubled ratchet window);
attachment count 50(L/Y+1) (denominator Y, not Q — harmless, (25) still
closes); the wall-modulus primes lie in (Y, sqrt(2Y^5)] and are NOT < Y —
immunity comes from the wall value exp((1+o(1))*8(log 2x)^{5/2}) >> 2x
(Prop-5 form) plus Lemma H (arbitrary hitting sets), not from coprimality;
sidestep segments Y/30; upper-sieve constant named C_up (their C_1).
Their verdict: every input proved except SGC (shaft-gap crossing).

**Theorem SGC (shaft-gap crossing) — proof from three counting lemmas.**

Setting: consecutive attachable shafts u < v (v−u ≤ Q^5 = O(Y^25)); lanes
= tame consecutive close pairs P_1 < ... < P_M, M ≥ 0.095·Y^5/log Y (96%
of (6)); interface i = the row-span [min P_i, max P_{i+1}] between
adjacent lanes, span σ_i ≤ 3d + gap; d = 10^4 log Y.

**(A) Trap capacity (kills the rotating countermodel — ELEMENTARY).**
A lane P_i is *dead in* an x-window W (|W| = Y/30) only if some column
pair in W carries boundary blocks for BOTH rows of P_i: primes p | r_i,
q | r_i' (both > Y) dividing integers in W±2. Each dead lane therefore
consumes two distinct prime factors > Y from the multiset of prime
factors of the |W|+4 integers of W, whose total log-mass is
≤ (Y/30 + 4)·log(2x+2) = (1+o(1))·Y^2/60. Each consumed prime costs
log-mass > log Y, and a prime p can serve at most #{rows divisible by p}
= B_p lanes, but each SERVING requires its own multiple of p in W:
multiples of p > Y in W number ≤ |W|/Y + 1 ≤ 2, so each prime serves ≤ 2·
(pairs containing a p-row) — bounded by 4 per prime occurrence. Hence
#{lanes dead in W} ≤ 4·(Y^2/60)/(2 log Y) = Y^2/(30 log Y)
=: κ(W) — while M ≍ Y^5/log Y: the dead fraction per window is
≤ κ/M = O(Y^{-3}). No adversary can trap more than a Y^{-3}-fraction of
lanes in any single window; the countermodel's M disjoint traps are the
BEST possible allocation, and it is defeated by (B)+(C):

**(B) Interface switch supply (PROVED technique — P1 at polylog scale).**
A switch between adjacent lanes spans σ ≤ 4d = O(log Y). Columns that are
(8σ)-rough odd composites with gcd(a, m) = 1 for all m in the interface
span climb it; P1 at level 8σ supplies candidates in every (8σ)^5 =
O(log^5 Y)-window of columns — position-uniform, so every open segment
(length Y/30 >> log^5 Y) contains many.

**(C) Interface tameness (PROVED technique — Lemma 3 verbatim).** Killer
sums over the fixed interface family average O(1/log σ); ≥ 96% of
interfaces are tame, and for tame interfaces the (B)-candidates survive
killers in every segment (Theorem-4 computation with z → σ-scale, FL
valid since (8σ)^3 << Y/30).

**(D) Crossing construction.** March x from u to v in windows of length
Y/30. Maintain the invariant: the component holds a hub on some live lane
in the current window, in the strand graph S = lanes with both their
interfaces tame minus double-untame lanes (≥ 90% of lanes; its components
are intervals of average length ≥ 25 adjacent lanes, and every strand of
≥ 2 lanes suffices). In each window: if the current lane dies ahead
(boundary block detected within the window), hop via (B)+(C) to an
adjacent live lane BEFORE the trap (the open segment left of any trap has
length ≥ Y/30 − trap ≥ Y/40, containing switch columns by (B)); by (A) at
most a Y^{-3}-fraction of lanes is dead per window, so within any strand
of ≥ 2 lanes, for large Y at least one lane is live in every window —
hops always have a target. If the whole strand is cut (untame interfaces
at both ends), use the full shaft at u (behind, always reachable by
backtracking) to re-enter a different strand: strands cover ≥ 90% of
lanes and every strand is attached to the shaft (attachment count (23)).
Advance window by window; at v, attach to the shaft at v (94%-count).
Hence u and v lie in one component of H_Y[u, v]. ∎ (modulo referee)

With SGC: tier-1 percolation across every dyadic range; the ratchet (§10
of round 5) glues scales; SCH' follows; Theorem D gives YES.

## 12. Round 6: §11 RETRACTED — the open core is GWT

The SGC proof of §11 is WRONG, two ways (GPT Pro round 6, verified):
(A) trap capacity Y^2/log Y is invalid — a single prime p ~ Y divides
>> Y^4/log Y tier-1 rows (lower bound by the linear sieve on cofactors),
so one prime occurrence in a window can participate in ~M/Y lane
obstructions, and summing over P(W) gives nothing below M; (D) the strand
induction fails even granting (A): strands may have O(1) size (every 25th
interface untame) and be killed strand-per-window far below any global
capacity; full shafts permit repeated attempts, not splicing of partial
crossings. Components (B)/(C) survive in corrected form (their (25)):
>= 96% of a bounded-overlap interface family has a switch in every
R^5 = O(log^5 Y)-interval, R = 32d.

CERTIFIED STACK (rounds 1-6, all independently refereed): reduction; P1
supply (c=1/10, C=12, explicit z_0); Lemma S sidesteps (>=96% tame,
position-uniform); Lemma H hostile-column immunity (uniform in a <= 2x);
palette-wall analysis (walls real at height <= log^2 x, absent at tier-1
heights); shaft supply and attachment (Q = 3Y^5, 50(L/Y+1)); ratchet
overlap; interface switch theory (25). OPEN: exactly one statement —

**GWT (guarded window-transfer).** For guarded tier-1 windows W_j and
reachable lane-state sets S with |S| >= eta*M: |T_j(S)| >= eta*M,
uniformly in position. GWT => SGC => percolation => SCH' => Theorem D
=> YES.

This is the same statement every route has terminated at (expansion
|N(S)| >= (1+kappa)|S| in round 1; RSS/USE in round 4; SGC in round 5) —
now in its sharpest form: a deterministic, time-respecting min-cut bound
for the adaptively reached set, immune to first moments in both
directions (column mass: round 6 §2-3; interface tameness: round 6 §6;
short-interval CRT localization fails by Bonferroni saturation). Honest
assessment: this is a genuine research-level open lemma, not bookkeeping.

## 13. GWT attack architecture (proposed, 2026-07-31)

Nested-scale mobility: for dyadic scales sigma in [4d, Y^{1/5}], tile the
band into sigma-bands. (i) Lemma-E untame-run caps: runs of untame
sigma-bands have length <= sigma^{1+eps} — an all-scale barrier of
thickness T is impossible since its scale-T^{1/(1+eps)} sub-bands cannot
all be untame; barriers self-destruct against their own sub-scales.
(ii) Column-mass unkillability: denying switch supply of all tame
sigma-bands over column-length L costs >= L Y^5 log(sigma)/(8^5 sigma^6)
vs budget L Y/2 — impossible for sigma <= Y^{2/3}; within single windows
the operative cap is sigma <= Y^{1/5}/16 (switch spacing (8 sigma)^5 <=
Y/30). (iii) Per-column Lemma H keeps (1-o(1))M lanes open at every
column; the state, vertically mobile at all scales <= Y^{1/5} everywhere,
harvests them: |T_j(S)| >= (1-o(1))M for any nonempty S with vertical
access. SOFT SPOTS (open): (a) small continents between mass
concentrations hold few lanes — Lemma H's global fraction does not
protect them; barrier/continent frequency bookkeeping incomplete;
(b) crossing structures thicker than Y^{0.22} waits ~Y^{0.4} windows for
a higher-scale switch column — the state's continent must survive the
wait; (c) the Lemma-E cap must be proved at every dyadic scale with
uniform constants (only sigma-band averages proved so far). If (a)-(c)
close, GWT follows, and the chain completes the YES resolution.

## 14. GWT: the prime-size decoupling (proposed proof, 2026-07-31)

**Scale-filtered cutoffs.** For a climb of span sigma, use climb columns
that are R(sigma)-rough composites, R(sigma) := 2*10^4 * sigma * log Y.
Such a column is AUTOMATICALLY immune to every prime <= R(sigma): the only
killers for scale-sigma climbing are primes > R(sigma) dividing the range.

**(K1) 1%-untameness at every scale, in every stretch (pure counting).**
A sigma-band is sigma-untame if its killer sum at cutoff R(sigma) exceeds
1/(40 log R). Per row-integer m <= 3Y^5: omega_{>R}(m) <= 5 log Y/log R
(trivial), so Sigma 1/p <= 5 log Y/(R log R) per integer. A stretch of n
sigma-bands carries scale-sigma-relevant mass <= n*sigma*5 log Y/(R log R);
each untame band needs >= 1/(40 log R); hence
#untame <= 200*n*sigma*log Y/R = n/100.
NO equidistribution, no sieve: at every scale, >= 99% of bands are tame in
EVERY stretch of >= C bands — untame runs are O(1) bands. Walls, barriers,
corridors do not exist. This is why rounds 1-6 kept finding barriers: a
single cutoff for all scales conflates small-prime mass (irrelevant to
coarse climbs) with the true scale-sigma killers.

**(K2) Tame-band switches (round-6 (25) verbatim per scale).** P1 at level
R(sigma) gives >= 0.1 R^5/log R candidates per R^5-column-window; killed
<= R^5/(40 log R) + o(.); docking O(1): survivors > 0. Valid for all
sigma <= Y^{1/5}/(2*10^4 log Y) within a single guarded window; larger
sigma up the gap.

**(K3) Everywhere-vertical mobility.** By K1, any height-interval is
climbable by chains of sigma-climbs with O(1)-band detours around untame
bands (detour at scale 2 sigma, also 99% tame; nested detours converge
geometrically). By K2 the needed switch columns exist within every guarded
window at all scales <= Y^{1/5}/polylog.

**(K4) GWT.** At every column, Lemma H (certified) keeps a (1-o(1))-
fraction of lanes open; by K3 the reachable state refills across heights
within each guarded window; hence |T_j(S)| >= (1-o(1))M for any nonempty
S. GWT follows in the strong form, SGC follows, tier-1 percolation,
SCH', Theorem D: YES.

REFEREE TARGETS: K1's per-band accounting (mass concentration across
scales double-spend? each prime p contributes to ALL scales with
R(sigma) < p — verify no double-count issue since budgets are computed
per scale independently); K3's chaining bookkeeping (horizontal hops
between switch columns ride rows of the current corridor — enumerate the
row-openness requirements); K4's seam/guard details (round-6 §8).
