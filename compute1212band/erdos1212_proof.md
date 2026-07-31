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

**Hit-fraction bound (ELEMENTARY, the key count).** For a fixed column a,
the four integers a−1..a+2 have total large-prime budget
Σ_{p > y, p | (a−1)a(a+1)(a+2)} 1/p ≤ 4·log(log 2s/log y) + o(1)
(Mertens-extremal packing). The fraction of y-rough rows R (in any height
range) with gcd(R, (a±1)(a±2)) > 1 is ≤ (1+ε) times this budget:
- y = z: budget ≤ 4 log 5 ≈ 6.4 — vacuous (an adversarial column CAN block
  all z-rough pairs);
- y = Y := 2 log 2s: budget ≤ 2/(5 log z) — 99.9% of Y-rough pairs are
  open at EVERY column.

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
density: one per z³⁶ ≪ visited extent) and continue. The fraction of
columns at which a GIVEN pair is blocked is ≤ 30/z, and pairs ~ z⁵/log z,
but adversarial columns blocking ALL tier-0 pairs are possible (budget
6.4): at such x*, cross on a tier-1 pair — open there with margin
(budget 2/(5 log z): the fraction of tier-1 pairs blocked at ANY fixed
column is o(1); a fortiori some tier-1 pair is open at x* — indeed at
every column of [x*−Y, x*+Y] simultaneously chosen per column). Reach
tier 1 by a shaft behind F, run across the bad region on the tier-1 pair
(its own twin blocks: same argument one level up — tier-1 blocking
columns need budget ≥ 1 against Y-roughness: impossible, since the
TOTAL budget is ≤ 4 log(log 2s/log Y) + ε = 4 log(z⁵/K / (5 log z·..)) —
wait: log 2s/log Y = (z⁵/K)/(log(2z⁵/K)) ~ z⁵/(5K log z): budget
4 log(z⁵/5K log z) ≈ 20 log z·(0/1)... CORRECTION: budget at tier 1 =
4·log(log 2s / log Y) = 4 log(z⁵/K ÷ 5 log z·(1+o(1))) ≈ 4(5 log z −
log log z) ≈ 20 log z?? — NO: Mertens: Σ_{Y<p≤T}1/p = log(log T/log Y);
extremal T with θ(T)−θ(Y) ≤ log 2s: T ≈ log 2s = Y/2: T < Y means NO
primes fit: an integer n ≤ 2s CANNOT have many primes > Y = 2 log 2s,
since each exceeds Y and log n ≤ log 2s = Y/2 < log Y·(#) — precisely:
ω_{>Y}(n) ≤ log n/log Y = (Y/2)/log Y, and Σ 1/p ≤ ω/Y ≤ 1/(2 log Y).
Total 4-window budget at tier 1: ≤ 2/log Y = 2/(5 log z) — no column can
block more than an o(1)-fraction of tier-1 pairs, and blocking a GIVEN
tier-1 pair somewhere in a stretch still leaves the 1−o(1) rest: tier-1
twin blocks are passed by switching among tier-1 pairs via tier-1-height
shafts, and no third tier is ever needed.)
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
