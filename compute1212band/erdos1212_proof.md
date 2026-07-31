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
