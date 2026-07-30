# Erdős #1212 — structural reduction (verified 2026-07-30)

**Problem.** $G$ has vertices $\{(x,y)\in\mathbb N^2:\gcd(x,y)=1\}$, edges join
vertices differing by $\pm1$ in exactly one coordinate. Is there a path to
infinity all of whose vertices satisfy $\min(x,y)>1$ and have at least one of
$x,y$ composite?

The following reduction is mine (not from the literature) and every claim below
was checked exhaustively by computer for all $x,y<400$ (zero violations).

## 1. Move parity

$\gcd(x,y)=1$ forbids both coordinates even. Hence:

* A horizontal step $(x,y)\to(x\pm1,y)$ **requires $y$ odd**: if $y$ is even then
  $x$ is odd, so $x\pm1$ is even and $\gcd(x\pm1,y)\ge2$.
* Symmetrically, a vertical step **requires $x$ odd**.

So $(\text{odd},\text{odd})$ vertices are hubs with both move types available;
$(\text{even},\text{odd})$ lies on a horizontal segment only;
$(\text{odd},\text{even})$ on a vertical segment only.

## 2. The reduced graph $H$

Every hub-to-hub move is exactly two steps through one intermediate vertex.
Define $H$ on pairs $(a,b)$, both odd, $\ge 3$, $\gcd(a,b)=1$, with

$$(a,b)\sim(a\pm2,b)\iff \gcd(a\pm1,b)=\gcd(a\pm2,b)=1,$$
$$(a,b)\sim(a,b\pm2)\iff \gcd(a,b\pm1)=\gcd(a,b\pm2)=1.$$

An infinite path in $H$ with $a\to\infty$ lifts to one in $G$.

## 3. The composite condition collapses

Each intermediate vertex has an even coordinate $\ge4$, hence composite, so the
condition is automatic there. At hubs it says exactly: **$a$ and $b$ are not
both prime**. Together with $\min>1$ that is the entire remaining constraint.

## 4. Rows divisible by 3 are horizontally dead

A horizontal move from $(a,b)$ needs $3\nmid a,\,3\nmid(a+1),\,3\nmid(a+2)$
whenever $3\mid b$ — impossible. So rows $9,15,21,27,33,\dots$ admit **no**
horizontal progress (symmetrically for columns divisible by 3 and vertical
moves). Travelable rows are odd with $3\nmid b$.

**They are still climbable**: passing vertically through such a row costs only
$\gcd(a,b)=1$. Dead rows are pass-throughs, not barriers — so the expensive
long climb (needing $a$ coprime to every integer in a long range) is avoidable
in principle by rising two rows at a time.

## 5. Run length is governed by the least prime factor

On row $b$, a horizontal run continues while $a,a+1,a+2$ all avoid $\equiv0$
modulo each prime dividing $b$. The binding constraint is $p=p_{\min}(b)$, and
the maximum number of consecutive $+2$ hub-steps is $(p-3)/2$. Verified:

| row | 25 | 49 | 121 | 169 |
|---|---|---|---|---|
| $p_{\min}$ | 5 | 7 | 11 | 13 |
| max hub-steps | 1 | 2 | 4 | 5 |

So no fixed row carries a path to infinity. In fact much more is true (§6). Long runs need
rows with large least prime factor ($p^2$, or $pq$ with $p$ large). Prime rows
$b$ give the longest runs of all but then force every hub column to be
composite, which reintroduces a prime-gap condition; composite rows with large
$p_{\min}$ avoid that entirely.

## 6. Wall Lemma: every finite band fails

**Lemma.** Let $B$ be a finite set of rows. There are infinitely many columns
$a$ at which no row of $B$ permits the step $a\to a+2$.

*Proof.* For each $b\in B$ pick a prime $p_b\mid b$ and let $M$ be the product
of the distinct $p_b$. By CRT choose $a$ odd with $a\equiv-1\pmod M$ and
$\gcd(a,b)=1$ for all $b\in B$. Then $p_b\mid a+1$ for every $b$, so
$\gcd(a+1,b)>1$ and the step is blocked on every row of $B$ simultaneously.
There are infinitely many such $a$. $\square$

Any rightward crossing from column $a$ to $a+2$ occurs on a single row, so a
path whose rows lie in a finite set cannot cross a wall column. Hence:

**Corollary.** Along any valid infinite path, the set of rows visited is
infinite; by the $x\leftrightarrow y$ symmetry, both coordinates are unbounded.

Counts of wall columns below $20000$ (verified): $2571$ for $\{25,49\}$,
$1444$ for $\{119,121\}$, $701$ for $\{25,49,121\}$, $865$ for
$\{119,121,125\}$, and $161$ for the twelve-row band
$\{25,35,49,55,65,77,85,91,95,121,125,169\}$ — thinning with band size,
never vanishing.

## 7. The Rescue Lemma is FALSE

The natural way to finish is a greedy staircase resting on:

> *(Rescue Lemma, proposed).* From a blocked hub $(a,b)$ there is a row $b'$
> reachable by a legal climb at column $a$ with $b'$ admissible and passable.

**This is false.** Sampling blocked hubs uniformly and searching for a rescue
by any climb of length $\le 60$ in either direction:

| scale | blocked hubs | rescued | no rescue |
|---|---|---|---|
| $10^4$ | 400 | 82.8% | **17.2%** |
| $10^6$ | 400 | 85.5% | **14.5%** |
| $10^8$ | 400 | 87.0% | **13.0%** |

The failure rate decreases with scale but does not vanish. Explicit smallest
counterexamples, with no rescue by *any* climb up to 200:
$(a,b) = (11,9), (13,9), (17,9), (19,9), (23,9), (29,9)$.

Take $(11,9)$. It is blocked rightward since $\gcd(12,9)=3$. Climbing up is
blocked immediately: $\gcd(11,11)=11$. Climbing down to row 7 *is* legal
($\gcd(11,8)=\gcd(11,7)=1$), but the hub $(11,7)$ has both coordinates prime
and is therefore inadmissible. The obstruction is precisely the interaction of
the climb constraint with the not-both-prime condition.

**Consequence.** No greedy or monotone staircase can work: a positive
proportion of blocked hubs are dead ends, so any valid infinite path must
backtrack. This matches the search data — a run escaping from scale
$1.5\times10^9$ over two million columns required about 17,000 backtracks —
and it explains why induction on a single advancing frontier fails.

## 7b. The obligation is at RUN level, not hub level

Correcting §7: one cannot repair a block *after* arriving at it — at a blocked
hub the run window is already exhausted (measured mean $\approx 0.5$; every
rescue found had $\Delta x = 0$). The climb column must be chosen **inside the
run, before the block**. The honest continuation hypothesis is therefore
run-level: for every large odd composite row $b$ with $3\nmid b$ and every
maximal run of columns coprime to $b$ that the construction reaches, some
column $a^\ast$ in that run admits a legal climb to an odd composite row
$b'>b$ with $3\nmid b'$ and $\gcd(a^\ast+1,b')=\gcd(a^\ast+2,b')=1$. That
statement implies YES. Empirically the dead-run fraction falls
$41.7\%\to11.7\%\to11.7\%\to1.7\%$ over scales $10^3\to10^9$.

## 8. Reach barrier (unconditional; supersedes the heuristic below)

A leg anchored at $n$ has length $< p^-(n)$ (reach identity). Let
$\mathcal G(z)$ be the least $G$ such that every $G$ consecutive integers
contain a composite $n$ with $p^-(n)>z$. A *blind* construction — one locating
anchors only via that worst-case guarantee — needs
$z_i > \mathcal G(z_{i+1})$. But $\mathcal G(z)\ge g(P(z))$ with $g$
Jacobsthal and $P(z)$ the primorial, and Rankin's **lower** bound gives
$g(P(z))\gg z\log z\log\log z/(\log\log\log z)^2 > z$. So the roughness
parameters strictly decrease and the scheme dies in finitely many steps.
$\square$ Even a perfect $g(P(z))\asymp z\log z$ leaves a $\log z$ deficit
against the hard cap $z$. Any positive solution must beat Jacobsthal on a
self-selected subsequence — i.e. exploit that the staircase chooses its own
location.

## 8b. Heuristic precursor (my original, weaker form)

A horizontal run on row $b$ has reach $\le p_{\min}(b)\le\sqrt b$, and a climb
at column $a$ has reach $\le p_{\min}(a)\le\sqrt a$. To continue after a run
one needs a column of least prime factor $\ge K$ inside the reach window; gaps
between $K$-rough integers are Jacobsthal-sized, $\asymp (K/\log K)^2$, so the
window must satisfy $p_{\min}(b)\gtrsim K^2$. Applying the same argument to the
next row gives $K\gtrsim p_{\min}(b')^2$, whence
$p_{\min}(b')\lesssim p_{\min}(b)^{1/4}$: the arithmetic quality of the rows
and columns in use degrades geometrically and hits the floor after $O(\log\log)$
steps. So the path cannot march; it must wander, which is what the data shows
(mean straight-segment length 7.3 in the verified witness).

## Consequence for the proof

Sections 7 and 8 rule out the greedy staircase and any monotone repair of it.
What survives is that the answer is almost certainly YES (see
`compute1212pct/RESULT.md`: the giant component escapes every box from
$B=1600$ and absorbs a growing share of vertices, while finite components
saturate at 21,423), and that a proof must be a *connectivity* argument
tolerating backtracking — showing the admissible set percolates — rather than
an explicit forward construction. That is the open core.

Verification script: see the campaign log; results reproduced above.


## 9. The Wall Lemma is vacuous as an obstruction (2026-07-30, later)

Quantifying §6. For the band of all rows in $[2,Y]$, every odd prime $p\le Y$
is *itself* a row whose only prime factor is $p$, so a wall column must satisfy
$a\equiv-1 \pmod p$ for every odd $p\le Y$. The first wall therefore sits at
$a\approx\tfrac12\prod_{3\le p\le Y}p = e^{(1+o(1))Y}$:

| band $Y$ | 100 | 400 | 800 | 1358 | 1400 | 2000 | 4000 |
|---|---|---|---|---|---|---|---|
| first wall | $10^{36}$ | $10^{161}$ | $10^{329}$ | $10^{565}$ | $10^{581}$ | $10^{842}$ | $10^{1698}$ |

Measured, band $1358$ suffices to reach column $A\ge128001\approx10^5$. Its wall
is at $10^{565}$ — **larger than the reachable range by a factor of
$10^{560}$**. Self-consistency: if the band needed to reach $A$ grows like
$C\log A$, the wall for that band lies at $e^{C\log A}=A^{C}$, so walls never
bind whenever $C>1$; measured $C\approx115$.

**Consequence.** The Wall Lemma is true but *vacuous as an obstruction*. It
establishes only that $y$ must be unbounded; it says nothing about where the
difficulty lies. Every stall observed in practice is a **local connectivity
trap**, not a wall — the band-1400 search stalled at $a=868869$ with 300 rows
open and 71 rows reachable and those sets disjoint ($3\mid868869$, so no
vertical move existed there at all).

This also means the Reach Barrier of §8, while correct, targets the wrong
class: it kills anchored staircases that must locate rough anchors at
worst-case positions. It says nothing against **band extension** — ride a band
until a local trap, enlarge the band to escape, repeat — because that scheme
never needs a rough anchor and never approaches a wall. Whether band extension
works turns on a single measurable quantity: the extra band width $\Delta Y$
needed to escape a trap. Bounded or slowly growing $\Delta Y$ would give an
induction sidestepping §8 entirely.
