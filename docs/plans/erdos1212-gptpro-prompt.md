# Prompt for GPT Pro — Erdős Problem #1212

Copy everything below the line.

---

I want a complete, rigorous proof of the following open problem (Erdős
Problem #1212, erdosproblems.com/1212, source [Er80, p.114]). It is open; 0
proof claims are lodged. Treat this as a research task, not an exposition task.

**Problem.** Let $G$ be the graph with vertex set
$\{(x,y)\in\mathbb N^2:\gcd(x,y)=1\}$, two vertices joined when they differ in
exactly one coordinate, by exactly $1$. Is there a path going to infinity in
$G$ all of whose vertices $(x,y)$ satisfy $\min(x,y)>1$ and "at least one of
$x,y$ is composite"?

Equivalently: does the subgraph induced on
$V=\{(x,y):\gcd(x,y)=1,\ \min(x,y)>1,\ x\text{ or }y\text{ composite}\}$ have an
infinite component? ($V$ is locally finite, so by König a ray exists iff some
component is infinite — you never have to fight injectivity.)

Everything below is established and machine-verified. Use it, but re-derive
what you rely on.

**(1) Move parity.** $\gcd(x,y)=1$ forbids both coordinates even. If $y$ is
even then $x$ is odd, $x\pm1$ is even, so $\gcd(x\pm1,y)\ge2$: a horizontal
step requires $y$ odd, a vertical step requires $x$ odd.

**(1b) Clean edge criterion.** In the hub graph below the edges are exactly
$(a,b)\sim(a+2,b)$ iff $\gcd\!\big(b,\;a(a+1)(a+2)\big)=1$, and
$(a,b)\sim(a,b+2)$ iff $\gcd\!\big(a,\;b(b+1)(b+2)\big)=1$. Movement in one
coordinate is governed entirely by the prime factors of the other: a prime
$p\mid b$ blocks exactly three residues of $a$ mod $p$. The hub reduction is
**exact, not merely sufficient** — verified by comparing $H$-components against
direct BFS in $G$ on $[2,260]^2$: no $H$-component splits in $G$, no
$G$-component merges two $H$-components.

**(2) Hub reduction (an equivalence, both directions proved).** Every
hub-to-hub move is two steps through an intermediate vertex whose even
coordinate is $\ge4$, hence composite. So the composite condition is automatic
at intermediate vertices and at hubs says exactly "$a,b$ not both prime". Work
in $H$: $(a,b)$ both odd $\ge3$, $\gcd(a,b)=1$, not both prime; edges
$(a,b)\sim(a\pm2,b)$ iff $\gcd(a\pm1,b)=\gcd(a\pm2,b)=1$, and
$(a,b)\sim(a,b\pm2)$ iff $\gcd(a,b\pm1)=\gcd(a,b\pm2)=1$.

**(3) Dead rows.** If $3\mid b$, row $b$ admits no horizontal move (one of
$a,a+1,a+2$ is divisible by 3); symmetrically for columns. Dead rows are still
climbable *through*, so they are pass-throughs, not barriers.

**(4) Run length (exact).** On row $b$ the maximum number of consecutive $+2$
steps is $(p^-(b)-3)/2$, $p^-$ = least prime factor. Upper bound by
three-consecutive-integers, lower bound by CRT. Verified: rows $25,49,121,169$
give $1,2,4,5$.

**(4b) Vertical mobility is the bottleneck, not horizontal.** Exhaustively over
all $a\le10^7$, the 37-row window $b\in[1327,1399]$ always has at least **two**
simultaneously open rows — never zero. Yet a band-1400 search stalls at
$a=868869$, where 300 rows are open and 71 are reachable but the two sets are
**disjoint**, and $3\mid868869$ so no vertical move exists there at all. Row
changes can only occur at columns coprime to 3, and a column of least prime
factor $p$ permits vertical runs of only about $p/3$. Hence: **the row must be
chosen one hop before the blocking column** — the same conclusion as (7)–(8).

**(5) Wall Lemma (proved).** For any finite set $B$ of rows there are
infinitely many columns $a$ at which no row of $B$ permits $a\to a+2$: pick a
prime $p_b\mid b$ for each $b$, set $M=\prod$ distinct $p_b$, choose $a$ odd
with $a\equiv-1\ (\mathrm{mod}\ M)$ and $\gcd(a,b)=1$ for all $b$; then
$p_b\mid a+1$ for every $b$. Hence **both coordinates are unbounded** along any
valid infinite path, and no finite/periodic certificate can exist. Sharp form: if $a=\prod\{\text{odd primes}\le B\}$ then there is **no vertex at
all** with $b\le B$ (checked $B=13,17,19,23$). So the band in use must grow, and
$y\gg\log x$. But walls are astronomically sparse, so bands carry paths very
far: a band of ~280 rows has its first wall beyond $\prod p_b$.

**(6) Reach identity (the crux).** In a staircase whose legs are anchored at
composite rows/columns, a leg anchored at $n$ has length $< p^-(n)$. The
distance a leg travels is capped by the least prime factor of its own anchor.

**(7) The naive "Rescue Lemma" is FALSE.** One cannot repair a block after
arriving at it. Counterexample: hub $(29,25)$ — coprime, 25 composite, blocked
since $\gcd(30,25)=5$; the only legal climb targets at column 29 are rows
$26,27,28$, and the sole odd one, 27, is divisible by 3 and horizontally dead.
Sampling random *blocked* hubs, no rescue exists for 57.6% at $10^3$, 35.6% at
$10^6$, 21.6% at $10^{12}$. Reason: at a blocked hub the run window is already
exhausted (measured mean $\approx0.5$; every rescue found had $\Delta x=0$).
**The climb column must be chosen inside the run, before the block.**

**(8) The correct obligation (run-level).** For every sufficiently large odd
composite row $b$ with $3\nmid b$ and every maximal run $[a_0,a_0+W]$ of columns
coprime to $b$ that the construction reaches, there is $a^\ast\in[a_0,a_0+W]$,
odd, $3\nmid a^\ast$, and a row $b'>b$ with $\gcd(a^\ast,s)=1$ for all
$s\in(b,b']$, $b'$ odd composite, $3\nmid b'$, and
$\gcd(a^\ast+1,b')=\gcd(a^\ast+2,b')=1$ (composite condition automatic when
$a^\ast$ is composite). **This implies YES.** Empirically the dead-run fraction
falls $41.7\%\to11.7\%\to11.7\%\to1.7\%$ across scales $10^3\to10^9$, with
escape columns per run growing $1.2\to18.9$. This is the statement to prove.

**(9) BARRIER THEOREM — applies ONLY to anchored staircases; see (11), which evades it.** Define
$\mathcal G(z)=\min\{G:$ every $G$ consecutive integers contain a composite $n$
with $p^-(n)>z\}$. Call a construction *blind* if it locates anchors using only
the guarantee "every window of length $\ge\mathcal G(z)$ contains an anchor of
roughness $>z$". **No blind construction yields an infinite staircase.** Proof:
if $z_i$ is the roughness demanded of the $i$-th anchor, then by (6) its leg has
length $<z_i$ and the next anchor must be found inside a window of that length,
so blindness forces $z_i>\mathcal G(z_{i+1})$. But
$\mathcal G(z)\ge g(P(z))$ with $P(z)=\prod_{p\le z}p$ and $g$ Jacobsthal's
function, and by Rankin's lower bound
$g(P(z))\gg z\log z\log\log z/(\log\log\log z)^2>z$. So $z_i>z_{i+1}$: a
strictly decreasing sequence of positive integers, which terminates. $\square$
This is not an artefact of weak upper bounds — even a perfect
$g(P(z))\asymp z\log z$ leaves a $\log z$ deficit against the hard cap $z$ from
(6). **Consequence: any positive solution must exploit that the staircase
chooses its own location — it must produce rough integers in windows far
shorter than the worst-case gap, at positions constrained by earlier choices.
Equivalently, it must beat Jacobsthal on a self-selected subsequence. **But see
(11): the band-extension scheme never needs a rough anchor and never approaches
a wall, so this barrier does not apply to it.**

**(10) Evidence the answer is YES.** Components of the induced subgraph on
$[2,B]^2$ for $B=400,800,1600,3200,6400$: largest has
$595,3444,107446,1406484,7900365$ vertices ($0.66\%\to32.65\%$ of admissible
vertices), touching the border from $B=1600$ on, while the largest component
*not* touching the border saturates at exactly 21,423 and is unchanged at
$B=1600,3200,6400$. Verified qualifying paths: **1,166,791 distinct vertices reaching $x=867{,}999$
with $y$ confined to $[7,1399]$** (re-verified standalone from file —
recomputing gcd, minimum, primality, unit steps, distinctness — with zero
violations); 2,202,427 vertices from $(1137,1582)$ to $(10^6,10^6{+}1)$; escapes at scales $10^9$ and $10^{12}$ with
$\Delta x=200{,}000$ and essentially no backtracking; a monotone staircase at
$10^9$ advancing $\Delta x=2\cdot10^6$ against $\Delta y=11{,}742$ (runs mean
903, max 32,484; climbs mean 5.3). Naive greedy dies within 1–61 cycles at every
scale — that is greed, not obstruction. Band growth is startlingly slow: exact bisection gives minimal band
$B^\ast(A)=1248$ at $A=4001$ and **$1358$ flat from $A=8001$ through
$A=128001$** — $A$ grows $375\times$ while the band grows $1.5\times$; the data
cannot separate $O(\log A)$ from $\approx A^{0.07}$. Band 2000 reaches
$3\times10^6$ without stalling. Left moves are necessary (a monotone
never-move-left search dies at $a=1275$ for every ceiling from 800 to 9600) but
rare — about 0.1% of hops. **Correction on growth rates, important.** A staircase-based analysis suggested
forced growth $y\gg x^{2/3}$ on composite rows and $y\gg x^{1/2}$ in general.
The $x^{2/3}$ claim is **refuted by the witness above**: at $x=868{,}000$ it
would demand $y\approx9100$, but the verified path holds $y\le1399$. So that
bound is an artefact of the restricted monotone-staircase class, not a property
of paths. Even $y\gg x^{1/2}$ looks doubtful — the ratio band$/\sqrt A$ falls
from $3.8$ at $A=128001$ to $1.5$ at $A=868000$. **The only lower bound I regard
as proved is $y\gg\log x$, from the sharp primorial wall in (5).** Do not
assume anything stronger; if you can prove a sharper forced-growth bound, that
is itself a publishable partial result. Warning: below $B\approx800$ the data
misleads — the largest component there is small and interior, reading as
evidence for NO.

**(11) BAND EXTENSION — the live route, and the one to attack.** Two facts kill
the framing above.

*Walls are astronomically far, hence irrelevant.* For the band of all rows in
$[2,Y]$, every odd prime $p\le Y$ is itself a row whose only prime factor is
$p$, so a wall needs $a\equiv-1\pmod p$ for all odd $p\le Y$: the first wall is
at $\approx\frac12\prod_{3\le p\le Y}p=e^{(1+o(1))Y}$, i.e. $10^{161}$ for
$Y=400$, $10^{565}$ for $Y=1358$, $10^{1698}$ for $Y=4000$. Band $1358$ carries
a path to $x\approx10^5$, so its wall is $10^{560}$ times beyond the reachable
range. Self-consistently, if the band needed to reach $A$ grows like $C\log A$
the wall sits at $A^{C}$, never binding for $C>1$; measured $C\approx95$–$115$.

*Every observed stall is a local connectivity trap, not a wall.* Of 391 traps
recorded, **0 were Wall-Lemma columns**. A typical trap has ~98 open rows but
only ~3 reachable, median row-distance 2 between the two sets. Walls do exist
(81 below $10^7$ for $Y=400$, 8 for $Y=800$, exactly one for $Y=1000$ at
$a=64\,822\,393$, none below $10^8$ for $Y\ge1200$) but searches die at local
traps thousands of times before nearing one.

*Escape cost is small and does not grow with $x$.* Define $\Delta Y$ = extra
band width needed to get past a trap and sustain travel. Measured over 377
events: median $\Delta Y=148$, p90 $454$, max $682$; as a fraction of the band,
$0.068,0.148,0.062,0.154,0.097$ for $Y=800,1000,1200,1400,1600$. Flat in $x$ at
fixed band ($Y=800$: $102,54,54,54$ across decades $10^4$–$10^7$). Bands only
ever extend upward ($b=3$ is the floor). A ratchet from $Y_0=1400$ reached
$x=2\times10^7$ with **two** extensions ($1399\to1685\to1849$); $Y_0=2000$
reached $10^7$ with **none**; band 1600 crossed 1.5M columns over four decades
with one trap. Trap density falls ~$10\times$ per 200–400 extra rows and
decays in $x$ (gaps between traps grew $4.3\times10^5\to1.9\times10^6
\to7.65\times10^6$ columns under the ratchet). Verified witness: a band-extension
path of 1,413,051 vertices (band $1399$ to $x=866001$, then band $1685$ across
the $a=868869$ trap to $x\approx10^6$), checked from the definition — 0 bad
vertices, 0 bad steps, 0 repeats.

*Mechanism.* 66.8% of traps have $3\mid a$, which kills **every** vertical move
in that column (one of $b,b+1,b+2$ is always divisible by 3) — double the base
rate, and 96% of frozen-frontier traps. Of the rest, $5\mid a$ and $7\mid a$ are
over-represented by 12% and 44%, chopping the column's vertical runs. Escape
therefore means backtracking to a nearby column with $3\nmid a$ and climbing
there — which is exactly what extra band width buys.

**What I want.** A proof that the induced subgraph has an infinite component.
The target is now specific:

> **Band Extension Lemma (to prove).** There is a function $\Delta(Y)=o(Y)$
> (empirically $\Delta\approx0.06$–$0.15\,Y$, and possibly bounded) such that
> from any position reachable within the band $[2,Y]$ that is locally trapped,
> extending the band to $[2,Y+\Delta(Y)]$ restores travel.

Iterating gives $Y\asymp C\log x$ and hence an infinite path, with walls never
binding since $C>1$. This scheme uses no rough anchors, so the barrier in (9)
does not apply to it.

Suggested attack. At a trap the frontier sits at a column $a$ with $3\mid a$
(two thirds of cases), so no vertical move exists there; the escape must occur
at a nearby column $a'<a$ with $3\nmid a'$, climbing to a row $b'$ that is open
at $a$ and beyond. Count: over the $\Theta(\Delta)$ new rows and the
$\Theta(W)$ candidate columns in the current run, bound below the number of
pairs $(a',b')$ with $\gcd(a',s)=1$ for $s\in(b,b']$ and
$\gcd(b',a(a+1)(a+2))=1$. The constraints are congruences modulo distinct small
primes, so CRT gives near-independence — but they are deterministic and
correlated through the shared row set, so the dependency must be handled
explicitly, not assumed. A second-moment or Lovász-local-lemma argument over
these pairs is the natural shape.

Fallbacks if that resists: (a) prove the weaker statement that trap density in
$x$ decays fast enough that a Borel–Cantelli-style argument over scales gives an
infinite path; (b) renormalization over blocks with the correlation handled;
(c) adapt Herzog–Stewart, who per Erdős's report proved the unrestricted
visible-lattice graph has a unique infinite component — report precisely what
transfers to the composite-restricted subgraph.

**Ground rules.** Referee standard: every lemma proved or cited with theorem
number. No hand-waved independence — verify the dependency structure
explicitly. If you cannot finish, give the sharpest fully proved partial result
plus an exact statement of the remaining gap. Note the honest limits of my
data: the $\Delta Y$ figures are upper bounds under a 1200-column backtrack
budget; the rate $Y\approx95\ln x$ rests on only two extension events above
$Y=1400$ (the bound $\Delta Y\lesssim300$ is far better supported); and nothing
proves $\Delta Y$ is bounded — only that it never exceeded 682 across 391 traps
spanning $x\in[10^4,2\times10^7]$.
