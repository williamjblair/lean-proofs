# Erdős Problem #1212 — structure theory, reduction, and the residual obligation

**Status: GAP-REMAINS.** Everything in §§1–6 is proved unconditionally. §7 isolates the
single remaining obligation and §8 proves a barrier theorem showing that a large and
natural class of arguments — every argument that establishes the anchors through
worst-case gap bounds for rough integers — provably *cannot* discharge it. §9 gives the
numerical evidence, which points strongly to the answer **YES**.

---

## 0. The problem

Let $G$ be the graph with vertex set $\{(x,y)\in\mathbb N^2 : \gcd(x,y)=1\}$ (the visible
lattice points), two vertices adjacent when they differ in exactly one coordinate and
there by $\pm 1$. Call a vertex **qualifying** when

$$\min(x,y)>1 \qquad\text{and}\qquad \text{at least one of } x,y \text{ is composite},$$

and let $Q$ be the subgraph of $G$ induced on the qualifying vertices. Erdős asks
[Er80, p. 114] whether $Q$ contains a path going to infinity.

Sources pinned 2026-07-30:

* `erdosproblems.com/1212` — status **OPEN**, tagged *"cannot be resolved with a finite
  computation"*. Two forum comments; **0 proof claims**.
* Formal statement: `formal-conjectures/FormalConjectures/ErdosProblems/1212.lean`,
  `theorem erdos_1212` with `answer(sorry)`, plus machine-checked *partial* lemmas
  (`vertical_leg_valid`, `horizontal_leg_valid`, `anchor_coprime_of_short_leg`, and three
  "isolation" lemmas).
* Prior art in the forum thread (ephraimduncan, 21 Jul 2026): a **drift obstruction** —
  a qualifying walk with $|y-x|\le D$ throughout is confined to $x \le D!\,(x_0+1)$,
  because $\gcd(m,m+d)\ge d>1$ once $d\mid D!\mid m$. Hence $\limsup|y-x|=\infty$ along any
  infinite path. Also: qualifying paths of every *finite* length exist (the column $x=P^2$
  at heights $2\le y\le P-1$), so no finite computation settles the problem negatively.
* Historical: the *weaker* question (only $\min(x,y)>1$) was settled by Stewart with the
  prime-pair path $(p_k,p_{k+1})\to\cdots\to(p_{k+1},p_{k+2})$. That path consists almost
  entirely of prime–prime vertices, so the compositeness condition destroys it outright.
  This is exactly why #1212 is harder than its 1979 ancestor.

Throughout, $p^-(n)$ denotes the least prime factor of $n>1$.

---

## 1. Reduction to the hub graph

**Lemma 1.1 (no vertex has two even coordinates).** Immediate from $\gcd(x,y)=1$.

**Lemma 1.2 (parity of moves).** Let $u,v$ be adjacent in $G$.
(a) If $u,v$ differ in the first coordinate then their common second coordinate is odd.
(b) If they differ in the second coordinate then their common first coordinate is odd.

*Proof.* (a) Write $u=(x,y)$, $v=(x\pm1,y)$. If $y$ were even then $\gcd(x,y)=1$ forces
$x$ odd, hence $x\pm1$ even, hence $2\mid\gcd(x\pm1,y)$, contradicting $\gcd(v)=1$.
(b) symmetric. $\square$

Call a vertex a **hub** if both coordinates are odd, and a **link** otherwise (exactly one
coordinate even, by Lemma 1.1). Adjacent vertices differ in one coordinate by $1$, so
one of them is a hub and the other a link: **$G$ is bipartite between hubs and links.**

**Lemma 1.3 (links have degree $\le 2$, in a forced direction).** Let $v=(x,y)$ be a link
with $x$ even (so $y$ is odd). Then the only neighbours of $v$ in $G$ are $(x\pm1,y)$.
Symmetrically, if $y$ is even the only neighbours are $(x,y\pm1)$.

*Proof.* $y$ odd and $x$ even give $y\pm1$ even, so $\gcd(x,y\pm1)\ge2$ and $(x,y\pm1)\notin V(G)$. $\square$

**Definition 1.4 (hub graph $H$).** Vertices: pairs $(a,b)$ with $a,b$ odd, $a,b\ge3$,
$\gcd(a,b)=1$, and **not both $a,b$ prime**. Edges:

$$(a,b)\sim(a+2,b) \iff \gcd(a+1,b)=\gcd(a+2,b)=1,$$
$$(a,b)\sim(a,b+2) \iff \gcd(a,b+1)=\gcd(a,b+2)=1.$$

**Theorem 1.5 (reduction).** $Q$ contains a ray if and only if $H$ contains a ray.

*Proof.* ($\Leftarrow$) Expand each $H$-edge into two $G$-steps through its link. For a
horizontal edge the link is $(a+1,b)$: it is a $G$-vertex by the edge condition, has
$\min>1$, and $a+1$ is even and $\ge4$, hence **composite**, so it is qualifying. For a
vertical edge the link is $(a,b+1)$ with $b+1$ even and $\ge4$, likewise qualifying. Hub
vertices are qualifying by Definition 1.4 (odd and $\ge3$ gives $\min>1$; the primality
clause is exactly "not both prime"). Injectivity is preserved.

($\Rightarrow$) A ray in $Q$ alternates hub, link, hub, … by bipartiteness. Consecutive
hubs on the ray are at $\ell^1$-distance $2$ and, by Lemma 1.3, differ in exactly one
coordinate by $2$; the intervening link supplies precisely the two gcd conditions of
Definition 1.4. Hub coordinates are odd with $\min>1$, hence $\ge3$; and a qualifying hub
has odd coordinates, so "at least one composite" is "not both prime". $\square$

**Remark 1.6 (the compositeness condition nearly evaporates).** Theorem 1.5 shows the
compositeness constraint is *automatic* at every link and bites only at hubs, where it
says exactly: $a,b$ are not both prime. In particular, **if the anchor carrying a leg is
composite, every vertex of that leg is qualifying for free.** This is the mechanism behind
`vertical_leg_valid` / `horizontal_leg_valid` in the Lean file.

**Lemma 1.7 (König; connectivity suffices).** $Q$ is locally finite (degree $\le4$).
An infinite, connected, locally finite graph contains a ray. Hence **$Q$ contains a ray
iff $Q$ has an infinite connected component**, and one never has to fight injectivity
directly.

---

## 2. Dead rows, dead columns, and run lengths

**Lemma 2.1 (rows divisible by 3 carry no horizontal edge).** If $3\mid b$ then $H$ has no
horizontal edge on row $b$; if $3\mid a$, none vertical at column $a$.

*Proof.* A horizontal edge on row $b$ requires $a,a+1,a+2$ all coprime to $b$; one of any
three consecutive integers is divisible by $3$. $\square$

So horizontal travel occurs only on rows $b\equiv\pm1\pmod 6$ and vertical travel only at
columns $a\equiv\pm1\pmod 6$. Rows divisible by 3 are **not barriers**: they can be climbed
through, they simply carry no sideways motion.

**Lemma 2.2 (exact run length).** Let $b$ be odd with $3\nmid b$ and $p=p^-(b)$. The
supremum over starting columns of the number of consecutive horizontal $H$-steps
$a\to a+2\to\cdots$ available on row $b$ equals
$$k_{\max}(b)=\tfrac{p-3}{2}.$$

*Proof.* *Upper bound.* A run of $k$ steps needs $2k+1$ consecutive integers coprime to
$b$, hence containing no multiple of $p$; a block of $\ge p$ consecutive integers contains
one, so $2k+1\le p-1$, i.e. $k\le\frac{p-2}{2}$, and as $p$ is odd, $k\le\frac{p-3}{2}$.
*Lower bound.* Between consecutive multiples of $p$ lie $p-1$ consecutive integers. By CRT
choose the block so that it also avoids every other prime factor $q\mid b$ (each such
$q>p$, so $q$ has at most one multiple in a block of length $p-1<q$, and the $q$ available
residues let us push it out); within the block both parities of starting column occur, so
a run of $\frac{p-3}{2}$ steps starting at an odd column fits. $\square$

Measured values agree exactly: $p^-=5,7,11,13,17,19,23,29,31 \Rightarrow k_{\max}=1,2,4,5,7,8,10,13,14$
(rows $25,49,121,169,\dots$ and the corresponding prime rows). Verified with **0 violations**
for all odd $b<200$ with $3\nmid b$ (§9).

**Corollary 2.3.** Since a *composite* row has $p^-(b)\le\sqrt b$, horizontal runs on
composite rows have $x$-length $<\sqrt b$. Long runs therefore require rows with a large
least prime factor, i.e. $b=q^2$ or $b=qr$ with $q$ large. Prime rows admit the longest
runs of all ($p^-(b)=b$), but on a prime row *every* hub column must be composite, which
reintroduces a consecutive-composites (prime-gap) requirement; composite rows with large
$p^-$ avoid that entirely.

---

## 3. Both coordinates are unbounded (Wall Lemma)

**Theorem 3.1 (Wall Lemma).** Let $B$ be any finite set of rows. Then there are infinitely
many odd $a$ such that **no** $b\in B$ admits the horizontal step $a\to a+2$.

*Proof.* Every $b\in B$ is odd and $>1$; pick a prime $p_b\mid b$ and let
$M=\prod_{b\in B}p_b$ over distinct values, so $M$ is odd. By CRT choose $a$ odd with
$a\equiv-1\pmod M$. Then $p_b\mid a+1$, so $\gcd(a+1,b)\ge p_b>1$ and the step $a\to a+2$,
which requires $\gcd(a+1,b)=1$, is blocked on every row of $B$ simultaneously. There are
infinitely many such $a$ (one per residue class mod $2M$). $\square$

**Corollary 3.2.** Along any ray in $H$ the set of visited rows is infinite, and by the
$x\leftrightarrow y$ symmetry of the problem so is the set of visited columns. Hence both
coordinates are unbounded along any qualifying path.

*Proof.* Suppose the visited rows lie in a finite set $B$. The ray is injective, so it
cannot live in a finite region; as rows are confined, the column coordinate is unbounded.
Columns are odd and change by $\pm2$, so starting from column $x_0$ the ray must, for each
odd $a>x_0$ that it exceeds, execute the step $a\to a+2$ at some moment; that step is a
horizontal edge lying on some row of $B$. Choosing $a$ a wall column for $B$ with $a>x_0$
(Theorem 3.1) gives a contradiction. $\square$

Corollary 3.2 rules out every bounded-band construction and, in particular, every
*periodic certificate*: no finite set of rows, however cleverly chosen, carries a path to
infinity. It complements the drift obstruction of the forum comment
($\limsup|y-x|=\infty$) and the Lean file's `right_neighbor_witness_free` /
`left_neighbor_witness_free` isolation lemmas. Together: **the only possible shape of a
positive answer is a staircase with $y\to\infty$.**

Numerical confirmation of Theorem 3.1 (§9): wall columns below $20000$ number
$2571$ for the band $\{25,49\}$, $1444$ for $\{119,121\}$, $701$ for $\{25,49,121\}$, and
$161$ even for the 12-row band $\{25,35,49,55,65,77,85,91,95,121,125,169\}$ — thinning as
the band grows, never vanishing, exactly as CRT predicts.

---

## 4. The composite-anchor staircase: a sufficient condition

**Theorem 4.1 (Staircase sufficiency).** Suppose there are strictly increasing sequences of
odd integers $(a_i)_{i\ge0}$, $(b_i)_{i\ge0}$ with, for every $i$:

* **(S1)** $a_i$ and $b_i$ are **composite**, $b_i\ge5$, $a_i\ge9$;
* **(S2)** $\gcd(a_i,s)=1$ for every integer $s\in[b_i,\,b_{i+1}]$;
* **(S3)** $\gcd(t,b_{i+1})=1$ for every integer $t\in[a_i,\,a_{i+1}]$.

Then $Q$ contains a ray, i.e. **#1212 has answer YES**.

*Proof.* Concatenate, for $i=0,1,2,\dots$, the vertical leg $\{(a_i,s):b_i\le s\le b_{i+1}\}$
followed by the horizontal leg $\{(t,b_{i+1}) : a_i\le t\le a_{i+1}\}$. Consecutive vertices
are adjacent in $G$; (S2) and (S3) make every vertex visible; $\min>1$ holds since
$a_i\ge9$, $b_i\ge5$; the composite condition holds on the vertical leg because $a_i$ is
composite and on the horizontal leg because $b_{i+1}$ is composite. Both coordinates are
non-decreasing and $a_i\to\infty$, so the walk is injective and leaves every finite box. $\square$

This is the unconditional core, and it is exactly the shape whose two halves are already
machine-checked in the Lean file (`vertical_leg_valid`, `horizontal_leg_valid`), with
`anchor_coprime_of_short_leg` supplying a sufficient criterion for (S2)/(S3).

**Proposition 4.2 (Reach identity).** In any staircase as in Theorem 4.1,
$$b_{i+1}-b_i < p^-(a_i), \qquad a_{i+1}-a_i < p^-(b_{i+1}).$$
Moreover, since the anchors are composite, $p^-(a_i)\le\sqrt{a_i}$ and $p^-(b_{i+1})\le\sqrt{b_{i+1}}$.

*Proof.* $[b_i,b_{i+1}]$ contains no multiple of $p:=p^-(a_i)$ by (S2); an interval of $p$
consecutive integers contains one; so its length $b_{i+1}-b_i+1\le p$. Same for (S3). $\square$

**Proposition 4.2 is the crux of the whole problem**: *the distance a leg can travel is
capped by the least prime factor of the anchor carrying it.* Rough anchors give long legs,
but rough anchors are exactly what is hard to locate inside a short window.

---

## 5. The "Rescue Lemma" is false as usually stated

A tempting induction step is:

> **(R)** From a hub $(a,b)$ that is blocked on its row, there is a row $b'>b$ reachable by a
> legal climb at column $a$ (i.e. $\gcd(a,s)=1$ for all $s\in(b,b']$) with $b'$ composite,
> $3\nmid b'$, and $\gcd((a+1)(a+2),\,b')=1$, so that travel resumes.

**(R) is false.**

**Counterexample 5.1.** Take $(a,b)=(29,25)$: a legitimate hub ($29$ prime, $25$ composite,
coprime), blocked on its row since $\gcd(30,25)=5$. The only prime factor of $29$ is $29$
itself and the next multiple of $29$ above $25$ is $29$, so a legal climb reaches at most
row $28$; the only odd row in $(25,28]$ is $27$, which is divisible by $3$ and therefore
horizontally dead (Lemma 2.1). No rescue exists at $(29,25)$.

This is not an isolated accident. Sampling random blocked hubs (§9):

| scale of $(a,b)$ | blocked hubs sampled | **no rescue exists** | mean run window at the blocked hub |
|---|---|---|---|
| $10^3$ | 250 | 144 (57.6%) | 0.54 |
| $10^4$ | 250 | 119 (47.6%) | 0.49 |
| $10^6$ | 250 |  89 (35.6%) | 0.47 |
| $10^9$ | 250 |  68 (27.2%) | 0.48 |
| $10^{12}$ | 250 |  54 (21.6%) | 0.45 |

The failure rate decays only very slowly (consistent with $\asymp 1/\log\log$) and shows no
sign of vanishing. Note also the second observation, which is decisive for how the proof
must be organised: **at a blocked hub the run window is already exhausted** (mean $\approx0.5$,
and every rescue found had $\Delta x=0$). One cannot repair a block after arriving at it.

**Corollary 5.2 (correct form of the induction step).** The climb column must be chosen
*inside the run, before the block*. The honest obligation is the run-level statement:

> **(LCH)** For every sufficiently large odd composite row $b$ with $3\nmid b$ and every
> maximal run $[a_0,a_0+W]$ of columns coprime to $b$ that the construction reaches, there
> is a column $a^\ast\in[a_0,a_0+W]$ with $a^\ast$ odd, $3\nmid a^\ast$, and a row $b'>b$
> with $\gcd(a^\ast,s)=1$ for all $s\in(b,b']$, $b'$ odd composite with $3\nmid b'$,
> $\gcd(a^\ast+1,b')=\gcd(a^\ast+2,b')=1$, and the composite condition satisfied on the
> climb (which holds automatically when $a^\ast$ is composite).

By Theorem 4.1, **LCH along the constructed chain $\Rightarrow$ YES.**

---

## 6. Why the naive greedy staircase dies, and why the general path does not

The greedy monotone staircase (always take the right-most legal climb column, then the
lowest legal row) gets stuck within a handful of cycles at every scale tested
($10^3$ to $10^7$; typically after 1–61 cycles). The reason is Corollary 5.2: greed spends
the run and then finds itself at a blocked hub with no climb.

With **backtracking**, the picture inverts completely. A depth-first search restricted to
*monotone* moves (east/north only) — which is precisely a staircase searched exhaustively
rather than greedily — advances freely at every scale $\ge10^6$: at $10^9$ it advanced
$\Delta x=2\cdot10^6$ using $2{,}028{,}712$ node expansions and only $16{,}969$ backtracks
(0.8%), yielding a **verified monotone qualifying path of $2{,}011{,}743$ vertices**.
So the obstruction is entirely local and repairable with $O(1)$ lookahead in practice.

Measured leg statistics of that path (the parameters of Theorem 4.1 in the wild):

| | count | mean length | max length | mean $p^-(\text{anchor})$ |
|---|---|---|---|---|
| horizontal runs | 2215 | 902.9 | 32484 | $2.8\cdot10^8$ |
| vertical climbs | 2214 | 5.3 | 34 | $2.7\cdot10^8$ |

$\Delta x=2\cdot10^6$ against $\Delta y=11{,}742$, a ratio of $170$: the staircase is strongly
lopsided, long runs on rough rows separated by cheap $+2$/$+4$ climbs, exactly as Corollary
2.3 predicts and comfortably consistent with the drift obstruction $\limsup|y-x|=\infty$.

---

## 7. The residual obligation, quantified

Fix a scale. On a row $b$ with $p^-(b)=q$ the run has $\le q$ columns (Lemma 2.2). We must
find inside it a column $a^\ast$ that is coprime to the $L$ rows we intend to climb through
($L\approx5$ in practice, $\le34$ observed). Writing $M_L=\prod_{s=b+1}^{b+L}s$, the
requirement is $\gcd(a^\ast,M_L)=1$ with $a^\ast$ composite; then the next row $b'$ must be
composite, $3$-free, and coprime to $a^\ast(a^\ast+1)(a^\ast+2)$.

*Heuristic count.* $\omega(M_L)\ll L\log b/\log\log b$, so integers coprime to $M_L$ have
density $\gg1/\log L$ and the run of length $q$ should contain $\gg q/\log L$ candidates. For
the row: $a^\ast(a^\ast+1)(a^\ast+2)$ has $O(\log a^\ast)$ prime factors, but a *fixed* prime
$p\ge5$ divides it only with "probability" $3/p$, and costs a factor $(1-1/p)$ when it does;
the expected log-loss is $\asymp\sum_p 3/p^2<\infty$, so on average the density of admissible
rows is $\gg\prod_{p\ge5}(1-3/p^2)>0$ — a **positive constant, independent of scale**
(the primes $2$ and $3$ always divide $a^\ast(a^\ast+1)(a^\ast+2)$, but admissible rows are
odd and $3$-free anyway, so they cost nothing extra). Hence the expected number of
continuations is $\gg q$, and the construction should never terminate. This is why every
heuristic points to **YES**, and why the numerics percolate so cleanly.

*What is missing.* Every one of these counts is an assertion about a **short interval at a
location the construction does not fully control**. That is precisely the regime in which
nothing unconditional is available. §8 shows the difficulty is structural, not a deficiency
of effort.

---

## 8. Barrier theorem: worst-case gap bounds provably cannot close the argument

Define, for $z\ge2$,
$$\mathcal G(z)=\min\{G : \text{every interval of } G \text{ consecutive integers contains a composite } n \text{ with } p^-(n)>z\}.$$
A "blind" construction is one that produces the anchors of Theorem 4.1 using only the
guarantee encoded by $\mathcal G$: *every window of length $\ge\mathcal G(z)$ contains an
anchor of roughness $>z$.*

**Theorem 8.1 (Reach barrier).** No blind construction produces an infinite staircase.

*Proof.* Let $z_i$ denote the roughness demanded of the $i$-th anchor. By Proposition 4.2
the leg carried by that anchor has length $<z_i$, and the next anchor must be found inside a
window of exactly that length. Blindness therefore requires
$$z_i \;>\; \mathcal G(z_{i+1}) \qquad\text{for all } i .$$
But $\mathcal G(z)\ge g(P(z))$, where $P(z)=\prod_{p\le z}p$ and $g$ is Jacobsthal's function
(dropping the compositeness demand only lowers $\mathcal G$), and by the Rankin-type lower
bound
$$g(P(z)) \;\gg\; z\,\frac{\log z\,\log\log z}{(\log\log\log z)^{2}} \;>\; z$$
for all large $z$. Hence $z_i>\mathcal G(z_{i+1})>z_{i+1}$: the roughness parameters form a
strictly decreasing sequence of positive integers, which terminates after finitely many
steps. $\square$

**Remark 8.2.** The barrier is *not* an artefact of weak upper bounds. Iwaniec's
$g(P(z))\ll z^2\log^2 z$ is far from the truth, but even a perfect Jacobsthal bound
$g(P(z))\asymp z\log z$ leaves a factor $\log z$ deficit against the hard cap $z$ imposed by
Proposition 4.2. The cap and the guarantee are on opposite sides of the same quantity.

**Corollary 8.3 (what any solution must do).** A positive solution must exploit the fact
that the staircase *chooses its own location*, i.e. it must produce rough integers in
windows far shorter than the worst-case gap, at positions constrained by earlier choices.
Equivalently it must beat Jacobsthal on a self-selected subsequence. No known technique
does this, which is consistent with the problem's OPEN status and with the site's remark
that it "cannot be resolved with a finite computation" (also independently implied by the
forum comment's finite-path construction, and by Corollary 3.2 here, which kills every
finite/periodic certificate).

---

## 9. Computational validation

All code in this directory; every claim below re-derived from the raw definition of $Q$
(no reliance on the reduction) unless stated.

**(a) Structure, exhaustive on $[2,400]^2$** (`path_search.py --box 400`). Zero violations of:
horizontal steps only on odd rows; vertical steps only at odd columns; every vertex with an
even coordinate $\ge4$ satisfies the composite condition; no horizontal edge on a row
divisible by 3; no vertical edge at a column divisible by 3; and the run-length formula
$k_{\max}=(p^--3)/2$ (checked for all odd $b<200$, $3\nmid b$, skipping rows whose maximal
run cannot fit in the box — the 32 "violations" in a first run were exactly that truncation
artefact, and vanish once the box is large enough for the row).

**(b) Components.** In $[2,400]^2$: $90{,}550$ qualifying vertices, $12{,}400$ components,
largest $595$ and interior — a small-box artefact. The component of $(9,10)$ is exactly
$\{(8,11),(9,10),(9,11),(10,11)\}$, reproducing the forum comment. Percolation is invisible
below $B\approx1600$; from a seed at scale $10^3$ upwards, BFS saturates a $200{,}000$-vertex
cap at essentially every seed tried (5 of 6 at scale $10^3$; 6 of 6 at $10^4,10^5,10^6$).

**(c) Wall columns** (Theorem 3.1), below $20000$: $2571$ for $\{25,49\}$, $1444$ for
$\{119,121\}$, $701$ for $\{25,49,121\}$, $161$ for the 12-row band. Independent
reproduction of the coordinator's counts.

**(d) Long verified paths.** DFS in the raw graph from $(1137,1582)$ reached $x=10^6$:
a simple path of **$2{,}202{,}427$ vertices**, $4{,}158{,}385$ node expansions, 46 s,
**zero violations** (coprimality, $\min>1$, not-both-prime at every vertex; unit steps;
injective). Escape tests at scale $10^9$ and $10^{12}$: $\Delta x=200{,}000$ reached with
$202{,}792$ and $200{,}682$ node expansions respectively — i.e. almost no backtracking —
each verified violation-free.

**(e) Monotone (staircase) paths.** East/north-only DFS: exhausts at scale $10^3$, but at
$10^6$ and $10^9$ reaches $\Delta x=10^5$ with $\approx1.0$–$1.2$ expansions per path vertex.
The $10^9$ run to $\Delta x=2\cdot10^6$ gave the leg statistics in §6, zero violations.

**(f) Rescue margin.** Two measurements (`rescue_margin.py`, `rescue_margin.json`,
`run_escape.json`).

*Blocked-hub level* (the table of §5): rescues per blocked hub average $0.72$ at $10^3$,
$1.34$ at $10^4$, $5.2$ at $10^6$, $7.8$ at $10^9$, $12.0$ at $10^{12}$, and the first
rescue stays cheap (mean climb $\approx4$ rows, max $16$). But a positive fraction of
blocked hubs — still $21.6\%$ at $10^{12}$ — admit **no** rescue at all.

*Run level* (the statement LCH actually needs, 120 sampled maximal runs per scale, run
window capped at 300 columns and climbs at 60 rows):

| scale | mean run window | mean escape columns per run | **runs with no escape** |
|---|---|---|---|
| $10^3$ | 8.2 | 1.18 | 50/120 = 41.7% |
| $10^5$ | 43.4 | 9.61 | 14/120 = 11.7% |
| $10^7$ | 69.3 | 14.02 | 14/120 = 11.7% |
| $10^9$ | 83.1 | 18.85 | **2/120 = 1.7%** |

This is the decisive numerical fact: measured at the level at which the induction step is
actually stated, the failure rate collapses with scale while the number of available
continuations grows roughly linearly with the run window. A dead run is a local event whose
frequency $\to0$; a backtracking staircase (§6) walks past them without difficulty.

**Interpretation.** The evidence for **YES** is strong and improves with scale: the
qualifying graph percolates, monotone staircases run freely, and the number of legal
continuations per step grows. None of this is a proof; every step of it is a finite
computation, and Corollary 3.2 shows no finite computation can be upgraded to a proof.

---

## 10. Self-adversarial pass

The four classic failure points, checked against this write-up:

1. **A transition column blocked in both rows.** Real and fatal in the naive two-row
   ladder: rows $9$ and $25$ (the natural "CRT with coprime periods $3$ and $5$" idea) do
   not work at all, because **row 9 admits no horizontal step whatsoever** (Lemma 2.1,
   $3\mid9$). More generally the two-row ladder is killed outright by the Wall Lemma
   (Theorem 3.1). Any argument of the "complementary blocking patterns" type is dead.
2. **An intermediate row whose gcd condition fails for all available columns.** This is
   exactly Counterexample 5.1 and the 21.6%–57.6% failure rates in §5. The naive Rescue
   Lemma is false; only the run-level version (Corollary 5.2) can be true.
3. **Prime–prime vertices sneaking in at transitions.** Eliminated structurally: by
   Remark 1.6 the condition bites only at hubs, and a composite anchor discharges it for a
   whole leg. All 2.2M-vertex and 2.0M-vertex paths above were verified against the raw
   not-both-prime condition with zero violations.
4. **The induction not escaping to infinity.** Handled two ways: Theorem 4.1 produces a
   strictly monotone path, so escape is automatic; and Corollary 3.2 + the forum drift
   obstruction show that *any* solution must have both coordinates unbounded and
   $\limsup|y-x|=\infty$ — the observed ratio $\Delta x/\Delta y\approx170$ is comfortably
   on the right side of that.

Two further self-attacks, on my own reasoning:

5. **Is Theorem 1.5 lossy?** No: both directions are proved, and the reduction is an
   equivalence, so no solution is lost by working in $H$.
6. **Could the barrier of §8 be circumvented by prime rows (which give the longest runs)?**
   On a prime row every hub column must be composite, so a run of length $\ell$ demands
   $\ell$ consecutive odd composites at a prescribed location — a prime-gap requirement,
   which is *harder* than the rough-number requirement it replaces. This exchange does not
   help.

---

## 11. Verdict

**GAP-REMAINS.**

*Established unconditionally here:* the hub reduction (Theorem 1.5) and its consequences —
dead rows/columns (Lemma 2.1), the exact run-length law (Lemma 2.2), the disappearance of
the compositeness condition off the hubs (Remark 1.6); the Wall Lemma and the unboundedness
of both coordinates (Theorem 3.1, Corollary 3.2), which kills every bounded-band and every
periodic certificate; the composite-anchor staircase sufficiency theorem (Theorem 4.1) and
the reach identity (Proposition 4.2); the falsity of the naive Rescue Lemma (§5); and the
reach barrier (Theorem 8.1), which rules out the entire class of blind/worst-case-gap
arguments.

*Not established:* the run-level continuation statement LCH of Corollary 5.2, which is the
whole remaining content of the problem. Everything points to its truth; nothing available
proves it.

*Expected answer:* **YES**, via a strongly lopsided staircase.

**Forced growth rate.** Proposition 4.2 also yields a lower bound on how fast $y$ must
grow, which is worth recording. Each climb contributes $\Delta y\ge2$; each run contributes
$\Delta x<p^-(b)$. If the staircase travels on composite rows, $p^-(b)\le\sqrt b\approx\sqrt y$,
so $dx/dy\ll\sqrt y$ and therefore
$$x \ll y^{3/2}, \qquad\text{i.e.}\qquad y \gg x^{2/3}.$$
If prime rows are also allowed, $p^-(b)=b$ gives only $x\ll y^2$, i.e. $y\gg x^{1/2}$. Either
way $y\to\infty$ polynomially in $x$, so the staircase cannot be made arbitrarily flat —
another way of seeing Corollary 3.2. (These are lower bounds on $y$; the measured path at
$x\approx10^9$ ran with $\Delta x/\Delta y\approx170$, far above the bound, as expected.)
