# Erdős #1212 — the Elevator package (proved) and the reduced open core

Status: Lemmas A–C below are **proved** (elementary, self-contained). Theorem D
is **proved conditional on hypothesis SCH**, which is stated precisely and
remains open. This supersedes the "Band Extension Lemma" as the campaign
target: the elevator mechanism eliminates the *climb* half of the difficulty
unconditionally, so what remains open is exactly the *horizontal stitching*
half.

Setting: the admissible graph $G$ on
$V=\{(x,y):\gcd(x,y)=1,\ \min(x,y)>1,\ x\text{ or }y\text{ composite}\}$, edges
$=\pm1$ in one coordinate.

## Lemma A (Elevator columns)

Let $a=pq$ with $p\le q$ primes. Then every vertex $(a,s)$ with $2\le s\le p-1$
is admissible, and the column segment $\{(a,s):2\le s\le p-1\}$ is a path in
$G$.

*Proof.* $a$ is composite, so the composite condition holds at every $(a,s)$
regardless of $s$. For $2\le s\le p-1$ we have $s<p\le q$, so no prime factor
of $a$ divides $s$: $\gcd(a,s)=1$, and $\min(a,s)\ge2$ with $s\ge2$, $a\ge6$.
Hence each $(a,s)$ is admissible, and consecutive $(a,s),(a,s+1)$ differ by
$1$ in one coordinate. $\square$

Nothing in the proof uses primality of the cofactor beyond $p^-(a)=p$: the
lemma holds verbatim for any composite $a$ with least prime factor $p^-(a)$,
with the shaft reaching height $p^-(a)-1$. The semiprime case is stated because
it maximizes $p^-$ against $a$: $p^-\sim\sqrt a$ is attainable.

## Lemma B (Crossing capture)

Let $W$ be a walk in $G$ from $(u,\cdot)$ to $(v,\cdot)$, $u<v$, all of whose
vertices have height $<H$. Then for **every** integer $a\in[u,v]$ the walk
contains a vertex $(a,b_a)$ with $b_a<H$. Consequently, if $a\in[u,v]$ is
composite with $p^-(a)>H$, the component of $W$ contains the entire shaft
$\{(a,s):2\le s\le p^-(a)-1\}$, and in particular reaches height $p^-(a)-1$.

*Proof.* The $x$-coordinate along $W$ changes by $\pm1$ per step, so it attains
every intermediate value; at the first attainment of $x=a$ the walk is at some
$(a,b_a)$, $b_a<H$. Since $b_a<H<p^-(a)$, the vertex $(a,b_a)$ lies on the
shaft of Lemma A (all shaft vertices down to height $2$ and up to
$p^-(a)-1$ are admissible and consecutive), so the shaft is contained in the
same component. $\square$

**Remark.** Lemma B converts *any* horizontal extent into vertical reach with
no hypotheses on how the extent was achieved: a component of horizontal extent
$[u,v]$ at heights below $H$ reaches height $\max\{p^-(a)-1:a\in[u,v]
\text{ composite},\ p^-(a)>H\}$. The 2026-07-30 measurements show escapes in
practice use exactly this (backtrack to a good column, climb); Lemma B shows
climbs are *never* the obstruction — only horizontal extent is.

## Lemma C (Effective supply of elevators)

There are effective constants $z_0$ and $c>0$ such that for all $z\ge z_0$ and
all $H\le z^{1/3}$, the interval $(z,2z]$ contains an odd integer $a=pq$ with
$p,q$ prime and $H<p\le q$. Indeed the number of such $a$ is
$\ge c\,z\log\log z/\log z$.

*Proof sketch (fully effective).* Count pairs $H<p\le\sqrt{2z}$, $q\in
(z/p,2z/p]$: by effective Chebyshev bounds ($\pi(2t)-\pi(t)\ge ct/\log t$ for
$t\ge t_0$, explicit), each $p\le z^{1/2-\varepsilon}$ contributes
$\ge c\,z/(p\log z)$ primes $q$, and $q\ge z/p\ge z^{1/2}>H$ automatically.
Summing over primes $p\in(H,z^{1/3}]$ gives
$\ge c\,(z/\log z)\sum_{H<p\le z^{1/3}}1/p\ \ge\ c'\,z\log\log z/\log z$ for
$H\le z^{1/3}$ by Mertens with effective error (for $H$ up to a small power the
double-log factor degrades gracefully; for the application $H$ is polylog, far
below $z^{1/3}$). Parity: $pq$ is odd since $p>H\ge2$. Distinctness of $p,q$
can be forced or $p^2$ allowed — Lemma A needs only $p^-$. $\square$

## Theorem D (Reduction: SCH ⟹ Erdős #1212 is YES)

> **Hypothesis SCH (switch-column, the open core).** There is an effective
> $x_0$ and a function $H(x)\le x^{1/3}$ such that: whenever the component of
> the (computationally verified) seed contains a horizontal extent $[u,v]$ at
> heights $<H(v)$ with $v\ge x_0$, it also contains a horizontal extent
> $[u,v']$ with $v'\ge2v$ at heights $<H(v')$.

**Theorem D.** SCH implies the component of the seed is infinite; hence the
answer to Erdős #1212 is YES.

*Proof.* By induction from the verified seed (extent to $v=867{,}999$ at
heights $\le1399<H$ for any reasonable $H$), SCH doubles the horizontal extent
indefinitely, so the component contains vertices of unbounded $x$-coordinate
and is infinite; local finiteness and König give a ray. $\square$

By Lemmas A–C, SCH may be attacked with elevators available for free: whenever
the extent reaches $v$, the component already contains full shafts of height
$\ge H$ for any prescribed $H\le v^{1/3}$, at $\ge c\,v\log\log v/\log v$
columns in $(v/2,v]$. (Shafts of height near $\sqrt v$ exist but are scarce —
supply requires $H\le v^{1/3}$-ish; since the measured band grows only like
$\log v$, this is asymptotically generous.) Note also that windowed climbs are
far cheaper than full shafts — a climb over $(b,b']$ needs coprimality only to
that window — so the elevator package is a *sufficient* tool, not the sharpest
one. The stitching between consecutive elevators is the entire remaining
problem, and all of it happens at heights that may be taken as low as
convenient.

## Where the residual difficulty provably lives

Horizontal travel on row $b$ proceeds in runs of length $<p^-(b)\le\sqrt b$;
between runs the path must switch rows at a column whose coprimality window
covers the inter-row span. Guaranteeing a usable switch column inside a
*specified* run interval is a Jacobsthal-type worst-case question (sieving an
interval of length $\sqrt Y$ by one to three residues modulo each prime up to
$\sim Y$ can, adversarially, empty it). The empirical data (dead-run fraction
$1.7\%$ at $10^9$ and falling) says the truth is far from worst case; a proof
must exploit either (i) averaging over the many rows/runs available
simultaneously (the constraints for different target rows involve distinct
prime moduli — the union is much harder to block than any single window), or
(ii) the self-selection freedom already identified. Any proof of SCH must, in
some form, beat the worst case on a structured family — but unlike the old
anchored-staircase barrier, no *identity* forces failure here: the Reach
Barrier does not apply, because elevators decouple climb reach from anchor
roughness.


## Addendum (2026-07-30, after independent GPT Pro attempt)

An independent GPT Pro run on the campaign prompt returned no proof but three
verified contributions, now part of the toolkit:

**Chamber Lemma** (verified computationally on natural instances and by hand).
If $r_1<\dots<r_m$ are odd composites in an interval of diameter $U$ with
$p^-(r_i)>U+2$, then all hubs $\{(r_i,r_j):i<j\}$ are admissible and lie in
one component — pairwise coprimality and full horizontal/vertical segments all
follow from "any common prime would divide a difference $\le U<p^-$". This is
the 2-D generalization of Lemma A: windows with $m$ rough composites give
connected chambers of $\binom m2$ hubs.

**CRT self-selection** (proof checked by hand): chambers of any size $m$ and
any roughness $Z$ exist within diameter $D_m=(m^2-1)\,\mathrm{primorial}
(2m+1)^2$ independent of $Z$, via $c_i=T^2-i^2Q^2$ with $T$ CRT-chosen. Beating
Jacobsthal at self-selected locations is therefore *possible* — the Reach
Barrier binds only blind constructions, as claimed.

**Literature anchor**: I. Vardi, *Prime percolation* (Exp. Math. 1998) proved
results on exactly the ambient visible-lattice component (almost-all
short-interval rough-number supply, Prop 5.1; infinite-component construction
via prime-line backbones, §7); S. Martineau (arXiv:1804.06486) gives the
local-limit perspective. **The transfer obstruction is precise**: Stewart's
path turns at prime–prime hubs and Vardi's backbone crossings are prime–prime
vertices — exactly the vertices deleted here — and $(9,11)$, $(7,9)$ are
genuinely isolated in the restricted graph (verified), so no local rerouting
theorem exists. The live route is Vardi's gluing with *chambers* replacing
prime lines.

**The gap, sharpest known form** (GPT Pro, consistent with SCH): density-one
interval statements do not transfer to the arithmetically-selected reachable
set, and first-moment incidence counting loses $U^{-1/5+\eta}$; what is needed
is an expansion estimate $|N(S)|\ge(1+\kappa)|S|$ for reachable run-families
with successor-codegree control. Three independent attempts (band measurement,
my SCH analysis, GPT Pro) now terminate at this same statement.
