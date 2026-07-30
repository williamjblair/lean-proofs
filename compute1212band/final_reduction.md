# Erdős #1212 — the converged reduction (2026-07-30, final form)

Three independent attempts (band-extension measurement, the SCH/elevator
analysis, GPT Pro's chamber approach) and a fourth pass through the
Vardi-transfer route all terminate at the same object. This note records the
final picture, including one corrected error.

## The scale dichotomy

Let $Z$ be a roughness parameter and call an integer $Z$-rough if
$p^-(n)>Z$.

- **Average case is trivial.** The density of $Z$-rough integers is
  $\prod_{p\le Z}(1-1/p)\sim e^{-\gamma}/\log Z$, so the *average* gap between
  consecutive $Z$-rough integers is $e^{\gamma}\log Z$ — for $Z=10^5$, about
  $21$. Chambers (grids of pairwise-coprime rough anchors, GPT Pro's Lemma
  2.1) therefore exist in essentially every window on average, and all local
  navigation mechanisms have enormous margins — matching the measured
  dead-run fraction of 1.7% at $10^9$ and falling.
- **Worst case is Jacobsthal.** The maximal gap is Jacobsthal's
  $g(P(Z))$, which by Rankin's lower bound is
  $\gg Z\log Z\log\log Z/(\log\log\log Z)^2$ — for $Z=10^5$, deserts of
  length $>3.5\times10^6$ *provably exist*, against an average gap of 21
  (ratio $1.7\times10^5$).

Every navigation guarantee we can prove is capped near $Z/\mathrm{polylog}$;
every desert that provably exists has length $Z\cdot\mathrm{polylog}$. The
shortfall factor is $\sim3\nu\log^2Z$ (computed: $\approx2100$ at $Z=10^5$)
and no amount of constant-chasing closes a polylog-factor gap that appears
on both sides of the same quantity.

## A corrected error (recorded so nobody re-trips on it)

I briefly believed a counting lemma: "from a chamber with $M$ rows of
pairwise-distinct large prime factors, some row travels $\ge M/3$
unconditionally, because first-blocks of distinct primes cannot crowd."
**This is false as stated.** Blocking row $r_i$ needs a multiple of one of
*its own* primes nearby, and one integer $n$ can be divisible by up to
$\nu=\lfloor\log_Z(2X)\rfloor$ distinct huge primes, so $D$ consecutive
integers can carry first-blocks for up to $3\nu D$ rows. The correct
statement is:

> **Lemma (desert-crossing, corrected).** From a chamber with $M$ rows whose
> large prime factors are pairwise distinct, some row admits unblocked travel
> of length $\ge M/(3\nu)$, where $\nu$ is the maximal number of primes
> $>Z$ dividing a single integer at the ambient scale.

Proved by counting blocked columns: each of the $D$ integers in the stretch
blocks $\le3\nu$ rows (via divisibility by $\le\nu$ chamber primes, each
owning one row, each blocking 3 residues). With $M\lesssim Z/\log Z$ rows
attainable and $\nu\ge1$, guaranteed travel is $\lesssim Z/(3\nu\log Z)$ —
short of desert length $Z\log Z$ by exactly the polylog factor above.

## Why two dimensions do not obviously save it

The path lives in $\mathbb N^2$ and can in principle route *around* a desert
(e.g., cross a column-desert on a single row of huge least prime factor,
switching rows at climb columns). Working this through: switches between
consecutive huge-$p^-$ rows (average spacing $\sim\log P$) need a climb
column coprime to the inter-row window; the window's *large* prime factors
contribute an exclusion sum $\sim\log y/\log\ell$ that defeats the plain
union bound, and choosing among $k$ candidate next-rows reintroduces the
same joint-alignment question. The 2-D freedom changes the constants, not
the structure: at every formulation level (runs+switches, chambers+chains,
desert-crossing, band extension) the obstruction is

> **the possible adversarial alignment of the large-prime factorizations of
> consecutive integers against the arithmetically-selected positions of the
> trajectory,**

with average-case margins of $10^5$ and worst-case impossibility, and
nothing in between controlled by known unconditional results.

## What a proof needs (the sharpest statement we can defend)

One of:
1. **Rarity input**: an unconditional bound on the *number or spacing* of
   near-extremal Jacobsthal configurations (gaps $\ge Z\,\mathrm{polylog}$
   between $Z$-rough integers) in dyadic ranges — even a second moment —
   strong enough that a trajectory with $\ge Z/\mathrm{polylog}$ freedom of
   placement provably dodges them. (Literature probe running; nothing known
   to us as of today.)
2. **Expansion input**: the reachable-run expansion estimate
   $|N(S)|\ge(1+\kappa)|S|$ with successor-codegree control (GPT Pro's form
   (6.1)), proved against the conditioning of the reachable set.
3. **Transfer input**: a version of Vardi's Section-7 gluing whose backbone
   is composite-safe (chambers/elevators replace prime lines — the crossings
   of prime lines are exactly the deleted prime-prime vertices, and $(9,11)$,
   $(7,9)$ are provably isolated, so no local rerouting exists) *and* whose
   exceptional-set accounting is done against the deleted set rather than
   uniformly. Vardi's own exceptional set is far larger than the deleted set,
   so this needs new sieve input, likely equivalent to 1.

## Status

**Proved and banked**: exact hub reduction; run-length law; Wall Lemma
(+ sharp primorial form, $y\gg\log x$); Reach Barrier (blind constructions
impossible); Elevator Lemmas A–C; Theorem D (SCH $\Rightarrow$ YES); Chamber
Lemma; CRT self-selection; the corrected desert-crossing lemma; refutations
of the naive Rescue Lemma and of the $x^{2/3}$ forced-growth claim.
**Evidence**: giant component absorbing 32.7% of vertices at $B=6400$;
verified witnesses to $x=867{,}999$ (band 1399) and $2$M-vertex paths at
$10^9$–$10^{12}$; dead-run fraction $1.7\%$ and falling.
**Open**: exactly the alignment statement above. The answer is, with high
confidence, YES; the theorem awaits one genuinely new global input.


## Literature verdict (probe of 2026-07-30, late)

**Q1 (rarity of deserts).** No unconditional counting of near-Jacobsthal
deserts exists. But three partial tools do: Montgomery–Vaughan (Ann. of Math.
1986) gives per-period gap moments mod $P(z)$ with arbitrary fixed polynomial
decay — deficient in (i) uniformity in the moment order and (ii) localization
to dyadic windows (the period $e^{(1+o(1))z}$ dwarfs any window, so per-period
counts do not constrain a single block). Gorodetsky (Math. Z. 2024) localizes
the *variance* dyadically. Decisively, **Gafni–Tao (arXiv:2508.06463, which
resolved Erdős #682 in Aug 2025) is a working template**: dyadically localized
desert counting via Montgomery 1970 + Montgomery–Soundararajan 2004 moments of
sifted sets, executed at gap scale $\log X$. The open question is exactly how
far that method stretches in $T$ once the $k$-dependence of constants is
tracked. Prompt v3 targets this.

**Q2 (successors of Vardi).** Vardi's visible-lattice paper is *Deterministic
percolation* (Comm. Math. Phys. 207 (1999) 43–66), not the Gaussian-moat
paper. Only mathematical successor line: Martineau (ECP 2022) and Le
Fourn–Liu–Martineau (arXiv:2509.08452, Sept 2025) — uniqueness of the infinite
cluster and no-infinite-black-cluster for the *annealed* random coprime
colouring; nothing deterministic, nothing on restricted subgraphs. Notably,
**Herzog–Stewart's claimed unique-infinite-component theorem for the ambient
graph appears in no published proof** (their 1971 Monthly paper contains
pattern-realization results only) — even the ambient uniqueness rests on
Vardi's later work and the 2025 annealed analogue.
