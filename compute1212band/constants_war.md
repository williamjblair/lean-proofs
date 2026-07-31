# The constants war — campaign charter (opened 2026-07-31)

Objective: break the scale-free draw in the #1212 pursuit/staircase game by
sharpening constants until either (WIN) staircases are deterministically
impossible, or (LOSS-INFO) the draw is shown exact, proving phase input is
unavoidable. Everything here is finite, defined calculation — no new ideas
required to START, though one may be needed to FINISH.

## Ground rules (from the 11-round record; violating these wastes the front)

1. The separator is STATIC (round 10): it pays once per rail, once per
   interface. No dynamic budget/refresh charging — the "6-event budget" is a
   count of what EXISTS, not what is SPENT.
2. All resource counts balance at every scale (the criticality theorem).
   A front is only viable if it races two quantities whose CONSTANTS are not
   yet sharp on both sides.
3. First moments over configurations are heuristics, not proofs; the DP
   surrogate (ase_survival.py) is the empirical oracle for any proposed
   inequality — test there first.

## The static staircase, exact necessary conditions

A staircase for reservoir R (rails r_1 < ... < r_N, factor-disjoint) is:
events e_i (block columns: e_i ≡ 0,-1,-2 mod one of r_i's two primes),
nondecreasing-ish, with e_i, e_{i+1} in a common climb-free gap of the
interface climb set. Certified: |e_{i+1} - e_i| <= D_i (the containing gap
length); staircase x-range = Sigma drifts <= Sigma D_i.

## Front A — the range race (OPENED with a win condition identified)

* Lower bound on range: every rail needs an event in the range. With the
  WIDE reservoir (p in [Z, Z*Y^{eta/2}]), the sparsest rail has events
  spaced >= max_r p_r/6 >= Z*Y^{eta/2}/6: range >= Z*Y^{eta/2}/6.
* Upper bound on range: Sigma D_i <= C polylog * S_max * E where S_i = rail
  spacings (D_i <= C S_i^2 polylog by the quadratic climb lemma) and S_max =
  max rail spacing.

**WIN CONDITION A: if max gaps between reservoir semiprimes are
<= Y^{eta/2}/polylog, no staircase exists — ASE follows, #1212 = YES.**
Status: needs gaps between E_2-numbers (p in dyadic range, pq in interval)
of length x^{theta}, theta < eta/5, in short intervals — beyond current
unconditional results (E_2 short-interval results are ~x^{1/5}). Track the
literature (Motohashi-type, Harman's sieve for E_2); any improvement to
x^{o(1)} closes the problem. Also try: engineer the reservoir (different
p-window shapes) to weaken the needed gap bound — the exponent eta/5 is not
optimized.

## Front B — the drift race (narrow reservoir)

With p in [Z, 2Z] all rails have events every <= 2Z/3: range arguments die,
but the DRIFT accounting sharpens: K ~ E/(4 log^2 Y) steps, per-step drift
<= D_i with mean climb-free gap ~ 2 e^gamma loglog Y and certified tail
(ingredient (i)). The chain needs its ~K events compatible with total range
~ K * mean-drift; the race is between the certified Sigma D_i^2 second
moment and the event-position dispersion mod the p_i (coprime moduli).
Compute both constants exactly. Empirical oracle first: measure in the
surrogate whether chains at narrow-reservoir parameters die faster
(prediction: yes, q_i ~ 12*D/p with D now loglog-scale).

## Front C — the event-count extremes

Sharpen "<= 6 events per rail per Z-span" and ">= 3 per 2Z-span (narrow
reservoir)" to exact extremes including boundary effects, and characterize
WHICH rails can share event columns (omega_{>Z}(a(a+1)(a+2)) <= 0.6Y/log Y
rails per column — but they must have DISJOINT primes dividing three fixed
integers: sharpen using the multiplicative structure of a(a+1)(a+2):
smooth-number bounds limit how many primes in [Z, 2Z] can divide it:
<= (Y/2)/log Z each factor... compute the true max).

## Front D — the latency constant

The quadratic climb lemma's constant C in G <= C h^2 log h: optimize the
sieve level; empirically gaps look POLYLOG (max 130 at h=48 over 3e6
columns) — if provable gaps ~ h polylog hold (linear latency), Front B's
drift bound tightens by h/log-factors. The proof would need equidistribution
of the coprime-to-Delta_B set beyond FL remainders — try Montgomery-Vaughan
style L^2 on the specific modulus set (one residue per prime!) which is
exactly the reduced-residues setting where MV is sharp.

## Standing orders

- Any front reaching a proved inequality: full referee round (GPT Pro), then
  Lean-check the counting core.
- Surrogate-test every proposed bound before proving (ase_survival.py,
  ase_surrogate.py).
- Log refuted attempts here with the failure mechanism.
- The prize at every front is total: any single win closes Erdős #1212 YES
  through the certified chain (win => ASE => GWT => SGC => percolation =>
  SCH' => Theorem D).

## Front B log — opening measurement (2026-07-31)

Narrow reservoir p in [Z, 2Z], height ~1e9, columns [1e7, 1.4e7]:
  Z=1200: K=7,  q_mean=0.033, logE[#stairs]=-12
  Z=2400: K=19, q_mean=0.019, logE[#stairs]=-751
q halves as Z doubles: q ~ c*D/Z confirmed on the narrow family (predicted
q ~ 12D/p with p ~ Z). Narrow rows are sparser (K ~ E/log^2) but every rail
has guaranteed events every <= 2Z/3 — the drift race is live: the chain's
per-step drift budget D ~ loglog-scale vs per-step event spacing ~ Z/3.
NEXT (proof side): formalize the drift race as a lattice count — chain of K
congruences with coprime moduli p_i in [Z,2Z], windows of width D_i around a
drifting center; the target inequality is that the count of K-chains is zero
because total window volume prod(6 D_i / p_i) * L < 1 with the D_i drawn
from the CERTIFIED tail (ingredient (i)) — the missing step remains the
deterministic bridge from volume < 1 to nonexistence, which needs the
dispersion/equidistribution of event positions mod the NEXT prime. On the
narrow family this is a single-scale statement: multiples of p in [Z,2Z]
within distance D of multiples of p' in [Z,2Z] — a Kloosterman-sum-adjacent
bilinear count. Next session: attempt the bilinear estimate; surrogate says
the truth is strongly on our side.

## Front B — bilinear opening analysis (2026-07-31, session end)

Single-pair count is ELEMENTARY and asymptotic: for p != p' in [Z,2Z],
events e = a mod p with e mod p' in a width-(2D+1) window: the sequence
kp mod p' is a full-period AP (gcd=1), each residue hit floor/ceil(L/(pp'))
times, so count = L(2D+1)/(pp') +- 36(2D+1), asymptotic once L >= 40 Z^2 D.
No Kloosterman needed at the pair level. The K-fold chain count via CRT:
<= 1 chain per (drift, residue) pattern (moduli product Z^K >> L), patterns
exponential — so counting bounds CANNOT give nonexistence (re-confirmed;
this is ground rule 3 in sharpest form). THE DETERMINISTIC BRIDGE, final
statement: show that for the ACTUAL prime set, the <= 1 CRT solution per
pattern lands OUTSIDE [A, A+L] for every admissible pattern — equivalently,
a simultaneous-approximation/dispersion statement about the CRT lifts.
Candidate tools for next session, in order: (1) the large sieve applied to
the pattern family (the patterns' CRT solutions as a well-spaced set);
(2) Weyl/Kloosterman dispersion on the two-term truncation with the third
modulus as the test; (3) LOSS-INFO branch: prove the draw exact by
constructing, for SOME admissible pattern family, a CRT solution in range —
which would show ASE needs the full interface conditions, not congruences
alone, and would redirect the war to Front A/D permanently.

## Front B — large sieve attack: ELIMINATED (2026-07-31)

Formulation: chain base e_1 must satisfy e_1 mod p_i in Omega_i,
|Omega_i| <= 3(2 S_i + 1), S_i = cumulative drift bound. Montgomery's
arithmetic large sieve: N(L) <= (L + Q^2)/Sigma with
Sigma = sum_{q <= Q squarefree} prod_{p|q} omega/(p - omega),
per-prime saving factor ~ p_i/(6 S_i) =: W_i, W ~ log^2 Y/loglog Y.
All three regimes fail structurally:
1. L = Z (chain-range window): Q <= L^{1/2} = Z^{1/2} < p_i — NO modulus
   fits; vacuous. The moduli exceed sqrt(interval): the classical
   large-modulus wall.
2. L = Z^2: Q = Z admits single primes only: Sigma ~ K W ~ Z/loglog Y
   vs L = Z^2: short by Z*loglog.
3. L = full shaft gap Y^25: Q = Y^{12.5} admits 5-prime products:
   Sigma ~ K^5 W^5 ~ Y^{12.5 - 5 eta} polylog vs L = Y^25: short by Y^{12.5}.
CONCLUSION: the large sieve cannot exploit more than ~L^{1/2}-worth of
modulus product, while the pattern family's power is the K-fold product
Z^K. Tool (1) eliminated with mechanism (not constants — structure).
This sharpens the target for tool (2): any useful dispersion estimate must
go BEYOND square-root cancellation in the modulus aspect, i.e. exploit the
specific structure (consecutive-prime moduli, drift-nested windows) rather
than generic well-spacing. Bilinear/Kloosterman route remains; also
consider: the DUAL large sieve / Gallagher's larger sieve (which WINS when
many residues are excluded per prime — here all but ~6S/Z of residues are
excluded: exactly the larger-sieve regime!!). NEXT: Gallagher's larger
sieve: N <= (Sigma log p - log L)^{-1}(Sigma log p ...) — with omega(p)
ADMITTED residues ~ 6S_i: larger sieve bound
N(L) <= (sum log p - log L) / (sum (log p)/omega(p) - log L)
which for omega ~ 6S << p can beat L^{1/2}-barriers. COMPUTE THIS FIRST
next session — the larger sieve is precisely designed for few-admitted-
residues and has no Q <= L^{1/2} wall.

## Front B — LARGER SIEVE YIELDS (2026-07-31, continued)

Gallagher's larger sieve has no sqrt(L) wall and fits our regime exactly
(few admitted residues per prime). Two new certified-grade results:

**B1 (base-point dispersion).** Chains of total range R0 admit base points
e_1 lying in <= 3(2 R0 + 1) residues mod EACH of the K primes p_i in [Z,2Z].
Gallagher: N <= (K log Z - log L)/(K log Z/(6R0+3) - log L). With
K log Z ~ Z/(2 log Y) >> log L = 25 log Y (any L up to the full gap):
  **N(candidate bases in the ENTIRE shaft gap) <= 6 R0 + O(1).**
The chain space is pinned to polynomially-few explicit locations — the
first dispersion statement of the campaign, from pure Gallagher, no
exponential sums.

**B2 (forced range).** omega_{>Z}(a(a+1)(a+2)) <= 3 log(2x)/log Z =
0.6 Y/log Y, so ONE column blocks <= 0.6Y/log Y rails, but the chain must
cut K ~ Y^{5/2-eta}/(4 log^2 Y) rails: it needs >= K log Y/(0.6Y) distinct
event columns; combined with the certified per-window capacity
(Y^2/(120 log Y) rails per Y/30-window), the chain needs
>= 30 K·(120 log Y)/Y^2 windows, hence
  **R0 >= Y^{3/2-eta}/polylog — vertical and short staircases are
  IMPOSSIBLE; every staircase is LONG.**

Composition: candidate bases <= 6 R0, and each candidate must satisfy K
interface conditions along its explicit trajectory. The war's state after
B1+B2: the staircase lives at >= Y^{3/2-eta}/polylog range, at <= 6 R0 + 3
identifiable base locations, cutting >= Y^{3/2-eta} distinct columns, each
column serving <= 0.6Y/log Y rails. REMAINING: kill the <= 6R0+3 candidates.
Each candidate is an EXPLICIT CRT datum; killing needs per-candidate
certificates that some interface has a climb (positive statement about
specific windows — back to phase, but now at polynomially many locations
instead of exponentially many patterns: the problem has been reduced from
exponential to polynomial. A union bound over Y^{3/2} candidates now only
needs per-candidate failure probability Y^{-3/2-} — i.e., ANY power-saving
equidistribution of climb columns in the relevant windows suffices, where
before we needed super-exponential. THE BAR HAS DROPPED FROM
exp(-cK) TO Y^{-3/2}.)

NEXT: per-candidate interface analysis — does the certified quadratic-
latency machinery (or MV reduced-residue L^2, Front D) give a power-saving
bound on the density of climb-free-aligned windows at a FIXED candidate
trajectory? This is the sharpest, most winnable statement of the entire
campaign.

## Front B — self-referee of B1/B2 + new B3 (pre-round-12)

B1 CORRECTION: Gallagher denominator positivity requires
omega = 6R0+3 < K log Z/log L: B1 valid only for
R0 <= Y^{5/2-eta}/(100 log^2 Y). Refinement available: nested
Omega_i <= 3(2 min(R0, S_i)+1), S_i = sum_{j<i} D_j, improves N by log K.
B2 checked: count-form of Lemma H applies to the subfamily; omega-cap
arithmetic verified.
**B3 (long-staircase exclusion, NEW).** R0 >= Y^{5/2-eta}/(100 log^2 Y)
forces average drift >= ~4 log^2 Y; certified gap-tail (ingredient (i))
makes gaps >= 4log^2 Y superpolynomially rare (density exp(-c log^2 Y/
loglog Y)); rare-gap column measure over any polynomial range, times the
omega-cap 0.6Y/log Y events/column, cannot host K ~ Y^{5/2-eta}/(4log^2 Y)
steps. Long staircases impossible.
TRICHOTOMY: short (< Y^{3/2-eta}/polylog) dead by B2; long
(> Y^{5/2-eta}/polylog) dead by B3; middle pinned to <= 6R0+3 explicit
candidates by B1. The war is now: kill polynomially many explicit
candidates, each needing only a Y^{-3/2-} per-candidate bound.

## Front B — per-candidate endgame: the pair-moduli dispersion target

Per candidate base (B1): each rail has <= ~3-6 events in range (R0 < p_i),
so trajectories are NEARLY RIGID; each interface needs |e_i - e_{i+1}| <=
P0 ~ log^4 Y (certified quadratic latency at rail spacing ~4log^2 Y) — an
O(P0/Z) coincidence per interface among O(1) explicit pairs.
Sharpening B1 with per-step adjacency: admitted set mod p_i p_{i+1} has
size 9 R0 (2P0+1) — density gain P0/R0 per pair vs single-prime sieving —
BUT: (a) Gallagher with pair moduli gives N <= omega_pair (worse — harmonic
form can't exploit density); (b) Montgomery's large sieve now FITS
(Q = Z^2 ~ Y^5 <= L^{1/2} = Y^{12.5}) but requires per-prime PRODUCT
admitted sets, and ours is non-product (the adjacency couples the pair).
THE FINAL ESTIMATE, exact form: a large-sieve/dispersion inequality over
the K/2 pair moduli q = p_i p_{i+1} ~ Z^2 with non-product admitted sets of
density 9 R0 P0/Z^2 — i.e., a Bombieri-Friedlander-Iwaniec-style dispersion
statement. Any saving over the trivial bound by Y^{epsilon} closes ASE
(needs per-candidate Y^{-5/2-eps}; trivial is ~Y^0; the heuristic truth is
Y^{-large}). This is the sharpest and most standard-shaped final statement
of the campaign: BFI dispersion with fixed well-factored moduli — the
technology exists in the literature (BFI I-III, Zhang-style variations)
and the moduli here are FLEXIBLY FACTORABLE BY CONSTRUCTION (we choose the
reservoir), which is exactly the property that makes dispersion estimates
provable. NEXT SESSION: set up the dispersion sum explicitly and check it
against BFI Theorem shapes; engineer the p-window if needed.

## The dispersion sum — explicit setup (2026-07-31, session close)

Moduli: q_i = p_i p_{i+1} ~ Z^2 for DISJOINT pairs (i odd), so the q_i are
pairwise coprime. Admitted sets Omega_i mod q_i: |Omega_i| <= 9 R0 (2P0+1)
(non-product: adjacency couples the pair). Trivial density sigma_i =
|Omega_i|/q_i ~ 18 R0 P0/Z^2.

Two shortcuts ELIMINATED with mechanism:
(S1) Turan/variance over all n in [L]: CRT gives exact independence across
coprime q_i, but the count bound bottoms at an additive O(1) — variance
methods cannot certify < 1. (The O(1) floor, again.)
(S2) Gallagher over pair moduli: N <= omega(q) ~ 18 R0 P0 — WORSE than
single-prime B1 (harmonic form cannot see density, only cardinality).
Positivity window also loses the top log^8 slice of the middle range.

THE SUM. Let a_n := 1[n in [A, A+L] satisfies the ODD-pair conditions]
(a CRT-sparse set, |supp a| <= 6 R0 + O(1) by B1). The needed estimate:
  D := sum_{i even} sum_{omega in Omega_i}
         ( sum_{n == omega (q_i)} a_n  -  |supp a| |Omega_i|/q_i )
with target |D| <= |supp a| * (K/2) * Y^{-eps} — equivalently: the even-pair
conditions thin the odd-survivors by their density, uniformly enough that
after K/2 even tests fewer than 1 survivor remains:
  #full-chain bases <= |supp a| * prod_{i even}(sigma_i + E_i),
and ANY E_i <= Y^{-eps} * sigma-scale closes ASE.
Structure available for a bilinear treatment (the BFI checklist):
1. supp(a) is CRT-parametrized by the odd moduli — n = CRT(residue vector)
   + m * (running modulus): explicit linear parametrization.
2. The test moduli q_i are FLEXIBLY FACTORABLE (q_i = p_i * p_{i+1}, both
   factors ~ Z, and WE CHOOSE the reservoir's p-window — can impose
   p_i ~ Z^alpha, p_{i+1} ~ Z^{2-alpha} for any alpha if the dispersion
   method wants unbalanced factorizations).
3. The admitted sets Omega_i are unions of <= 9 intervals-in-progressions
   (a x b + drift window): additive structure for completing sums /
   Kloosterman.
Reduction of the target to Kloosterman-type sums: opening 1[n == omega
(q_i)] by additive characters e(h n / q_i), h < q_i, the sum over the
CRT-parametrized supp(a) factors into products of geometric sums over the
odd moduli — incomplete character sums with moduli products — the standard
completion gives Kloosterman/Ramanujan sums with moduli q_i and arguments
involving the inverses of the odd running modulus mod q_i. Weil bounds give
square-root cancellation per modulus: heuristic total saving Z^{-1/2} per
test — VASTLY more than the needed Y^{-eps}. The work: (a) the running
modulus of supp(a) exceeds L (sparse regime) — completion must be done on
the RESIDUE-VECTOR parametrization, not on n directly; (b) uniformity in
the 9-interval structure of Omega_i; (c) summing errors over K/2 tests.
This is a finite, explicitly-posed exponential-sum problem. NOTHING in the
11-round record obstructs it: it is not a counting argument (it certifies
cancellation, not cardinality), not dynamic, and phase-aware by nature —
it IS the phase input, in provable form.
