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
