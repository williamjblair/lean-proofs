# The dodge proof (rarity => SCH'): program, one new gap, one reformulation
(2026-07-30, final session notes — derived by hand, unproved except as marked)

## Reformulation SCH' (diagonal chambers — drops the height constraint)
Low-height SCH conflicts with chamber geometry: chambers built from rough
integers in a window at scale s have BOTH coordinates ~s. Fix: Theorem D
needs only unboundedness, so replace SCH by
  SCH': a chamber at scale s in the component  =>  a chamber at scale
  s' in (s, 2s] in the component,
connected by travel on chamber rows + climbs. Heights grow with s — allowed.

## GAP FOUND: compositeness is not free
Theorem 3 counts z-rough INTEGERS; the construction needs z-rough
COMPOSITES (rows must be composite: on a prime row, runs break at every
prime column ~ log v apart; verified empirically — prime rows were nearly
useless in the witness data). In short windows one CANNOT unconditionally
rule out all rough integers being prime (prime clusters; MV's 2L/log L cap
is far above the rough count). Patch — Theorem 3' (to prove, same
machinery): prime-cluster rarity via moments of a level-D Selberg MAJORANT
of the primes (a bounded-level divisor sum => Lemma 5 localizes its moments
unconditionally; mean ~ 2L/log D << rough count for D = X^{1/(10k)}).
Then "good window" = (>= 2 rough composites in length z/2) fails rarely.

## The real structure: multi-scale crossing
Rarity bounds COUNT bad windows, not their worst clustering: fixed-k
Theorem 3 cannot exclude a contiguous bad run of length up to ~X^{1/(k+1)}.
Crossing bad runs of length G needs rows of roughness > G — whose own
short-window supply fails on the NEXT scale's bad regions. The proof is
therefore a renormalization over scales: bad regions at level j are crossed
on rows of roughness_j+1, with levels' bad-region lengths shrinking
geometrically relative to available roughness, topped off by Lemma C's
global supply. Traps to avoid: (i) the recursion must terminate in O(log
log X) levels with summable failure; (ii) at each level the crossing row
must be reachable (chamber/elevator mechanics, all proved); (iii)
compositeness patch needed at every level.

## Status
All ingredients proved (Thm 3, Lemma 5, chambers, elevators, Lemma C,
hub mechanics) except: Theorem 3' (routine, same method) and the multi-
scale assembly (the genuine remaining construction). This is the last
piece of Erdős #1212.
