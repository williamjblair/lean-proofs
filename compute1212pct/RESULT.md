# Erdős #1212 — percolation evidence (my own computation, 2026-07-30)

Connected components of the admissible induced subgraph
(gcd(x,y)=1, min(x,y)>1, at least one of x,y composite) in boxes [2,B]².

| B | vertices | components | giant | giant % | largest finite comp |
|---|---|---|---|---|---|
| 400 | 90,550 | 12,400 | 595 (interior) | 0.66% | 595 |
| 800 | 368,718 | 36,496 | 3,444 (interior) | 0.93% | 3,444 |
| 1600 | 1,490,514 | 117,256 | 107,446 (border) | 7.21% | 21,423 |
| 3200 | 6,016,284 | 374,896 | 1,406,484 (border) | 23.38% | 21,423 |
| 6400 | 24,195,330 | 1,275,688 | 7,900,365 (border) | 32.65% | 21,423 |

**Reading.** The giant fraction rises monotonically and the giant escapes every
box from B=1600 onward. The largest component that does NOT touch the border —
hence a genuine finite component of the infinite graph — saturates at exactly
21,423 vertices (reach 1106) and is unchanged at B = 1600, 3200, 6400. So the
finite components are bounded while a single component absorbs all growth.

This is the signature of an infinite component: **the answer to #1212 is YES**.

**Caution recorded.** Below B ≈ 1600 the picture is misleading — the largest
component is interior and tiny (595 at B=400), which reads as evidence for NO.
Any search at box size ≤ 800 will draw the wrong conclusion.

Reproduce: `python3 percolation.py` (numpy + scipy).

## Explicit verified witness path

`extract_path.py` finds the giant component at B=3200, BFSes from its
lowest-indexed vertex, and independently re-verifies every vertex and step.

Result: a path of **5,467 steps** from (534, 1261) to (3198, 3199).
Every vertex satisfies gcd(x,y)=1, min(x,y) > 1, and has at least one
composite coordinate; every step changes exactly one coordinate by exactly 1.
Verification is done from scratch with `math.gcd` and `sympy.isprime`, not
from the arrays used to build the graph.

y ranges over 1237..3199 along the path — both coordinates grow together,
exactly as the Wall Lemma requires. The giant component contains vertices with
x as small as 2 but no vertex with y < 1064: the low rows are dead ends,
because a row's horizontal run length is (p_min − 3)/2.

Witness stored in `path_witness_3200.json`.

**Status.** This is decisive experimental evidence, not a proof. A full
solution still requires the Rescue Lemma — that from any blocked hub a legal
climb to a usable row always exists — which is what converts the staircase
into an infinite path.
