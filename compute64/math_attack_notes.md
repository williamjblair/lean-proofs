# Erdős #64 — mathematical attack notes (2026-07-30)

Session findings from the structural/constructive attack (agent-derived,
key proofs re-checked; computational claims backed by scripts in the
session scratchpad `eg64/`). Complements `lemma_verification.md`.

## Proven this session

**Circulants are dead.** Every circulant graph of degree ≥ 3 contains a
4-cycle, hence is never an Erdős–Gyárfás counterexample. Proof: with two
distinct jump classes {±a}, {±b}: 0, a, a+b, b is a C4 (jumps a, b, −a, −b;
vertices distinct since a,b ≠ 0, a ≠ b, a+b ≠ 0). The only degree-≥3
circulants with one full jump class are cubic C_{2m}(±a, m); there
0, a, a+m, m is a C4. ∎ (Checked by hand; elementary.)

**Truncation spectrum formula** (machine-verified on K4, Petersen). For
cubic G, the truncation T(G) (vertices → triangles) has cycle spectrum
{3} ∪ ⋃_{ℓ∈spec(G)} [2ℓ, 3ℓ] (every integer in the intervals): a cycle
visits each triangle at most once, gaining +1 or +2 per visit,
independently. Consequence: T(G) avoids powers of 2 iff spec(G) lies in
windows {5}, {9,10}, {17..21}, {33..42}, ... — and no cubic graph on ≤ 16
vertices has spectrum inside the windows; iterated truncation always dies
(intervals of multiplicative width ≥ 3/2 accumulate to width 2, which
always contains a power of 2).

**Theta-composition calculus** (machine-verified at n=29). For a two-pole
network H (poles s,t of degree 2, interior δ≥3, path-length set P, cycle
set C), gluing three copies at the poles gives a δ≥3 graph with spectrum
exactly C ∪ (P+P). A "gadget" with (P+P) ∪ C avoiding powers of 2 would
instantly disprove Erdős 64. Exhaustive search: no such gadget exists
through n = 14 (general) and n = 19 (bipartite).

**Congruence obstructions.** Bondy–Vince (two cycle lengths differing by
≤ 2) forbids one-residue-class spectra mod m ≥ 3; all-odd spectra are
impossible (theta ⟹ even cycle). Only two-class unions like {1,2} or
{2,3} mod 4 survive the obstruction — and empirically zero graphs with
such spectra exist among all 98k C4-free δ≥3 graphs, n ≤ 15.

**Infinite counterexample located.** The "hexagon tree" (hexagons fused
along alternating edges, dual an infinite cubic tree) is an infinite cubic
graph whose every cycle has length 4f + 2 ≡ 2 (mod 4) — no power-of-2
cycles, every edge on a cycle. The entire difficulty of the negative
direction is compactification: closing the structure introduces dual
cycles whose realizable boundary lengths fill even intervals [2c, 4c] of
multiplicative width 2, which always contain a power of 2.

**Cages closed out.** All 18 (3,9)-cages (n=58), the (3,10)-cages (n=70)
and the (3,11) record graph (n=112) contain C16 — girth alone cannot carry
a counterexample through the n < 64 window (girth ≥ 9 cubic needs n ≥ 58).

## The organizing observation

Rigidity/flexibility dichotomy: every length-transporting device in a
δ≥3 environment offers ≥ 2 local options (+1/+2 per triangle, 2/4 per
hexagon patch, path detours); accumulated options fill an integer interval
of multiplicative width 2, which always contains a power of 2. A
counterexample requires length-rigidity, and rigidity is empirically
incompatible with min degree 3 (100% of 12,230 two-pole networks at
n=11..13 have longest s–t path ≥ 2× shortest; zero mod-4-rigid pole pairs
among all C4-free δ≥3 graphs n ≤ 13).

**Path-flexibility conjecture (new, finite-checkable).** In any graph
where all vertices except two poles s,t have degree ≥ 3, there are s–t
paths of lengths p < q with q ≥ 2p and the path spectrum meets every gap
of size ≤ 2 in between (hence P+P contains a power of 2). If true, the
composition route to a counterexample is dead; if false, its counterexample
seeds an Erdős-64 counterexample via the theta-composition. Sits strictly
between Bondy–Vince and Erdős 64.

## Flagged for verification (not yet cross-checked against literature)

- Bondy–Vince exact hypothesis (min degree 3 vs all-but-two vertices).
- Chen–Saito 1994: cycle ≡ 0 mod 3 in δ≥3 graphs (recalled from memory).
- Whether girth-9 cubic graphs on 60/62 vertices are enumerated anywhere;
  whether irregular δ≥3 girth-9 graphs on 46–57 vertices exist (Moore
  bound 46) — the only remaining girth-based candidates under 64 vertices.
