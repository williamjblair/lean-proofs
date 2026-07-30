# Verified minimal-counterexample lemmas for Erdős #64 (2026-07-30)

"Minimal counterexample": graph G, δ(G) ≥ 3, no cycle of length 2^k (k ≥ 2),
minimizing order, then size (lexicographic — load-bearing).

## Verdicts (adversarial re-derivation, this campaign)

- **Carr Lemma 0.1** (every proper subgraph has δ ≤ 2): VERIFIED.
- **Carr Cor 0.1(1)** (every vertex has a degree-3 neighbor): VERIFIED via
  G − v: some u has d_{G−v}(u) ≤ 2, forcing u ∼ v and d_G(u) = 3.
- **Markström / Carr Cor 0.1(2)** (degree-≥4 vertices independent): VERIFIED
  (delete an edge between two degree-≥4 vertices: same order, smaller size,
  still δ ≥ 3, no new cycles). Needs lexicographic minimality; no
  connectivity subtlety.
- **Carr Thm 0.1** (≥ 4/7 of vertices have degree 3): VERIFIED
  (4|V₄| ≤ e(V₃,V₄) ≤ 3|V₃|).
- **jul059 forum claim 2026-07-26** (> 2/3 of vertices have degree exactly 3):
  **VERIFIED as a theorem**, with gaps filled. Correct construction: when
  4|V₄| = e(V₃,V₄) = 2|V₃| (all inequalities tight: V₄ 4-regular into V₃,
  G[V₃] a perfect matching M), define H on V₄ joining u,w iff they share a
  V₃-neighbor — i.e., delete M, suppress degree-2 remnants; do NOT contract
  matched pairs (that variant breaks: triangles through M-edges create
  multiedges and lift lengths land in [2^k, (3/2)2^k]). C₄-freeness of G
  (4 = 2²) makes H simple, 4-regular, and x ↦ {u_x,w_x} injective; H is
  smaller, δ(H) = 4, so order-minimality gives a 2^k-cycle in H, which lifts
  edge-by-edge (u–x–w) to a simple 2^{k+1}-cycle in G. Contradiction. Hence
  |V₃| ≥ 2|V₄| + 1, so |V₃|/|V| > 2/3. Strictly improves Carr's 4/7.

## Draft comment for erdosproblems.com/forum (Will to post if desired)

> I checked jul059's July 26 argument and it is correct: strictly more than
> 2/3 of the vertices of a minimal counterexample have degree exactly 3. The
> inequalities 4|V4| ≤ e(V3,V4) ≤ 2|V3| follow from the two corollaries in
> Carr (arXiv:2605.22844); equality forces every V4-vertex to have degree
> exactly 4 and every V3-vertex to have exactly two V4-neighbors and one
> V3-neighbor, so V3 induces a perfect matching. One clarification on the
> contraction: define H on V4 by joining u,w whenever they share a
> V3-neighbor (equivalently, delete the matching edges and suppress the
> degree-2 remnants). Do not contract matched pairs; triangles u-x-y then
> create multiedges and lift lengths become uncontrolled. Since G has no C4,
> H is simple and 4-regular and x -> {u,w} is injective, so a 2^k-cycle in H
> (order-minimality) lifts to a 2^{k+1}-cycle in G. Hence |V3| ≥ 2|V4|+1,
> and the non-strict 2/3 bound needs no contraction at all.
