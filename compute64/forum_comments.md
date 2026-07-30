# Draft comments for erdosproblems.com/64 (for Will to post if desired)

## 1. Verification of jul059's 2/3 argument

See `lemma_verification.md` (bottom) — confirms the >2/3 degree-3 density
theorem with the construction clarified (delete matching + suppress, not
pair-contraction).

## 2. New computational result: vertex-transitive census scan

> Computational data point: I scanned the Potočnik–Spiga–Verret census of
> cubic vertex-transitive graphs (complete up to order 1280; the Zenodo
> database 6576526 contains 111,705 graphs including entries up to order
> 2048) for cycles of length 2^k, k ≥ 2. Every graph in the database
> contains one: 5,783 have a C4, 16,644 more have a C8, 89,161 more have a
> C16, and the remaining 117 (high-girth cages and truncations, girth up
> to 14) have a C32; none required length 64 or beyond. Each kill is
> certified by an explicit vertex list, re-verified independently of the
> search code. So there is no vertex-transitive cubic counterexample on
> ≤ 1280 vertices; in particular this subsumes the published Cayley-graph
> cases (generalized quaternion/dihedral/semidihedral/p³ and orders 2p²,
> 4p) for cubic connection sets in that range. The dominant pattern is
> exactly the "honeycomb" one: most census graphs have small cycle
> spectrum ≡ 2 (mod 4) (no C4, C8) but pick up a C16 from wrapped
> hexagonal patches. Certificates and code: [repo link].

## 3. General lower bound (pending n=18 completion)

> I extended the exhaustive verification for general (arbitrary degree
> sequence) graphs of minimum degree 3: every connected C4-free graph with
> δ ≥ 3 on at most N vertices contains a cycle of length 8 or 16, so a
> counterexample to #64 must have more than N vertices. Previous published
> bound: 17 vertices (Royle, cited in Markström 2004, structure-restricted
> search below 16 vertices). This search has no structural assumptions
> beyond connectivity (a minimal counterexample component is connected)
> and C4-freeness (4 = 2²). Orders 4–17: 36.5M graphs total, every one
> contains a C8. [N and final counts to be filled when n=18 completes.]
