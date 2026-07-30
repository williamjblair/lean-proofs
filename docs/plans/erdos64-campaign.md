# Erdős #64 campaign (Erdős–Gyárfás conjecture)

**Statement.** Does every finite graph with minimum degree ≥ 3 contain a cycle
of length 2^k for some k ≥ 2? ([erdosproblems.com/64](https://www.erdosproblems.com/64),
OPEN, $1000, tagged FALSIFIABLE. Erdős and Gyárfás believed the answer is
negative.) Formal statement: `google-deepmind/formal-conjectures`,
`FormalConjectures/ErdosProblems/64.lean` (`Erdos64.erdos_64`, `answer(sorry)`).

Campaign started 2026-07-30. Working artifacts in `compute64/`.

## Honest framing

This is an open research problem. Liu–Montgomery (JAMS 2023, arXiv:2010.15802)
prove it for average degree above an enormous uncomputed constant d₀ via
sublinear expanders; nothing touches min degree 3. The campaign goal is
*maximal genuine progress*: extending the computational frontier, verifying
recent unvetted lemmas, and scanning unexplored graph classes. A full solution
would require either a breakthrough proof or a finite counterexample.

## Literature frontier (verified 2026-07-30)

- **Positive partial results**: K_{1,m}-free with min degree ≥ m+1 (Shauger
  1998); planar claw-free (Daniel–Shauger 2001); 3-connected cubic planar,
  with a cycle of length 2^m, m ≤ 7 (Heckman–Krakovski, EJC 2013; Exoo's
  420-vertex example shows m ≥ 5 needed); claw-free δ≥3 have a 2^k or 3·2^k
  cycle (NEHB, DMGT 2014); P₈-free (Gao–Shan 2022) → P₁₀-free (Hu–Shen 2024)
  → P₁₃-free (Hegde–Sandeep–Shashank, arXiv:2410.22842, preprint): cycle of
  length 4 or 8; diameter-2 (Carr, arXiv:2508.19302): cycle of length 4 or 8;
  Cayley graphs of generalized quaternion / dihedral / semidihedral / order-p³
  groups (Ghaffari–Mostaghim 2018) and orders 2p², 4p (Ghasemi–Varmazyar 2021).
- **Average degree**: ≥ d₀ (astronomical) suffices (Liu–Montgomery). Sudakov–
  Verstraëte: avg degree e^{O(log* n)} suffices asymptotically.
- **Minimal counterexample structure**: degree-≥4 vertices form an independent
  set (Markström 2004); every vertex has a degree-3 neighbor, ≥ 4/7 of
  vertices have degree exactly 3 (Carr, arXiv:2605.22844); claimed
  improvement to > 2/3 posted on the erdosproblems forum 2026-07-26 by
  jul059 (ChatGPT 5.6-derived, unverified — verification is WP4 below).
- **Exhaustive searches** (stale): general min-degree-3 counterexample ≥ 17
  vertices (Royle ~2003, C₄-free constrained generation < 16... reported as 17
  by Wikipedia/UCSD); cubic counterexample ≥ 30 (Markström 2004, all cubic
  graphs through order 28; counts of {C₄,C₈}-free cubic: 4/23/251 at
  24/26/28); unpublished Markström extension: every cubic graph on ≤ 52
  vertices has a 4-, 8- or 16-cycle (cited in Exoo, arXiv:1403.5636 —
  f(4) ∈ [54,78], f(5) ≤ 450); bipartite counterexample ≥ 32
  (Nowbandegani–Esfandiari ~2011).
- **Base q ≥ 3 contrast**: arbitrarily large cubic graphs with no q-power
  cycles exist (Bensmail, DMGT 2017) — base 2 is essential.
- **Never scanned before**: the Potočnik–Spiga–Verret census of all 111,360
  cubic vertex-transitive graphs on ≤ 1280 vertices (Zenodo 6576526).

## Work packages

- **WP1 — PSV census scan** (novel): witness-certified scan of all cubic VT
  graphs ≤ 1280 for power-of-2 cycles. Kills carry explicit cycle
  certificates (auditable via `verify_witnesses.py`, which uses independent
  parsing); survivor status is established by an all-roots search that does
  not assume vertex-transitivity. Any survivor = counterexample = negative
  solution of #64. Expected: full kill ⇒ new partial result subsuming the
  published Cayley-graph cases up to order 1280.
- **WP2 — general lower bound**: `geng -c -f -d3 n | checkc` for n = 17, 18,
  19, (20). Sieve covers all connected C₄-free min-degree-3 graphs — every
  counterexample has a connected induced counterexample component, so no
  minimality lemmas are needed for soundness. Each clean n raises the
  22-year-old bound of 17.
- **WP3 — cubic sieve validation**: reproduce Markström's counts 4/23/251 of
  {C₄,C₈}-free cubic graphs at orders 24/26/28 with an independent toolchain
  (geng + checkc vs his minibaum + custom checker).
- **WP4 — lemma verification**: adversarial check of Carr's lemmas and the
  jul059 2/3-density argument; draft forum comment for Will to post.
- **WP5 — mathematical attack**: proof/counterexample strategy exploration
  (covering constructions, cycle-space congruence obstructions, circulant
  spectra); honest assessment.

## Toolchain correctness

- `checkc.c` (C sieve): C₄ via common-neighbor popcount; exact-length-L cycle
  via min-vertex-rooted DFS with BFS-distance pruning. Validated against
  brute-force `networkx.simple_cycles` on 400 random graphs × L ∈ {4..10}
  and named graphs (`cyclecheck.py`), and against OEIS A002851 cubic counts
  (19/85/509/4060 at n=10/12/14/16); {C₄,C₈}-free cubic counts cross-checked
  against Markström (WP3).
- `scan_census.py`: independent sparse6 parser validated against networkx on
  census sample rows; DFS and meet-in-the-middle witness searches cross-
  validated on 35 graphs; every kill certificate re-checked at creation and
  again by `verify_witnesses.py`.

## Status

- [x] **WP1 census scan complete: no vertex-transitive cubic counterexample
  up to order 1280** (and none among the extra census rows up to order
  2048). All 111,705 graphs in the Zenodo 6576526 database killed with
  explicit witness cycles: 5,783 by C₄, 16,644 by C₈, 89,161 by C₁₆
  (the honeycomb-type mass whose small cycle lengths are ≡ 2 mod 4),
  117 by C₃₂ (high-girth cages/truncations; hardest: girth 12–14 graphs
  and truncated Foster/Biggs–Smith); none required C₆₄ or beyond. This
  subsumes all published Cayley-graph partial results (orders p³, 2p²,
  4p) for the cubic case up to order 1280. Certificates in
  `compute64/witnesses.jsonl.gz`; independent re-verification via
  `verify_witnesses.py` (networkx parsing, from-scratch checks) —
  **VERIFICATION PASSED 2026-07-30**: 111,705/111,705 valid certificates.
  4 = 2² note: scan checked every length 2^k ≥ 4 up to each graph's order.
- [x] WP5 math attack: see `compute64/math_attack_notes.md` — circulants
  proven dead (all contain C₄), truncation spectrum formula, theta-
  composition gadget calculus (no gadget ≤ 14 vertices), hexagon-tree
  infinite counterexample (all cycle lengths ≡ 2 mod 4), rigidity/
  flexibility dichotomy, and the new finite-checkable path-flexibility
  conjecture sitting between Bondy–Vince and Erdős 64.
- [x] **WP2 orders 4–18 exhausted, zero survivors → no Erdős-64
  counterexample on ≤ 18 vertices** (previous published bound: 17, Royle
  ~2003 via structure-restricted generation below order 16). Self-contained:
  no C₄-free δ≥3 graphs exist below order 10; every one of the 34,758,006
  such graphs at order 17 and all 834,711,846 at order 18 contains an
  8-cycle — the C₁₆ stage never engaged at any order ≤ 18. No structural
  assumptions beyond connectivity (a counterexample has a connected
  counterexample component) and C₄-freeness (4 = 2²). n=19 marathon
  running (56 parts, 14-way, ~29 h; `compute64/wp2/run19.sh`).
- [x] WP3 n=24: total 117,940,535 = OEIS A002851 exactly; {C₄,C₈}-free
  count = **4 = Markström's published value**; all four contain a C₁₆.
  n=26: total 2,094,480,864 = A002851 exactly; {C₄,C₈}-free = **23 =
  Markström**; zero survivors. n=22 also clean (7,319,447 = A002851,
  zero {C₄,C₈}-free). Pipeline doubly validated. n=28 COMPLETE: 40,497,138,011 cubic graphs,
  3,566,400,992 C₄-free, **251 {C₄,C₈}-free = Markström's published
  value**, zero survivors. Three independent exact order-matches
  (4/23/251 at n=24/26/28) against an independent toolchain.
- [x] WP4 verdicts: Carr arXiv:2605.22844 fully VERIFIED (Lemma 0.1,
  Cor 0.1(1),(2), Thm 0.1). jul059's 2026-07-26 forum argument (> 2/3 of
  minimal-counterexample vertices have degree exactly 3) **VERIFIED as a
  theorem** after filling gaps: in the tight case the V₃-matching must be
  deleted and degree-2 remnants suppressed (H = common-neighbor graph on V₄;
  contracting matched pairs instead is unsound — multiedges + uncontrolled
  lift lengths). C₄-freeness gives H simple 4-regular; 2^k-cycle in H lifts
  to 2^{k+1} in G. Details + draft forum comment:
  `compute64/lemma_verification.md`.
- [ ] WP5 synthesis (math-attack agent running)
