# Erdős #617 (r=5, n=26) — search log

Ground truth: `core.py` (`is_counterexample`). Objective used everywhere:
`obj = Σ_{6-sets S} #(colors missing among S's 15 edges)` — equals
`core.violations` (Σ_c #independent-6-sets of class c). `obj = 0` ⟺ counterexample.

## W2 — stochastic local search (`sls.c`)

Engine: C, exact incremental objective. State = 325 colors. Move = pick random
violated 6-set S + missing color b; recolor one of S's 15 edges to b
(best-of-`sample_k` violated sets, delta-evaluated exactly over the 10,626
6-sets containing the edge; tabu on undoing recent recolors with tenure
`10 + nviol/64 + rand(10)`; aspiration on new global best; `noise` prob of a
random repair edge instead of best). Reload global best + 2–5 random-edge
perturbation after `reload_after` stagnant moves or drift > best+`drift`.
Consistency self-check (full recount) every 20M moves. Scoring cross-checked
exactly against `core.violations` on random colorings (3/3 match, plus probes).

Throughput ~2.7k moves/s per chain (each move ≈ up to 60 exact delta evals).

History of engine iterations (all logged, failures included):
- v1 Metropolis SA (T0 0.35–0.8): froze — single-edge deltas here are
  O(50–500), acceptance collapsed (624 accepts / 23M proposals). Discarded.
- v2 WalkSAT best-of-15-in-one-set: drift far above best (2428 vs 908).
- v3 (current) TabuCol-style best-of-4-sets + reload: robust.

Seeds: `0` uniform random; `1` random {6,5,5,5,5} clique-partitions/color
(structurally doomed per coordinator's K6-free lemma — kept only as probe);
`2` AG(2,5)-based valid K_25 (color 0 = rows∪cols rook graph, colors 1–4 =
slope parallel classes) + random 26th vertex; `3` random circulant
(difference classes on Z_26).

### Results (probes 150 s + production 4×4 h chains)

| seed | start obj | best obj reached |
|------|-----------|------------------|
| AG25 | ~4,100 | 813 |
| random | ~43,000 | 808–815 |
| circulant | ~45,000 | 783 |
| clique-partition | ~25,000 | (frozen engine v1; dropped) |

Universal plateau at **obj ≈ 780–815** from every seed family, reached in
~2 min, then no improvement for hours of aggregate chain time. Production
chains: `runs/p{1..4}.log`, best colorings in `runs/p*_*.best.txt`.

### Plateau autopsy (the key structural finding)

For the plateau solutions analyzed: **every violated (S,c) contains one fixed
pair of vertices** {u,v} (e.g. {2,23} in `pC.best.txt`, 814/814 violated sets).
Contracting v into u yields a **valid K_25 coloring** (0 bad 6-sets, verified
exhaustively). So the local search always terminates at:
  valid K_25 coloring + one vertex split into "near-twins", with the split
  pair uncoverable.
Class structure of one harvested K_25: sizes (60,51,62,62,65) — NOT the AG
structure (100,50,50,50,50); the valid-K_25 space is richer than the affine
family.

## W3 — completion / extension SAT (exact, CaDiCaL 1.9.5 via pysat)

`w3_completion.py`: freeze best coloring outside a freed vertex set F, free
all edges touching F, exact SAT on the rest.
On `pC.best.txt` (obj 814, bad pair {2,23}):

| freed vertices | free edges | result | time |
|---|---|---|---|
| {2,23} | 49 | UNSAT | 0.0 s |
| {2,23,16,17} | 94 | UNSAT | 0.2 s |
| +{12,15} (6) | 135 | UNSAT | 1.8 s |
| +{21,19} (8) | 172 (53% of all edges) | UNSAT | 38.7 s |

I.e. the fixed 18-vertex interior already forbids ANY completion of the other
8 vertices.

`w3_extend.py`: a valid K_26 coloring restricted to any 25 vertices is a valid
K_25 coloring, so K_26 SAT ⟺ some valid K_25 coloring is 1-vertex-extendable.
Extension test per K_25 coloring = 125-var SAT. Results: AG construction →
UNSAT 0.00 s; harvested SLS K_25 → UNSAT 0.00 s.

`w3_certificate.py`: counting certificate. For attach vertex w, per color c,
H_c = N_c(w) must (i) hit every independent 5-set of class c, (ii) contain no
5-clique of class c (else mono-K_6); the H_c partition the 25 vertices. With
h_c = min admissible |H|: Σ_c h_c > 25 ⟹ non-extendable.

| K_25 coloring | class h_c values | Σ h_c |
|---|---|---|
| AG(2,5) rook+4 classes | 8,25,25,25,25 | 108 |
| SLS-harvested (60,51,62,62,65) | 8,8,8,8,8 | 40 |

Both ≫ 25. Conjecture worth proving (would settle UNSAT): h_c ≥ 6 for every
class of every valid K_25 coloring (then Σ ≥ 30 > 25).

## W1 — full SAT with symmetry breaking (`w1_encode.py`, `w1_solve.py`)

Encoding (n parameterized): one-hot 5×NE vars; pairwise EO per edge; coverage
clause per (6-set, color); complete color-symmetry lex-leader
(first-occurrence prefix chain); vertex lex-leader for 25 adjacent
transpositions; per-class cardinality 55 ≤ |G_c| ≤ 105 (Turán / counting,
seqcounter). n=26: 194,175 vars, 1,554,525 clauses (`runs/w1_full.cnf`).

Pipeline validation on n=25 (known SAT via AG): with vertex lex-leader,
CaDiCaL made no visible progress in ~40 min (lex-leader forces the lex-min
representative — hard); killed, relaunched without vertex lex
(`runs/w1_n25_nolex.log`) to validate the sat-side of the pipeline.

## Session 2026-07-10 ~11:20 — babysit + classification route

### Solver harvest
- **W1 n=25 nolex pipeline validation: SAT in 358 s** (CaDiCaL, 0 bad 6-sets
  on independent recheck) — the W1 encoder is validated on the SAT side.
  (The first launch died with the old session; relaunched, done.)
- **r=3 general K_10: UNSAT in 222.5 s** (Kissat404, `small_r3.log`) —
  calibration anchor vs the known theorem PASSES.
- r=4 general K_17: first run died with old session; relaunched (running).
- E7 general (fixing_sat identity, Kissat404): still running (~1 h in).
  Second opinion `general_cadical.py` (Cadical300) died with the old session;
  relaunched (running). 2^13 / 2^12-1-1 orbit-fixing: still running.
- W1 full n=26 (CaDiCaL): still running. m* edge-bound run (min edges of a
  (6,6)-Ramsey graph on 26 vts; >65 would prove UNSAT by counting): still
  running — NOTE its stdout is block-buffered into a session task file,
  output appears only at flush/exit.
- SLS p3/p4: still running to their 4 h walls, plateau 808/781, no change.
- **anneal617 ×12 KILLED** (~50 min in): best 808 = SLS plateau, strictly
  dominated by sls.c, was oversubscribing the 16-core box. Trajectories in
  `anneal_*.err`.

### CORRECTION to the W3 certificate table
The earlier AG row "h = 8,25,25,25,25" is wrong (pre-fix code). Current
`w3_certificate.py` (with the unrestricted-feasibility check): AG slope
classes are 5 disjoint K_5s, any H hitting all line-transversals must
contain a full line = forbidden 5-clique ⇒ **h_c = ∞**. AG true vector:
(8, ∞, ∞, ∞, ∞).

### Classification route (new)
- **Harvest complete**: 77 valid K_25s from sls25 (w1/w2 workers,
  `runs25/harvest.tsv`). Every one: h_c ∈ {8, ∞} per class, Σ ≥ 40,
  extension UNSAT.
- **Isomorphism classification** (`classify25.py`, invariant fingerprint +
  exact colored-iso backtracking): the 79 known valid K_25s (77 harvested +
  probe + AG) are **pairwise non-isomorphic** — 79 iso classes. The valid
  space is enormous; enumeration up to iso is hopeless. Classification
  pivots to proving the counting lemma instead.
- **Translation-invariant family COMPLETELY classified** (`trans_enum.py`):
  Z_5^2-invariant valid K_25 colorings = 16,200 raw SAT solutions =
  **exactly 2 classes** up to GL(2,5) × color perms:
  rep#0 = AG (sizes 50,50,50,50,100; h = ∞,∞,∞,∞,8);
  rep#1 = **NEW**, sizes (50,50,50,75,75), h = (∞,8,∞,∞,8). Both ext-UNSAT.
- **Local-move structure** (`freedom25.py`): edge e recolorable keeping
  validity ⟺ every 6-set ∋ e has ≥2 edges of e's color. Every sampled
  non-AG valid K_25 has **exactly 50 free edges** (= 300 − 5·50 Turán
  excess); AG has 100 (its whole rook class). The valid space is NOT rigid:
  every point has 200–400 single-edge neighbours.
- **Random walks in the valid space** (`walk25.py`, >1100 accepted moves per
  chain): h stays (8,8,8,8,8) almost everywhere, **but 25 steps from AG a
  class with h_c = 5 appears** (h = 5,8,8,8,8, Σ = 37, ext still UNSAT).
  ⇒ the clean sub-lemma "h_c ≥ 6 always" is **FALSE**. The viable lemma is
  Σ_c h_c > 25 itself. Empirical min Σ so far: **37** (budget 25).
- **Target-lemma SAT** (`lemma_h6_sat.py`): single instance asking
  "∃ valid K_25 with class-0 h ≤ B" (995,275 clauses; encoder property-
  tested: flips SAT/UNSAT exactly at the independently computed h = 8 on a
  harvested coloring). B=5 launched — given the walk's h=5 find it should
  return SAT with a witness; kept running for confirmation.
- **Σh descent** (`hclimb25.py`, 3 chains): hill-climb on Σ h_c over the
  valid space via free-edge moves; any Σ ≤ 25 triggers immediate extension
  SAT + core verification. Running; all chains floor at exactly 37 =
  5 + 4·8, corroborating the one-cheap-class picture below.
- **Cheap-class anatomy** (h=5 witness `runs25/hclimb_ag.best.txt`): the
  h=5 class is the degraded rook class — 94 edges, only 270 ind-5-sets,
  H = one grid line {0,5,10,15,20} (no longer a 5-clique after the walk
  removed line edges). Cheap ⟹ BIG: sizes (94,52,51,51,52). Edge budget
  (300 total, 50 floor/class) then forbids ≥2 cheap classes if cheap ⟹
  ≥76 edges (2·76 + 3·50 = 302 > 300).
- **Decomposed lemma instances** (`lemma_variants.py`, all launched under
  Kissat404, ~1–1.4M clauses each):
  - LEMMA-A `edges 75`: valid K_25 + class-0 h ≤ 5 + |E_0| ≤ 75.
    UNSAT ⟹ at most one cheap (h≤5) class per valid K_25.
  - LEMMA-B `floor 1`: valid K_25 + class-0 h ≤ 1. UNSAT ⟹ h_c ≥ 2 always.
  - LEMMA-SUM `sum`: five per-class admissible H_c with Σ|H_c| ≤ 25
    (no disjointness — pure counting relaxation of E7).
    UNSAT ⟹ Σ h_c > 25 for every valid K_25 ⟹ **r=5 n=26 settled UNSAT**.
  Proof routes to the theorem: LEMMA-SUM alone, or (LEMMA-A ∧ LEMMA-B:
  Σ ≥ 2 + 4·6 = 26 > 25), or E7 directly. Three independent jugulars now
  in flight.
- E3 (5^5·1 cycling, hardest symmetric family) had died with its session —
  relaunched.
- **Certification prep**: exact E7 instance dumped to `runs/e7_general.cnf`
  (1625 vars, 1,154,726 clauses, DIMACS). pysat's Kissat404 exposes no
  proof logging — the DRAT rerun on an UNSAT verdict needs a standalone
  kissat (`brew install kissat` or build), then
  `kissat --no-binary runs/e7_general.cnf runs/e7_general.drat`.

## Status / read

- No witness. All claimed results verified against `core.py` where applicable.
- Read: **strongly leaning UNSAT.** Every seed family funnels to the same
  "valid K_25 + irreducible split pair" plateau at obj ≈ 800; exact SAT
  completion around the defect (up to 53% of edges freed) is UNSAT in seconds;
  every valid K_25 examined (79 pairwise non-isomorphic + the 2-member
  complete translation-invariant classification + >2200 walk steps) is
  non-extendable, Σ h_c ≥ 37 ≫ 25.
- Calibration anchors now in place: r=3 general UNSAT (known theorem
  reproduced), n=25 SAT (pipeline finds the affine solution's space).
- Open jugular: E7 general UNSAT run; then rerun with DRAT proof logging
  for the certification artifact.
