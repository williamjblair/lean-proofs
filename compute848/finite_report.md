# Erdős #848 finite-side verification: results and scalability study

Date: 2026-07-30.  Files: `finite_verify.py` (Deliverable 1),
`finite_scale.py` (Deliverable 2), certificates `finite_cert_100000.json`,
`finite_cert_1000000.json`.  Nothing in `finite_engine.py` /
`exact_smallN.py` was modified; `finite_engine.build_universe` is used as an
independent cross-check oracle (it was itself validated against brute force).

## Deliverable 1 — exact verification of f(N) = |A7(N)|

**Statement verified.**  For every N with 1 <= N <= 10^6:

    f(N) := max{ |A| : A ⊆ [1,N], ab+1 non-squarefree for all a,b ∈ A (a=b incl.) }
          = |A7(N)| = floor((N+18)/25).

**Exceptions found: NONE** (we looked, per-N, with signed margins recorded;
the smallest margins are listed below).

### Argument, per case (each is an independently checkable certificate)

Every valid A lies in U(N) = {x <= N : x^2+1 non-squarefree}
= A7 ∪ A18 ∪ O (A7: x ≡ 7 mod 25, A18: x ≡ 18 mod 25, O: smallest witness
prime >= 13, equivalently x mod 25 ∉ {7,18}).  A7 and A18 are internally
complete (25 | ab+1, self-pairs included), so f(N) >= |A7(N)| always, via
A = A7(N).  Upper bound:

**Case 1 — cliques inside A7 ∪ A18.**  Such a clique is S7 ∪ S18 with
complete cross-compatibility.  Certificate: m18(N) *disjoint* pairs
(a_i, b_i) ∈ A7×A18, all <= N, with a_i·b_i + 1 *squarefree*.  Any clique
must miss at least one endpoint of each pair (the two endpoints are
mutually incompatible), so its size is <= (m7 + m18) − m18 = m7(N).
No König/LP duality is needed by the verifier — only "pairs disjoint, each
product+1 squarefree".  The pairs are maintained for *every* N
simultaneously: elements arrive in increasing order and each A18-arrival
is matched via an augmenting path in the incompatibility graph; the full
path log is stored in the certificate (`mixed_case.events`) and replayed
edge-by-edge (with fresh squarefree tests) by
`finite_verify.py --verify <cert>`.  Maximum-vertex-biclique in a bipartite
graph is polynomial (this is König in disguise), which is why no branch and
bound was needed for the mixed case at all.
[1e5: 4000 events, 1380 needed a nontrivial path, longest paths length 4;
saturation never failed.]

**Case 2 — cliques containing an outsider x.**  |C| <= 1 + |compat(x) ∩ U ∩
[1,N]| =: b0(x,N), where compat(x) = {a : xa+1 non-squarefree} is computed
*exactly* by sieving a ≡ −x^{−1} (mod q^2) over all primes q <= sqrt(xM+1)
(q ∈ {2,3,5} included — cross/outsider pairs can be witnessed by q=2 or 3;
q | x skipped since then q ∤ xa+1).  b0 <= m7(N) is checked for all
N ∈ [x, M] at once by evaluating at the jump points of the left side (it
jumps only at elements of compat(x)∩U; m7 is nondecreasing).  Where b0
fails, escalation:

* b1(x,N) = 1 + |compat(x)∩O∩[1,N]| + |c7(N)| + |c18(N)| − ν(N), with ν(N)
  a family of disjoint incompatible pairs *inside* compat(x), both
  endpoints <= N (same one-endpoint-lost argument, applied to the class
  part of the clique; the outsider part is bounded by cardinality).
  Greedy, monotone in N, each candidate pair inspected at most once.
* b2 (never needed): b1 with exact Hopcroft–Karp matching and the outsider
  part replaced by 1 + exact ω of the small outsider-only subgraph.
* Anything b2 cannot close would be resolved by exact search and reported
  as an exception; this never triggered.

### Results

| M | outsiders | b0 closed | b1 closed | b2 needed | worst b0 margin | worst b1 margin | exceptions | wall |
|---|---|---|---|---|---|---|---|---|
| 2·10^4 | 500 | 368 | 132 | 0 | −62 (x=15787) | 0 | 0 | 1.6 s |
| 10^5 | 2511 | 1931 | 580 | 0 | −449 (x=44179, N=99968) | 0 | 0 | ~30–60 s |
| 10^6 | 25144 | (see cert) | (see cert) | 0 | (see cert) | (see cert) | 0 | (below) |

(14 workers on the 16-core M-series machine; the 10^6 row is filled from
`finite_cert_1000000.json`.)

The b1 margin of exactly 0 occurs only at tiny prefixes (x=41 at N=43 and
x=70 at N=70, where e.g. |C| <= 1+1+1 = 3 = m7(70)); all asymptotically
relevant escalations close with margin growing linearly in N.  Structure of
the escalations: (i) *small* outsiders (x = 239, 251, 437, 577, 829, …)
have compat-density > 1/25 and fail b0 at essentially every N — b1 closes
them everywhere; (ii) *large* outsiders (x ≳ 0.2·M) fail b0 on
N ∈ [x, ~x + few·10^3] where m7(N) has not yet outgrown the compat count
below x.  Worst-case density |compat(x)∩U|/M ≈ 0.0445 > 1/25 = 0.04
(x=44179 at 1e5; same phenomenon at 1e6/1e7 samples), so b0 alone can
never suffice at any scale — the matching subtraction is essential.

### Cross-validation (independent of the engine)

* `exact_smallN.py 600` re-run: brute-force max cliques give
  f(N) = |A7(N)| for all N <= 600 (63-vertex universe).  Matches.
* Independent networkx `max_weight_clique` on the full prefix graphs at
  N = 600, 1200, 1800, 2500, 3000: ω = 24, 48, 72, 100, 120 = |A7(N)|.
  Matches.
* Universe & outsider sets cross-checked against
  `finite_engine.build_universe` (itself brute-validated) up to 20000.
* compat(x) lists for 8 random outsiders per run re-derived by pure
  trial-division squarefree tests over all of U — exact match.
* The mixed-case certificate is replayed after every run (fresh squarefree
  tests on every logged edge, saturation re-checked at every arrival).

### How to re-run / re-verify

    python finite_verify.py --M 100000 --spot     # full verification, ~1 min
    python finite_verify.py --verify finite_cert_100000.json   # replay

Implementation notes: the per-outsider sweep and the escalations run on a
fork-based multiprocessing pool (14 workers); case-1 augmenting-path BFS
uses bitmask rows with numpy set-bit extraction and a free-vertex bitmask
short-circuit (rows precomputed in parallel for M >= 3·10^5).  The b1
greedy currently constructs pairs for all of c18 rather than stopping at
the deficit; capping it at the deficit (sound, since any pair family
works) is the first optimization a C port should make — it is the measured
Θ(M²) term.

## Deliverable 2 — scalability toward N0 = 10^9–10^10

Prototypes and measurements in `finite_scale.py`
(`python finite_scale.py all --M 1000000`).

### (a) Universe construction

| op | measured (Python) | C estimate |
|---|---|---|
| sqrt(−1) mod p, sympy `sqrt_mod` | 45.5 µs/p | — |
| sqrt(−1) mod p, direct c^((p−1)/4), c QNR | 3.0 µs/p (×15 vs sympy) | ~0.1–0.3 µs (Montgomery) |
| + Hensel lift to mod p^2 | 9.9 µs/p | ~0.15 µs |
| full universe build, M=10^6 | 0.2 s | — |

Total root-sieve work is π(M)/2 modexps + ~0.052·M sieve marks; at
M = 10^10 that is ~1.1·10^8 modexps ≈ minutes single-core in C, plus a
segmented bitmap sieve.  **Universe construction is not a bottleneck at any
target M.**  Outsider density is stable: |O(M)|/M = 0.02511 / 0.02514 /
0.02514 at M = 10^5 / 10^6 / 10^7 (≈ Σ_{p≡1(4), p>=13} 2/p^2 with
inclusion–exclusion), so |O(10^9)| ≈ 2.5·10^7, |O(10^10)| ≈ 2.5·10^8.

### (b) Per-outsider compat work

*Naive sieve* (one modular inverse per prime q <= sqrt(xM)): measured
980–1400 ns per prime in Python (M = 10^6 and 10^7 agree; the cost is one
`pow(x,-1,q^2)` plus loop overhead per prime, plus negligible strided
numpy marking).  C with a Lehmer/binary-gcd inverse: ~60 ns/prime, i.e.
t_x ≈ 60 ns · π(sqrt(xM)) — at M=10^9, x~M this is ~3 s *per outsider*,
times 2.5·10^7 outsiders = dead.  Per-x naive does not scale; two remedies
were prototyped and measured:

* **Global large-q batching** (the q^2 > M regime, <=1 element per residue
  class <= M): for fixed q, get a0(x) = −x^{−1} mod q^2 for *all* outsiders
  at once by Montgomery batch inversion — 1 modpow + 3 mulmods per x
  instead of 1 modpow per (x,q).  Measured (M=10^6, |O|=25144, 40 primes
  q > 10^3): 458 ns vs 1033 ns per (q,x) — ×2.26 in Python where `pow` is
  C-native; in C the gap is the true 3·mulmod ≈ 10 ns vs inverse ≈ 60 ns,
  ×5–10.  Verified hit-identical.  This wins for scans over *all* q in a
  band, but the total π(M)·3|O| mulmod cost still explodes at 10^9 — batch
  inversion is a constant-factor tool, not the asymptotic fix.

* **Hybrid small-q sieve + large-square k-enumeration** (the asymptotic
  fix, exactness preserved).  For s > S0, x·a+1 = k·s^2 forces
  k <= (xM+1)/S0^2 =: K0 and s^2 ≡ k^{−1} (mod x); enumerate, per k <= K0
  with gcd(k,x)=1, the <= 2^{ω(x)+1} square-root classes of k^{−1} mod x
  and walk s through each class up to sqrt((xM+1)/k).  Every exact division
  gives a genuine witness (s^2 | xa+1 — s need not be prime), and every hit
  with a prime witness q > S0 is found at k = (xa+1)/q^2.  **Verified
  exactly equal to the naive compat set** on samples at M = 10^6 and 10^7.
  Measured op counts per x with S0=(xM)^{1/3}: at 10^6, ~1.1k inverses +
  ~9k sqrt_mod(x) calls + ~130 candidates vs ~70k inverses naive; at 10^7,
  ~4k + ~16k + ~170 vs ~500k — the hybrid already wins ×2–3.6 in *Python*
  at 10^7 despite sympy-sqrt_mod overhead (~30–50 µs/call); in C
  (Tonelli + CRT ≈ 2 µs, inverse ≈ 60 ns) with the balanced cutoff
  S0 ≈ (66·ln S0 · xM)^{1/3} the per-x cost is

      t_x ≈ 60ns·π(S0) + 2µs·(xM/S0²)   ≈ 13 ms (M=10^8), 57 ms (10^9), 250 ms (10^10)

  vs naive 0.35 s / 3 s / 26 s — an asymptotic (xM)^{1/6}-ish gain, ×25–100
  at the target sizes.  Requires factoring each outsider x (one segmented
  SPF sweep over [1,M], trivial) and 2-adic care in sqrt mod x.

* **The real wall: the escalation phase (b1).**  ~23% of outsiders need b1
  (this fraction is intrinsic: worst compat density 0.0445 > 0.04), and the
  summed deficit that the per-x matchings must cover is
  Σ_x deficit ≈ 9.2·10^{−6}·M² pairs (measured 91,919 at M=10^5, i.e.
  Θ(M²) total pairs), each certified pair costing ~1.6 squarefree tests of
  v ~ M² (trial division to v^{1/3} — certifying *squarefreeness*, unlike
  finding a witness, has no early exit).  This term dominates everything
  at scale (see table).

  **ν_glob shortcut (measured, promising):** the disjoint incompatible
  pairs used by b1 do not depend on x — incompatibility is a property of
  (a_i, b_i) alone.  So the *global* case-1 matching can be reused: count
  ν_glob(x,N) = #{i : a_i, b_i both ∈ compat(x), both <= N}.  Measured at
  M=10^5 over *all* 1,129,905 b0-failing jump points: ν_glob >= deficit at
  99.41% of points; 552/580 escalated outsiders are closed everywhere with
  no per-x pairs at all, and the remaining 28 need top-up matchings of at
  most 87 pairs (vs deficits up to 449) — a measured ~54× reduction in
  constructed-pair volume (conservatively 50× used in the projections).
  ν_glob is countable during the same hybrid enumeration (endpoint hash
  lookups), so its cost rides on b0.  Caveat: measured at one scale;
  needs confirmation at 10^6/10^7 before being load-bearing.  If it
  generalizes, an analytic version ("the global
  matching restricted to compat(x) has size >= deficit(x) + 1") is exactly
  the kind of local-density lemma the math track could prove once,
  eliminating the per-x escalation entirely.

### (c) Memory (bitsets over classes)

| M | U bitmap | outsider list | endpoint tables (ν_glob) | case-1 row (one) |
|---|---|---|---|---|
| 10^8 | 12.5 MB | 20 MB | 64 MB | 0.5 MB |
| 10^9 | 125 MB | 200 MB | 640 MB | 5 MB |
| 10^10 | 1.25 GB | 2 GB | 6.4 GB | 50 MB |

Rows for the case-1 matching are streamed (computed, used in the BFS,
discarded); nothing needs all-pairs storage.  All fits a 48 GB machine
even at 10^10; memory is not the constraint — arithmetic is.

### Projected wall-clock, 16 cores, C implementation

Cost model: inverse mod q² 60 ns, mulmod 3 ns, sqrt-roots mod composite x
2 µs, trial-division step 1.2 ns; measured densities/deficits as above.
(`python finite_scale.py project` regenerates this table.)

| M | universe | b0 (hybrid) | b1 direct | b1 with ν_glob | case-1 | wall (direct) | wall (ν_glob) |
|---|---|---|---|---|---|---|---|
| 10^8 | <1 core-min | 9.2 core-h | 860 core-h | 26 core-h | 5.9 core-h | **2.3 days** | **~2.6 h** |
| 10^9 | <1 core-min | 400 core-h | 3.6·10^5 core-h | 7.5·10^3 core-h | 255 core-h | 926 days | **~21 days** |
| 10^10 | ~min | 1.8·10^4 core-h | 1.5·10^8 core-h | 3.0·10^6 core-h | 1.1·10^4 core-h | ~10^3 years | ~21 years |

### Verdict

* **10^7**: reachable with the existing Python engine in hours (no new
  code); with a C extension, minutes.
* **10^8**: comfortably feasible — ~2 days on 16 cores with a direct C
  port of the exact chain; ~2 hours if ν_glob holds up.  This is the
  honest "safe" ceiling for the certified chain as it exists.
* **10^9**: infeasible direct (~2.5 core-years, dominated by certified
  squarefree tests in the escalation matchings); **feasible (~3 weeks on
  16 cores, ~5 days on 64) iff the ν_glob reduction generalizes** — that
  is the single engineering(+math) contingency to resolve next.
* **10^10**: out of reach for this bound chain in any variant (the b1
  arithmetic alone is >10^6 core-hours even after the ν_glob saving; b0
  hybrid is ~2 core-years as well).  Meeting N0 = 10^10 requires either
  the math track pushing N0 down to <= ~10^9, or a structurally different
  outsider argument (e.g. proving the escalation lemma analytically for
  all x above some fixed x0, leaving only finitely many x for computation).

Recommendation to the math track: the finite side can *certify* up to
10^8 now and 10^9 with one contingency; aim N0 <= 10^9, ideally 10^8.
A one-shot analytic lemma of the form "for every outsider x and N >= N1,
|maxbiclique(compat(x) ∩ (A7×A18))(N)| + |compat(x)∩O(N)| + 1 <= N/25"
(the quantities the engine measures; empirically true with linear margin)
would replace the entire escalation phase above N1.
