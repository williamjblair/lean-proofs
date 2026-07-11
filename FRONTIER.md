# FRONTIER.md — the Erdős portfolio

One page per campaign state: what is proved (kernel-verified, axioms ⊆
`[propext, Classical.choice, Quot.sound]`, attested in
`attestations.json`), what is open (stated exactly), and what is
refuted (with witnesses — do not re-attempt). This file is the master
dashboard, the source for external proof-attempt prompts (`codex/`),
and the intended seed corpus for the Vela frontier ingest.

Verification discipline (applies to every claim entering this repo):
generation is untrusted; claims pass through (1) exact-arithmetic
reproduction, (2) adversarial audit against the falsification record,
(3) Lean formalization behind the axiom gate, (4) attestation. See
`compute730/audit.md` for the intake-audit template.

---

## Erdős #686 — N = 4 has no equal-length block-quotient representation

Status: OPEN upstream; here reduced to two exact hypotheses.
Docs: `PROGRESS_Erdos686.md`. Modules: `ErdosProblems/Erdos686*.lean`.

UNCONDITIONAL: every k ≤ 15 with gap d < 10^120 (Runge + mod-p covers
for even k; Farey-descent certificates for odd k); the k=14 case for
all d; the terminal reduction `erdos686_false_of_thue_tails_and_smooth`.

NEW BANKED RESTRICTIONS: exact p-adic square localization for every
`p^e|d`, `p≥k` (cubic at an odd center), giving
`p^(2e)<A_k d` with `A_k=14,17,23,26,29,35`; hence dominant components
are impossible.  Valuation concentration supplies the missing small-prime
case: for every prime base, a whole gap `d=p^e≥10^120` is impossible in
all six odd rows.  The exact loss is bounded by
`14! * 35 * 13^30 < 10^120`.  Reflection compression is kernel-checked.
The exact equation also has a global quadratic lift: with
`X_i=3(n+i)-d`, coefficient cancellation in
`prod(X_i+4d)=4 prod(X_i+d)` gives
`d^2 | prod_i X_i` with no prime-base or localization exception.
Global residual concentration now cleans every prime-power component,
including bases `2` and `3`, into a square divisor of one residual with an
explicit loss.  Combining two such components with second and third local
Taylor lifts closes **every** gap having exactly two distinct prime divisors
below `10^120`; no `p,q>=k` hypothesis remains.  Thus any surviving odd-tail
gap has at least three distinct prime divisors.  The same obstruction
calculus closes an arbitrary supplied pair of coprime cleaned owner buckets
under the exact all-prime loss table
`G_k=108,1620,136080,1224720,242494560,18914575680`: an exact solution
equipped with `HasAtMostTwoGlobalResidualOwners` has `d<10^120`.  This is a
strict conditional interface, but the finite prime-factor grouping step is
now kernel-banked: global concentration constructs one certified assignment,
and any two-index cover of its nonzero cleaned owner range constructs the
predicate and contradicts the cutoff.  Consequently every target-size
solution has a certified assignment whose nonzero cleaned range cannot be
covered by two indices.  The finite negative-cover argument is now
kernel-banked through an explicit witness: in that same assignment there are
three distinct prime factors with nonzero cleaned exponents, pairwise-distinct
owners, pairwise-coprime cleaned powers, factor divisibility, and square
residual divisibility.  This is an at-least-three witness, not an
exactly-three decomposition when more owners remain.  For three cleaned
residual buckets, exact second-
and third-order eliminations are kernel-banked and all
1,035 target index triples have distinct zero slopes.  The exact fourth local
lift is now banked as well: each cleaned component supplies one cubic
owner-adic obstruction, and the three cyclic obstructions compose modulo
`P^3,Q^3,R^3`.  A Hensel/CRT family with 121-digit gap satisfies the square,
moment, and all local congruences through fourth order while failing both the
equation and short window, so the exact remaining three-bucket node is
archimedean/short-CRT rather than a finite resultant.
Two additional global moment identities use `2^2=4` to make
`d^3` divide explicit constant-plus-linear coefficient combinations.  They
are cubic combinations, not cubic divisibility of either residual product.
For `k≥16`, the
ratio window gives both `n>9d` and `kd<5n`.  Maximum-valuation owner
matching across the exact lower and upper blocks compresses the whole lower
block into `(k-1)!` times the lcm of
`d-k+1,...,d+k-1`, including all small prime bases.  This forces two explicit
lcm transition inequalities but does not close large `d`, because the host
interval still has `2k-1` possible differences.  A second composition uses
the reflection center `S=2n+d+k+1`: after the parity coefficient and one
factorial loss, every residual prime power lands on lower and upper owners
`i,j` and divides `|i+j-(k+1)|`.  Non-reflected pairs land in
`lcm(1,...,k-1)`; the exact surviving alternative is the reflected alignment
`j=k+1-i`.  Aggregating the lower landing proves the distinct necessary
divisibility `S | reflectionCoeff(k)*(k-1)!*reflectionDiffLcm(k,d)`.
Every lower term is
composite, and the
published Nair-Shorey `4.42k` theorem closes the paper-level wedge
`50(d+k-1)≤221k`; only the downstream implication is in Lean because
the external theorem itself is not formalized.

ODD-TAIL ROUTE AUDIT: a complete exact `k=5` counterfamily refutes the
first two primitive-scale congruences as an unbounded closure mechanism.
The surviving floor pin `g²=floor(5A₃/A₅)` is proper but does not control
the infinite CF tail.  Imposing the discriminant square reconstructs the
original smooth genus-6 plane quintic (genus-2 sign quotient), so that
cover is target-strength rather than a lower-genus reduction.

OPEN CORE:
1. `OddThueTailHypothesis` — for odd k ∈ {5..15}, no solution with
   d ≥ 10^120. Each tail extends ~1 decade per 2 CF terms; unbounded
   closure needs effective irrationality for 4^{1/k} below Liouville
   (none exists; hypergeometric method structurally fails at these k)
   or new CF structure. Watch: Calegari–Dimitrov–Tang holonomy program.
   The one- and two-distinct-prime-support subcases are now excluded for
   every prime base.  The remaining gap has at least three distinct prime
   divisors.  For arbitrary prime support, finite factorization, owner choice,
   coprime bucket assembly, and `g<=G_k` are now banked.  The certified
   assignment of any target-size solution has three explicit distinct
   nonzero cleaned owner witnesses; the remaining task is to contradict that
   multi-owner branch.  The extraction does not absorb further owner buckets
   into the bounded loss.
   In the exactly-three-cleaned-bucket slice, the current exact
   gap is the quantified short-CRT/window lemma in
   `compute/campaign686/three_bucket_findings.md`, now including the fourth
   cyclic divisibilities from `Erdos686FourthLocalLift.lean`; four-or-more
   buckets remain unrestricted by that lemma.
2. `LargeKSmoothHypothesis` — no k ≥ 16 solution with an entirely
   (d+k)-smooth lower block (prime obstruction banked; census: two
   clusters in 145+ billion window points, neither an equation solution).

REFUTED (witnesses in repo): fixed-prefix row-16 boundary
((984, 3177026, 4480) passes rows 1..16); bare residual obstruction;
affine-saturation-only; congruence-only for (4,5); prefix a ≤ 14 and
row-prefix j ≤ 15.

## Erdős #617 — Erdős–Gyárfás balanced-coloring conjecture

Status: r ≤ 4 known (1999); r = 5 UNDER ACTIVE DECISION (live fleet).
Docs: `PROGRESS_Erdos617.md`; live logs `compute617/sat_log.md`.
Module: `ErdosProblems/Erdos617.lean` (deletion/extension framework).

PROVED: counterexample classes are (6,6)-Ramsey graphs; affine family
exactly empty; silent classes need ≥ 76 edges ⟹ two-silent case
closed; ≥ 4 classes need ≥ 59 edges; the conditional reduction
`statement_five_of_extension_demand`.

OPEN: the r = 5 verdict (in flight: SMS direct + decisive legs +
sub-cube swarm, zero SAT anywhere); then the uniform-r generalization
(extension-demand lemmas for all r) — the full-solve path.

## Erdős #23 — triangle-free bipartization ≤ N²/25

Status: OPEN; exact result claimed for N ≤ 200 (arXiv:2606.28041) —
verified here bit-for-bit except one unpublished solver-history file.
Dirs: `compute23/` (gates 1–3).

PROVED HERE: the connected-B inequality Γ ≤ N² checked on 49.7M
instances (N ≤ 13); equality cases are ALL balanced odd-cycle blow-ups
C_{2k+1}[q] (infinite two-parameter family — the true reason all
certificates self-tighten); sandwich theorem: universal Lemma RL is
conjecture-strength; RL proved on trees, s ≤ 1, and now for every
`|M|=1` instance.  The former gap G-A is closed by a symmetric
two-demand component ledger (complete paper proof, two hostile audits,
exact structural replay).  Lean now constructs and checks the bridge-cut reduction,
geodesic coordinates, canonical off-corridor components, exact `q_C/r_C`
partition sums, attachment spans, ridden-index/owner counting, and the
ordinary/exceptional local charge, including the simultaneous canonical
ride/excursion assignment and the repaired exceptional tail.  The final
kernel theorem `gapGA_symmetric_bounds` proves both SE1 and SE2.  A new
series-composition reduction closes every remaining RL* instance containing
an interior stub-geodesic bridge whose two components each have at least four
vertices: rooted cut validity composes cutwise, the exact RL budget is
superadditive, and both induced minimal composites are strictly smaller.
The hostile audit includes the `n=14`, distances `[4,4]`, and `n=17`,
distances `[4,6]`, middle-regime fixtures.

OPEN CORE: the multi-edge aggregation G-B / inductive RL* in the exact
region `n ≥ 14`, `2 ≤ s < (d+1)²/(2p(d))`, `|M| ≥ 2`, now restricted so
every interior stub-geodesic bridge leaves a component of order at most
three.  This is weaker than a 2-connected reduction; the bridge-free core
remains conjecture-strength and quarantined.

## Erdős #699 — common prime factor p ≥ i of C(n,i), C(n,j)

Status: OPEN ("probably very deep" — Erdős). Docs:
`PROGRESS_Erdos699.md`. Library: `lean/Erdos699/` (521 theorems).
i ≤ 2 banked; i = 3 reduced to a split/gcd obstruction with the
normalized kernel PROVEN globally nonempty (digit constraints must be
re-injected). Small-i j ~ n/2 core is anti-concentration over all
large primes — parked.

## Erdős #730 — same prime support of consecutive central binomials

Status: claimed proof AUDITED; its decisive uniform incomplete-block
lemma is FALSE as quantified.  On the Q branch, `a=2r` makes the map
affine modulo `p^(2r)`, and translated intervals contain exponentially
more restricted outputs than the claimed density, even after retaining
the exact valuation.  A stronger progression construction fixes the low
`s=max(2r-a,0)` output digits first and extends the obstruction through
`s/r<kappa_p/(1-kappa_p)`.  Its exact `p=5,r=432,s=176` witness lies in the
former separated range and refutes the proposed signed Fourier inequality
itself by a factor above `1.164`.  This does not refute Erdős #730.  The
maximal-r valuation payment has therefore been enlarged uniformly to the
full strict high-valuation band `s<r`; it remains paper-proved and
exact-audited below `0.01` for every `X>=2^57`.  The band forces
`r+1<=a`, so Lean checks the clean threshold `X<2B^2(p^a)^2`, dyadic step
certificates, and the exact endpoint payment `0.0048569067...`.  The infinite reciprocal-tail
aggregation and real root/floor monotonic transfer remain outside the kernel;
the corrected aligned-block argument now pays the full higher-power part
`2<=a<=r` of the complementary range by less than `174/625`, across all four
branches.  The sharper `6/5` endpoint normalization, exact quadratic block
identity, and terminal budget arithmetic are kernel-banked; the digit count,
166-prime rational certificate, tail, and branch aggregation remain
paper/exact rather than kernel-expanded.  The only unpaid exponent slice is
maximal-`r` `a=1`; together with an explicitly defined short/top contribution
it must total at most `1779/2500-delta`.  The intake must also prove the common
event-multiplicity coverage bridge before summing those categories.  Exact
sparse Gauss completion is
audited, but its triangle majorant is exponentially insufficient for
`p=5,7,11`; a new signed estimate with a payable error is required.  Bonus
banked: 1,556 certified consecutive
pairs via the sound Kummer criterion.

## Erdős #64 — cycles of length 2^k under min degree 3

Status: QUEUED (background witness search when cores free). Known
reductions recorded in task #17.

## Erdős #727

Status: inherited conditional architecture (~400 banked theorems,
`ErdosProblems/Erdos727.lean`) from a prior campaign; not yet audited
by this pipeline. TODO: map its ladder into this dashboard.
