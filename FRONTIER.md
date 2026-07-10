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

OPEN CORE:
1. `OddThueTailHypothesis` — for odd k ∈ {5..15}, no solution with
   d ≥ 10^120. Each tail extends ~1 decade per 2 CF terms; unbounded
   closure needs effective irrationality for 4^{1/k} below Liouville
   (none exists; hypergeometric method structurally fails at these k)
   or new CF structure. Watch: Calegari–Dimitrov–Tang holonomy program.
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
exact structural replay); its ledger arithmetic and theorem interfaces are
kernel-checked in `ErdosProblems/Erdos23GapGA.lean`, while the component
construction itself still awaits Lean formalization.

OPEN CORE: the multi-edge aggregation G-B / inductive RL* in the exact
region `n ≥ 14`, `2 ≤ s < (d+1)²/(2p(d))`, `|M| ≥ 2`; the 2-connected
core (conjecture-strength, quarantined); and kernel formalization of the
already-audited G-A component construction.

## Erdős #699 — common prime factor p ≥ i of C(n,i), C(n,j)

Status: OPEN ("probably very deep" — Erdős). Docs:
`PROGRESS_Erdos699.md`. Library: `lean/Erdos699/` (521 theorems).
i ≤ 2 banked; i = 3 reduced to a split/gcd obstruction with the
normalized kernel PROVEN globally nonempty (digit constraints must be
re-injected). Small-i j ~ n/2 core is anti-concentration over all
large primes — parked.

## Erdős #730 — same prime support of consecutive central binomials

Status: claimed proof AUDITED AND CAPPED (`compute730/audit.md`):
elementary skeleton sound (machine-verified), decisive analytic
content private, public bound fails the union budget (1.2 > 1).
Named missing lemma: uniform incomplete-block restricted-digit count.
Bonus banked: 1,556 certified consecutive pairs via the sound
Kummer criterion.

## Erdős #64 — cycles of length 2^k under min degree 3

Status: QUEUED (background witness search when cores free). Known
reductions recorded in task #17.

## Erdős #727

Status: inherited conditional architecture (~400 banked theorems,
`ErdosProblems/Erdos727.lean`) from a prior campaign; not yet audited
by this pipeline. TODO: map its ladder into this dashboard.
