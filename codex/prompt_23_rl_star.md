# Prompt: the inductive step RL* for Erdős #23 (the unlock)

## Current task statement

This is the remaining one-stub inductive gap in the machine-verified
scaffolding for Erdős #23 (β(G) ≤ N²/25 for triangle-free G). Closing it is
necessary progress, but it is not by itself a full proof of #23: the current
paper chain eliminates a cut vertex crossed by exactly one monochromatic
edge, while the multi-stub case and the final connected/2-connected core
remain separate quantified obligations. Do not infer those obligations from
RL* without proving them.

Setup (all definitions self-contained in
`compute23/gate3/lemma_rl_proof.md §1`, williamjblair/lean-proofs):
a **one-stub rooted instance** R = (B, M, w, x₀) is a connected bipartite
B on n vertices, internal edges M (same-side pairs, d_B ≥ 4, B ∪ M
triangle-free), root w, single stub at x₀, satisfying the rooted flip
condition RFC: ∀ T ⊆ V∖{w}, e_M(δT) + [x₀∈T] ≤ e_B(δT). Write
d = d_B(w,x₀) ≥ 1, s = n−1−d ≥ 0 (slack), Γ_int = Σ_{uv∈M}(d_B(u,v)+1)²,
p(d) the parity-minimal partner distance (p∈{1,2,3}, d+p even ≥ 4).

**TARGET (RL\*, the inductive step).** Assume Conjecture Γ holds for all
valid instances on ≤ n vertices (equivalently, index the outer induction by
the larger minimal-composite order `n+p(d)`). Prove
**Lemma RL** for every valid one-stub rooted instance on n vertices:

    Γ_int  ≤  s·(2d + 2 + s) + 2·s·p(d).

By the reductions below this is needed ONLY in the residual regime

    n ≥ 14,   2 ≤ s < (d+1)²/(2·p(d))   (hence d ≥ 3),   |M| ≥ 2,

AND, after the banked complete corridor-bridge elimination and the first two
boundary theorems, only for instances admitting a root-stub geodesic all of
whose edges are B-nonbridges and satisfying

    5 ≤ s,   d ≤ 2s−2.

The case `d=2s` is now kernel-closed by
`Erdos23GapGBEqualityBoundary.totalCost_le_rlBudget_of_doubleSlack_allNonbridge_sameSide`.
The next row `d=2s−1` is kernel-closed by
`Erdos23GapGBOneDefectAlignment.totalCost_le_rlBudget_of_oneDefect_allNonbridge_sameSide`:
the exact mass/span/overlap trichotomy eliminates the span case and turns
both surviving cases into a one-high binary BFS chain with literal demand
alignment. Proving RL in the remaining residual — combined with the proved large-slack and
single-edge cases — gives the one-stub RL* statement in full. It does not
silently discharge the separate multi-stub or connected-core obligations.

A complete solution proves RL in this regime with every constant
explicit and no unproved aggregation asserted. A proof of a strictly
larger sub-regime than the banked series slice (e.g. all |M| = 2, or the
bridge-free case, or a new joint bound valid on all of RFC) is
substantial partial progress and should be reported as such — but a
reduction to a lemma of RL-equivalent strength is NOT progress.

## Verified context you may rely on (kernel-checked; statements in
`compute23/gate3/lemma_rl_proof.md`, branch `codex-ga-preserved` /
main of williamjblair/lean-proofs)

- **G-A is CLOSED** (Erdos23GapGA*.lean, audited in gap_ga_audit.md):
  the single-edge laws SE1 (D ≤ 2s) and SE2 (2D ≤ 2s+d) hold for any
  two geodesics under the two-demand cut condition; hence RL for |M| = 1
  is a theorem (Thm 6.2). You may use SE1/SE2 for each M-edge
  individually; the gap is purely their AGGREGATION for |M| ≥ 2.
- **Series superadditivity is banked** (gap_gb_series): if an interior
  stub-geodesic edge is a B-bridge splitting into components each with
  ≥ 4 vertices, RFC composes cutwise, Γ_int and s split exactly, and the
  RL budget is superadditive — so such instances reduce to smaller ones.
  The residual therefore excludes those bridges.
- **Large-slack is PROVED** (Thm 7.1): if 2s·p(d) ≥ (d+1)², RL follows
  from the induction hypothesis through order n directly (B ∪ M is a valid instance on n
  vertices, so Γ_int ≤ n² = RHS − 2sp + (d+1)² ≤ RHS). This is why the
  open regime is bounded slack s < (d+1)²/(2p).
- **Reductions/rigidity (all PROVED, §3):** s ≤ 1 forces M = ∅; trees
  satisfy RL for any |M| (Thm 3.7); crossing-free cut vertices superadd;
  crossed cut vertices reduce to rooted instances; minimal
  counterexamples have every B-leaf M-loaded.
- **One-stub corollary (PROVED modulo RL, §9):** RL implies the k=1 pair
  inequality (Thm 9.2: Γ₁+Γ₂+(d₁+d₂+1)² ≤ N²−2s₁s₂ via partner
  admissibility Lemma 9.1), excluding a cut vertex crossed by exactly one
  M-edge in a minimal counterexample. Section 11 explicitly leaves the
  multi-stub pair inequality open; the connected/2-connected case is not a
  consequence of §9 alone.
- **Equality boundary (PROVED):** on a fully nonbridge corridor with
  `d=2s` and `s≥5`, canonical singleton tiles give `s-1` capacity-two cuts;
  RFC, block projection, and bipartite parity prove the exact RL budget in
  `Erdos23GapGBEqualityBoundary.lean`. The live BF-RL boundary is strict.
- **One-defect boundary (PROVED):** on a fully nonbridge corridor with
  `d=2s−1` and `s≥5`, canonical intervals have exactly one mass, span, or
  overlap defect. Bipartiteness kills span; Lean derives the complete
  one-high BFS geometry, exact level alignment for every legal same-side
  demand, and the RL budget in `Erdos23GapGBOneDefectAlignment.lean`.
- **Two-demand distance-four slice (PROVED):** in the strict BF residual,
  if `|M|=2` and either internal distance is four, RFC supplies SE2 for the
  other distance and exact residue-sensitive arithmetic proves RL. Kernel:
  `Erdos23GapGBTwoDemand.totalCost_le_rlBudget_of_twoDemands_existsDistanceFour`.
- **Two-demand weighted slices (PROVED):** if `|M|=2` and `2d<s`, RFC
  supplies both rooted SE2 and the internal-pair weighted bound
  `Dmin+2Dmax<=2(s+d)`; exact convex arithmetic proves RL without the false
  joint-distance sum.  For positive even `d`, the same argument closes
  `2d<=s` and the next three rows `2d-3<=s<=2d`. Kernels:
  `totalCost_le_rlBudget_of_twoDemands_twoLength_lt_slack` and
  `totalCost_le_rlBudget_of_twoDemands_even_near_twiceLength` in
  `Erdos23GapGBTwoDemandWeighted`.
- **Sandwich theorem (PROVED, Thm 2.7):** the UNCONDITIONAL (non-
  inductive) universal RL is conjecture-strength — do NOT attempt it.
  The whole point of RL* is that under the induction hypothesis the hard
  large-s regime is free and the frontier collapses to bounded slack.
- **Equality family (proved, exhaustive N ≤ 13 + construction):**
  RL/Γ is tight exactly on balanced odd-cycle blow-ups C_{2k+1}[q]; any
  proof must be exactly tight on both ends (long-thin odd cycles and
  short-fat C₅[q]). The tight families have d = 1 and live OUTSIDE the
  residual regime — the residual excludes the self-tight configurations.
- **Thin-corridor rigidity data (machine-checked):** in the open regime
  the extremal interior is a SINGLE edge with D = 2s, never two: max
  Γ_int at s = 2 is 25 (flat, 4 ≤ d ≤ 13); at s = 3 it is 50 at d = 3,
  then 25 at d = 4,5 and 49 for 6 ≤ d ≤ 11. Exploit this — the binding
  constraint concentrates mass on one edge.

## Falsification record — dead aggregation families (exact witnesses in
`compute23/gate2/`; do NOT re-derive)

- **Volume aggregation** Σ_M D_uv + d ≤ e(B): FALSE in general graphs —
  gate 2's L¹ kill (n = 12 witness) violates the unrooted form; only the
  tree case survives.
- **Per-vertex load:** killed by C3's forced-hub configuration (hub load
  10 > 8 at n = 8) — no vertex-load aggregation can hold.
- **Naive per-edge SE1/SE2 + summation:** wrong direction —
  (Σ(D_i+1))² ≥ Σ(D_i+1)², giving only Γ ≤ |M|(2s+1)², far above RHS for
  |M| ≥ 2 at small d.
- **Two-demand joint sum:** `D₁+D₂ ≤ n+p(d)−2` is FALSE even in the live
  strict all-nonbridge residual.  The exact `n=76,d=11,s=64,p=1` RFC
  fixture has `(D₁,D₂)=(38,38)`, hence `76>75`; its RL cost is nevertheless
  only `3042≤5760`.  The cutwise gadget proof and exact checker are in
  `compute23/gate3/agent_weighted_dual/joint_distance_counterexample_audit.md`.
  Do not rephrase this linear conclusion as a missing lemma.
- **Known LEAD (not a claim):** a JOINT bound of the form
  Σ_i (D_i − 4) ≤ 2s − 4 + (capacity excess) matches ALL current data
  (verified on the equality family, the n = 8 double-broom, the n = 12
  path-packing witness, and all thin-corridor families) but has NOT been
  derived from RFC. Deriving it from the flip condition — or finding the
  correct joint potential that is exactly tight on C_{2k+1}[q] and the
  single-edge D = 2s extremal — is the most promising open route. Any
  candidate joint bound MUST be checked against: both ends of the
  equality family, the n = 8 double-broom (forced-hub), and the n = 12
  path-packing witness, before it is claimed.
- Flag-algebra escalation is OUT OF SCOPE (order-10 is self-tight on the
  equality family; order-11 infeasible).

## Orchestration

Diverse portfolio, register every route before investing:
Gale–Hoffman/flow duality of RFC (the equality-at-paths case identifies
the tight dual); a joint potential Σ_i φ(D_i) exactly tight on both
extremal families (x² alone is pinned by the two ends — find the
cross-term); discharging/charging that vanishes on odd-cycle blow-ups by
construction; stability around the equality family; extending the banked
series-superadditivity past the min(|A|,|C|) ≤ 3 bridge restriction to
bridge-free segments. Adversarial audit (the `compute730/audit.md`
template): every candidate lemma checked against BOTH ends of the
equality family, the n = 8 double-broom, and the n = 12 path-packing
witness; every "essentially/matches-data" phrase converted to a proved
inequality from RFC. Return a complete proof of RL in the residual
regime, or the strongest rigorously proved sub-regime with its exact
remaining gap as one quantified lemma. Do not converge early. At least
4 hours before any return. Public search for standard background only —
not to determine the status of Erdős #23.

## Intake (non-negotiable, mirrors codex/GOAL.md)

Any returned proof enters as an UNVERIFIED CLAIM and passes: (1)
adversarial audit against this falsification record; (2) exact-arithmetic
reproduction of every computational claim; (3) Lean formalization behind
the kernel axiom gate [propext, Classical.choice, Quot.sound], no
native_decide; (4) attestation. A proof that cannot survive step 1 in
principle (asserted aggregation, unquantified uniformity, circular
RL-strength) should not be returned.
