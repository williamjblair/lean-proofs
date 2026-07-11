# Prompt: the inductive step RL* for Erdős #23 (the unlock)

## Current task statement

This is the single remaining mathematical gap between the machine-
verified scaffolding and a complete proof of Erdős #23 (β(G) ≤ N²/25 for
triangle-free G). Everything below it in the dependency chain is proved
and kernel-checked; everything above it follows by an already-proved
corollary chain. Close this and #23 falls.

Setup (all definitions self-contained in
`compute23/gate3/lemma_rl_proof.md §1`, williamjblair/lean-proofs):
a **one-stub rooted instance** R = (B, M, w, x₀) is a connected bipartite
B on n vertices, internal edges M (same-side pairs, d_B ≥ 4, B ∪ M
triangle-free), root w, single stub at x₀, satisfying the rooted flip
condition RFC: ∀ T ⊆ V∖{w}, e_M(δT) + [x₀∈T] ≤ e_B(δT). Write
d = d_B(w,x₀) ≥ 1, s = n−1−d ≥ 0 (slack), Γ_int = Σ_{uv∈M}(d_B(u,v)+1)²,
p(d) the parity-minimal partner distance (p∈{1,2,3}, d+p even ≥ 4).

**TARGET (RL\*, the inductive step).** Assume Conjecture Γ holds for all
valid instances on ≤ n−1 vertices (the induction hypothesis). Prove
**Lemma RL** for every valid one-stub rooted instance on n vertices:

    Γ_int  ≤  s·(2d + 2 + s) + 2·s·p(d).

By the reductions below this is needed ONLY in the residual regime

    n ≥ 14,   2 ≤ s < (d+1)²/(2·p(d))   (hence d ≥ 3),   |M| ≥ 2,

AND, after the banked series-superadditivity theorem, only for instances
where every interior stub-geodesic edge e that is a B-bridge has
min(|A_e|, |C_e|) ≤ 3 (bridge-free segments, endpoint-near bridges, and
genuine multi-edge aggregation). Proving RL here — combined with the
proved large-slack case (Thm 7.1) and single-edge case (Thm 6.2) — gives
RL* in full, and RL* closes #23 by induction on n (base case n ≤ 13,
exhaustive).

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
  from the induction hypothesis directly (B ∪ M is a valid instance on n
  vertices, so Γ_int ≤ n² = RHS − 2sp + (d+1)² ≤ RHS). This is why the
  open regime is bounded slack s < (d+1)²/(2p).
- **Reductions/rigidity (all PROVED, §3):** s ≤ 1 forces M = ∅; trees
  satisfy RL for any |M| (Thm 3.7); crossing-free cut vertices superadd;
  crossed cut vertices reduce to rooted instances; minimal
  counterexamples have every B-leaf M-loaded.
- **Corollary chain (PROVED modulo RL, §9):** RL ⟹ the k=1 pair
  inequality (Thm 9.2: Γ₁+Γ₂+(d₁+d₂+1)² ≤ N²−2s₁s₂ via partner
  admissibility Lemma 9.1) ⟹ Γ ≤ N² ⟹ #23. So RL* is genuinely
  sufficient; you do not need to re-prove anything above it.
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
