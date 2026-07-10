# Prompt: the connected-case inequality for Erdős #23

## Current task statement

Let G be a finite triangle-free graph on N vertices, χ a maximum cut,
M the set of monochromatic (same-side) edges, B the bipartite graph of
cut edges, and for uv ∈ M let d_B(u, v) be the B-distance (even, ≥ 4,
by maximality and triangle-freeness). Define
Γ = Σ_{uv ∈ M} (d_B(u, v) + 1)².

TARGET (inductive form RL*, sufficient for the program): assuming the
inequality Γ ≤ N² holds for all connected instances on fewer than n
vertices, prove it for connected instances on n vertices — OR prove
outright the localized gap G-A below, which completes the |M| = 1 case
unconditionally.

GAP G-A (fully self-contained; see compute23/gate3/lemma_rl_proof.md
in willblair0708/lean-proofs): in a valid rooted one-stub instance
where the M-endpoint lies OFF the stub corridor, prove the single-edge
laws SE1 (D ≤ 2s) and SE2 (2D ≤ 2s + d). The on-corridor cases are
proved; the obstruction is one double-count in a ledger argument
(E ≤ q + 2r); all definitions and the verified data are in the cited
file.

## Verified context

- Γ ≤ N² has ZERO counterexamples over all 49.7 million max cuts of
  all connected triangle-free graphs with N ≤ 13.
- "B connected" is equivalent to "G connected" (proved).
- EQUALITY CASES (proved, exhaustive N ≤ 13 + exact construction):
  precisely the balanced odd-cycle blow-ups C_{2k+1}[q] — an infinite
  two-parameter family. Any proof must be exactly tight on all of it:
  both the long-thin end (odd cycles) and the short-fat end (C₅[q]).
- Proved reductions: crossing-free cut vertices superadd; crossed cut
  vertices reduce exactly to rooted instances; minimal counterexamples
  have every B-leaf M-loaded; RL holds on trees, for s ≤ 1 (which
  forces M = ∅), and for |M| = 1 on-corridor via SE1 ∧ SE2; the
  large-slack regime 2s·p(d) ≥ (d+1)² holds under the inductive
  hypothesis. Corollary chain proved modulo RL: no minimal
  counterexample has a singly-crossed cut vertex.
- The sandwich theorem (proved): universal (non-inductive) Lemma RL is
  equivalent to Γ up to O(N) — do NOT attempt it directly; work with
  RL* or G-A.

## Falsification record — dead certificate families (exact witnesses
in compute23/gate2/)

Self-tight or false, killed by exact search: path-packing L¹ (n = 12
witness with Σ(d+1) > e); local-load L² (n = 8 double-broom, forced
hub load 10 > 8); Hölder product (n = 9: 84 > 81); fixed-split and
Minkowski per-block potentials (15 obstruction pairs); effective-
resistance substitution (strictly insufficient at C₅[2]); convex path
functionals other than x² (pinned by the two ends of the equality
family). Every kill happens at mixed-even-distance / forced-hub
configurations. Flag-algebra escalation is out of scope (order-10 is
self-tight at the equality family; order-11 infeasible).

## Orchestration

Diverse portfolio: Gale–Hoffman/flow dualities of the rooted flip
condition (the equality-at-paths case identifies the tight dual);
block superadditivity with boundary-corrected potentials (the naive
ones are dead — the surviving "true pair inequality" is verified on
all 2,463 signature pairs to n_B ≤ 9); discharging/charging schemes
that vanish on odd-cycle blow-ups by construction; stability arguments
around the equality family. Adversarial audit: every candidate lemma
must be checked against the equality family (both ends), the n = 8
double-broom, and the n = 12 path-packing witness. Return a complete
proof of RL* or G-A; else the strongest proved statement plus its
exact remaining gap as one quantified lemma. At least 4 hours before
any return. Public search for standard background only.
