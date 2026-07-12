# Erdos 23 d=2s Equality Boundary Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Prove the exact `d = 2s` bridge-free equality boundary of the rooted Erdős 23 lemma by constructing `s-1` RFC cuts, bounding their capacity, and comparing every legal demand distance with its number of crossed cuts.

**Architecture:** Work in a new Lean module importing `Erdos23GapGBJoint`.  First expose exact consequences of singleton, disjoint, even-tiled attachment intervals: each tile is a four-cycle block and the prefix immediately before every internal even corridor vertex has exactly two boundary edges.  Then use RFC to show each such cut is crossed by at most one internal demand, and prove a block-coordinate distance bound before applying the banked articulation-cut arithmetic theorem.

**Tech Stack:** Lean 4, Mathlib finite simple graphs, exact natural-number arithmetic, the canonical off-corridor component API, and the existing Erdős 23 RL budget lemmas.

---

### Task 1: Isolate the equality-boundary theorem surface

**Files:**
- Create: `ErdosProblems/Erdos23GapGBEqualityBoundary.lean`

**Step 1:** State the graph, geodesic, bipartite, RFC, legality, and demand-family hypotheses without introducing an axiom or private theorem.

**Step 2:** Add a compile-only skeleton whose conclusion is the exact `rlBudget s (2*s)` inequality.

**Step 3:** Run `lake env lean ErdosProblems/Erdos23GapGBEqualityBoundary.lean`; expect only errors at deliberately unfinished local proof nodes.

### Task 2: Recover the chain-of-diamonds structure

**Files:**
- Modify: `ErdosProblems/Erdos23GapGBEqualityBoundary.lean`

**Step 1:** Prove that a canonical component whose finset has cardinality one has a unique off-corridor vertex.

**Step 2:** Combine the even-tile interval identity with attachment membership to prove adjacency to the two tile endpoints.

**Step 3:** Use bipartiteness to exclude adjacency to the middle corridor vertex, and component singleton/disjointness to exclude all other off-corridor edges.

**Step 4:** Compile the module and inspect all theorem axioms.

### Task 3: Construct and count the `s-1` RFC cuts

**Files:**
- Modify: `ErdosProblems/Erdos23GapGBEqualityBoundary.lean`

**Step 1:** Define the cut at internal block boundary `k` as the complement of the canonical left region immediately before corridor coordinate `2*(k+1)`.

**Step 2:** Prove the root is outside, the stub is inside, and exactly two graph edges cross the cut.

**Step 3:** Apply RFC to show the sum of demand-separation indicators at each cut is at most one.

**Step 4:** Compile and check the exact `Fin (s-1)` cardinality identity.

### Task 4: Prove the legal-demand distance comparison

**Files:**
- Modify: `ErdosProblems/Erdos23GapGBEqualityBoundary.lean`

**Step 1:** Define a block coordinate for every graph vertex from its corridor coordinate or its singleton component tile.

**Step 2:** Construct a walk from any vertex to the appropriate corridor articulation of length at most one.

**Step 3:** Concatenate those endpoint links with the corridor subwalk and prove `dist_B(u,v) <= 2 * crossedCuts(u,v) + 2`, including root/stub endpoint truncation.

**Step 4:** Check boundary cases `s=1`, first/last block, corridor articulation endpoints, and same-block endpoints.

### Task 5: Close and audit the boundary

**Files:**
- Modify: `ErdosProblems/Erdos23GapGBEqualityBoundary.lean`
- Create: `compute23/gate3/agent_d2s/equality_boundary_audit.md`

**Step 1:** Instantiate `totalCost_le_doubleSlackBudget_of_articulationCuts` with the RFC cut-separation indicators.

**Step 2:** Run `lake env lean ErdosProblems/Erdos23GapGBEqualityBoundary.lean` and verify every printed theorem uses only `[propext, Classical.choice, Quot.sound]` or a subset.

**Step 3:** Record a dependency tree and hostile boundary audit, with any unresolved step stated as one quantified lemma.

**Step 4:** Hand the kernel-checked source and audit to the parent agent for integration and repository-wide verification.
