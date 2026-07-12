# Erdos 23 d=2s-1 One-Defect Boundary Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Classify and, where possible, close the all-nonbridge BF-RL boundary `d = 2s-1` using the exact one-unit interval deficit.

**Architecture:** Create a separate Lean module. First formalize the three-term deficit identity and its exhaustive one-defect trichotomy. Then eliminate the span-defect case using the bipartite coloring, analyze cut capacities in the mass-defect and overlap-defect geometries, and land any surviving graph construction in a sharpened articulation-resource inequality for `|M| >= 2`.

**Tech Stack:** Lean 4, Mathlib finite simple graphs, canonical off-corridor components, exact natural-number arithmetic, and the rooted cut-condition API.

---

### Task 1: Prove the one-defect identity and trichotomy

**Files:**
- Create: `ErdosProblems/Erdos23GapGBOneDefect.lean`

**Step 1:** Define the mass, span, and overlap deficits with all natural-subtraction side conditions explicit.

**Step 2:** Prove their sum is `2s-d` from `sum q_C=s`, full corridor coverage, interval containment, and the canonical span bounds.

**Step 3:** Specialize to `d=2s-1` and prove exactly one deficit equals one while the other two equal zero.

### Task 2: Classify the three geometries

**Files:**
- Modify: `ErdosProblems/Erdos23GapGBOneDefect.lean`

**Step 1:** Mass defect: prove one component has size two, all others size one, all spans are saturated, and intervals are pairwise disjoint.

**Step 2:** Span defect: prove all components are singleton, exactly one interval has size one, all others size two, and intervals are pairwise disjoint.

**Step 3:** Overlap defect: prove all components are singleton with size-two intervals and total overlap multiplicity exactly one.

**Step 4:** Use the proper Boolean coloring to eliminate the singleton size-one interval case.

### Task 3: Sharpen the d=2s-1 resource arithmetic

**Files:**
- Modify: `ErdosProblems/Erdos23GapGBOneDefect.lean`

**Step 1:** Prove that with at least two demands, positive resources, total resource at most `s-1`, and `D_i<=2r_i+2`, each `r_i<=R-1`.

**Step 2:** Derive `sum r_i^2<=R(R-1)` and the exact budget `rlBudget s (2s-1)=5s^2+2s` for `s>=5`.

**Step 3:** State the exact RFC cut interface needed to apply this arithmetic.

### Task 4: Construct capacity-two cuts in the surviving geometries

**Files:**
- Modify: `ErdosProblems/Erdos23GapGBOneDefect.lean`

**Step 1:** In the mass-defect chain, select `s-1` corridor cuts through the unique three-edge block and prove every selected cut has capacity at most two.

**Step 2:** In the overlap-defect chain, identify the unique over-covered coordinate and choose one parity class of `s-1` corridor cuts avoiding it.

**Step 3:** Prove every demand satisfies the distance comparison against the selected-cut count, using same-side parity at the endpoint losses.

### Task 5: Close or isolate the exact residual

**Files:**
- Create: `compute23/gate3/agent_d2s/one_defect_audit.md`

**Step 1:** Instantiate the sharpened resource theorem from RFC in every classified case whose cut construction is proved.

**Step 2:** Run `lake env lean ErdosProblems/Erdos23GapGBOneDefect.lean` and inspect all theorem axioms.

**Step 3:** Record either full `d=2s-1` closure or one quantified graph lemma containing only the unclosed defect case.
