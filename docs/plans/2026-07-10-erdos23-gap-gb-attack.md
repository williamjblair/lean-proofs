# Erdős 23 Gap G-B Attack Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Prove one new quantified, kernel-clean lemma that genuinely narrows the multi-edge RL* middle regime, or produce an exact counterexample that kills the chosen route.

**Architecture:** Work from the rooted flip condition and a fixed stub geodesic, extracting multiplicity information from canonical level cuts without assuming the conjecture-strength two-connected core. First use an exact verifier on all available rooted fixtures and targeted `n >= 14`, `|M| >= 2` corridor instances. Then formalize only the route that survives, keeping every source, test, finding, and Lean theorem in newly created files.

**Tech Stack:** Lean 4 and mathlib; Python 3 exact integer arithmetic; repository `lake` build and axiom checks.

---

### Task 1: Freeze the exact candidate inequality

**Files:**
- Create: `compute23/gate3/gap_gb_attack_findings.md`
- Create: `compute23/gate3/gap_gb_attack_verify.py`

**Step 1: Record the target variables**

Define the corridor levels, each internal edge's level interval, the level multiplicity `m_r`, the number of extra cut edges `b_r - 1`, and the exact RL budget.

**Step 2: Implement an exact fixture decoder**

Reuse read-only helpers from `compute23/gate3/rl_lib.py`; compute every quantity with integers and recheck RFC directly.

**Step 3: State one quantified candidate**

State every quantifier and side condition explicitly, including `n >= 14`, `|M| >= 2`, `2 <= s < (d+1)^2/(2p(d))` where relevant.

### Task 2: Hostile falsification

**Files:**
- Create: `compute23/gate3/test_gap_gb_attack_verify.py`

**Step 1: Write boundary tests**

Cover `n = 14`, `s = 2`, `s = 3`, exactly two internal edges, mixed distances, shared endpoints, and the known forced-hub/path-packing witnesses when they instantiate the rooted setting.

**Step 2: Run the test before accepting the candidate**

Run: `python3 -m unittest compute23/gate3/test_gap_gb_attack_verify.py -v`

Expected: a failing witness is printed exactly, or all enumerated assertions pass.

**Step 3: Reduce any failure to a compact exact certificate**

If false, record `B`, `M`, `w`, `x0`, RFC minimum slack, distances, and both sides of the candidate inequality in `gap_gb_attack_findings.md`.

### Task 3: Prove the surviving arithmetic/combinatorial node

**Files:**
- Create: `ErdosProblems/Erdos23GapGBAttack.lean`

**Step 1: Write the theorem surface**

Use a standalone namespace and import only existing proved infrastructure. Do not edit shared imports or manifests.

**Step 2: Prove the minimal statement**

Expand every informal phrase such as "aggregate capacity" into a finite-sum or per-level inequality. Do not assume RL, Gamma, or a two-connected reduction.

**Step 3: Build the new module**

Run: `lake env lean ErdosProblems/Erdos23GapGBAttack.lean`

Expected: exit 0.

**Step 4: Inspect axioms**

Run: `lake env lean` on a temporary `#print axioms` consumer or the repository's focused axiom checker.

Expected: only `[propext, Classical.choice, Quot.sound]` where graph finiteness requires them.

### Task 4: Audit and hand off

**Files:**
- Create: `compute23/gate3/gap_gb_attack_audit.md`

**Step 1: Build a dependency tree**

Give each node a PASS/FAIL verdict and identify which nodes are mathematical, computational, or kernel checked.

**Step 2: Re-run exact verification**

Run the full new unittest file and the focused Lean build from a clean process.

**Step 3: Report the exact frontier change**

Return either the proved quantified lemma and the narrower remaining gap, or the exact counterexample and the route it kills. Do not claim RL* or Erdős #23 itself unless every dependency is closed.
