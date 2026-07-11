# Erdős 730 First-Power and Short-Top Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Attack the remaining `a=1` corrected range and short/top contribution inside the exact post-payment budget.

**Architecture:** Run two independent routes.  Route A studies aligned `p^r` block counts relative to their exact mean, falsifies overstrong constants, and isolates the weakest surviving uniform discrepancy lemma.  Route B treats the shortest `r=1` blocks and top boundary directly, testing the logarithmically inflated main term and retaining the existing explicit top congruence classes.  In parallel, sharpen the already proved `a>=2` endpoint factor so the genuine remaining budget is not artificially small.

**Tech Stack:** Exact Python integers and `Fraction`, bounded NumPy scans, pytest, Lean 4 algebra.

---

### Task 1: Sharpen the higher-power endpoint factor

**Files:**
- Create: `compute730/campaign_uniform/repair/far/first_power_routes.py`
- Create: `compute730/campaign_uniform/repair/far/test_first_power_routes.py`

**Step 1:** Certify `log(5)>8/5` with the existing rational atanh bounds.

**Step 2:** Replace the factor `2` in the root-class endpoint inequality by `6/5` for `r>=2`.

**Step 3:** Recompute the exact four-branch `a>=2` payment and remaining budget.

### Task 2: Aligned-block discrepancy attack

**Files:**
- Modify only the new files from Task 1.

**Step 1:** Test the candidate `max block <=2*mean` on exact corrected maps.

**Step 2:** Preserve the first exact counterexample if false and scan the weaker `8/3` constant on the feasible grid.

**Step 3:** State the surviving discrepancy lemma with exact constants; do not count a finite scan as proof.

### Task 3: Shortest-block and top-boundary attack

**Files:**
- Modify only the new files from Task 1.
- Create: `ErdosProblems/Erdos730FirstPowerRoutes.lean`

**Step 1:** Scan every admissible `r=a=1` Q/S case through prime 1000 against both the uninflated and rigorously lower certified inflated main term.

**Step 2:** Bank an exact uninflated-main counterexample and the finite no-counterexample boundary for the inflated target.

**Step 3:** Kernel-prove the improved endpoint cross inequality and exact remaining-budget arithmetic.

### Task 4: Honest residual

**Files:**
- Create: `compute730/campaign_uniform/repair/far/first_power_routes_findings.md`

**Step 1:** Separate proved arithmetic, exact finite falsification, and conjectural discrepancy bounds.

**Step 2:** State the one remaining quantified `a=1` plus short/top lemma with its revised budget.

**Step 3:** Run all related tests and axiom checks; do not edit shared campaign integration files.
