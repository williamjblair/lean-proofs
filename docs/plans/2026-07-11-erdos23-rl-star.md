# Erdős 23 RL Star Completion Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Prove the inductive rooted lemma RL in the exact residual regime, or bank the strongest strictly larger rigorously proved sub-regime with one quantified remaining lemma.

**Architecture:** Start from the existing exact rooted-instance enumerators and build an independent hostile harness for joint multi-edge potentials.  Promote only a candidate that survives the equality families, forced-hub double broom, path-packing witness, global small-instance enumeration, and thin-corridor families.  Formalize the surviving arithmetic/composition theorem in Lean, connect it to the existing series and component-ledger modules, and run the manifest, axiom, attestation, and full-build gates.

**Tech Stack:** Lean 4.29.1, mathlib, Python 3 exact integer arithmetic, NumPy integer cut enumeration, pytest, Markdown audit reports.

---

### Task 1: Freeze the exact frontier and candidate registry

**Files:**
- Create: `compute23/gate3/gap_gb_joint_registry.md`
- Read: `compute23/gate3/lemma_rl_proof.md`
- Read: `compute23/gate3/gap_gb_series_findings.md`
- Read: `compute23/gate2/analysis.md`

**Step 1:** Record the residual hypotheses `n>=14`, `2<=s`, `2*s*p(d)<(d+1)^2`, `|M|>=2`, and the endpoint-near-bridge restriction.

**Step 2:** Register four routes before computation: RFC cut-duality, a two-edge joint excess potential, deletion/induction on bridge-free corridor segments, and endpoint-near series absorption.

**Step 3:** Record the mandatory hostile fixtures and the exact reason each killed aggregation route fails.

**Step 4:** Commit the plan and registry before implementing a candidate.

### Task 2: Build the independent joint-potential falsifier

**Files:**
- Create: `compute23/gate3/gap_gb_joint_verify.py`
- Create: `compute23/gate3/test_gap_gb_joint_verify.py`
- Reuse: `compute23/gate3/rl_lib.py`
- Reuse: `compute23/gate3/rl_enumerate.py`
- Reuse: `compute23/gate3/rl_corridor.py`

**Step 1:** Write failing tests for exact RFC checking, residual-regime classification, bridge-component sizes, per-edge distances, RL mass, and candidate joint excesses.

**Step 2:** Implement exact rooted-instance metrics without floating point or producer imports beyond the frozen graph parser and BFS helpers.

**Step 3:** Reproduce the equality-family, double-broom, path-packing, and thin-corridor boundary fixtures.

**Step 4:** Test the candidate bounds `|M|<=s`, `sum(D_i-4)<=2*s-4`, their two-edge restrictions, and capacity-corrected variants; emit the first exact counterexample for every failure.

**Step 5:** Run `PYTHONPATH=. pytest -q compute23/gate3/test_gap_gb_joint_verify.py`; require all reproduction tests to pass.

### Task 3: Prove the strongest surviving graph slice

**Files:**
- Create: `compute23/gate3/gap_gb_joint_findings.md`
- Create or modify only on success: `ErdosProblems/Erdos23GapGBJoint.lean`

**Step 1:** Convert the surviving empirical statement into a fully quantified RFC lemma with every capacity-excess term defined.

**Step 2:** Prove the graph-theoretic inequality from symmetric RFC, the component ledger, bridge restrictions, and finite-set double counting; do not assume the target RL inequality.

**Step 3:** Derive the exact quadratic RL budget for the covered slice and state the complement as one quantified lemma.

**Step 4:** If every global candidate fails, prove the strongest proper slice among all `|M|=2`, bridge-free corridor, or endpoint-near bridges, and record exact witnesses preventing a broader claim.

### Task 4: Hostile-audit the candidate independently

**Files:**
- Create: `compute23/gate3/gap_gb_joint_hostile_verify.py`
- Create: `compute23/gate3/test_gap_gb_joint_hostile_verify.py`
- Create: `compute23/gate3/gap_gb_joint_hostile_audit.md`
- Create: `ErdosProblems/Erdos23GapGBJointAudit.lean`

**Step 1:** Reconstruct every finite computation independently and freeze producer hashes.

**Step 2:** Audit the dependency tree node by node, including both equality-family ends, the forced hub, the path-packing witness, centers, bridges, and boundary slack.

**Step 3:** Re-prove every public Lean theorem under independent hostile names.

**Step 4:** Reject any theorem-strength hidden lemma, unquantified uniformity, or use of `native_decide`.

### Task 5: Integrate and verify the banked result

**Files:**
- Modify: `ErdosProblems.lean`
- Modify: `Audit.lean`
- Modify: `proofs.yaml`
- Modify: `FRONTIER.md`
- Modify: `codex/prompt_23_connected_B.md`
- Modify: `compute23/gate3/lemma_rl_proof.md`
- Modify: `attestations.json`

**Step 1:** Add only independently audited theorem surfaces to the manifest and axiom audit.

**Step 2:** Run focused pytest and Lean builds, then `./scripts/check_manifest.sh` and `./scripts/check_axioms.sh`.

**Step 3:** Regenerate attestations with `python3 scripts/emit_attestations.py`.

**Step 4:** Run `git diff --check` and the full `lake build`.

**Step 5:** Commit the verified checkpoint, explicitly distinguishing a full RL* proof from a proper partial slice.
