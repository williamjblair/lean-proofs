# Erdős 686 Row-22 Kernel Recovery Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Convert the already-audited row-22 finite local cover from a quarantined source-level certificate into an axiom-clean Lean theorem, then wire it into the live Erdős 686 residual.

**Architecture:** Recover the exact producer from the dangling Git blob left by the quarantined pass, but never reuse its compiled objects. Regenerate every local prime table from the independent exact verifier, compile the real ordinary-kernel dependency chain, and use a balanced packed bitvector tree for the 24 interval certificates. Only after terminal `#print axioms` passes may the row-22 theorem enter the aggregate imports, audit, manifest, progress ledger, and final residual exclusions.

**Tech Stack:** Lean 4.29.1, mathlib 4.29.1, Python 3 exact integers, pytest, Git object inspection, repository manifest and axiom gates.

---

### Task 1: Recover and pin the exact producer

**Files:**
- Create: `compute/campaign686/agent_k22_packed_kernel/generate_clean_cover.py`
- Modify: `compute/campaign686/agent_k22_packed_kernel_audit/hostile_audit.md`
- Test: `compute/campaign686/agent_k22_packed_kernel_audit/test_packed_kernel_hostile_verify.py`

1. Recover dangling blob `d84836e8a5f8b979cf1813dd25d63a9b54b9ce3a` and verify its SHA-256 is `7493555e4d482819a9bbbc6ea0dec7d976c6f8c6d117677b4f7538c72fed3993`.
2. Save the producer under the checked-in path, preserving `decide +kernel`, the 133 local tables, 602 shards, four mod-46 branches, 24 packed chunks, and the corrected `List.not_mem_nil, or_false` simplification.
3. Add phase flags so local tables and packed files can be generated and tested independently without producing axiom stubs.
4. Run the quarantine verifier before generation and expect `FAIL_KERNEL_QUARANTINED`.

### Task 2: Prove one clean local-table slice end to end

**Files:**
- Generate: `ErdosProblems/Erdos686EvenK22TableDefs.lean`
- Generate: `ErdosProblems/Erdos686EvenK22TableP23S0.lean`
- Generate: `ErdosProblems/Erdos686EvenK22TableP23.lean`
- Create: `compute/campaign686/agent_k22_packed_kernel_audit/LocalTableAxiomCheck.lean`

1. Generate only the definitions and prime-23 shard.
2. Run `lake env lean ErdosProblems/Erdos686EvenK22TableP23S0.lean` and expect success from the real source.
3. Import the built theorem in `LocalTableAxiomCheck.lean` and print its axioms.
4. Require the axiom set to be a subset of `[propext, Classical.choice, Quot.sound]` with no theorem-named axiom.

### Task 3: Regenerate and compile all 133 local tables

**Files:**
- Generate: `ErdosProblems/Erdos686EvenK22TableP*.lean`
- Generate: `ErdosProblems/Erdos686EvenK22Tables.lean`

1. Regenerate the 602 real table shards and 133 dispatch modules.
2. Run the independent source audit and require the historical table-mask digest.
3. Build the aggregate table module from source, never from a stub `.olean`.
4. Print axioms for representative first, middle, and last prime tables and require only permitted standard axioms.

### Task 4: Replace the stack-overflowing sequential packed evaluator

**Files:**
- Generate: `ErdosProblems/Erdos686EvenK22PackedDefs.lean`
- Generate: `ErdosProblems/Erdos686EvenK22PackedB*.lean`
- Generate: `ErdosProblems/Erdos686EvenK22PackedShards.lean`

1. Define a balanced periodic-tree evaluator with a soundness theorem from per-prime residue bits to the final bit.
2. Generate the exact 132-leaf balanced tree for each of the 24 audited chunks.
3. Prove the 24 zero-bitvector certificates with `decide +kernel` and no `native_decide`.
4. Check the exact last-survivor/kill-prime records against `EXPECTED_KILLS`.

### Task 5: Close row 22 in Lean

**Files:**
- Generate: `ErdosProblems/Erdos686EvenK22PackedCover.lean`
- Modify: `ErdosProblems/Erdos686EvenK22Core.lean`
- Modify: `ErdosProblems.lean`
- Modify: `Audit.lean`

1. Compile `even22_packed_candidate_impossible` from the 24 packed shards.
2. Compose it with `even22_large_gap_reduction` and `even22_small_gap_impossible` to prove unconditional row-22 exclusion for every `d >= 22`.
3. Print axioms for the packed theorem and the unconditional row theorem.
4. Require exactly the permitted axiom subset and no generated theorem-named axioms.

### Task 6: Reproduce, attest, and update the live frontier

**Files:**
- Modify: `proofs.yaml`
- Modify: `attestations.json`
- Modify: `PROGRESS_Erdos686.md`
- Modify: `FRONTIER.md`
- Modify: `compute/campaign686/approach_registry.md`
- Modify: `compute/campaign686/agent_k22_packed_kernel_audit/hostile_audit.md`

1. Run both independent Python verifier suites and record deterministic payload hashes.
2. Run `lake build`, `./scripts/check_manifest.sh`, and `./scripts/check_axioms.sh`.
3. Update the large-row exclusion list to include `k=22`, without weakening `LargeKSmoothHypothesis` or claiming the full problem solved.
4. Record runtime, memory, source digest, compiler versions, and the implication from verifier acceptance to the row-22 theorem.
5. Commit only after all gates pass.

### Task 7: Return to the two terminal mathematical hypotheses

**Files:**
- Modify: `docs/plans/2026-07-10-erdos686-full-solve.md`
- Modify: `PROGRESS_Erdos686.md`

1. Recompute the exact `FinalResidual686Hypothesis` after row 22 is removed.
2. Resume Target 1: derive a two-component gcd/magnitude saving for arbitrary all-owner odd-tail configurations, retaining additional owners rather than absorbing them into an unbounded loss.
3. Resume Target 2: derive a cross-row capacity bound from every divisibility `n+i | product_j(d+j-i)` in the strict live strip `k^2 < 18d`.
4. Mark the persistent goal complete only after both terminal hypotheses are discharged and the unconditional final theorem passes all Lean and repository gates.
