# Erdős 686 All-Owner Assembly Hostile Audit Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Independently hostile-audit the frozen `Erdos686AllOwnerAssembly` package, including every public theorem surface, every exact-arithmetic producer claim, and every named boundary case, without modifying or integrating producer artifacts.

**Architecture:** Freeze the five producer artifacts by SHA-256, treating the producer's omitted findings digest as an explicit audit item. Build a separate Lean importer that restates all 30 public theorem conclusions from producer definitions and hypotheses, plus an independent Python verifier and tests that reconstruct finite products, owner grids, lifts, casts, target bounds, and counterfixtures without importing producer verifier code.

**Tech Stack:** Lean 4.29.1, mathlib 4.29.1, Python 3 exact integer arithmetic, `pytest`, SHA-256, repository audit scripts.

---

### Task 1: Freeze and inventory the producer boundary

**Files:**
- Read: `ErdosProblems/Erdos686AllOwnerAssembly.lean`
- Read: `compute/campaign686/all_owner_assembly_verify.py`
- Read: `compute/campaign686/test_all_owner_assembly_verify.py`
- Read: `compute/campaign686/all_owner_assembly_findings.md`
- Read: `docs/plans/2026-07-10-erdos686-all-owner-assembly.md`

**Step 1:** Recompute all five SHA-256 hashes and fail if any declared digest changes.

**Step 2:** Record the findings digest `1610f635ecdf37f8c192fbd7f4866d33d6089602f1599fced1f178be3497b3d9` as auditor-frozen; flag that the producer handoff omitted it.

**Step 3:** Enumerate all public definitions, the certificate structure, the certificate constructor, and the 30 public theorem surfaces.

### Task 2: Write failing hostile exact-arithmetic tests

**Files:**
- Create: `compute/campaign686/test_all_owner_assembly_hostile_verify.py`

**Step 1:** Add hash-freeze tests for all five producer artifacts.

**Step 2:** Add independent exhaustive target-row tests for full `Icc 1 k` grids, including empty buckets equal to one, centers, endpoints, `k=5`, and `k=15`.

**Step 3:** Add exact fixtures for `d=1`, small primes `2,3,5`, composite assigned factors, loss positivity, product decomposition, residual cofactor positivity, Nat/Int casts, and second/third obstruction divisibility.

**Step 4:** Add adversarial tests showing that further owners are retained by the full grid and that the certificate does not imply the block equation or close Erdős #686.

**Step 5:** Run `python3 -m pytest compute/campaign686/test_all_owner_assembly_hostile_verify.py -q`; expect failure because the hostile verifier does not exist.

### Task 3: Implement the independent hostile verifier

**Files:**
- Create: `compute/campaign686/all_owner_assembly_hostile_verify.py`

**Step 1:** Implement independent grid, bucket, residual, cofactor, polynomial-coefficient, obstruction, and certificate evaluators using only Python integers and finite products.

**Step 2:** Reproduce the producer's target row count, bucket placements, bounds, and all exact sample computations without importing `all_owner_assembly_verify.py`.

**Step 3:** Exhaustively audit `k in {5,7,9,11,13,15}`, every owner index, empty buckets, row centers, endpoints, and the target constants `C,D`.

**Step 4:** Construct negative controls for dropped owners, nonpositive factors, violated square divisibility, false casts, zero loss, and overread closure claims.

**Step 5:** Run hostile and producer tests together; expect all tests to pass.

### Task 4: Independently re-prove every public Lean theorem

**Files:**
- Create: `ErdosProblems/Erdos686AllOwnerAssemblyHostileAudit.lean`

**Step 1:** Import only `ErdosProblems.Erdos686AllOwnerAssembly` and restate all 30 theorem statements under fresh `hostile_` names.

**Step 2:** Give independent proofs from definitions and upstream lemmas rather than invoking the corresponding producer theorem.

**Step 3:** Rebuild the `AllOwnerAssemblyCertificate` constructor conclusion and existential wrapper conclusion under fresh theorem names; inspect all positivity and cast seams.

**Step 4:** Add concrete small-prime, empty-bucket, center, endpoint, `d=1`, and target-bound examples.

**Step 5:** Add `#check` and `#print axioms` for every producer and hostile theorem surface.

**Step 6:** Run `lake env lean ErdosProblems/Erdos686AllOwnerAssemblyHostileAudit.lean`; expect PASS with only allowed axioms.

### Task 5: Write the hostile audit report

**Files:**
- Create: `compute/campaign686/all_owner_assembly_hostile_audit.md`

**Step 1:** Report PASS or FAIL per dependency-tree node and per public theorem.

**Step 2:** State the exact role of empty buckets and prove that full-grid assembly does not absorb, discard, or bound further owners.

**Step 3:** Separate kernel-banked theorems from finite Python diagnostics and state the exact remaining quantified lemma without claiming closure.

**Step 4:** Include frozen producer hashes, fresh hostile artifact hashes, exact test counts, build results, axiom gate, forbidden-token gate, and reproduction commands.

### Task 6: Run final non-mutation and audit gates

**Files:**
- Verify: all producer artifacts remain byte-identical
- Verify: shared imports, manifests, attestations, and root status docs remain untouched

**Step 1:** Run producer and hostile `pytest` suites, `py_compile`, producer Lean, hostile Lean, and focused `lake build` commands.

**Step 2:** Run axiom and forbidden-token scans; reject `native_decide`, `sorry`, `admit`, custom axioms, and unsafe declarations.

**Step 3:** Recompute the five producer SHA-256 hashes and compare them to Task 1.

**Step 4:** Run `git diff --check` and report the exact uncommitted hostile files. Do not stage, commit, or edit integration files.
