# Erdős 730 Unit-Range Block Hostile Audit Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Independently decide whether the frozen unit-range-block candidate rigorously pays the full `2<=a<=r` contribution by less than `58/125`, while isolating every paper-only or still-open dependency.

**Architecture:** Freeze the producer artifacts by SHA-256 and reconstruct the proof without importing their verifier. Build a separate exact-arithmetic implementation of aligned-block counts, translated interval covers, family normalization, the double geometric series, finite prime sum, and tail. In parallel, rebuild and inspect the four Lean theorems, then issue a scoped audit that distinguishes exact paper mathematics from what the kernel actually states.

**Tech Stack:** Lean 4.29.1 with mathlib, Python 3 standard-library exact integers and `fractions.Fraction`, pytest, POSIX shell.

---

### Task 1: Freeze the candidate and map its dependencies

**Files:**
- Read: `ErdosProblems/Erdos730UnitRangeBlock.lean`
- Read: `compute730/campaign_uniform/repair/far/unit_range_block.py`
- Read: `compute730/campaign_uniform/repair/far/test_unit_range_block.py`
- Read: `compute730/campaign_uniform/repair/far/unit_range_block_findings.md`
- Read: `docs/plans/2026-07-10-erdos730-unit-range-block.md`
- Create: `compute730/campaign_uniform/repair/far/unit_range_block_hostile_audit.md`

**Steps:**
1. Record each producer SHA-256 and all four public Lean declarations.
2. Expand the claimed payment into explicit nodes: root class, aligned blocks, normalization, maximal `r`, double sum, finite prime certificate, tail, and four branches.
3. Mark which nodes are proved in Lean, exact-checked externally, banked inputs, or open assumptions.

### Task 2: Reconstruct the exact arithmetic independently

**Files:**
- Create: `compute730/campaign_uniform/repair/far/unit_range_block_hostile_verify.py`
- Create: `compute730/campaign_uniform/repair/far/test_unit_range_block_hostile_verify.py`

**Steps:**
1. Implement the quadratic block identity, low-word alphabet count, and arbitrary translated-interval aligned-block cover using only standard-library arithmetic.
2. Verify the exact deleted-digit count `(H-1)H^(r-1)` and test both forbidden-digit orientations.
3. Re-derive `q(N-1)<=X`, `4P<=N`, and the division-free normalized inequality, including minimal and off-by-one boundary fixtures.
4. Symbolically sum `sum_(a>=2) p^-a sum_(r>=a) rho_(p,r)` and compare exact finite truncations to `(p+1)/(p(p-1)(2p+1))`.
5. Generate all 166 primes from `5` through `997`, compute the exact rational partial sum, prove the `p>1000` integer tail, and apply exactly the endpoint factor `2` and union-bound factor `4`.

### Task 3: Attack hidden assumptions and overlap

**Files:**
- Modify: `compute730/campaign_uniform/repair/far/unit_range_block_hostile_verify.py`
- Modify: `compute730/campaign_uniform/repair/far/test_unit_range_block_hostile_verify.py`

**Steps:**
1. Model actual root-class lengths for affine branch forms and verify the orientation and off-by-one content of `q(N-1)<=X`.
2. Verify that maximal `r` is unique when it exists, that the paid `r>=a>=2` range includes `a=r` and `(a,r)=(2,2)`, and that `a=1` remains excluded.
3. Test arbitrary translated intervals against the `floor(N/P)+2` envelope, including exact alignment, one-point intervals, and both-boundary intersections.
4. Check that the exact-valuation deleted output digit is one of the allowed low digits on each branch and that branch unavailability can only decrease the union bound.
5. Express the strict-band, unit-range, and short/top index sets explicitly and reject any overlap or double count.

### Task 4: Rebuild the kernel surface

**Files:**
- Create: `ErdosProblems/Erdos730UnitRangeBlockAudit.lean`

**Steps:**
1. Import the frozen source and print the assumptions of all four public theorems.
2. Check their exact signatures and require assumptions to be a subset of `[propext, Classical.choice, Quot.sound]`.
3. Run the source build and a forbidden/private declaration scan.
4. Record that digit counting, root-class construction, maximal-`r` selection, the 166-prime certificate, and the four-branch union are absent from the exported kernel surface unless an actual theorem is found.

### Task 5: Issue the scoped verdict

**Files:**
- Complete: `compute730/campaign_uniform/repair/far/unit_range_block_hostile_audit.md`

**Steps:**
1. Report frozen and audit hashes, exact counts, rational sums, boundary fixtures, and test/build results.
2. Distinguish paper/exact validity from kernel-expanded coverage.
3. State the one remaining gate: the normalized `a=1` maximal-`r` contribution plus short/top budget must fit below `263/500-delta` for some explicit `delta>0`.
4. Make no producer, shared import, manifest, attestation, or commit changes.
