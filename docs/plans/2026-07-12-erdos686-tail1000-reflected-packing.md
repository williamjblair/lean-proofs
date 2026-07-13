# Erdős 686 Tail-1000 Reflected Packing Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Close, behind the Lean kernel, every exactly-three cleaned-bucket slice whose owners are the center and a reflected pair in the odd target rows `5, 7, 9, 11, 13, 15`, under the already-banked `d >= 10^1000` odd-tail cutoff.

**Architecture:** Extend the existing center/reflected determinant module rather than introduce a parallel theory.  First certify that all 27 reflected pairs lie below the upgraded cutoff.  Then prove one equation-facing wrapper: from the block equation, a supplied exact center/reflected residual decomposition, and the cleaned-gap factorization, derive the center cubic bound, the two endpoint third-obstruction divisibilities, determinant nonvanishing and size, and finally the packing contradiction.  Keep the result explicitly scoped to this exactly-three slice; arbitrary owner configurations remain open.

**Tech Stack:** Lean 4 / Mathlib, exact Python integers, pytest, repository manifest and axiom gates.

---

### Task 1: Freeze the exact tail-1000 cutoff table

**Files:**
- Modify: `compute/campaign686/reflected_three_bucket_verify.py` or the existing reflected-packing verifier selected after inspection
- Modify/Create: the matching focused pytest file

**Step 1: Add failing coverage for all 27 reflected pairs**

Enumerate `k in {5,7,9,11,13,15}` and `1 <= r < (k+1)/2`.  Reconstruct the center, determinant, and aggregate-loss constants independently and assert

```text
H(k)^2 * K(k,r)^3 * G(k)^12 < 10^200 < 10^1000.
```

Record per-row maxima and assert the exact counts: 27 total, 12 old, 15 newly closed.

**Step 2: Reproduce the exact arithmetic**

Run the focused verifier and pytest suite with bytecode and cache disabled.  Do not use floating point or logarithms to establish any inequality.

### Task 2: Add the ordinary-kernel cutoff certificate

**Files:**
- Modify: `ErdosProblems/Erdos686ReflectedThreeBucketDeterminant.lean`

**Step 1: Prove the all-pair numerical certificate**

Add `target_reflected_packing_cutoff_certificate_tail1000` for every target row and every reflected distance.  Prove the stronger intermediate `< 10^200` by finite `norm_num`, then transport it to `< 10^1000` monotonically.

**Step 2: Add the tail-1000 packing corollary**

Specialize `no_reflected_three_bucket_of_packing_bounds` to the target constants, `targetAggregateLoss k`, and `10^1000`.

**Step 3: Compile and inspect axioms**

Run the module directly and require every new public theorem to report only `[propext, Classical.choice, Quot.sound]`.

### Task 3: Assemble the equation-facing center/reflected contradiction

**Files:**
- Modify: `ErdosProblems/Erdos686ReflectedThreeBucketDeterminant.lean`

**Step 1: Freeze the supplied decomposition interface**

The theorem takes the exact block equation, target-row and reflected-position hypotheses, `10^1000 <= d`, positive `g,P,Q,R`, the cleaned factorization `d = g*P*Q*R`, ownership divisibilities at the center and endpoints, and exact residual identities

```text
X       = a*P^2,
X - 3r  = b*Q^2,
X + 3r  = c*R^2.
```

It may take the standard grouped-loss hypothesis `g <= targetAggregateLoss k`, but it must not take the center cubic bound, endpoint product bound, determinant nonvanishing, or determinant size as assumptions.

**Step 2: Derive the center cubic bound from the equation**

Instantiate `center_raw_cube_lt_factorial_sq_mul` at the center owner and the row-specific base/residual ceiling already available from the exact ratio window.  Normalize its coefficient to `targetReflectedCenterCubeBound k`.

**Step 3: Derive both endpoint third divisibilities**

Apply `third_order_local_lift` at each endpoint and compose with the exact three-bucket residual differences through `three_bucket_third_obstruction_dvd_sq`.  Normalize the two results to `reflectedLeftThird` and `reflectedRightThird` using the reflected coefficient identities.

**Step 4: Build and bound the determinant**

Use `reflected_three_bucket_product_identity` for the cofactor product, `target_reflected_third_inner_ne_zero` for nonvanishing, `reflected_third_determinant_dvd_endpoint_squares` for endpoint-square divisibility, and `reflected_third_inner_abs_lt` plus the exact determinant identity for the size bound.  Make every cast and positivity condition explicit.

**Step 5: Invoke the packing contradiction**

Combine the derived center and endpoint bounds with the tail-1000 cutoff certificate.  The resulting headline theorem must conclude `False` from the equation-facing supplied decomposition alone.

### Task 4: Adversarial audit and metadata repair

**Files:**
- Create: `compute/campaign686/reflected_three_bucket_tail1000_findings.md`
- Create: `compute/campaign686/reflected_three_bucket_tail1000_hostile_audit.md`
- Modify: the reflected-packing exact verifier and tests
- Modify: `compute/campaign686/agent_t2_high_component/high_component_verify.py`
- Modify: its focused test file

**Step 1: Audit the dependency tree**

List each derived premise separately: residual ceiling, center cube, endpoint third divisibilities, product identity, determinant nonzero, determinant absolute bound, loss ceiling, and numerical cutoff.  Give each node a proved/open verdict and replace every phrase such as “uniformly” or “essentially” by its exact quantifiers and inequality.

**Step 2: Replay boundary fixtures**

Check the `d=1` telescopes, Hensel/CRT congruence families, empty/unit buckets, endpoint distances `r=1` and `r=(k-1)/2`, and all six target rows.  State exactly which theorem hypothesis excludes each non-equation fixture.

**Step 3: Correct stale high-component metadata**

Change the banked high-component verifier verdict from `MATHEMATICAL_PASS_LEAN_OPEN` to a Lean-closed status supported by a focused test.  Do not alter its mathematics.

### Task 5: Campaign integration and repository gates

**Files:**
- Modify: `ErdosProblems.lean`
- Modify: `Audit.lean`
- Modify: `proofs.yaml`
- Modify: `FRONTIER.md`
- Modify: `PROGRESS_Erdos686.md`
- Modify: `compute/campaign686/approach_registry.md`
- Modify: `compute/campaign686/audit.md`
- Modify: `attestations.json` through the repository emitter

**Step 1: Register only the proved slice**

Record that all 27 center/reflected exactly-three-cleaned-bucket pairs close under `d >= 10^1000`.  Do not claim `OddThueTailHypothesis`, arbitrary-owner closure, Target 1, or Erdős #686.

**Step 2: Run focused and full gates**

Run exact Python reproduction, focused pytest, direct Lean compilation, `git diff --check`, manifest checks, the repository axiom gate, deterministic attestation emission, and the full `lake build ErdosProblems` gate.

**Step 3: Commit and push main**

Verify the worktree is clean after committing, verify `main` equals `origin/main`, and report the exact commit hash and the remaining quantified #686 gap.
