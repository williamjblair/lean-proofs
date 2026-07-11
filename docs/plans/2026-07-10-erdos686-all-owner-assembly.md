# Erdős 686 All-Owner Assembly Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Assemble every cleaned residual owner on the full grid `[1,k]` into an exact bounded-loss factorization and compose it with the generic multi-owner second/third obstructions and target-size zero exclusion.

**Architecture:** Define one bucket `P_i` for every grid index using the already banked grouped-left product; empty buckets are exactly one.  Prove the original gap equals the unchanged grouped loss times the product of all grid buckets by commuting the finite prime and owner products, then define each residual cofactor by exact division and feed the resulting progression, local lifts, and window bounds into `Erdos686MultiOwnerExtension`.  The final theorem will expose the complete obstruction system while explicitly leaving the nonzero short-window branch open.

**Tech Stack:** Lean 4.29.1 with mathlib, Python 3 exact prime factorization and finite products, pytest.

---

### Task 1: Exact all-owner arithmetic model

**Files:**
- Create: `compute/campaign686/all_owner_assembly_verify.py`
- Test: `compute/campaign686/test_all_owner_assembly_verify.py`

**Step 1: Write failing tests**

Test all six target rows and gaps in a deterministic finite range, including `d=1`, prime powers of 2 and 3, primes at least `k`, empty owner buckets, coincident prime owners, and assignments using both endpoints.

**Step 2: Run the focused test**

Run: `python3 -m pytest compute/campaign686/test_all_owner_assembly_verify.py -q`

Expected: import failure before the verifier exists.

**Step 3: Implement independent assembly**

For each prime `p|d`, reproduce the cleaned exponent and loss exponent.  Assign `p^t` to exactly one bucket and check

```text
d = product_p p^(v_p(d)-t) * product_{i=1}^k product_{owner(p)=i} p^t.
```

Record exact counts for empty buckets, zero-clean factors, bases 2 and 3, and endpoint assignments.

**Step 4: Verify residual quotient fixtures**

Generate exact synthetic residual progressions `X_i=a_i P_i^2`, check quotient reconstruction and step-three differences, and reproduce the composed obstruction formulas.

### Task 2: Full-grid bucket definitions

**Files:**
- Create: `ErdosProblems/Erdos686AllOwnerAssembly.lean`

**Step 1: Define the grid bucket and residual cofactor**

Use

```text
allOwnerBucket k d owner i = globalResidualGroupedLeft k d owner i
allOwnerCofactor k n d owner i = localResidual n d i / allOwnerBucket(...)^2.
```

**Step 2: Re-export factor and square divisibilities**

Specialize `globalResidualGroupedLeft_dvd_factor` and
`globalResidualGroupedLeft_square_dvd_residual` for every grid index.

**Step 3: Prove exact quotient reconstruction**

From square divisibility, prove

```text
localResidual n d i = allOwnerCofactor(...) * allOwnerBucket(...)^2.
```

### Task 3: Exact all-owner gap factorization

**Files:**
- Modify: `ErdosProblems/Erdos686AllOwnerAssembly.lean`

**Step 1: Prove one-prime placement**

For `p in d.primeFactors`, use the assignment's in-range owner to show that the product of `globalResidualGroupedLeftFactor` over the whole grid is exactly the cleaned power `p^t`, including `t=0`.

**Step 2: Commute the finite products**

Prove the product of all grid buckets equals the product of every retained cleaned prime power.

**Step 3: Reconstruct the gap**

Combine the retained product with `globalResidualGroupedLossFactor_mul_clean` and `Nat.prod_factorization_pow_eq_self` to obtain

```text
d = globalResidualGroupedLoss k d * product_{i in Icc 1 k} allOwnerBucket k d owner i.
```

**Step 4: Retain the exact target-row loss ceiling**

Compose with `globalResidualGroupedLoss_le_targetAggregateLoss` without changing the loss.

### Task 4: Residual progression and local lifts

**Files:**
- Modify: `ErdosProblems/Erdos686AllOwnerAssembly.lean`

**Step 1: Prove positivity and exact residual differences**

Under the multiplier-four equation and target window, prove every cofactor is positive and

```text
a_i P_i^2 - a_j P_j^2 = 3(i-j)
```

in signed integers.

**Step 2: Derive the gap quotient at every bucket**

From `d=g*product P_i` and bucket positivity, prove

```text
d = P_i * (g * product_{j!=i} P_j).
```

**Step 3: Instantiate second and third local lifts**

Use the existing factor, residual, and equation hypotheses to derive each local second and third divisibility with the unchanged opposite product.

### Task 5: Compose the all-owner obstruction system

**Files:**
- Modify: `ErdosProblems/Erdos686AllOwnerAssembly.lean`

**Step 1: Map the natural owner grid into the integer finite-family interface**

Prove the exact product, erase, cardinality, and delta identities required by `Erdos686MultiOwnerExtension`, or add an audit-transparent natural-index wrapper that invokes its generic algebra.

**Step 2: Prove all second/third composed divisibilities**

For every grid owner `i`, derive `P_i|O_i` and `P_i^2|F_i`.

**Step 3: Instantiate uniform zero exclusion**

Use `2d<n`, hence `localResidual>5d`, the target coefficient bounds, grid cardinality `k in {5,...,15}`, and the exact bounded-loss factorization to prove every `O_i` is nonzero.

**Step 4: State the strongest equation-level wrapper**

Return one certified assignment, the unchanged loss and full bucket/cofactor family, exact factorization, window/progression facts, local lifts, nonzero composed obstructions, and divisibilities.  Do not claim contradiction or Target 1 closure.

### Task 6: Audit findings and gates

**Files:**
- Create: `compute/campaign686/all_owner_assembly_findings.md`

**Step 1: Write the dependency tree and theorem surface**

Separate existing inputs, new assembly lemmas, finite-family composition, and the exact open node.

**Step 2: State every boundary explicitly**

Cover empty buckets, zero-clean factors, bases 2 and 3, endpoints, center owners, `d=1` telescopes, and four-or-more live owners.

**Step 3: Run final gates**

Run:

```bash
python3 -m pytest compute/campaign686/test_all_owner_assembly_verify.py -q
python3 -m py_compile compute/campaign686/all_owner_assembly_verify.py \
  compute/campaign686/test_all_owner_assembly_verify.py
lake env lean ErdosProblems/Erdos686AllOwnerAssembly.lean
lake build ErdosProblems.Erdos686AllOwnerAssembly
```

Expected: all tests and builds pass, all public theorem surfaces use only allowed axioms, and no shared file changes.
