# Erdős 686 Multi-Owner Extension Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Determine whether the certified four-or-more-owner branch yields a bounded-loss second/third-order obstruction, and bank the strongest exact non-circular lemma or an explicit counterfamily.

**Architecture:** Generalize the three-bucket elimination to a finite family of pairwise-coprime cleaned components without moving the unselected components into the loss.  Independently enumerate every owner subset in the six target rows, audit zero-obstruction slopes and size bounds, then test whether the surviving nonzero obstructions or a three-bucket selection inequality can close the branch.  The Lean file will contain only generic algebra or inequalities that are strictly weaker than the target.

**Tech Stack:** Lean 4.29.1 with mathlib, Python 3 exact integers and `fractions.Fraction`, pytest.

---

### Task 1: Exact finite-family model

**Files:**
- Create: `compute/campaign686/multi_owner_extension_verify.py`
- Test: `compute/campaign686/test_multi_owner_extension_verify.py`

**Step 1: Write failing tests**

Add tests for the generalized second and third obstruction formulas on signed fixtures for owner-family sizes `3..15`, including center owners, reflected owners, endpoints, and loss factors divisible by `2` and `3`.

**Step 2: Run the focused test**

Run: `python3 -m pytest compute/campaign686/test_multi_owner_extension_verify.py -q`

Expected: FAIL because the verifier module does not yet exist.

**Step 3: Implement exact formulas**

For owner `s` in a family `S`, implement

```text
Delta_s = product(s-u, u in S\{s})
O_s = 3 * (C_s*A + 4*D_s*g^2*(-3)^(|S|-2)*Delta_s)
F_s = -3*O_s + 20*E_s*g^2*d*(-3)^(|S|-1)*Delta_s.
```

Verify these are congruent to the cofactor-multiplied second and third local lifts modulo `P_s` and `P_s^2` respectively.

**Step 4: Run the tests**

Run: `python3 -m pytest compute/campaign686/test_multi_owner_extension_verify.py -q`

Expected: PASS.

### Task 2: Finite target-row audit

**Files:**
- Modify: `compute/campaign686/multi_owner_extension_verify.py`
- Modify: `compute/campaign686/test_multi_owner_extension_verify.py`

**Step 1: Add failing finite-scan assertions**

Enumerate every subset `S` of every target row with `4 <= |S| <= k`.  Require exact counts, maximum zero-slope coefficients, simultaneous-zero multiplicity, and the worst coefficient in the zero equation.

**Step 2: Implement the scan**

Use exact integers and `Fraction`; do not use floats.  Record whether distinct owners can have the same positive zero slope and whether the equation-level lower residual bound `X_s > 5d` excludes every zero at `d >= 10^120` under the original `g <= G_k`.

**Step 3: Run the tests and report**

Run: `python3 compute/campaign686/multi_owner_extension_verify.py --pretty`

Expected: deterministic JSON with all counts and exact extrema.

### Task 3: Selection and route falsification

**Files:**
- Modify: `compute/campaign686/multi_owner_extension_verify.py`
- Modify: `compute/campaign686/test_multi_owner_extension_verify.py`

**Step 1: State candidate pigeonhole inequalities**

For sorted components `P_1 >= ... >= P_t` with `product P_i=d/g`, test the sharp guaranteed product of the largest three and the resulting complementary product.  Keep `g` unchanged in the statement.

**Step 2: Search for exact exponent counterfamilies**

Represent component sizes by rational exponents `alpha_i >= 0`, `sum alpha_i=1`.  Determine whether the window bounds `2 alpha_i <= 1` and the top-three product alone can bound the complement.  Produce an explicit family if not.

**Step 3: Test obstruction scaling**

Compare `P_s` with the best archimedean bound on `|O_s|`.  If the exponent inequality is non-closing for `t>=4`, record the exact exponent deficit rather than claiming progress.

### Task 4: Kernel-bank the genuine algebraic node

**Files:**
- Create: `ErdosProblems/Erdos686MultiOwnerExtension.lean`

**Step 1: Write the generic product-congruence lemma**

Prove that pairwise step-three residual identities replace the product of all opposite square residuals by `(-3)^(t-1) Delta_s` modulo the owner component and its square.

**Step 2: Prove the generalized second/third composition**

State the theorem over a finite index set so it does not assume primality, positivity, or the target equation.  Do not introduce an unbounded enlarged loss.

**Step 3: Prove only a non-circular zero-exclusion inequality**

If the finite-family theorem surface becomes disproportionate, instead bank the exact abstract inequality converting `X_s>5d`, `d=g*product(P_s)`, and `X_s=a_s P_s^2` into a lower bound for `product(a_s)`.  Do not formalize a theorem equivalent to the full target.

**Step 4: Compile and inspect axioms**

Run: `lake env lean ErdosProblems/Erdos686MultiOwnerExtension.lean`

Expected: success and only `[propext, Classical.choice, Quot.sound]` on public theorems.

### Task 5: Auditable findings

**Files:**
- Create: `compute/campaign686/multi_owner_extension_findings.md`

**Step 1: Write the dependency tree**

Separate exact algebra, finite enumeration, equation-level lower bounds, and any unproved interface.

**Step 2: Quantify every bound**

Replace all phrases such as “essentially bounded” or “one large bucket” by an explicit inequality.  Include the exact remaining gap or counterfamily.

**Step 3: Run final gates**

Run:

```bash
python3 -m pytest compute/campaign686/test_multi_owner_extension_verify.py -q
lake env lean ErdosProblems/Erdos686MultiOwnerExtension.lean
git diff --check -- docs/plans/2026-07-10-erdos686-multi-owner-extension.md \
  compute/campaign686/multi_owner_extension_verify.py \
  compute/campaign686/test_multi_owner_extension_verify.py \
  compute/campaign686/multi_owner_extension_findings.md \
  ErdosProblems/Erdos686MultiOwnerExtension.lean
```

Expected: all focused gates pass; no shared registry or active producer file is modified.
