# Erdős 686 Third-Obstruction Nonzero Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Prove that the exact target-row block equation forces every composed third obstruction to be nonzero, both on the complete owner grid and in the supplied exactly-three cleaned-bucket slice.

**Architecture:** Reuse the banked residual-product lower bound instead of adding another congruence.  For four or more owners, the cofactor product grows at least quadratically in the target-size gap, so it dominates the linear-in-`d` third-obstruction correction uniformly.  For exactly three owners, use the row-specific ratio-window lower bound to force each selected residual above an explicit multiple of `d`, then discharge the finite coefficient comparison with an ordinary-kernel Boolean certificate.

**Tech Stack:** Lean 4 / Mathlib, exact Python integers and `fractions.Fraction`, pytest, repository axiom and manifest gates.

---

### Task 1: Freeze the exact coefficient inequalities

**Files:**
- Create: `compute/campaign686/third_obstruction_nonzero_verify.py`
- Create: `compute/campaign686/test_third_obstruction_nonzero_verify.py`

**Step 1: Write the failing tests**

Test the six target rows, every ordered distinct owner triple, the residual-floor table

```python
RESIDUAL_FLOOR = {5: 8, 7: 12, 9: 15, 11: 20, 13: 23, 15: 29}
```

and the exact inequalities

```python
0 < 9 * abs(C) * L**3 - 180 * abs(E * delta)
108 * abs(D * delta) < 10**120 * (
    9 * abs(C) * L**3 - 180 * abs(E * delta)
)
```

where `C,D,E` are independently reconstructed signed elementary-symmetric coefficients and `delta=(owner-left)*(owner-right)`.

**Step 2: Run the focused test and confirm it initially fails**

Run: `PYTHONDONTWRITEBYTECODE=1 python3 -m pytest -q -p no:cacheprovider compute/campaign686/test_third_obstruction_nonzero_verify.py`

Expected: failure because the verifier module does not yet exist.

**Step 3: Implement the exact verifier**

Independently reconstruct the local cofactor polynomial, enumerate all 6,210 ordered target triples, verify the two displayed inequalities, report per-row minimum margins, and replay the `k=9,15`, `d=1` telescopes as out-of-domain boundary fixtures.

**Step 4: Run exact reproduction**

Run:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 compute/campaign686/third_obstruction_nonzero_verify.py
PYTHONDONTWRITEBYTECODE=1 python3 -m pytest -q -p no:cacheprovider compute/campaign686/test_third_obstruction_nonzero_verify.py
python3 -m py_compile compute/campaign686/third_obstruction_nonzero_verify.py compute/campaign686/test_third_obstruction_nonzero_verify.py
```

Expected: all exact inequalities and tests pass.

### Task 2: Prove the generic domination lemmas

**Files:**
- Create: `ErdosProblems/Erdos686ThirdObstructionNonzero.lean`

**Step 1: Add a generic signed domination theorem**

Prove that, for positive `g,d,A`,

```lean
9 * |C| * A >
  (180 * |E*delta| * d + 108 * |D*delta|) * g^2
```

implies

```lean
-9*C*A + 180*E*g^2*delta*d + 108*D*g^2*delta != 0.
```

Use `Int.natAbs`, exact casts, and triangle inequalities; do not divide in `ℤ`.

**Step 2: Add the three-component cofactor-product lower bound**

From `d=g*P*Q*R` and

```lean
L*d <= a*P^2,
L*d <= b*Q^2,
L*d <= c*R^2,
```

prove `L^3*g^2*d <= a*b*c` by multiplying the residual inequalities, rewriting `d^2=g^2*P^2*Q^2*R^2`, and cancelling positive `d^2`.

**Step 3: Run the module**

Run: `lake env lean ErdosProblems/Erdos686ThirdObstructionNonzero.lean`

Expected: compile success with no `sorry`, `admit`, `axiom`, or `native_decide`.

### Task 3: Add the finite target-row certificate

**Files:**
- Modify: `ErdosProblems/Erdos686ThirdObstructionNonzero.lean`

**Step 1: Define computable tables and certificate**

Define `targetThirdResidualFloor`, a Boolean certificate over `List.range (k+1)`, and table-based versions of the two exact inequalities from Task 1 using the existing second/third coefficient tables.

**Step 2: Prove the six-row ordinary-kernel certificate**

Use `by decide`, not `native_decide`, for rows `5,7,9,11,13,15`, then transport table coefficients to `localSecondConstant`, `localSecondLinear`, and `localThirdQuadratic` with the existing table-equality lemmas.

**Step 3: Prove the exactly-three nonzero theorem**

Combine the certificate, the generic domination theorem, the component-product lower bound, `d>=10^120`, and the row-specific residual floors to prove

```lean
targetThreeBucketThirdObstruction k owner left right a b c g d != 0.
```

for every ordered distinct target triple.

**Step 4: Compile and inspect axioms**

Run: `lake env lean ErdosProblems/Erdos686ThirdObstructionNonzero.lean`

Expected: every public theorem reports a subset of `[propext, Classical.choice, Quot.sound]`.

### Task 4: Derive row-specific residual floors from the equation

**Files:**
- Modify: `ErdosProblems/Erdos686ThirdObstructionNonzero.lean`

**Step 1: Prove the target residual-floor theorem**

From `ratio_window_four_nat heq`, prove for `i in Icc 1 k` and `d>=10^120`:

```lean
targetThirdResidualFloor k * d <= localResidual n d i.
```

Use `row_base_lower_k5`, `row_base_lower_k11`, `row_base_lower_k13`, and `row_base_lower_k15`; use the exact `11/9` and `7/6` linearizations for rows 7 and 9.  Make every natural-subtraction positivity premise explicit.

**Step 2: Add an equation-facing wrapper**

Given three residual decompositions and `d=g*P*Q*R`, apply the floor theorem at all three owners and discharge the exactly-three nonzero theorem.

**Step 3: Compile and test the boundary cases**

Confirm the wrapper requires `d>=10^120`, so the `k=9,15`, `d=1` telescopes remain valid and out of scope.

### Task 5: Extend the full-grid certificate

**Files:**
- Modify: `ErdosProblems/Erdos686ThirdObstructionNonzero.lean`
- Modify: `ErdosProblems/Erdos686AllOwnerAssembly.lean` only if the theorem packages cleanly without changing existing definitions.

**Step 1: Prove uniform multi-owner third-obstruction domination**

Use `multi_owner_cofactor_product_scaled_lower`, cardinality `4<=|S|<=15`, the existing coefficient bounds `|D|<10^12`, `|E|<10^10`, and `|(-3)^r Delta|<=3^14*15^14` to show the cofactor term dominates the correction for every `d>=10^120`.

**Step 2: Instantiate the all-owner assembly**

For every grid owner, derive

```lean
multiOwnerThirdObstruction ... != 0
```

from `AllOwnerAssemblyCertificate`, retaining unit buckets and the original grouped loss.

**Step 3: Compile the producer and hostile audit**

Run direct Lean compilation for the new module and the all-owner audit importer.

### Task 6: Adversarial audit and campaign integration

**Files:**
- Create: `compute/campaign686/third_obstruction_nonzero_findings.md`
- Create: `compute/campaign686/third_obstruction_nonzero_hostile_audit.md`
- Create: `compute/campaign686/third_obstruction_nonzero_hostile_verify.py`
- Create: `compute/campaign686/test_third_obstruction_nonzero_hostile_verify.py`
- Modify after hostile audit: `ErdosProblems.lean`, `Audit.lean`, `proofs.yaml`, `FRONTIER.md`, `PROGRESS_Erdos686.md`, `compute/campaign686/approach_registry.md`, `compute/campaign686/audit.md`

**Step 1: Audit every dependency**

Convert all phrases such as “dominates” and “uniform” into the exact inequalities proved above.  Replay empty buckets, center owners, bases 2 and 3, the two `d=1` telescopes, and the 121/130-digit CRT congruence falsifiers.  State explicitly that those CRT fixtures fail the short equation/residual floor and hence do not refute the new theorem.

**Step 2: Register only the proved reduction**

Update the frontier from “zero and nonzero third-quotient branches” to the exact surviving all-nonzero branch.  Do not claim `OddThueTailHypothesis`, Target 1, or #686 solved.

**Step 3: Run all gates**

Run exact Python tests, direct Lean builds, `git diff --check`, `bash scripts/check_manifest.sh`, `bash scripts/check_axioms.sh`, `python3 scripts/emit_attestations.py`, and `lake build ErdosProblems`.

Expected: all gates pass and attestations reproduce deterministically.
