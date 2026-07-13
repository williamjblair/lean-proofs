# Large-Row Owner Aggregation Probe Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use the repository's exact-arithmetic and Lean audit workflow task-by-task.

**Goal:** Determine whether maximal lower/upper owner matching plus reflection forces a uniform contradiction in the live large-row residual, or exhibit an exact structural obstruction.

**Architecture:** First inventory only the kernel-banked hypotheses exposed by the four required Lean modules. Then reconstruct those hypotheses with exact integer arithmetic on the mandatory non-equation fixture and nearby adversarial data. Promote only a genuinely stronger quantified lemma; otherwise freeze the smallest counterfixture and state the exact missing correlation.

**Tech Stack:** Lean 4.29.1/mathlib, Python 3 exact integers and `fractions.Fraction`, pytest.

---

### Task 1: Theorem-surface inventory

**Files:**
- Read: `ErdosProblems/Erdos686CenterComponentLogStrip.lean`
- Read: `ErdosProblems/Erdos686MatchingCompression.lean`
- Read: `ErdosProblems/Erdos686ReflectedAlignmentSquareLift.lean`
- Read: `ErdosProblems/Erdos686FinalResidual.lean`

1. Record each exact divisibility, size inequality, and owner-supply premise.
2. Separate equation-derived hypotheses from arbitrary row-divisibility hypotheses.
3. Identify every place where a maximal owner, reflected owner, or common prime power must be the same object.

Status: complete.

### Task 2: Exact fixture reconstruction

**Files:**
- Create: `compute/campaign686/agent_large_owner_aggregation/large_owner_aggregation_verify.py`
- Create: `compute/campaign686/agent_large_owner_aggregation/test_large_owner_aggregation_verify.py`

1. Reproduce `(k,n,d)=(984,3177026,4480)` and its rows `1..16` exactly.
2. Factor the relevant lower terms, upper terms, gap, and reflection center.
3. Compute all maximal-valuation owner matches and reflected offsets.
4. Freeze exact checks showing which candidate aggregation statements survive or fail.

Status: complete.

### Task 3: Quantified outcome

**Files:**
- Create: `compute/campaign686/agent_large_owner_aggregation/findings.md`
- Create: `compute/campaign686/agent_large_owner_aggregation/hostile_audit.md`

1. Attempt a uniform owner-collision or product/lcm lemma using only banked hypotheses.
2. If false, state one quantified false lemma and give the exact fixture witness.
3. State the strongest rigorously surviving lemma and the single exact missing correlation.

Status: complete; the route is obstructed by an exact aggregate-only fixture.

### Task 4: Verification

1. Run focused pytest with bytecode and cache disabled.
2. Run every verifier twice and compare canonical payload hashes.
3. Scan for floating point, `sorry`, `admit`, `native_decide`, and unquantified closure language.
4. Run `git diff --check` on the isolated directory.

Status: complete after the focused audit commands recorded in `findings.md`.
