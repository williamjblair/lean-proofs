# Erdős 686 Fourth Local Lift Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Derive, kernel-check, and adversarially evaluate the fourth-order local Taylor congruence for the exactly-three-cleaned-owner Erdős 686 core.

**Architecture:** Extend the signed local cofactor expansion by its cubic coefficient, prove the generic modulo-`H^3` algebra, and eliminate the two opposite square residuals at each owner without dividing. Mirror every polynomial identity with independent exact-integer Python checks, then use a lifted CRT witness to decide whether the new congruence creates a bounded obstruction or merely one further local Hensel condition.

**Tech Stack:** Lean 4.29.1 with mathlib, Python 3 exact integers and `fractions.Fraction`, pytest.

---

### Task 1: Freeze the exact algebra

**Files:**
- Create: `compute/campaign686/fourth_local_lift_verify.py`
- Test: `compute/campaign686/test_fourth_local_lift_verify.py`

**Step 1:** Write symbolic/exact fixture tests for the denominator-cleared fourth-order identity, including nonzero `A` values.

**Step 2:** Run `python3 -m pytest compute/campaign686/test_fourth_local_lift_verify.py -q` and confirm the missing implementation fails.

**Step 3:** Implement the exact local formula and the three-bucket square-residual elimination using integers only.

**Step 4:** Run the focused tests and require all signs and coefficients to agree on signed exhaustive fixtures.

### Task 2: Formalize the kernel spine

**Files:**
- Create: `ErdosProblems/Erdos686FourthLocalLift.lean`

**Step 1:** Define the cubic local Taylor coefficient and prove the fourth-power cofactor remainder.

**Step 2:** Prove the generic fourth-order local algebra with conclusion modulo `H^3` and all `A`-dependent corrections present.

**Step 3:** Lift the algebra to `blockProduct`, then prove the three-bucket composed divisibility from the two exact square-residual differences.

**Step 4:** Run `lake env lean ErdosProblems/Erdos686FourthLocalLift.lean` and inspect every public theorem with `#print axioms`.

### Task 3: Hostile route verdict

**Files:**
- Modify: `compute/campaign686/fourth_local_lift_verify.py`
- Modify: `compute/campaign686/test_fourth_local_lift_verify.py`
- Create: `compute/campaign686/fourth_local_lift_findings.md`

**Step 1:** Extend the existing three-bucket CRT construction by one owner-adic digit and verify the square residual, second, third, and fourth local congruences exactly.

**Step 2:** Check the genuine block equation and verified short window separately so the witness cannot be misreported as a problem counterexample.

**Step 3:** State the strongest proper result and the exact remaining gap; explicitly classify whether the fourth lift yields a fixed bounded resultant.

**Step 4:** Run focused pytest, the exact report, Lean compilation, forbidden-token scan, and `git diff --check` without editing shared imports, manifests, attestations, or campaign dashboards.
