# Erdős 686 Even-Tail Coefficient Certificate Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Kernel-bank a generic, explicit coefficient certificate that turns an integral Runge polynomial part and lower-degree nonzero deficit into a no-quotient-four theorem beyond a computable threshold.

**Architecture:** Add one isolated Lean module importing `Erdos686EvenTailRunge.lean`. Define finite coefficient L1 norms, prove coefficientwise evaluation and leading-term dominance lemmas over `Polynomial ℤ`, package the polynomial identity, centered bridge, degrees, leading coefficients, and threshold inequalities in a certificate structure, then prove an equation-facing no-solution theorem. Do not claim the arbitrary-r descending square-root construction; identify that construction as the sole remaining uniform certificate-supply lemma.

**Tech Stack:** Lean 4.29.1, mathlib `Polynomial ℤ`, exact integer arithmetic, ordinary kernel reduction only.

---

### Task 1: Define explicit coefficient norms

**Files:**
- Create: `ErdosProblems/Erdos686EvenTailCoefficientCertificate.lean`

**Step 1:** Define `coefficientAbsSumBelow P m` as the integer sum of `|P.coeff i|` over `i < m`.

**Step 2:** Prove that evaluation of a degree-at-most-`q` polynomial at an integer `W ≥ 1` is bounded by `coefficientAbsSumBelow P (q+1) * W^q`.

**Step 3:** Compile with:

```bash
lake env lean ErdosProblems/Erdos686EvenTailCoefficientCertificate.lean
```

Expected: no errors.

### Task 2: Prove leading-term dominance

**Files:**
- Modify: `ErdosProblems/Erdos686EvenTailCoefficientCertificate.lean`

**Step 1:** Split `P.eval W` into its leading term and lower coefficients using `Polynomial.eval_eq_sum_range'` and `Finset.sum_range_succ`.

**Step 2:** Prove the lower-part bound by `coefficientAbsSumBelow P q * W^(q-1)` for positive `q`.

**Step 3:** Derive the scaled deficit bounds

```text
6 |L| W^q < 7 |D(W)|
7 |D(W)| < 8 |L| W^q
```

from `D.coeff q = L`, `D.natDegree ≤ q`, `L ≠ 0`, and `W > 7F`.

**Step 4:** Derive `2*T(W) > W^r` from leading coefficient `C ≥ 1`, `T.natDegree ≤ r`, and `W > 2A`.

**Step 5:** Recompile and inspect all theorem axioms.

### Task 3: Package the certificate and close the equation-facing theorem

**Files:**
- Modify: `ErdosProblems/Erdos686EvenTailCoefficientCertificate.lean`

**Step 1:** Define `EvenTailCoefficientCertificate r` with fields for `S,T,D,C,q,L,A,E,F,M`, the polynomial square identity, centered-product bridge, degree/leading-coefficient metadata, exact norm equalities, and the four strict threshold inequalities.

**Step 2:** For a hypothetical solution, instantiate centers `v=2n+2r+1`, `w=v+2d`; derive `S(w)=4S(v)`, `v≤w`, the ratio-power bound, positivity of both `T` evaluations, the small-deficit-difference bound, and the strict deficit ratio bound.

**Step 3:** Apply `integral_runge_trap` to prove

```lean
blockProduct (2*r) (n+d) ≠ 4 * blockProduct (2*r) n
```

whenever `r≥2` and `d≥max (2*r) M`.

**Step 4:** Print axioms for every public theorem and confirm only `[propext, Classical.choice, Quot.sound]` appear.

### Task 4: Audit and hand off

**Files:**
- Create: `compute/campaign686/agent_t2_even_tail_coefficient/hostile_audit.md`

**Step 1:** Record the exact dependency tree, boundary conditions `r=1`, `q=0`, `d=2r`, and zero-deficit exclusion.

**Step 2:** State the exact remaining construction lemma: for every `r≥2`, construct an `EvenTailCoefficientCertificate r` by the descending rational square-root recurrence and explicit denominator clearing.

**Step 3:** Run:

```bash
lake env lean ErdosProblems/Erdos686EvenTailCoefficientCertificate.lean
rg -n '\b(sorry|admit|native_decide)\b' ErdosProblems/Erdos686EvenTailCoefficientCertificate.lean
git diff --check -- ErdosProblems/Erdos686EvenTailCoefficientCertificate.lean compute/campaign686/agent_t2_even_tail_coefficient/hostile_audit.md
```

Expected: Lean succeeds; grep finds no forbidden proof devices; diff check succeeds.
