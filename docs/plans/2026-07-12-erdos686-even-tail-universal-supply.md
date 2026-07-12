# Erdős 686 Universal Even-Tail Supply Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Construct an `EvenTailCoefficientCertificate r` for every `r>=2` entirely inside Lean.

**Architecture:** Add one isolated supply module. First prove a field-generic descending cancellation lemma producing a monic rational polynomial `Q` with `deg(Q^2-S)<r` for any monic degree-`2r` polynomial `S`. Define the centered even polynomial directly as the product of the `2r` linear centered factors, prove its centered bridge and simple root at `1`, then clear denominators through `IsLocalization.integerNormalization`. Finally choose the exact coefficient norms and maximum threshold definitionally and populate the existing certificate record.

**Tech Stack:** Lean 4.29.1, mathlib `Polynomial`, `IsMonicOfDegree`, `IsFractionRing.integerNormalization`, exact rational/integer arithmetic.

---

### Task 1: Descending rational square-root recurrence

**Files:**
- Create: `ErdosProblems/Erdos686EvenTailSupply.lean`

**Steps:**
1. Define the one-step correction `a=-(Q^2-S)_{r+j}/2` and `Q'=Q+aX^j`.
2. Prove that if `Q` is monic of degree `r` and `deg(Q^2-S)<r+j+1`, then `Q'` is monic of degree `r` and `deg(Q'^2-S)<r+j`.
3. Iterate the step from `j=r-1` down to `j=0`.
4. Prove existence and uniqueness of monic `Q : ℚ[X]` with `deg(Q^2-S)<r`.
5. Compile and print axioms.

### Task 2: Centered polynomial and non-square proof

**Files:**
- Modify: `ErdosProblems/Erdos686EvenTailSupply.lean`

**Steps:**
1. Define `evenCenteredPolynomial r` as the product of the `2r` centered linear factors.
2. Prove the evaluation bridge to `centeredBlockProduct`.
3. Prove it is monic of degree `2r`.
4. Factor out the `i=r` term `X-1` and prove the remaining product is nonzero at `1`.
5. Prove `S(1)=0` but `S'(1)!=0`, hence no nonzero scalar multiple of `S` can be a polynomial square.

### Task 3: Integral denominator clearing

**Files:**
- Modify: `ErdosProblems/Erdos686EvenTailSupply.lean`

**Steps:**
1. Apply `IsLocalization.integerNormalization (nonZeroDivisors ℤ)` to `Q`.
2. Normalize the sign of its nonzero scalar multiplier so the integral polynomial has positive leading coefficient `C`.
3. Define `D=T^2-C^2S` and transfer `deg D<r` from the rational identity.
4. Use the simple-root theorem to prove `D!=0`, then set `q=D.natDegree` and `L=D.coeff q`.

### Task 4: Populate and audit the universal certificate

**Files:**
- Modify: `ErdosProblems/Erdos686EvenTailSupply.lean`
- Create: `compute/campaign686/agent_t2_even_tail_supply/hostile_audit.md`

**Steps:**
1. Set `A,E,F` to the exact coefficient sums.
2. Set `M=max(2A+1,7F+1,10E+1,2r)` after converting nonnegative integer norms to naturals.
3. Construct `EvenTailCoefficientCertificate r` and prove `universal_even_tail_certificate_supply`.
4. Derive the unconditional effective even-tail theorem from the existing supply wrapper.
5. Compile, print axioms, scan for `sorry`, `admit`, and `native_decide`, and record the exact boundary audit.
