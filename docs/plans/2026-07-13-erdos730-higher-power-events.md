# Erdős 730 Higher-Power Events Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Prove unconditionally that the normalized cardinality of `localHigherPowerWitnessesUpTo X` tends to zero.

**Architecture:** Group local witnesses by branch and higher prime power `(p,a)`, prove that divisibility by `p^a` confines the parameter to one root progression, and identify the branch test value on that progression with the existing p-adic permutation polynomial.  The lower-half digit condition then gives a block count with depth `Nat.log p (X / p^a)`; sum the geometric terms by the existing Tannery theorem and pay terminal `+1` terms with the existing higher-prime-power-pair estimate.  Work directly on `main` because the user explicitly requested no further worktrees.

**Tech Stack:** Lean 4.29.1, pinned Mathlib 4.29.1, `lake build`, `#print axioms`, repository source-hygiene gates.

---

### Task 1: Root progression and exceptional-prime exclusion

**Files:**
- Create: `ErdosProblems/Erdos730HigherPowerEvents.lean`

**Step 1:** Import `Erdos730BranchEvents`, `Erdos730DigitBoxes`, `Erdos730ObstructionMaps`, and `Erdos730HigherPowerDensity`.

**Step 2:** Prove every prime occurring in a local branch obstruction is different from `2`, `3`, `41`, and `43`, using `branch_mod_3` and `fixed_primes_do_not_divide_branches`.

**Step 3:** Prove that such a prime is coprime to the selected branch slope, hence so is every positive power `p^a`.

**Step 4:** Prove that two parameters whose branch values are divisible by `p^a` are congruent modulo `p^a`.

**Step 5:** Build and run the audit after each theorem so failures expose the exact missing dependency.

### Task 2: Exact branch-map specialization

**Files:**
- Modify: `ErdosProblems/Erdos730HigherPowerEvents.lean`

**Step 1:** Define the four root-progression coefficients matching equations (16)--(17): common quadratic coefficient, branch-dependent `u`, and residual coefficient magnitude/sign.

**Step 2:** Prove that the natural `branchTestValue` agrees after integer casting with `PhiP`, `PhiQ`, `PhiR`, or `PhiS`, including the odd-cofactor division-by-two cases.

**Step 3:** For `q=p^a`, a root residue `x0`, cofactor `c0`, and progression index `k`, prove the exact equality between the branch test value and `padicBranchMap p (...) (...) b (...) k` modulo `p^r`.

**Step 4:** Prove the residual coefficient is a unit modulo `p^r` from the exceptional-prime exclusions.

### Task 3: Finite block count for one branch and prime power

**Files:**
- Modify: `ErdosProblems/Erdos730HigherPowerEvents.lean`

**Step 1:** Define the finite parameter fiber for fixed `(L,p,a)`.

**Step 2:** In the nonempty case choose one root, use quotient/remainder by `p^a` to inject every fiber element into `Finset.range (X / p^a + 1)`, and prove the image satisfies the specialized p-adic digit-box predicate.

**Step 3:** Apply `padicBranchAllowedCount_le` with `r = higherPowerDepth p a X` and `H = halfDigitCount p`; retain the exact `r=0` case.

**Step 4:** Convert the result to the explicit finite bound
`((X / p^a + 1) / p^r + 1) * halfDigitCount p ^ r`.

### Task 4: Ledger injection and global finite bound

**Files:**
- Modify: `ErdosProblems/Erdos730HigherPowerEvents.lean`

**Step 1:** Inject each local higher-power witness into `(L,p,a,x)` and recover its unique cofactor from `branchValue L x = p^a*d`.

**Step 2:** Show every occurring `(p,a)` belongs to `higherPrimePowerPairs (higherPowerBranchHeight * X)` using the uniform branch-height bound.

**Step 3:** Sum the one-fiber estimate over four branches and all higher-prime-power pairs.

**Step 4:** Cast the finite inequality to reals and bound its normalized geometric part by `4 * ∑' i, higherPowerEnvelope X i`, with one terminal payment per `(L,p,a)`.

### Task 5: Limit theorem and hostile audit

**Files:**
- Modify: `ErdosProblems/Erdos730HigherPowerEvents.lean`
- Create: `ErdosProblems/Erdos730HigherPowerEventsAudit.lean`

**Step 1:** Sandwich the normalized witness count between zero and the existing four-branch envelope-plus-terminal function.

**Step 2:** Apply `tendsto_four_mul_higherPowerEnvelope_and_terminal_zero` to prove `tendsto_normalizedLocalHigherPowerWitnessCount`.

**Step 3:** Explicitly audit the root-class theorem, branch-map identity, one-fiber count, finite global inequality, and final limit theorem.

**Step 4:** Run:

```sh
lake build ErdosProblems.Erdos730HigherPowerEventsAudit
rg -n 'sorry|admit|native_decide' ErdosProblems/Erdos730HigherPowerEvents*.lean
git diff --check
```

Expected: the build succeeds; audited theorems use only `[propext, Classical.choice, Quot.sound]`; the source scan and whitespace check are clean.
