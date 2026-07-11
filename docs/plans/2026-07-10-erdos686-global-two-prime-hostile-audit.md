# Erdős 686 Global Two-Prime Hostile Audit Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Independently decide whether `two_prime_support_below_cutoff_of_global_residual_lifts` closes every distinct-prime two-support case for the six admissible values of `k` under the exact Erdős 686 hypotheses.

**Architecture:** Freeze the producer artifacts by SHA-256, reconstruct the theorem's dependency tree from source, and validate the Lean surface independently of producer scripts. Reimplement every finite coefficient and size certificate with separate exact-integer code, exhaust the branch partition (including primes 2 and 3 and coincident owners), and record a hostile PASS or a minimal quantified failure in a separate audit report.

**Tech Stack:** Lean 4.29.1, mathlib, Lake, Python 3 exact integers, `unittest`, POSIX shell.

---

### Task 1: Freeze inputs and reconstruct the dependency tree

**Files:**
- Read: `ErdosProblems/Erdos686GlobalResidualConcentration.lean`
- Read: `ErdosProblems/Erdos686GlobalResidualTwoPrime.lean`
- Read: `ErdosProblems/Erdos686TwoPrimeSecondLift.lean`
- Create: `compute/campaign686/global_two_prime_hostile_audit.md`

**Steps:**
1. Verify all producer SHA-256 values.
2. Extract every public theorem used by the endpoint and map each hypothesis to the target.
3. Flag any circular theorem-strength hypothesis, private bridge, or missing positivity/coprimality condition.

### Task 2: Audit the kernel surface from a clean module state

**Files:**
- Read: the two frozen Lean modules.
- Create temporarily: `/tmp/Erdos686GlobalTwoPrimeAudit.lean`

**Steps:**
1. Delete only the two target `.olean` files and rebuild them with Lake.
2. Run standalone `#check` and `#print axioms` on the endpoint and every novel public dependency.
3. Scan sources for `sorry`, `admit`, `native_decide`, `axiom`, unsafe declarations, and theorem-strength private assumptions.
4. Require the axiom set to be a subset of `[propext, Classical.choice, Quot.sound]`.

### Task 3: Reproduce finite certificates independently

**Files:**
- Create: `compute/campaign686/global_two_prime_hostile_verify.py`
- Create: `compute/campaign686/test_global_two_prime_hostile_verify.py`

**Steps:**
1. Implement the six `k` rows and local constant/linear/quadratic coefficients from definitions.
2. Enumerate every owner pair, center branch, simultaneous-zero branch, and prime assignment including 2 and 3.
3. Recompute concentration losses, cofactor bounds, local obstruction bounds, and the final `< 10^120` contradiction with exact integers.
4. Add mutation-sensitive tests for boundary equality and all claimed maxima.
5. Run the independent test suite and compare its totals with the Lean finite tables.

### Task 4: Issue the hostile verdict

**Files:**
- Complete: `compute/campaign686/global_two_prime_hostile_audit.md`

**Steps:**
1. Record exact command outputs, counts, maxima, SHA-256 values, theorem surface, and axioms.
2. Check hypotheses against `d = p^e q^f`, distinct primality, the global product square lift, owner concentration, and `d >= 10^120`.
3. Return `PASS` only if every branch is covered; otherwise state one exact quantified residual lemma.
4. Do not modify producer files and do not commit.
