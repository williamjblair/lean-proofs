# Erdős 699 Prime Radical Forcing Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Package the `i = 3` per-prime product-forcing lemmas as finite radical divisibility statements over all primes `p ≥ 5` dividing each window row.

**Architecture:** Add one finite product definition and generic prime-product divisibility lemmas to `lean/Erdos699/Proved/Basic.lean`, then derive the two `i = 3` radical wrappers from the existing per-prime wrappers. Use a temporary WIP `#check` file for red-green API validation and update `notes/PROGRESS.md` only after the Lean proof compiles.

**Tech Stack:** Lean 4, Mathlib `Nat.primeFactors`, Lake, exact Python criterion tests.

---

### Task 1: Red Check

**Files:**
- Create: `lean/Erdos699/WIP/PrimeRadicalForcingTest.lean`

- [x] **Step 1: Write the failing Lean API check**

```lean
import Erdos699.Proved.Basic

#check Erdos699.primeRadicalGE
#check Erdos699.prime_coprime_finset_prod_of_not_mem
#check Erdos699.finset_prod_primes_dvd_of_forall_dvd
#check Erdos699.primeRadicalGE_dvd_of_forall_prime_dvd
#check Erdos699.i_three_window_one_primeRadicalGE_dvd
#check Erdos699.i_three_window_two_primeRadicalGE_dvd
```

- [x] **Step 2: Run the WIP check and verify it fails**

Run: `lake env lean lean/Erdos699/WIP/PrimeRadicalForcingTest.lean`

Expected: unknown identifier errors for the six new names.

### Task 2: Lean Radical Product Lemmas

**Files:**
- Modify: `lean/Erdos699/Proved/Basic.lean`

- [x] **Step 1: Define the thresholded prime radical**

Add after the existing `i_three_window_two_product_forcing` theorem:

```lean
/-- Product of the prime divisors of `m` that are at least `lo`, without multiplicity. -/
def primeRadicalGE (lo m : ℕ) : ℕ :=
  ∏ p ∈ m.primeFactors.filter (fun p => lo ≤ p), p
```

- [x] **Step 2: Prove generic finite-product divisibility**

Add:

```lean
theorem prime_coprime_finset_prod_of_not_mem {p : ℕ} (hp : p.Prime) (s : Finset ℕ)
    (hs : ∀ q ∈ s, q.Prime) (hnot : p ∉ s) :
    p.Coprime (∏ q ∈ s, q) := by
  -- induction on `s`; use `Nat.coprime_primes` and `Nat.Coprime.mul_right`.
```

```lean
theorem finset_prod_primes_dvd_of_forall_dvd {s : Finset ℕ} {x : ℕ}
    (hprime : ∀ p ∈ s, p.Prime) (hdiv : ∀ p ∈ s, p ∣ x) :
    (∏ p ∈ s, p) ∣ x := by
  -- induction on `s`; use `Nat.Coprime.mul_dvd_of_dvd_of_dvd`.
```

```lean
theorem primeRadicalGE_dvd_of_forall_prime_dvd {lo m x : ℕ}
    (h : ∀ p : ℕ, p.Prime → lo ≤ p → p ∣ m → p ∣ x) :
    primeRadicalGE lo m ∣ x := by
  -- specialize the finite-product lemma to `m.primeFactors.filter`.
```

- [x] **Step 3: Prove the two i=3 radical wrappers**

Add:

```lean
theorem i_three_window_one_primeRadicalGE_dvd {n j : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q) (hn : 1 < n) :
    primeRadicalGE 5 (n - 1) ∣ j * (j - 1) :=
  primeRadicalGE_dvd_of_forall_prime_dvd fun p hp hp5 hpdvd =>
    i_three_window_one_product_forcing (p := p) hnone hp hp5 hn hpdvd
```

```lean
theorem i_three_window_two_primeRadicalGE_dvd {n j : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q) (hn : 2 < n) :
    primeRadicalGE 5 (n - 2) ∣ j * (j - 1) * (j - 2) :=
  primeRadicalGE_dvd_of_forall_prime_dvd fun p hp hp5 hpdvd =>
    i_three_window_two_product_forcing (p := p) hnone hp hp5 hn hpdvd
```

- [x] **Step 4: Run the proved file**

Run: `lake env lean lean/Erdos699/Proved/Basic.lean`

Expected: clean elaboration with no warnings.

### Task 3: Green Check and Progress Log

**Files:**
- Modify: `notes/PROGRESS.md`
- Delete: `lean/Erdos699/WIP/PrimeRadicalForcingTest.lean`

- [x] **Step 1: Rebuild and run the WIP API check**

Run:

```bash
lake build Erdos699.Proved.Basic
lake env lean lean/Erdos699/WIP/PrimeRadicalForcingTest.lean
```

Expected: the WIP file prints all six theorem/type signatures.

- [x] **Step 2: Update progress**

Add a `[R]` entry:

```markdown
- [R] Defined `Erdos699.primeRadicalGE` and proved
  `Erdos699.i_three_window_one_primeRadicalGE_dvd` and
  `Erdos699.i_three_window_two_primeRadicalGE_dvd`, packaging the `i = 3`
  per-prime window forcing as radical divisibility for all primes `p ≥ 5`
  dividing `n - 1` and `n - 2`. This is T4 support only; T4/T5 remain open.
```

- [x] **Step 3: Remove the temporary WIP file**

Delete `lean/Erdos699/WIP/PrimeRadicalForcingTest.lean`.

### Task 4: Verification and Commit

**Files:**
- Modify: `lean/Erdos699/Proved/Basic.lean`
- Modify: `notes/PROGRESS.md`
- Create: `docs/superpowers/plans/2026-07-05-erdos699-prime-radical-forcing.md`

- [x] **Step 1: Run verification gates**

Run:

```bash
python3 -m pytest compute/tests/test_criterion.py -q
rg -n "\bsorry\b|\badmit\b" lean/Erdos699/Proved || true
git diff --check
lake build
bash scripts/check_axioms.sh
bash scripts/check_manifest.sh
```

Run the local axiom audit:

```bash
lake env lean --stdin <<'EOF'
import Erdos699.Proved.Basic
#print axioms Erdos699.i_three_window_one_primeRadicalGE_dvd
#print axioms Erdos699.i_three_window_two_primeRadicalGE_dvd
EOF
```

Expected: all checks pass; direct axiom audit reports only `[propext, Classical.choice, Quot.sound]`.

- [ ] **Step 2: Commit**

```bash
git add docs/superpowers/plans/2026-07-05-erdos699-prime-radical-forcing.md \
  lean/Erdos699/Proved/Basic.lean notes/PROGRESS.md
git commit -m "feat: prove erdos699 i3 radical forcing"
```
