# Erdős 730 Near-Affine Payment Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Prove an explicit normalized first-moment upper bound for the corrected #730 near-affine valuation band, or isolate an exact obstruction.

**Architecture:** Parameterize each branch valuation by its unique residue class modulo `p^a`, choose the digit-block exponent `r` maximally from the resulting `k`-interval, and convert the near-affine inequality into a lower bound on the prime power `p^a`. Sum the resulting high-prime-power occurrence weights with explicit elementary constants and verify every finite inequality by exact integer or rational arithmetic.

**Tech Stack:** Python 3 standard library, `fractions.Fraction`, pytest, Markdown audit artifacts.

---

### Task 1: Encode the exact branch and interval geometry

**Files:**
- Create: `compute730/campaign_uniform/repair/near_affine_payment.py`
- Test: `compute730/campaign_uniform/repair/test_near_affine_payment.py`

**Step 1:** Write tests for the four branch slopes, the uniform branch bound `M_X=380808X+19`, unique residue-class counts, and exact base-`p` digit lengths.

**Step 2:** Run `python3 -m pytest compute730/campaign_uniform/repair/test_near_affine_payment.py -q` and verify the missing module fails collection.

**Step 3:** Implement the branch geometry and exact integer helpers.

**Step 4:** Re-run the focused test and require all geometry cases to pass.

### Task 2: Prove the near-band prime-power threshold

**Files:**
- Modify: `compute730/campaign_uniform/repair/near_affine_payment.py`
- Modify: `compute730/campaign_uniform/repair/test_near_affine_payment.py`

**Step 1:** Add exact tests for `kappa_p<=1/3` via `8p^2<=(p+1)^3`, `eta=1/12`, the implication `a>19r/12`, and the absence of exponent `a=1` from the near band.

**Step 2:** Implement maximal admissible `r` and derive `p^a>(X/(2W_X))^(38/81)` with `W_X=((43/38)log M_X)^C`.

**Step 3:** Exhaustively verify the integer implication over a broad finite grid, using the exact powered inequality `q^81(2W)^38>X^38` with a rational upper bound for `W` in certificate tests.

### Task 3: Sum occurrence weights

**Files:**
- Modify: `compute730/campaign_uniform/repair/near_affine_payment.py`
- Modify: `compute730/campaign_uniform/repair/test_near_affine_payment.py`

**Step 1:** Test the elementary tail bound
`sum_{p,a>=2,p^a>=Y}p^(-a) <= 2Y^(-1/2)+3Y^(-2/3)`
against exact finite sums.

**Step 2:** Implement the four-branch normalized payment
`8Y^(-1/2)+12Y^(-2/3)+4sqrt(M)/X+4log_2(M)M^(1/3)/X`.

**Step 3:** Produce exact rational finite-cutoff diagnostics without using them as theorem premises.

### Task 4: Write the dependency-tree finding

**Files:**
- Create: `compute730/campaign_uniform/repair/near_affine_payment_findings.md`

**Step 1:** State every quantifier, define the maximal choice of `r`, and record the cofactor digit-length relation.

**Step 2:** Give the dependency tree and a per-node verdict.

**Step 3:** State scope precisely: this proves the near-affine payment tends to zero under the maximal-`r` protocol and makes no far-range Fourier or global-budget claim.

### Task 5: Verify the artifact

**Files:**
- Test: `compute730/campaign_uniform/repair/test_near_affine_payment.py`

**Step 1:** Run the focused pytest suite.

**Step 2:** Run the diagnostic CLI and compare its exact certificate fields with the findings file.

**Step 3:** Run `git diff --check` on the new repair artifacts.
