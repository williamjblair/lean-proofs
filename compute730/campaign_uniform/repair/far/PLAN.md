# Erdős 730 Separated Far-Range Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Derive and audit the sharpest explicit incomplete-block estimate obtainable from exact Fourier expansion and sparse quadratic completion in the separated #730 range.

**Architecture:** Replace the restricted-output set by the exact-valuation alphabet, expand its indicator modulo `p^(2r)`, and reduce every incomplete quadratic sum by completion to explicitly supported prime-power Gauss sums. Quantify the resulting absolute-value loss, test it adversarially, and isolate the precise bilinear cancellation inequality if absolute completion cannot close.

**Tech Stack:** Python 3, `fractions.Fraction`, NumPy for exact integer window counts, pytest, Markdown audit artifacts.

---

### Task 1: Exact Fourier input

**Files:**
- Create: `compute730/campaign_uniform/repair/far/far_fourier.py`
- Test: `compute730/campaign_uniform/repair/far/test_far_fourier.py`

**Step 1:** Write failing tests for the exact-valuation output alphabet and its cardinality.

**Step 2:** Implement the forbidden least digit (`0` on P/Q and `(p-1)/2` on R/S), exact restricted-set enumeration, and factorized Fourier metadata.

**Step 3:** Prove and test the exact cumulative Fourier-energy identity for frequencies divisible by `p^v`.

### Task 2: Sparse quadratic completion

**Files:**
- Modify: `compute730/campaign_uniform/repair/far/far_fourier.py`
- Modify: `compute730/campaign_uniform/repair/far/test_far_fourier.py`

**Step 1:** Encode the conductor `d=max(2r-v-a-v_p(A),0)`.

**Step 2:** Verify exactly on small prime powers that complete Gauss sums vanish unless the completion frequency lies in the required residue class.

**Step 3:** Implement the explicit incomplete-sum majorant
`2N/p^(d/2)+p^(d/2)(1+d log p)` for `d>0`, retaining the affine `N` bound for `d=0`.

### Task 3: Hostile-check absolute completion

**Files:**
- Modify: `compute730/campaign_uniform/repair/far/far_fourier.py`
- Modify: `compute730/campaign_uniform/repair/far/test_far_fourier.py`

**Step 1:** Compute exact certified block lengths `ceil(p^r(log p^r)^2)` using rational logarithm intervals.

**Step 2:** Scan every admissible branch and separated tuple for `p=5,7,11` in the feasible exact ranges.

**Step 3:** Compare maximum cyclic counts to the cleared main term and compare the absolute Fourier/Gauss majorant to the available target slack.

### Task 4: State the exact residual

**Files:**
- Create: `compute730/campaign_uniform/repair/far/far_range_findings.md`

**Step 1:** Give the exact Fourier identity and all Gauss-support constants, including the extra `v_7(A)=1`.

**Step 2:** Record whether the absolute completion closes; if it does not, give its exact quantitative failure rather than an `O(polylog)` claim.

**Step 3:** State the single bilinear cancellation inequality sufficient for the advertised far estimate and clearly mark it OPEN.

**Step 4:** Record any genuinely proved subrange and all exact finite hostile checks without extrapolating them.

### Task 5: Verify

**Files:**
- Test: `compute730/campaign_uniform/repair/far/test_far_fourier.py`

**Step 1:** Run the focused far-range pytest suite.

**Step 2:** Run the far diagnostic CLI.

**Step 3:** Run the full `compute730/campaign_uniform` suite and `git diff --check` on the far artifacts.
