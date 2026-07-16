# Erdős #686 Full-Solve Campaign After the k=5 Mordell-Weil Certificate

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Complete a rigorous, audited proof of Erdős Problem #686 from the current repository state, beginning with rational-point completeness for the rank-five k=5 genus-two curve.

**Architecture:** Preserve the kernel-checked k=5 proper-support theorem and the all-k canonical-owner infrastructure. Run the direct k=5 arithmetic-geometry lane as an independently certified exact-computation campaign, then close the remaining fixed odd rows and the large-k mass-distribution branch before assembling the terminal Lean theorem. Every external arithmetic result must have frozen source, machine-readable output, an offline hostile verifier, and an explicit statement of whether it is unconditional.

**Tech Stack:** Lean 4 and Mathlib, Python 3 exact arithmetic and pytest, Magma V2.29-8 exact arithmetic, FLINT-backed certificate generation, repository manifest/axiom/attestation tooling.

---

### Task 1: Bank the corrected full Mordell-Weil certificate

**Files:**
- Verify: `compute/campaign686/k5_genus2/magma_rank_certificate.m`
- Verify: `compute/campaign686/k5_genus2/rank_certificate.json`
- Verify: `compute/campaign686/k5_genus2/magma_rank_verify.py`
- Modify: `compute/campaign686/k5_genus2/curve_model.md`
- Modify: `compute/campaign686/gpt_pro_update_audit.md`
- Modify: `PROGRESS_Erdos686.md`
- Modify: `FRONTIER.md`

**Step 1: Run the offline certificate verifier**

Run:

```bash
python3 compute/campaign686/k5_genus2/magma_rank_verify.py
```

Expected: `PASS`, rank `5`, two-Selmer dimension `5`, determinant `-1`, and no target pullback among the 36 known points.

**Step 2: Run the online Magma reproduction**

Run:

```bash
python3 compute/campaign686/k5_genus2/magma_rank_verify.py --online
```

Expected markers:

```text
MW_INVARIANTS [ 0, 0, 0, 0, 0 ]
FINITE_INDEX true
PROVED true
RANK_BOUND 5
POINT_DIFFERENCE_DETERMINANT -1
```

**Step 3: Run the regression test**

Run:

```bash
python3 -m pytest -q compute/campaign686/k5_genus2/test_magma_rank_verify.py
```

Expected: one passing test.

**Step 4: Remove all stale rank-four and Selmer-dimension-four claims**

State exactly:

```text
J(Q) is isomorphic to Z^5.
The five supplied affine point differences form a basis because their
coordinate matrix in the proved Magma basis has determinant -1.
Rank, finite-index generation, and saturation are closed.
Rational-point completeness remains open.
```

### Task 2: Freeze the eight-cover decomposition

**Files:**
- Create: `compute/campaign686/k5_genus2/two_cover_pair_field.m`
- Create: `compute/campaign686/k5_genus2/two_cover_certificate.json`
- Create: `compute/campaign686/k5_genus2/two_cover_verify.py`
- Create: `compute/campaign686/k5_genus2/test_two_cover_verify.py`
- Modify: `compute/campaign686/k5_genus2/findings.md`

**Step 1: Write the verifier test**

The test must assert:

```python
result = verify_offline()
assert result["verdict"] == "PASS"
assert result["cover_count"] == 8
assert result["pair_resolvent_degree"] == 15
assert result["pair_resolvent_irreducible"] is True
assert result["factor_degrees"] == [2, 4]
assert result["known_point_class_counts"] == [2, 4, 4, 4, 4, 4, 6, 6]
assert result["elliptic_covers_constructed"] == 8
```

**Step 2: Run the test and confirm it fails before the verifier exists**

Run:

```bash
python3 -m pytest -q compute/campaign686/k5_genus2/test_two_cover_verify.py
```

Expected: import or missing-certificate failure.

**Step 3: Freeze exact Magma source**

The source must:

1. construct the monic sextic;
2. compute `TwoCoverDescent(C)`;
3. form and factor the pair-sum resultant;
4. select the irreducible degree-15 resolvent;
5. factor the sextic over the pair field into degrees 2 and 4;
6. map every two-cover class into the quadratic factor algebra;
7. construct all eight elliptic quartic covers;
8. report the distribution of the 34 known affine points among the eight classes.

**Step 4: Implement the offline hostile verifier**

Use exact `fractions.Fraction` arithmetic to verify the frozen resolvent coefficients, degree, class-count total, cover count, and certificate schema. Do not accept a Boolean-only transcript as the sole offline evidence.

**Step 5: Run offline and online verification**

Run:

```bash
python3 compute/campaign686/k5_genus2/two_cover_verify.py
python3 compute/campaign686/k5_genus2/two_cover_verify.py --online
python3 -m pytest -q compute/campaign686/k5_genus2/test_two_cover_verify.py
```

Expected: all eight covers constructed and all tests passing.

### Task 3: Determine each elliptic-cover Mordell-Weil group

**Files:**
- Create: `compute/campaign686/k5_genus2/elliptic_covers/cover_00.m`
- Create analogous files through: `compute/campaign686/k5_genus2/elliptic_covers/cover_07.m`
- Create: `compute/campaign686/k5_genus2/elliptic_covers/verify_cover_mw.py`
- Create: `compute/campaign686/k5_genus2/elliptic_covers/certificate.json`
- Test: `compute/campaign686/k5_genus2/elliptic_covers/test_verify_cover_mw.py`

**Step 1: Optimize the degree-15 number field once**

Use `OptimizedRepresentation` and freeze both the original and optimized defining polynomials together with the exact field isomorphism.

**Step 2: Minimize each elliptic model**

For each cover, freeze:

- the quartic model;
- the birational elliptic curve;
- the transformation maps in both directions;
- a known rational point;
- discriminant and conductor data sufficient to identify the model.

**Step 3: Compute unconditional Mordell-Weil data one cover per run**

For each cover, require:

```text
torsion subgroup
rank lower bound
rank upper bound
finite-index subgroup
saturation proof
generator coordinates
```

Do not bank GRH-conditional rank bounds as unconditional.

**Step 4: Verify every generator and transformation offline**

Check exact curve membership and both composition identities on generators and known pullback points.

**Step 5: Run each cover independently**

Run:

```bash
python3 compute/campaign686/k5_genus2/elliptic_covers/verify_cover_mw.py --cover 0 --online
```

Repeat through cover `7`. Expected: every cover has a proved full Mordell-Weil group or an explicitly isolated missing upper-bound/saturation obligation.

### Task 4: Exhaust the rational points on all eight covers

**Files:**
- Create: `compute/campaign686/k5_genus2/elliptic_covers/chabauty_cover_00.m`
- Create analogous files through: `compute/campaign686/k5_genus2/elliptic_covers/chabauty_cover_07.m`
- Create: `compute/campaign686/k5_genus2/rational_points_complete.json`
- Create: `compute/campaign686/k5_genus2/rational_points_complete_verify.py`
- Test: `compute/campaign686/k5_genus2/test_rational_points_complete_verify.py`

**Step 1: Attempt elliptic Chabauty cover by cover**

For every cover, use the proved Mordell-Weil group and the relevant rational-coordinate map. Freeze the prime set, residue classes, local exclusions, and returned points.

**Step 2: Fall back to a high-rank Mordell-Weil sieve where elliptic Chabauty does not close**

The sieve certificate must include:

- the full basis of `J(Q)`;
- reduction matrices modulo every selected good prime;
- the image of every rational residue class on `C(F_p)`;
- accumulated surviving cosets;
- a height bound or two-cover restriction making the finite search exhaustive.

**Step 3: Verify the final point list**

The offline verifier must prove:

```text
exactly 36 distinct weighted-projective points
all satisfy the genus-two equation
every cover output maps into this list
every listed point belongs to a certified cover output
the two points at infinity are included
```

**Step 4: Reject bounded-search-only evidence**

The certificate must expose an unconditional completeness marker. A statement such as `search_bound = 20000` with `proved_all = false` is a failing result.

### Task 5: Close the entire k=5 equation

**Files:**
- Create: `ErdosProblems/Erdos686K5RationalPoints.lean`
- Create or modify: `ErdosProblems/Erdos686K5Final.lean`
- Modify: `ErdosProblems.lean`
- Modify: `Audit.lean`
- Modify: `proofs.yaml`

**Step 1: Import the externally certified complete point list**

Represent the 36 points as exact weighted-projective rational data and kernel-check curve membership.

**Step 2: Prove the inverse-map audit**

For each of the 36 points, prove either:

- the inverse denominator vanishes at the already excluded point `(4,300)`;
- the inverse value is not a rational square;
- or its pullback fails `n >= 0` or `d >= 5`.

**Step 3: Assemble the k=5 no-solution theorem**

Compose:

```text
centered solution maps to C(Q)
C(Q) is the certified 36-point set
no certified point has a target integral pullback
```

Expected: an unconditional Lean theorem excluding all target k=5 solutions, not only the large-d proper-support range.

### Task 6: Complete proper support for k=7,9,11,13,15

**Files:**
- Extend the existing generated certificate families under `ErdosProblems/`
- Modify generators under `compute/campaign686/`
- Add per-k hostile audit directories under `compute/campaign686/`

**Step 1: Use valid parameter rows**

Use:

```text
k=7,9: existing positive-budget parameters
k=11: s=2, mu=112, r=1230
k=13: s=3, mu=171, r=2220
k=15: s=6, mu=272, r=4074
```

Increase `s` only when an exact basis-height audit demonstrates the need.

**Step 2: Generate and kernel-check local, elimination, Bezout, and endpoint modules**

Keep local modules, dense elimination rows, central exceptions, and endpoint assemblies split into bounded-memory files.

**Step 3: Run hostile audits**

Require zero `native_decide`, zero `sorry`, zero `admit`, all expected `.olean` files, and only the repository’s allowed axioms.

### Task 7: Eliminate complete support for k=7,9,11,13,15

**Files:**
- Create fixed-k residual-profile and diagonal-allocation modules under `ErdosProblems/`
- Create exact resultant and modular-certificate generators under `compute/campaign686/`

**Step 1: Enumerate residual profiles**

Use the canonical identities:

```text
r[j+1] * U[j+1] - r[j] * U[j] = 1
c[i+1] * s[i+1] * V[i+1] - c[i] * s[i] * V[i] = 1
A[j,i] divides d+i-j
```

**Step 2: Build exact global elimination certificates**

Prefer exact resultants, modular contradictions, effective S-unit reductions, CRT combinations, and adjacent-product separation. Do not return to normalized local jets.

**Step 3: Assemble a no-solution theorem for each fixed odd k**

Each theorem must independently pass its manifest, axiom, and hostile-verifier gates.

### Task 8: Close the large-k branch

**Files:**
- Create diagonal-capacity linear-program certificate modules
- Create near-permutation and diffuse-regime arithmetic modules
- Modify the terminal Erdős 686 assembly module

**Step 1: Formalize the exact linear relaxation**

For:

```text
w[j,i] = log(A[j,i]) / log((k+1)d)
```

replace analytic shorthand by exact rational inequalities with certified error terms.

**Step 2: Prove the stability dichotomy**

Show that every feasible mass distribution is quantitatively either near-permutation or diffuse.

**Step 3: Eliminate the near-permutation regime**

Prove that the necessary residual row multipliers exceed the factorial/small-prime mass budget.

**Step 4: Eliminate the diffuse regime**

Use simultaneous row/column equations and diagonal capacity to obtain a certified entropy loss, resultant contradiction, CRT obstruction, or support-interpolation saving.

### Task 9: Final repository assembly and attestation

**Files:**
- Modify: `ErdosProblems.lean`
- Modify: `Audit.lean`
- Modify: `proofs.yaml`
- Regenerate: `attestations.json`
- Modify: `PROGRESS_Erdos686.md`
- Modify: `FRONTIER.md`

**Step 1: Build the complete repository**

Run:

```bash
lake build
```

Expected: every target builds.

**Step 2: Run all hostile verifiers**

Run every campaign-specific verifier, including k=5 proper support, k=5 genus-two certificates, fixed odd rows, and large-k certificates.

**Step 3: Run manifest and axiom audits**

Require exact theorem-count agreement, no unapproved axioms, no `native_decide`, and no proof placeholders in the full Erdős 686 dependency cone.

**Step 4: Regenerate attestations and verify the diff**

Run the repository attestation generator, then:

```bash
git diff --check
```

Expected: no whitespace errors.

**Step 5: Declare completion only at the terminal theorem**

The campaign is fully solved only when the repository contains and audits an unconditional theorem covering every admissible `k`, `n`, and `d` in Erdős Problem #686.
