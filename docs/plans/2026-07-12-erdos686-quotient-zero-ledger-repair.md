# Erdős 686 Quotient-Zero Ledger Repair Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Replace the stale short-window quotient-zero campaign ledger with the already-proved equation-facing fact that every target three-bucket third quotient is nonzero, while independently recording the exact historical `10^1000` cutoff computation without treating it as progress on the live all-nonzero branch.

**Architecture:** Add one small corollary to the exact-ratio third-sign module: a nonzero composed third obstruction represented as `P^2*z` forces `z != 0`, cyclically at all three owners.  Separately reconstruct all 2,603 historical two-zero placements with exact integers and the upgraded cutoff, including the sharp 131-digit boundary.  Preserve the frozen historical quotient package and add an additive audit that explains why its zero branches are obsolete.  Update only current campaign surfaces; do not rewrite frozen findings or claim closure of any all-nonzero cell.

**Tech Stack:** Lean 4 / Mathlib, exact Python integers, pytest, repository manifest and axiom gates.

---

### Task 1: Add the equation-facing quotient-nonzero corollary

**Files:**
- Modify: `ErdosProblems/Erdos686ExactRatioThirdSign.lean`

**Step 1: State the exact quotient interface**

Extend `exactRatio_target_three_bucket_all_third_obstructions_nonzero` with a corollary taking the same target-row, owner, exact decomposition, residual, and block-equation hypotheses together with three identities

```lean
T_i = (P : ℤ)^2 * zP
T_j = (Q : ℤ)^2 * zQ
T_l = (R : ℤ)^2 * zR.
```

Conclude `zP != 0 ∧ zQ != 0 ∧ zR != 0`.  Each branch must substitute a supposed zero quotient into the corresponding identity and contradict the existing nonzero-obstruction theorem.  Do not assume primality or divide by a component.

**Step 2: Compile and inspect axioms**

Run the module directly and require the new public theorem to report only the allowed kernel axioms.  Reject `native_decide`, `sorry`, `admit`, and new axioms.

### Task 1A: Normalize the fifth lift and freeze the failed-resultant certificate

**Files:**
- Modify: `ErdosProblems/Erdos686FifthLocalLift.lean`

**Step 1: Split the reduced fifth coefficient by gap degree**

Define the exact linear and quadratic coefficient polynomials `R1` and `R2` and prove universally

```text
R5(d) = 27*K4 + d*R1 + d^2*R2.
```

The proof must be a direct polynomial identity over `ℤ`, not a finite table check.  In particular export `R5(0)=27*K4` as the load-bearing dead-route certificate.

**Step 2: Prove the normalized fourth-quotient lift**

If `d=P*M`, the reduced fourth numerator is `P*q`, and the reduced fifth numerator is divisible by `P^2`, prove

```text
P | 27*q + M*R1*g^4.
```

Also prove the converse reconstruction if it packages cleanly: the normalized quotient congruence together with the fourth quotient identity implies the reduced fifth square divisibility.  Do not call this a component bound or cyclic resultant; the new quotient `q` is unbounded and is not controlled by the third-quotient lattice.

**Step 3: Compile and inspect axioms**

Run the fifth-lift module directly and require the same allowed-axiom surface.

### Task 2: Reconstruct the historical tail-1000 cutoff exactly

**Files:**
- Create: `compute/campaign686/short_window_quotient_tail1000_verify.py`
- Create: `compute/campaign686/test_short_window_quotient_tail1000_verify.py`

**Step 1: Independently enumerate all placements**

Reconstruct the local coefficient polynomial, reduced fourth coefficient, primitive three-row lattice weights, row loss bounds, coefficient LCM, and majorant without importing the frozen producer.  Enumerate the 2,603 noncentral two-zero placements in rows `5,7,9,11,13,15`.

Independently reconstruct the reduced fifth coefficient and assert the universal decomposition on a broad exact signed fixture grid plus all 6,210 ordered target views.  Freeze that the linear coefficient is nonzero in every target view and that the quadratic coefficient vanishes only in the 54 oriented center/reflected views.  These checks reproduce the Lean identities but do not replace their proofs.

**Step 2: Freeze exact counts and the sharp cutoff**

Assert:

```text
row totals: 18, 75, 196, 405, 726, 1183
zero-weight contradictions: 2, 3, 4, 5, 6, 7
numeric closures at 10^1000: 2,576
all closures at 10^1000: 2,603
historical additions beyond 10^120: exactly 282, all in row 15
```

For each nonzero-weight case compute

```text
Dmin = isqrt(floor(M/W)) + 1,
M = L^2 * |Gamma| * G_k^12,
```

and assert `W*(Dmin-1)^2 <= M < W*Dmin^2`.  Freeze the global 131-digit maximum, its two reflected attaining placements, the row-wise digit ceilings, and the facts that `10^130` leaves exactly two cases while `10^131` closes all.

**Step 3: Run focused exact reproduction**

Run the standalone verifier, pytest with caches disabled, and `py_compile`.  Use no floating point or logarithmic comparison for a load-bearing inequality.

### Task 3: Adversarially audit the logical status

**Files:**
- Create: `compute/campaign686/short_window_quotient_tail1000_findings.md`
- Create: `compute/campaign686/short_window_quotient_tail1000_hostile_audit.md`

**Step 1: Separate historical arithmetic from the live equation branch**

Give a dependency tree showing that the finite cutoff scan is exact but mathematically superseded: the block equation and exact ratio window already prove all three third obstructions nonzero at `d >= 10^120`, and the new quotient corollary converts that statement to quotient language.  State that no zero-quotient cutoff is used to prove the live all-nonzero residual.

**Step 2: Record both failed next-pass routes**

Audit the tempting all-owner reflected-pair inference

```text
q_i | H_i, q_j | H_j, gcd(q_i,q_j)=1  =>  q_i*q_j | H_i-H_j
```

as false, with the exact `k=5,n=25177,d=6790,g=97` fixture and the residue modulo `49`.  Also record the exact fifth-order identity `R5(0)=27*K4`: after the `d^2` term drops modulo `P^2`, the surviving statement contains the unbounded fourth quotient and does not yield a fixed resultant.

**Step 3: Replay boundary cases**

Include center zero coefficients, the 27 reflected zero-weight cases, unit buckets, bases `2` and `3`, the two `d=1` telescopes, and the 121/130-digit Hensel/CRT fixtures.  State precisely which hypotheses place each outside the live theorem.

### Task 4: Repair current campaign surfaces

**Files:**
- Modify: `FRONTIER.md`
- Modify: `PROGRESS_Erdos686.md`
- Modify: `compute/campaign686/approach_registry.md`
- Modify: `compute/campaign686/audit.md`
- Modify if registered by the manifest: `ErdosProblems.lean`, `Audit.lean`, `proofs.yaml`
- Regenerate: `attestations.json`

**Step 1: Remove stale live-gap claims**

Replace claims that one-zero, center-zero, or 282 row-15 two-zero placements remain open with the exact current statement: every quotient-zero branch is equation-facing impossible from `d >= 10^120`; at `d >= 10^1000` the live exactly-three census is 1,008 nonreflected, all-three-nonzero, sign-mixed triples after the 27 reflected triples are removed.  Keep the historical `10^120` finite counts labeled as historical diagnostics.

**Step 2: State the unchanged genuine gap**

Do not claim `OddThueTail1000Hypothesis`, Target 1, `FinalResidual686Hypothesis`, or Erdős #686.  The remaining odd arm is the arbitrary-owner joint-nonzero short-window problem; the large-row smooth residual is unchanged.

### Task 5: Run gates, commit, and push main

**Step 1: Run focused gates**

Run exact Python reproduction, focused pytest, direct Lean compilation, the new audit importer if added, and `git diff --check`.

**Step 2: Run repository gates**

Run manifest validation, the allowed-axiom gate, deterministic attestation emission, and a proportionate Lean build covering every changed import surface.  If the manifest changes, run the full repository build.

**Step 3: Publish the banked correction**

Commit on `main`, push `origin/main`, verify exact local/remote commit equality and a clean worktree, and report that this checkpoint repairs the attack registry but does not complete the active #686 goal.
