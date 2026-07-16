# Erdős 686 Secant-Pairing and Tangent-Defect CRT Audit Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Audit, formalize, certify, and bank the direct large-\(k\) secant-pairing and tangent-defect CRT package without weakening the active \(k=5\) lane.

**Architecture:** Build the package in dependency order: generic exact secant arithmetic, zero-secant geometry, an explicit finite pairing algorithm, the product bound, interpolation and tangent-defect congruences, then exact threshold certificates. Every accepted interface is added to the ordinary Lean audit surface before any tail theorem is claimed.

**Tech Stack:** Lean 4.29.1, mathlib, Python standard-library exact integers and `fractions.Fraction`, repository manifest/axiom/attestation scripts.

---

### Task 1: Source and artifact audit

**Files:**
- Read: `/Users/williamblair/.codex/attachments/1f82548d-fb9e-4e42-b260-dabfc4dae6a6/pasted-text.txt`
- Create: `compute/campaign686/matching_tail_import_report.md`

1. Read the attachment to EOF and compute its SHA-256.
2. Inventory every linked certificate and verifier; record missing attachments as unavailable rather than accepted.
3. Separate claims into accepted, repaired, rejected, and unresolved.

### Task 2: Two-owner secant kernel

**Files:**
- Create: `ErdosProblems/Erdos686SecantPairing.lean`
- Modify: `Audit.lean`
- Modify: `proofs.yaml`

1. Define the signed secant form over `ℤ`.
2. Prove each owner modulus divides the form using the two incident divisibilities.
3. Combine the two divisibilities using explicit coprimality.
4. Run `lake env lean ErdosProblems/Erdos686SecantPairing.lean`.

### Task 3: Zero-secant geometry

**Files:**
- Modify: `ErdosProblems/Erdos686SecantPairing.lean`

1. Prove the exact ratio identity from a zero secant without division.
2. Prove equal signs, unit offset gap, and row gap greater than `(k-1)/2` from the audited scale inequality.
3. Prove that zero-secants form a graph of maximum degree one.
4. Run the focused Lean build.

### Task 4: Controlled pairing

**Files:**
- Modify: `ErdosProblems/Erdos686SecantPairing.lean`
- Create: `compute/campaign686/secant_pairing_certificate.json`

1. Define the deterministic adjacent-pair scan.
2. Replace each forbidden adjacent pair together with the following pair by two cross-pairs; handle a final forbidden pair by repairing with its preceding retained pair.
3. Prove the scan decreases the number of unprocessed vertices at every recursive call.
4. Prove pair disjointness, parity coverage, nonzero secants, and total offset-gap at most twice the support span, hence at most `4*(k-1)`.
5. Run the focused Lean build and exact verifier.

### Task 5: Product upper bound

**Files:**
- Modify: `ErdosProblems/Erdos686SecantPairing.lean`

1. Multiply the pairwise secant divisibilities using pairwise coprimality.
2. Apply exact AM-GM in a denominator-cleared form.
3. Account for the optional unpaired owner exactly.
4. Run the focused Lean build.

### Task 6: Matching interpolation and tangent defect

**Files:**
- Create: `ErdosProblems/Erdos686TangentDefectCRT.lean`
- Create: `compute/campaign686/tangent_defect_crt_certificate.json`

1. Define the integer Lagrange interpolation polynomial `Phi`.
2. Prove its node values and `M ∣ L*(n+d)+Phi(-n)`.
3. Prove the Taylor identity modulo each owner square without dividing by a node value.
4. Derive the exact tangent-defect square divisibility and CRT for `U`.
5. Run the focused Lean build and exact verifier.

### Task 7: Exact threshold

**Files:**
- Create: `compute/campaign686/matching_tail_threshold.json`
- Create: `compute/campaign686/verify_matching_tail.py`

1. Compute exact `pi(k)` with a certified sieve.
2. Compare lower and upper bounds after clearing all rational denominators; do not use logarithms as acceptance conditions.
3. Scan all `k` below the candidate threshold and prove a symbolic monotonic tail beyond it.
4. Record the smallest certified `K0`, boundary witnesses, and SHA-256 hashes.
5. Run `python3 compute/campaign686/verify_matching_tail.py`.

### Task 8: Bank and publish

**Files:**
- Modify: `Audit.lean`
- Modify: `proofs.yaml`
- Modify: `PROGRESS_Erdos686.md`
- Modify: `attestations.json`
- Modify: `compute/campaign686/matching_tail_import_report.md`

1. Add every accepted headline theorem to the manifest and audit.
2. Run focused Lean builds, `lake env lean Audit.lean`, `bash scripts/check_manifest.sh`, and `bash scripts/check_axioms.sh`.
3. Regenerate attestations and rerun both exact verifiers.
4. Commit and push the verified checkpoint directly to `main`.

