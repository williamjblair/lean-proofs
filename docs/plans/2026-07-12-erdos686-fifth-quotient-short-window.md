# Erdős 686 fifth-quotient short-window checkpoint

> **For Codex:** execute this plan on `main`; do not create a worktree.  Treat every
> generated identity or finite scan as untrusted until independently reproduced,
> adversarially audited, Lean-checked, and attested.

**Goal:** Bank the equation-facing fourth/fifth-quotient size and nonvanishing
consequences for all 1,008 nonreflected exact three-bucket geometries at
`d >= 10^1000`, without claiming that the remaining simultaneous nonzero branch
is closed.

**Architecture:** Extend the existing short-window/fifth-lift modules with the
symbolic quotient bounds and the exact elimination identity.  Reproduce every
finite coefficient/sign claim in a deterministic exact-arithmetic script and
record the dependency tree plus hostile fixtures.  Keep the sixth-order/global
coupling research separate from the banked checkpoint unless it yields a complete
new theorem.

**Tech Stack:** Lean 4/mathlib, Python integer and `fractions.Fraction` arithmetic,
pytest, repository manifest/axiom/attestation gates.

---

### Task 1: Reproduce the 3,024-position arithmetic ledger

**Files:**
- Create: `compute/campaign686/fifth_quotient_short_window_verify.py`
- Create: `compute/campaign686/test_fifth_quotient_short_window_verify.py`
- Create: `compute/campaign686/fifth_quotient_short_window_findings.md`
- Create: `compute/campaign686/fifth_quotient_short_window_hostile_audit.md`

1. Recompute the exact `W_s` and `V_s` constants for every cyclic position in
   all 1,008 nonreflected triples.
2. Check the homogeneous `J_s` leading form on adjacent rational root brackets,
   including monotonicity and endpoint signs.
3. Derive and verify a uniform lower-degree coefficient majorant strictly below
   `10^46`, and replay the 1,004-digit Hensel fixture as a congruence-only
   falsifier.
4. Add focused pytest assertions for counts, extrema, boundary rows, and exact
   fixture remainders.

### Task 2: Formalize the symbolic quotient consequences

**Files:**
- Modify: `ErdosProblems/Erdos686FifthLocalLift.lean`
- Modify or create a narrowly scoped generated certificate module only if the
  3,024 finite sign ledger is too large for the symbolic module.

1. Prove the exact `z -> w` short-window bound with all positivity/nonzero side
   conditions explicit.
2. Prove the `N_s=27*w_s+M_s*R1_s*g^4` bound and the consequence
   `P_s^2 < V_s*g^4*d` under normalized divisibility and `N_s != 0`.
3. Prove the exact elimination identity `d^4*P_s*N_s=g^4*J_s(X_s,d)`.
4. Attempt an ordinary-kernel finite sign certificate.  If that wrapper is not
   practical in this checkpoint, keep the 3,024-position nonvanishing ledger
   explicitly exact-computational and do not advertise it as Lean-banked.

### Task 3: Audit, manifest, and publish the checkpoint

**Files:**
- Modify: `FRONTIER.md`
- Modify: `PROGRESS_Erdos686.md`
- Modify: `proofs.yaml`
- Modify: `Audit.lean`
- Regenerate: `attestations.json`

1. State exactly that exact arithmetic finds all 3,024 fifth numerators
   nonzero, that this finite claim is not Lean-banked without a kernel wrapper,
   and that the 1,008 simultaneous mixed-sign systems remain open.
2. Record why cyclic multiplication, the mixed `w`-lattice, and congruence-only
   sixth iteration do not yet imply a cutoff.
3. Run focused pytest and direct Lean checks, then `lake build ErdosProblems`,
   `lake env lean Audit.lean`, manifest, axiom, attestation, forbidden-token, and
   `git diff --check` gates.
4. Commit and push the verified checkpoint to `main` only after every gate passes.
