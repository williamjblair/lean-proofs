# Independent source-diff review — Erdős 399 Cambie Result

## Verdict: BLOCKED

The theorem, source fidelity, modular proof, focused build, axiom footprint,
manifest wiring, hashes, rights scope, and five-file diff all pass. The exact
feature state is blocked by one attestation-provenance overclaim:
`attestations.json` names
`ci:github-actions:williamjblair/lean-proofs` as `verifier_actor`, and the
generator describes the file as a CI attestation, but the exact feature branch
and commit have no GitHub Actions run. The repository workflow does not run on
ordinary feature-branch pushes; it runs on `main`, pull requests, or manual
dispatch. A deterministic local regeneration can establish byte consistency,
but it cannot establish that CI was the performer.

This review changes no proof, feature branch, source repository, Vela state,
Palomar state, production system, PR, issue, comment, or external discussion.

## Frozen objects and diff

- Base/current `origin/main`: commit
  `852ffa6b50f3501a66d7ffbc116d8ae9b749c60c`, tree
  `cde7ce73ec0453a5ee79d1cb0ab886f1c719bdea`.
- Feature: commit `b1214142e8130f56e6b6f6355ecea572bbbfe1bd`,
  tree `c010d4e69d1972e9f2d1a96a26277ccd151ff915`, sole parent the
  exact base.
- `origin/main...b1214142` changes exactly five declared files:
  `Audit.lean`, `ErdosProblems.lean`,
  `ErdosProblems/Erdos399Cambie.lean`, `attestations.json`, and
  `proofs.yaml` (`118` insertions, `1` deletion).
- The proof file SHA-256 independently reproduces
  `4edae3c97056d2d5409de10bcdd32d7492a81420738d16d213ee2b2ba11188be`.
  The worktree remained clean after the build; no generated/source mismatch
  was present.

## Frozen source and exact type

- Fresh shallow checkout of Formal Conjectures commit
  `9c4d5821819656af53c5473ded2116ea14a7ff1c`, tree
  `4ccf4dbcb68d8cc097551213ed13b184f910f110`.
- `FormalConjectures/ErdosProblems/399.lean` SHA-256 is exactly
  `79c50670ecacbd211abb8211814729c8e3aacc5c7055f3790842e381e53f36be`.
- The realized declaration elaborates as:

  ```text
  Erdos399.erdos_399.variants.cambie {n x y : ℕ} :
    x.Coprime y → 1 < x * y → n ! ≠ x ^ 4 + y ^ 4
  ```

  This is the complete FC target type at lines 75–76. It is only the coprime,
  plus-sign, fourth-power occurrence; it does not claim the general
  `x^k ± y^k` statement, the minus-sign counterexample, or another variant.

## Proof and domain review

- `fourth_mod_eight` reduces every natural to one of all eight residues and
  proves `z^4 % 8 = z % 2`; no parity class is omitted.
- For `4 ≤ n`, `8 ∣ n!`. Equality modulo eight forces both parity residues to
  zero, hence both `x` and `y` are even, contradicting `x.Coprime y`.
- For `n = 3`, `3! % 8 = 6`, while two fourth-power residues sum modulo eight
  to at most `2`; the equality is impossible.
- For `n ≤ 2`, the exact factorial bound `n! ≤ 2` plus the assumed equality
  forces `x ≤ 1` and `y ≤ 1`, contradicting `1 < x*y`.
- Thus all natural endpoints are covered, including `n = 0`, and the product
  hypothesis correctly excludes zero/degenerate bases. No hidden positivity,
  integer, or nonzero assumption is introduced.
- The new proof contains no `sorry`, `admit`, declared axiom, `unsafe`, or
  `native_decide` dependency.

## Focused clean reproduction

Pinned environment: Lean `4.29.1`; Mathlib manifest revision
`5e932f97dd25535344f80f9dd8da3aab83df0fe6`; `lake-manifest.json`
SHA-256
`f4c3e1fea9e745548c15b78b91015489277625c3dee15ab1ebe8bf6acf57b320`.

```text
lake exe cache get
lake build ErdosProblems.Erdos399Cambie
  PASS: 8248/8248 jobs, 34s

#check Erdos399.erdos_399.variants.cambie
  exact type shown above

#print axioms Erdos399.erdos_399.variants.cambie
  [propext, Classical.choice, Quot.sound]

bash scripts/check_manifest.sh
  PASS: manifest matches the audit (67 theorem(s))
```

The claimed axiom list is exact and contains neither `sorryAx` nor compiler
trust. `Audit.lean` audits the theorem, `ErdosProblems.lean` imports its module,
and `proofs.yaml` binds the exact theorem, FC path/commit/hash, producer commit,
candidate hash, evaluation commit, and rights statement. The declared
candidate SHA-256 `ea3d1599...afb6` and evaluation Case 5 disposition were also
reproduced from their exact Math commits. The repository has a root MIT
licence; FC target bytes are Apache-2.0, and the proof correctly scopes itself
as an independently retained MIT contribution.

The new attestation entry's theorem, path, proof hash, and axiom footprint all
match. Reconstructing the canonical manifest report from all 67 unchanged/base
entries plus the new independently checked footprint reproduces the committed
`verifier_output_hash`
`sha256:7aef30014408f5a6f980826686eeb8b2efb549825d2d6d5fa27d02f9962dff5e`.
The only blocker is performer provenance, not content consistency.

An additional non-gating integration-test invocation stopped on the ambient
local `vela 0.977.3`, while the repository checker pins `0.977.2`; its failures
occurred before the feature-specific fixture assertions and are not evidence
against this proof. No Vela binary or repository was changed.

## Minimal correction and handoff

No mathematical or Lean source correction is required. Before PASS, do one of:

1. run the repository `verify` workflow on exact commit
   `b1214142e8130f56e6b6f6355ecea572bbbfe1bd` and retain the green run that
   executes the attestation-regeneration equality check; or
2. change the attestation schema/generator and committed field to name the
   actual non-CI performer/projection, then regenerate and review that new
   commit.

Until one of those exact-state corrections exists, do not describe the
committed projection as performed by GitHub Actions. A green proof build alone
is Verification evidence, not acceptance, Decision, or Standing.
