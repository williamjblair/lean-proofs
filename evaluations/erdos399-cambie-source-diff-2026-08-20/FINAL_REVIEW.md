# Final independent re-review — Erdős 399 Cambie Result

## Verdict: PASS

The corrected immutable feature head passes the bounded source-diff review.
The mathematical theorem and proof were already correct at the prior blocked
review; commit `3104ee7112778f78390adda3a37aca01b195f4d5` removes the sole
attestation-performer overclaim without changing theorem or proof bytes. This
is evidence that the exact bounded Lean result is ready for its separate
handoff. It is not Formal Conjectures source-owner acceptance, scientific
acceptance, a Vela Decision, or Standing.

## Frozen objects and correction

- Feature commit: `3104ee7112778f78390adda3a37aca01b195f4d5`;
  tree `e72217710af310f70f08996b723ea347574e69b6`; sole parent
  `b1214142e8130f56e6b6f6355ecea572bbbfe1bd`.
- The correction delta is exactly three files: modified
  `attestations.json`, modified `scripts/emit_attestations.py`, and new
  `tests/test_emit_attestations.py` (69 insertions, 18 deletions).
- Schema `lean-proofs.attestations.v0.2` now separately records
  `verification_method: lean_kernel` and
  `evidence_generator: local:openai-codex`. The generator calls the file a
  deterministic local evidence projection, expressly disclaims a CI
  performer/outcome claim, and says hosted outcomes belong in their own run
  receipts.
- The generator fixes both values as constants; neither CI environment nor
  runtime input can rewrite the generator actor. Two focused tests passed and
  require schema v0.2, the exact local generator, absence of
  `verifier_actor`/`verifier_method`, and absence of a GitHub Actions actor.
  Regression to the former unsupported actor would therefore require a
  reviewed source/test change rather than occur through execution context.
- Relative to frozen base `852ffa6b50f3501a66d7ffbc116d8ae9b749c60c`,
  the corrected head changes the five previously reviewed result files plus
  the emitter and its new test: seven files total. The original five-file
  denominator and all prior mathematical findings are preserved.

## Hosted run is partial evidence only

GitHub Actions run `32407303167` is a failed manual run on parent
`b1214142e8130f56e6b6f6355ecea572bbbfe1bd`, not a run on corrected head
`3104ee71`. It is a partial exact-parent receipt for the unchanged proof bytes:

- checkout, full Lean build, axiom audit, manifest check, and published Vela
  Core `0.977.2` build passed;
- `Erdos399.erdos_399.variants.cambie` was reported with axioms
  `[propext, Classical.choice, Quot.sound]`;
- native integration then failed with
  `Vela native integration: FAIL: toolchain or proof index count drift`;
- `Proof attestations are in sync` was skipped.

The run is neither a green workflow nor an attestation-regeneration receipt.
Its failure predates the attestation step and does not contradict the
independent local byte comparison below.

## Full-head source and proof evidence

- Formal Conjectures commit
  `9c4d5821819656af53c5473ded2116ea14a7ff1c` has tree
  `4ccf4dbcb68d8cc097551213ed13b184f910f110`. Exact file
  `FormalConjectures/ErdosProblems/399.lean` hashes to
  `79c50670ecacbd211abb8211814729c8e3aacc5c7055f3790842e381e53f36be`.
- The realized declaration elaborates exactly as
  `Erdos399.erdos_399.variants.cambie {n x y : ℕ} : x.Coprime y →
  1 < x * y → n ! ≠ x ^ 4 + y ^ 4`. It is the complete FC `cambie`
  occurrence and only the coprime plus-sign fourth-power occurrence.
- `ErdosProblems/Erdos399Cambie.lean` remains byte-identical to the prior
  review and hashes to
  `4edae3c97056d2d5409de10bcdd32d7492a81420738d16d213ee2b2ba11188be`.
- All domain cases remain covered. For `4 ≤ n`, divisibility by eight plus
  `z^4 % 8 = z % 2` forces both bases even, contradicting coprimality. For
  `n = 3`, residue six cannot be a sum of two fourth-power residues. For
  `n ≤ 2` (including `n = 0`), the factorial bound forces both bases at most
  one, contradicting `1 < x*y`. The residue lemma checks all eight base
  classes. No hidden positivity, nonzero, or integer-domain assumption is
  added.
- The proof contains no `sorry`, `admit`, declared axiom, `unsafe`, or
  `native_decide`; exact `#print axioms` is
  `[propext, Classical.choice, Quot.sound]`.
- `Audit.lean`, `ErdosProblems.lean`, `proofs.yaml`, and
  `attestations.json` consistently name the exact theorem, module, FC commit,
  FC source hash, proof hash, and rights scope. The root MIT license and the
  Apache-2.0 FC source notice are not conflated; the proof is described as
  independently retained MIT bytes.

## Clean pinned reproduction

A fresh detached clone was checked out at the exact commit/tree. Its pinned
environment is Lean `4.29.1`, Mathlib revision
`5e932f97dd25535344f80f9dd8da3aab83df0fe6`, and
`lake-manifest.json` SHA-256
`f4c3e1fea9e745548c15b78b91015489277625c3dee15ab1ebe8bf6acf57b320`.

```text
python3 -m unittest tests.test_emit_attestations
  PASS: 2 tests
lake build ErdosProblems.Erdos399Cambie
  PASS: 8248/8248 jobs
lake build ErdosProblems
  PASS: 8347/8347 jobs
#check Erdos399.erdos_399.variants.cambie
  PASS: exact FC type above
#print axioms Erdos399.erdos_399.variants.cambie
  PASS: [propext, Classical.choice, Quot.sound]
bash scripts/check_manifest.sh
  PASS: manifest matches the audit (67 theorem(s))
python3 scripts/emit_attestations.py
  PASS: wrote 67 attestations
git diff --exit-code -- attestations.json
  PASS: regenerated bytes equal committed bytes
```

The regenerated v0.2 document retains verifier-output hash
`sha256:7aef30014408f5a6f980826686eeb8b2efb549825d2d6d5fa27d02f9962dff5e`
and Cambie proof/axiom fields exactly. The clean clone returned to an empty
tracked/untracked status after the temporary exact-type check was removed.

## Handoff

No correction remains within this review scope. The smallest next step is a
separate integration or source-owner handoff that cites exact feature commit
`3104ee71` and this PASS, while accurately retaining hosted run `32407303167`
as failed partial evidence only. Do not infer acceptance, Decision, or
Standing from this review.
