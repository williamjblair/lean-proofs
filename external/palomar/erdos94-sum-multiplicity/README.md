# Erdős 94 external-check readiness snapshot

This directory is a non-publishing, source-owned snapshot for a potential
future Palomar mechanical check. It is not a submission, registration,
credential, status record, Vela object, or authority decision.

`Challenge.lean` contains the trusted statement and one deliberate Comparator
hole. `Solution.lean` delegates to the proved source declaration.
`config.json` compares exactly `erdos94_sum_multiplicity` and permits only
`propext`, `Quot.sound`, and `Classical.choice`. `formalization.yaml` records
scope, provenance, review, limitations, and exact pins. `DIGESTS.sha256`
records the frozen byte identities.

The substantive proof is commit
`423344341fbfdf4f8f684a302c5d05379125e7dc` in
`williamjblair/lean-proofs`; the repository promotion preserves that commit as
an ancestor rather than rewriting it. The snapshot uses Lean 4.29.1, Mathlib
`5e932f97dd25535344f80f9dd8da3aab83df0fe6`, and PrimeNumberTheoremAnd
`d7f9e2bfdcc7e34dfb9328b7494a6d424ff50c96`.

Local preparation, which does not contact Palomar:

```sh
lake update lean-proofs
lake build Challenge Solution
```

An authorized external checker can then run `leanprover/comparator` against
`config.json` with a toolchain-compatible `lean4export` and a real Linux
`landrun` sandbox. A macOS fake-landrun run is not an adversarial sandbox and
must be labeled accordingly. No one should submit this snapshot, register it,
or retain a bearer status URL without explicit user authorization at that
time.
