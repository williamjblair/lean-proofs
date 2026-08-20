# Erdős 1074 finite-computation evidence

This directory retains the bounded executable certificate used to discover
and independently replay the EHS membership classification for `m = 0..17`.
It is computational evidence only: it is not formally verified, not a Lean
proof, and does not establish any claim beyond the displayed finite run.

The program and stdout are byte-for-byte copies from Math branch
`codex/docker-result-batch-3-conversion-2026-08-20` at commit
`beb0b4e6e68a4646c0d7da96597e1f175e2a8d22`, tree
`c4a103e2917c98835cbdeb1f0c573c28c91d2f52`, packet
`results/2026-08-20-docker-batch-3-conversion/CASE-4-ERDOS-1074.md`.
The certificate uses only Python's standard library and runs offline.

- `certificate.py`: SHA-256
  `aa18c73e7d44b4b45210256370f4d04fce97b5239a37caf7df55be7b223d0637`
- `certificate.stdout.txt`: SHA-256
  `32dbde16b9754e8d3c8419b93bfd95f766e7930967103a1a3b80c8c11e1a0685`
- `ErdosProblems/Erdos1074EHSNumbers.lean`: SHA-256
  `4088fd824ad2dffe1cec725f42a08a2abe02fc87f63c4c86ef7d29d635faf046`
- focused pinned build stdout: `lean-build.stdout.txt`, produced by
  `lake build ErdosProblems.Erdos1074EHSNumbers`
- focused axiom output: `axioms.stdout.txt`, produced by an exact-type bridge
  importing the theorem and running `#print axioms`
- Lean toolchain file SHA-256:
  `7dc000621e0046d1aada809e2b7177e64454645cf4c741e9daaf79c99ec2e7a2`
- Lake manifest SHA-256:
  `f4c3e1fea9e745548c15b78b91015489277625c3dee15ab1ebe8bf6acf57b320`
- exact Formal Conjectures source: commit
  `9c4d5821819656af53c5473ded2116ea14a7ff1c`,
  `FormalConjectures/ErdosProblems/1074.lean`, SHA-256
  `72b74c90c3fbdf66fedcd744d6c90da05fdfc7e87673a016787ae4586c705c45`

The certificate bytes in this directory are retained under the adjacent MIT
`LICENSE`. The Formal Conjectures source is not copied here and remains
Apache-2.0. The independent Lean proof is separately checked in
`ErdosProblems/Erdos1074EHSNumbers.lean` under the repository MIT license.

No Formal Conjectures adoption, source-owner endorsement, Vela Check,
Decision, Standing, Palomar submission, or scientific acceptance is implied.
