# Erdős #686: k=5 proper-support hostile audit

Status: **PASS**.

The independent verifier reads the emitted Lean sources directly and imports
no certificate generator. It checks:

- all 25 puncture endpoints;
- 1,272 split local-row modules, including 120 central five-section modules;
- 477 dense elimination leaves and 53 thin assemblies;
- all 25 Bézout kernels and non-common-zero assemblies;
- exact endpoint coverage in the global 25-way case split;
- absence of `native_decide`, `sorry`, and `admit`;
- presence of every compiled `.olean`;
- the actual axiom footprint of
  `no_k5_tail_solution_of_proper_support`.

The verifier passed with:

```text
25 puncture endpoints
1,272 local-row modules
477 dense elimination leaves
53 thin elimination assemblies
25 Bézout kernels
1,954 source files in the checked manifest
source manifest SHA-256:
  5c9a236db0b7eae01248c674e8b83ef43cbbcbb6a3822864aeaa543ecb4e6ba0
axioms:
  propext, Classical.choice, Quot.sound
```

The focused pytest also passes `1 test`. The repository-wide build,
807-theorem manifest audit, 1,286-declaration axiom gate, and regeneration of
807 attestations all pass.

Reproduce with:

```bash
python3 compute/campaign686/k5_proper_support_audit/k5_proper_support_hostile_verify.py
python3 -m pytest -q \
  compute/campaign686/k5_proper_support_audit/test_k5_proper_support_hostile_verify.py
```
