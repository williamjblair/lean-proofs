# Erdős 686 matched-owner dichotomy checkpoint

> **For Codex:** execute on `main` without a worktree.  Preserve the existing
> fifth-quotient checkpoint and do not claim owner supply.

**Goal:** For a supplied exact large-base lower owner and its equation-forced
upper match, bank the explicit nonzero factorial-slope gap bound and close the
zero slope to a fixed second coefficient.

**Architecture:** Reuse the banked large-prime matching and local coefficient
interfaces.  Separate the nonzero residual by an integer absolute-value bound.
In the zero branch, normalize the factorial coefficients by their gcd, factor
the exact block polynomial by `Z^2`, prove its quadratic coefficient nonzero
from strict harmonic monotonicity, and conclude `Z` divides that fixed
coefficient.

**Verification:** Add exact boundary fixtures for `p=k`, both owner parities,
center harmonic zero, the row-22 and row-984 non-equation fixtures, and the
`d=1` telescopes.  Run focused Lean, exact arithmetic where used, full audit,
manifest, axiom, attestation, and project build gates.

### Task 1: Formalize the generic matched-owner algebra

- Create or extend a narrowly scoped `ErdosProblems/Erdos686MatchedOwner*.lean`
  module.
- Prove the sharp cofactor ratio and the nonzero residual gap bound.
- Prove the zero residual parameterization and `Z | c2` factorization.
- Prove `c2 != 0` uniformly using the exact signed factorial/harmonic
  coefficient order; do not leave this as a finite or analytic assertion.

### Task 2: Audit and integrate

- Add hostile findings and any exact verifier/tests needed for boundary data.
- Update `FRONTIER.md`, `PROGRESS_Erdos686.md`, the approach registry,
  `proofs.yaml`, `Audit.lean`, and regenerate `attestations.json`.
- State exactly that every supplied large-base owner obeys the dichotomy, but
  no theorem supplies such an owner in every remaining equation.
