# Erdős 686 multi-owner extension hostile-audit plan

**Scope.** Audit the frozen MultiOwnerExtension producer only.  Do not modify
the producer, its verifier, tests, findings, or plan.

## Tasks

1. Verify all five frozen SHA-256 digests before importing or reproducing any
   producer result.
2. Re-derive the signed second/third finite-family formulas independently and
   test non-prefix, permuted, reflected, center, negative-component, `g=0`,
   `p=2`, and `p=3` fixtures.
3. Independently enumerate every target subset of size `4..k`; reproduce
   subset/slope/collision counts, exact extrema, and actual `C,D,Delta` bounds.
4. Audit the target zero-exclusion inequality at every boundary: `t=4`,
   `d=10^120`, negative coefficients, zero `D`, centers, and reflected slope
   collisions.
5. Reconstruct the 130-digit CRT route falsifier without importing producer
   functions; verify all local/composed congruences, block failure, and exact
   short-window failure.
6. Independently import the Lean module, restate load-bearing algebra/size
   bridges, check all public theorem signatures and axioms, and report any
   claim whose prose exceeds its hypotheses.

## Acceptance

- Exact integer/rational arithmetic only.
- Producer files remain byte-identical.
- Separate hostile verifier, tests, Lean importer, and findings.
- `pytest`, `py_compile`, producer tests, hostile Lean importer, producer Lean
  build, axiom gate, forbidden-token scan, and whitespace check pass.
