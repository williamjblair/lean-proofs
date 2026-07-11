# Erdős 686 lattice-sign attack plan

**Goal.** Determine whether the exact three-quotient lattice identity can turn
short-window signs into a target-size contradiction, without modifying the
frozen quotient package.

## Work items

1. Reconstruct, for all 1,035 target owner triples, the oriented primitive
   cross-product weights, the nonzero correction coefficient, and the exact
   quotient sign thresholds
   `lambda = 20 E delta / C + 12 D delta / (C d)`.
2. Certify over every `d >= 10^120` that unequal threshold orderings cannot
   change; handle the reflected equal-root triples separately and enumerate
   both open sign cells and exact zero boundaries.
3. Test whether every weighted lattice term has one sign.  Record exact mixed
   coefficient counterfixtures and exact realized fourth-lift counterfixtures
   when cancellation survives.
4. Turn every genuine one-sided cell into an explicit component/gap bound,
   compare it with `10^120`, and isolate the remaining mixed-cancellation or
   single-zero cases as one quantified size lemma.
5. Formalize only the generic one-sided size bridge in Lean, audit its axioms,
   and verify the exact scan with focused tests.

## Acceptance checks

- Exact rational arithmetic only; no floating-point sign decisions.
- All 1,035 triples counted exactly, including 27 zero weight components,
  reflected centers, `p = 2`, `p = 3`, and the two `d = 1` telescopes.
- Separate coefficient counterfixtures from full local fourth-lift fixtures.
- `pytest`, `py_compile`, focused `lake build`, axiom audit, forbidden-token
  scan, and `git diff --check` all pass.
