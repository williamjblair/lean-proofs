# Hostile audit: center/reflected fifth specialization

## Dependency tree

1. Reconstruct `C,D,E,F,G` from the signed local cofactor product.
2. Substitute center parity (`D=F=0`) and reflected offsets `(r,-r)` into the
   reduced fifth coefficient.
3. Expand both endpoint third obstructions and take their residual-weighted
   determinant.
4. Use the exact three-residual product identity to turn a zero inner factor
   into one explicit cubic.
5. Prove the cubic nonzero from the exact rational ratio lower bound and the
   row residual ceiling.
6. Convert endpoint-square divisibility into a strict size bound.
7. Combine it with the center cubic and exact aggregate-loss bounds.

## Per-node verdict

1. **Pass.** The verifier rebuilds all coefficients; it does not import a
   frozen coefficient list for the calculation.
2. **Pass, negative result.** In every pair the constant and quadratic terms
   are exactly zero, while the linear slope is nonzero.  This is not counted
   as a closure.
3. **Pass.** More than 100,000 signed exact fixtures reproduce the determinant
   identity.  Lean proves the symbolic identity and `Q^2R^2` divisibility.
4. **Pass.** Lean proves the exact product identity and cancellation of `g^2`
   under the quantified hypothesis `g != 0`.
5. **Pass.** All 27 coefficient certificates are ordinary kernel arithmetic;
   the bound is the explicit inequality in the findings, not an
   "essentially positive" assertion.
6. **Pass.** Lean proves the `natAbs` divisor-to-size conversion and the full
   archimedean bound.
7. **Pass for 12 pairs, fail for 15.** The exact cutoff comparison is emitted
   pair by pair.  The failure is not rounded away: the first failed exact
   cutoff is larger than `10^120`.

## Boundary and falsification checks

- Both reflected orientations are counted: 27 pairs are 54 views.
- `r=1` and every outer boundary `r=(k-1)/2` are included.
- Signed determinant fixtures include negative `t,g,d,X` as an algebra audit.
- The target theorem uses `d >= 10^120`, not an asymptotic `d`.
- The fifth coefficient is recorded as linear, not mislabeled constant.
- The 15 surviving pairs are stated explicitly; no sixth-order or private
  uniformity lemma is hidden behind the result.

## Kernel gate

`Erdos686ReflectedThreeBucketDeterminant.lean` reports only
`[propext, Classical.choice, Quot.sound]` on its public theorem surfaces.  It
contains no `sorry`, `admit`, new axiom, `native_decide`, or theorem-strength
placeholder.

The later `10^1000` supplied-slice upgrade is audited separately in
`compute/campaign686/reflected_three_bucket_tail1000_hostile_audit.md`; this
historical audit retains its correct `10^120` 12-pair PASS / 15-pair FAIL.
