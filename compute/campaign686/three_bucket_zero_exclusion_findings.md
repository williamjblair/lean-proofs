# Erdős 686 target-row zero-obstruction exclusion

Status: **row-quantified Lean wrapper proved; hostile audit pending.**

The generic three-bucket LCM checkpoint proved that a vanishing composed
second obstruction forces

```text
d | L*g^4,
```

but left the target-row coefficient bounds outside Lean.  The new module
`ErdosProblems/Erdos686ThreeBucketZeroExclusion.lean` closes exactly that
formal interface.

## Exact statement

For a target row `k in {5,7,9,11,13,15}`, three distinct owners `i,j,l`,
pairwise-coprime positive cleaned components `P,Q,R`, and

```text
d = g*P*Q*R,                 1 <= g <= 18,914,575,680,
P | O_i, Q | O_j, R | O_l,
P^2 | F_i, Q^2 | F_j, R^2 | F_l,
```

Lean proves that `d>=10^120` implies `O_i,O_j,O_l` are all nonzero.  Here
`O_s` and `F_s` are the already-banked three-bucket second and third
obstructions.

## Dependency tree

```text
assume O_l = 0
|
+- eliminate O_l from O_i and O_j
|  +- P | A*g^2
|  `- Q | B*g^2
+- use F_l with O_l=0
|  `- R^2 | K*g^2*d
+- finite target-row certificate
|  +- 0 < A,B < 10^30
|  `- 0 < K < 10^18
+- pairwise-coprime LCM packing
|  `- d | A*B*K*g^4
`- rounded numeric cutoff
   `- (10^30)^2*10^18*18,914,575,680^4 < 10^120
```

The same theorem is applied cyclically to exclude zeros at `i` and `j`.

## Exact finite reproduction

`three_bucket_zero_exclusion_verify.py` reconstructs every Taylor
coefficient from the defining affine product.  It checks all `6,210`
ordered triples of distinct owners.  The exact maxima are

```text
max |A| = 174368230097267947732992000,
max |K| = 12847056696714240,
```

both strictly below the rounded Lean ceilings.  The rounded final majorant
is below `10^120` with integer quotient margin `7`.

## Scope boundary

This proves only that the three composed second obstructions are nonzero in
a target-size exactly-three-owner tuple.  It does not exclude the nonzero
branch, the four-or-more-owner branch, or the full odd tail.  The remaining
three-owner core is still the quantified short-window/CRT lemma after adding
`O_i,O_j,O_l != 0`.

## Reproduction

```bash
lake env lean ErdosProblems/Erdos686ThreeBucketZeroExclusion.lean
python3 compute/campaign686/three_bucket_zero_exclusion_verify.py --pretty
python3 -m pytest \
  compute/campaign686/test_three_bucket_zero_exclusion_verify.py -q
```
