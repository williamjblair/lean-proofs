# Erdős 686 fifth-quotient short-window checkpoint

Status: **generic quotient bounds and elimination identity proved in Lean;
3,024-position nonvanishing ledgers reproduced with exact arithmetic but not
yet imported as a finite Lean certificate.**

This checkpoint does not close the simultaneous nonzero three-bucket branch or
Erdős #686.

## Kernel-checked symbolic surface

`ErdosProblems/Erdos686FifthLocalLift.lean` now proves the following generic
statements.

- `three_bucket_opposite_third_quotient_lt` converts the exact nonnegative
  product identity
  `d^2*A*Z = g^2*X*Y*T` and the three strict input bounds into
  `A*Z < U^2*B*g^4*d`.
- `three_bucket_fourth_quotient_abs_lt` converts
  `P*w = 27*C^2*A*z + K*g^4`, `d=P*M`, and the opposite-product bound into
  `|w| < W*g^4*M`, where
  `W = 27*|C|^2*U^2*B+|K|`.
- `three_bucket_normalized_fifth_numerator_abs_lt` converts
  `N=27*w+M*R1*g^4` into `|N| < V*g^4*M`, where `V=27*W+|R1|`.
- `three_bucket_component_sq_lt_of_normalized_fifth` proves that
  `P | N`, `N != 0`, and the preceding bound imply
  `P^2 < V*g^4*d`.
- `three_bucket_normalized_fifth_eliminant_identity` proves the exact identity

  ```text
  d^4*P*N = g^4*J(X,d),

  J(X,d) = 729*C^2 *
    (-9*C*X*(Y*Z)^2
      + delta*d^2*Y*Z*(180*E*d+108*D))
    + d^4*(27*K+d*R1),
  Y = X-3*deltaLeft,  Z = X-3*deltaRight,
  delta = deltaLeft*deltaRight.
  ```

The direct Lean check reports only axioms within
`[propext, Classical.choice, Quot.sound]`; the component-square theorem needs
only `propext`.  No `native_decide` is used.

## Exact 3,024-position ledger

The independent verifier reconstructs `C,D,E,F,G`, `K`, `R1`, and `R2` from
the affine products for each row, rather than importing an older campaign
verifier.  It enumerates all nonreflected triples and all three cyclic owners.

```text
k:                         5    7    9    11    13    15
nonreflected triples:      8   32   80   160   280   448
cyclic positions:         24   96  240   480   840  1344
totals: 1,008 triples and 3,024 cyclic positions
```

Across those positions, `R1` and `R2` are never zero.  The exact size extrema
are

```text
min W = 8516648448                         at (5,(1,2,3),owner 3)
max W = 20714179680564865272345420107181874741248000
                                                at (15,(1,14,15),owner 1)
min V = 230722131456                       at (5,(1,2,3),owner 3)
max V = 837008896359187552793649914881094977585152000
                                                at (15,(1,14,15),owner 1)
```

For the normalized fifth numerator the degree-five homogeneous form is

```text
f(x) = -6561*C^3*x^5 + 131220*C^2*E*delta*x^2 + R1.
```

The adjacent root brackets are checked by the exact integer inequalities
`lo^k < 4*100000^k < hi^k`.  Linearizing both exact power windows gives, for
owner `s`, the two finite corrections

```text
3*(100000-hi*k)/(hi-100000)+3*s,
3*(100000*k-lo)/(lo-100000)+3*s.
```

Their maximum absolute value over all six rows and all owners is exactly
`2303322/4841 < 1000`; hence at `d>=10^1000` the correction is less than
`1000/d < 1/100`.  This proves that the verifier's exact `1/100` padding
absorbs the complete power-window/owner correction, not merely the raw owner
shift.

On the resulting row-specific rational intervals, the scan finds no interior
critical point and no endpoint sign change.  The smallest exact endpoint margin is

```text
78561122159975755860732369169163215593189
---------------------------------------------------
5202861943105675888242343750000
```

at `(k,triple,owner,side)=(5,(1,3,4),3,lower)`.  It is greater than one.  With
`|X|<=36d`, the largest exact lower-degree coefficient majorant is

```text
5803459849500468008887094102834483923255296000 < 10^46,
```

at `(15,(1,2,15),owner 15)`.  Therefore the leading term strictly dominates
the remainder for `d>=10^1000`, conditional on the already-banked target
ratio interval.

The independently reconstructed fourth eliminant has homogeneous form

```text
f4(x) = -243*C^3*x^5 + 4860*C^2*E*delta*x^2.
```

It also has zero interior critical points and zero endpoint sign changes.  Its
minimum endpoint margin is

```text
3058554623558303407428783455243082059007
--------------------------------------------------
5202861943105675888242343750000
```

and its maximum remainder majorant is

```text
214942957388906222551373855660536441602048000 < 10^46.
```

Thus the exact-computational ledger finds every fourth quotient `w` and every
normalized fifth numerator `N` nonzero at the target cutoff.  This universal
finite conclusion is deliberately not described as Lean-banked: there is no
ordinary-kernel row-quantified certificate module in this checkpoint.

## Falsification fixture

The verifier independently constructs an exponent-166 CRT/Hensel tuple with
a 1,004-digit gap and a 6,023-digit `n`.  All three local fifth remainders,
reduced remainders, and normalized remainders are exactly zero, while all
named `z`, `w`, and `N` values are nonzero.  Nevertheless both the upper
short-window condition and the original block equation are false.

Consequently, congruence iteration alone is not a solution.  The exact block
equation and its archimedean window remain load-bearing.

## Remaining quantified gap

Even after imposing the exact-computational nonvanishing ledger and the Lean
component-square bounds, one must still exclude all 1,008 simultaneous
mixed-sign systems satisfying the three cyclic quotient identities and the
exact block equation in the target short window.  Multiplying the three
component-square bounds has the wrong exponent and does not supply that
exclusion.

## Reproduction

```bash
lake env lean ErdosProblems/Erdos686FifthLocalLift.lean
PYTHONDONTWRITEBYTECODE=1 python3 -m pytest -q -p no:cacheprovider \
  compute/campaign686/test_fifth_quotient_short_window_verify.py
PYTHONDONTWRITEBYTECODE=1 \
  python3 compute/campaign686/fifth_quotient_short_window_verify.py
```
