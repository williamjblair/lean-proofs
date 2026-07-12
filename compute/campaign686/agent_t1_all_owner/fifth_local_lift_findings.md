# Erdős 686 fifth local lift: exact findings

Date: 2026-07-12

## Kernel-banked consequences

`ErdosProblems/Erdos686FifthLocalLift.lean` keeps the quartic coefficient
`G` of the signed local cofactor.  If

```text
3L-HM = A H^2
```

and the exact block equation holds, the new local obstruction is

```text
H^4 |
  3 * (3*T3 + H^2*(-9 D A^2 + 36 E A M^2 + 84 F M^4))
  + 20 H^3 M^3 (12 A F + 17 G M^2).
```

The theorem is equation-facing: `fifth_order_local_lift` derives this from
the actual block equation and the factor and residual identities.

For three cleaned buckets, write `t=abc`, `x=i-j`, `y=i-l`, and let `W4`
be the banked fourth cyclic obstruction.  The exact fifth composition is

```text
P^4 | W5,
W5 = 3 W4 + P^3 g^3 Q R K5,
K5 = -540 t E (x+y) + 2160 t F xy + 27540 G g^2 (xy)^2.
```

If the composed third obstruction is `P^2 z`, fifth order lifts the former
ordinary quotient congruence to

```text
P^2 |
  9bc z + 3J + P g^3 Q R K5,
```

where `J` is the exact fourth correction.  The Lean theorem
`target_three_bucket_fifth_obstruction_dvd_fourth` derives `W5` from the
actual equation and three supplied square residuals.  All public theorem
surfaces use only `[propext, Classical.choice, Quot.sound]`.

## Fixed-coefficient reduction

Eliminating `t` with the third obstruction gives

```text
P^2 | 729 C^2 bc z + R5(C,D,E,F,G,d,x,y) g^4.
```

The exact polynomial `R5` is defined in Lean as
`threeBucketReducedFifthCoefficient`.  It has degree at most two in `d`.
The coefficient of `d^2`, before the common nonzero factor
`874800 xy`, is

```text
E * (-C E (x+y) + 4 C F xy - D E xy).
```

Exact enumeration of all 6,210 ordered distinct target triples gives:

| degree-two status | ordered owner views |
|---|---:|
| nonzero | 6,156 |
| zero | 54 |

The 54 zero views are exactly the center owner with the other two owners
reflected.  Thus the generic fixed term is bounded by an explicit constant
times `g^4 d^2`, not by an explicit constant times `g^4 d`.  Taking absolute
values of this congruence therefore does not produce the missing uniform
fourth-power component bound.  The center-reflected 54-view subfamily has a
lower-degree coefficient and remains a legitimate specialized lane.

## Exact CRT replay

The frozen fourth-order fixture uses

```text
k = 5,
owners = (1,2,4),
components = (101^20, 103^20, 107^20),
d = 101^20 * 103^20 * 107^20
  = 8528006514942991411329818759017663024603296760011487105481658555774743359211568625230878556970868752918452276874633718401.
```

It has 121 digits.  Its three local fifth remainders and three composed
fifth remainders are nonzero, so the frozen fourth-order representative
does not accidentally satisfy the new condition.

Writing the old free square-residual parameter as `s`, adding `d^3 v`
preserves fourth order.  After division by `P_i^3`, the fifth finite
difference is exactly

```text
-81 C_i (d/P_i)^5  (mod P_i).
```

It is a unit for all three components.  CRT therefore selects `v mod d` and
produces another 121-digit-gap representative.  The lifted representative
has a 725-digit `n` and satisfies, at all three owners:

- the local fifth obstruction modulo `P_i^4`;
- the composed fifth obstruction modulo `P_i^4`;
- the squared third-quotient congruence modulo `P_i^2`;
- the reduced fixed-coefficient congruence modulo `P_i^2`;
- nonvanishing of every composed third obstruction;
- divisibility of the direct block difference by `P_i^6`.

It still fails the exact block equation and every coarse upper residual
window `0 < X_i < 14d`.  Hence it is a route falsifier, not an Erdős 686
counterexample.  It proves that fifth order plus all-nonzero third
quotients does not yield a congruence-only contradiction.  A surviving
argument must use the verified short window or another global relation.

## Reproduction

```bash
lake env lean ErdosProblems/Erdos686FifthLocalLift.lean
PYTHONPATH=. pytest -q \
  compute/campaign686/agent_t1_all_owner/test_fifth_local_lift_verify.py
python3 compute/campaign686/agent_t1_all_owner/fifth_local_lift_verify.py --compact
```

The exact verifier checks 10,080 denominator identities and 111,780 signed
cyclic composition fixtures, including component `3`, negative data, and
unit opposite components.
