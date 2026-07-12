# Erdős 686 odd tail: reverse scale divisibility

Status: a bounded valuation-discrepancy theorem is proved and Lean-banked.
It sharpens the center cubic lift but does not close the infinite tail.

Reproduce:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 -m \
  compute.campaign686.agent_cf_tail.scale_newton_verify
lake env lean ErdosProblems/Erdos686CFTailScale.lean
```

## 1. The first reverse Newton step

Retain the primitive-scale notation

```text
A_j = 4*v^j-u^j,  z=g^2,
E=e_r=(r!)^2,  F=e_(r-1).
```

The constant coefficient gives `z | E*A_1`; write

```text
E*A_1 = z*q.                                               (1)
```

Dividing the full low-end Horner identity once by `z` gives

```text
q = F*A_3 (mod z).                                         (2)
```

This is the first p-adic Newton step at `z=0`.  It is stronger than the
one-way divisibility because it identifies the complementary factor modulo
the entire square scale.

## 2. Fixed resultant loss

For `gcd(u,v)=1`, the linear and cubic remainders satisfy

```text
gcd(A_1,A_3) | 60.                                         (3)
```

Indeed `u=4v (mod A_1)`, so

```text
A_3 = 4v^3-u^3 = -60v^3 (mod A_1),
```

and primitivity cancels `v^3`.  The theorem
`gcd_linear_cubic_dvd_sixty` is the kernel proof.

Equations (1)-(3) imply

```text
gcd(z,q) = gcd(z,F*A_3) | 60*E*F.                          (4)
```

The equality is (2); for the bound, a common divisor divides both
`E*F*A_1` and `E*F*A_3`, hence divides
`E*F*gcd(A_1,A_3)`.  This is Lean-banked as
`scale_quotient_gcd_bound`.

The six exact discrepancy bounds are

| k | `60*e_r*e_(r-1)` | prime factorization |
|---:|---:|---|
| 5 | 1,200 | `2^4*3*5^2` |
| 7 | 105,840 | `2^4*3^3*5*7^2` |
| 9 | 28,339,200 | `2^10*3^3*5^2*41` |
| 11 | 18,209,664,000 | `2^10*3^3*5^3*11*479` |
| 13 | 24,047,622,144,000 | `2^14*3^7*5^3*7*13*59` |
| 15 | 58,528,432,134,144,000 | `2^14*3^7*5^3*7^2*266681` |

All products and factorizations are reproduced by trial division in
`scale_newton_verify.py`.  An exhaustive sanity sweep checks 79,817
primitive below-side pairs with `v<=500`; the largest observed
`gcd(A_1,A_3)` is exactly 60.

The same argument is not limited to the cubic coefficient.  For every
`s=t+1` with `u^s<=4v^s`, Lean proves

```text
gcd(A_1,A_s) | 4*(4^t-1).
```

Consequently any low-end Horner remainder `H` satisfying
`H=F*A_s (mod z)` obeys

```text
gcd(z,H) | 4*(4^(s-1)-1)*E*F.
```

These are `gcd_linear_power_remainder_dvd` and
`scale_horner_remainder_gcd_bound`.  Thus, outside one explicit finite bad
divisor per row, every stage of the p-adic Newton recurrence is simple.

## 3. Exact good-prime consequence

Let `p` be a prime not dividing `60*E*F`.  If `p|g`, then `p|z`, while (4)
gives `p` not dividing `q`.  Since `p` also does not divide `E`, (1) yields

```text
v_p(A_1) = v_p(z) = 2*v_p(g).                             (5)
```

Because

```text
A_1 = (3Y-d)/g,
```

equation (5) is the exact center valuation

```text
v_p(3Y-d) = 3*v_p(g).                                     (6)
```

Thus every good prime in the center scale has *exactly* cubic residual
valuation, not merely the previously known cubic divisibility.  Only the
explicit fixed primes in the table can have excess valuation.

The valuation-free kernel package now records the complete factorization.
Write `H=p^a`, `g=H*g0`, with `p` absent from `g0`, and retain
`d=g(u-v)`, `Y=gv`.  Lean proves

```text
d = H*(g0*(u-v)),       gcd(H,g0*(u-v))=1,
Y = H*(g0*v),           gcd(H,g0*v)=1.
```

Under `E*A1=g^2*q` and the corresponding good-component coprimality, it
also produces `a1` with

```text
A1   = H^2*a1,          gcd(H,a1)=1,
g*A1 = H^3*(g0*a1),     gcd(H,g0*a1)=1.
```

The dependency is

```text
good_scale_prime_not_dvd_primitive_denominator
good_scale_prime_not_dvd_primitive_gap
  -> good_primePower_exact_gap_and_center
  -> good_primePower_exact_gap_center_residual.
```

All surfaces compile behind the required axiom gate.

## 4. Hostile third- and fourth-order Hensel test

The exact components do **not** create a local third- or fourth-order
contradiction.  For a good prime, reduction of the full scale polynomial
modulo `p` is

```text
Q_k(u,v,g) = +/- E*(4v-u) (mod p).
```

Its derivative in `u` is the unit `-/+E`.  Therefore the root `u=4v mod p`
is simple and lifts one digit at a time.  The exact verifier
`scale_hensel_flexibility_verify.py` performs this lift by enumerating all
`p` possible next digits—no Hensel library or floating arithmetic—and checks
that exactly one digit works at every stage through `p^32`.

For each row it then chooses an integer representative with

```text
gcd(u,v)=1,  v<u<2v,  u^k<4v^k.
```

The choice is deterministic.  If `r` is the lifted residue in `[0,p^32)`,
put `M=p^32`, `L=r-1`,

```text
v=L*M+1,  u=L*M+r=v+(r-1).
```

Then `gcd(u,v)=gcd(r-1,(r-1)M+1)=1`; the lifted residue is preserved; and
the ratio is close enough to one that the exact integer tests
`v<u<2v` and `u^k<4v^k` hold.  With `a=3`, `g=p^3`, every fixture has exactly

```text
v_p(u-v)=v_p(v)=0,
v_p(A1)=6,
v_p(d)=v_p(Y)=3,
v_p(g*A1)=9,
v_p(E*A1/g^2)=0,
Q_k(u,v,g)=0 (mod p^32).
```

In particular the *full* scale congruence, not merely a truncated local
formula, survives `p^(3a)`, `p^(4a)`, and even `p^(5a)`.  The frozen summary
is:

| k | p | decimal digits of `(u,v)` | exact `v_p(Q_k)` |
|---:|---:|---:|---:|
| 5 | 7 | `(54,54)` | 32 |
| 7 | 11 | `(67,67)` | 32 |
| 9 | 11 | `(67,67)` | 32 |
| 11 | 13 | `(72,72)` | 32 |
| 13 | 17 | `(79,79)` | 32 |
| 15 | 17 | `(78,78)` | 32 |

The JSON report prints every exact residue, digit, and representative.

These are local-congruence fixtures, not exact integer roots.  They hostilely
falsify the proposed inference that a fixed third/fourth/fifth good-prime
obstruction or any fixed local lifting depth bounds the center component.
An infinite-tail closure must combine the exact component with a genuinely
global or archimedean restriction.

## 5. Hostile check against an overstrong reverse claim

The quotient need not be coprime to `z`.  The checked `k=5` unbounded
low-filter counterfamily at `t=1` has

```text
z = 13,216,743,914,256,
q = 4*A_1/z = 52,866,975,656,724,
gcd(z,q) = 12.
```

It satisfies the constant and first Newton congruences, so `gcd(z,q)=1`
cannot be inferred from those identities.  The bounded loss (4), not
coprimality, is the valid conclusion.  The counterfamily is not a full root
and is used only to falsify the stronger local inference.

Both genuine `d=1` telescopes also pass the Newton audit.  They have `z=1`,
so (4) is vacuous, as it must be.

## 6. Why this does not close the tail

The result partitions the owner picture cleanly but leaves both infinite
possibilities:

1. If no cleaned owner lies at the center, owner-offset gcd bounds can make
   `g=gcd(d,Y)` bounded.  The primitive case `g=1` remains, and a fixed
   scale still leaves the original infinite Thue/CF tail.
2. If a center bucket carries the unbounded part of `g`, (6) removes excess
   good-prime valuation, but it does not bound the size or number of those
   good primes.  The existing cubic size inequality remains compatible with
   arbitrarily large mixed-prime gaps.

Consequently the exact remaining Target 1 lemma is unchanged:

```text
forall k in {5,7,9,11,13,15}, forall n d,
  10^166 <= d -> B(k,n+d) != 4*B(k,n).
```

The reverse Newton theorem is a proper restriction usable by the
three-owner/center-bucket attack; it is not presented as an infinite-tail
solution.
