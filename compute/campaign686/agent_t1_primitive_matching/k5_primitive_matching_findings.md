# Erdős 686, k=5 primitive factor matching

Status: exact global interface banked; one fixed-affine subcase bounded;
neither the primitive `g=1` branch nor the k=5 tail is closed.

## 1. Exact common quotient

Put

```text
X=g*u,  Y=g*v,  z=g^2,  gcd(u,v)=1,
U=(z*u^2-1)(z*u^2-4),
V=(z*v^2-1)(z*v^2-4).
```

The centered k=5 equation is

```text
u*U = 4*v*V.                                      (1)
```

Euclid cancellation in (1), followed by cancellation of the positive
factor `v`, gives one and the same integer `a`:

```text
U= v*a,                 4*V = u*a.                (2)
```

It is not enough to retain the two divisibilities separately; equality of
the two quotient values is exactly the residual content of (1).

The exact polynomial remainders are

```text
U = 4 (mod u),          V = 4 (mod v),
U = 4 (mod z),          V = 4 (mod z).
```

Consequently (2) gives the fixed coprimality losses

```text
gcd(a,u) | 4,           gcd(a,v) | 16,
gcd(z,v*a) | 4,         gcd(z,u*a) | 16.           (3)
```

In particular no odd prime divisor of `g` divides `u`, `v`, or `a`.
The first two conclusions in (3) are Lean-banked as
`k5_common_quotient_gcd_u_dvd_four` and
`k5_common_quotient_gcd_v_dvd_sixteen`.  The two local quadratic factors
have gcd dividing `3`, also kernel-banked.

These statements are proper restrictions but they do not make `a` small:
in the target strip `a` has order `z^2*v^3`.

## 2. One matching variable

For odd `g`, the already banked scale divisibility

```text
g^2 | 4(4v-u)
```

loses no factor `4`.  Write

```text
4v-u=z*t,               W=g^3*t=g(4v-u).           (4)
```

The two matching directions in (2) then compress to

```text
v | (W-1)(W+1)(W-2)(W+2),                          (5)
u | (W-4)(W+4)(W-8)(W+8).                          (6)
```

No parity hypothesis on `u` is hidden in (6): multiplying `4V` by the
fixed factor `64` absorbs all powers of two.  Both implications are
Lean-banked as `k5_upper_matching_compresses_to_W` and
`k5_lower_matching_compresses_to_W`.

The exact ratio strip gives

```text
2.68*v < 4v-u < 2.69*v.
```

Thus the existing scale estimate improves in the odd-scale subcase only to
`g^2 <= 4v-u < 2.69v`.  This changes the constant, not the exponent, and is
not a tail closure.

## 3. Fixed affine rays are finite

Suppose, for fixed coprime positive `A,B`, that

```text
u=A*t,                  v=B*t-1.                   (7)
```

If the first matching direction holds, then the exact resultant identity
gives

```text
v | R(A,B),
R(A,B)=(A^2-B^2)(A^2-4B^2).                       (8)
```

Hence, whenever `R(A,B) != 0`,

```text
B*t-1 <= |R(A,B)|,
t <= (|R(A,B)|+1)/B.                              (9)
```

The divisibility (8) is Lean-banked as
`k5_affine_ray_resultant_dvd`.  This is a genuine noncircular bound on
every fixed rational ray.  It is not uniform because `A` and `B` may grow
with the solution.

Five exact two-direction matching fixtures produced by (7) are reproduced
by the verifier.  The largest is

```text
(A,B)=(37499,28500),
(u,v)=(73847134203073,56125318669499).
```

Both divisibilities hold, while the two quotient values in (2) are unequal.

## 4. Exact flexibility tests

### 4.1 Both matching directions, primitive `g=1`

The verifier exhaustively factors every modulus `2 <= v <= 200000`, builds
all roots of

```text
(x^2-1)(x^2-4)=0 (mod v)
```

prime-power by prime-power, and checks the reverse matching direction.
There are exactly 25 primitive rows in the strict target ratio strip.  None
has equal common-quotient candidates.  Two natural forward chains are

```text
6649 -> 8721 -> 11440,
228998 -> 300375 -> 394001.
```

The second chain endpoint is above the frozen scan bound but is reproduced
independently by direct factorization.  These chains refute descent rules
that replace a matched coordinate by the next matched coordinate and assume
it must decrease.

### 4.2 Unbounded one-direction boundary family

For every integer `m>=0`, set

```text
g = 2+969m,
H = 51g,
v = 19(H^2-1),
u = 25H^2-76.
```

Then, exactly,

```text
gcd(u,v)=1,
131v < 100u < 132v,
4v-u = 51^3*g^2,
v | (g^2*u^2-1).
```

The last assertion follows from

```text
g^2*u^2 = H^6 (mod v),
H^6-1=(H^2-1)(H^4+H^2+1),
19 | H^4+H^2+1
```

because `H=7 (mod 19)`.  The member `m=10^40` has gap strictly greater
than `10^120`.  It fails the reverse matching direction and is therefore
not a candidate solution.  Its role is precise: no argument using only the
scale condition, primitivity, the exact ratio strip, factor gcd `<=3`, and
the upper-to-lower matching direction can close the target.

## 5. Exact remaining gap in this lane

The unresolved statement is not “essentially a Pell equation.”  In the
notation (2), the exact missing implication is:

> For `d=g(u-v)>=10^120`, `131v<100u<132v`, `z=g^2`, and `gcd(u,v)=1`,
> prove that no positive `a` simultaneously satisfies
> `U=v*a` and `4V=u*a`.

That statement is the k=5 target rewritten, so it is not counted as a new
lemma or as progress.  The proper new content is (3), the one-variable
compression (5)--(6), and the fixed-ray bound (9).
