# Erdős 686: two-large-prime second-lift audit

Audit date: 2026-07-10.

## Verdict

**PASS for the stated clean regime.**  If an odd-row gap has exactly two
distinct prime-power components

```text
d = p^e q^f,  e,f>0,  p,q prime,  p != q,
```

and both bases are at least the row length, then the exact block equation
forces `d < 10^120` in every row `k=5,7,9,11,13,15`.  Thus no target-size
solution exists in this regime.  The result is a proper restriction, not a
proof of the full odd tail: it does not cover a two-prime gap with a base
below `k`, or a gap with at least three distinct prime divisors.

The Lean implementation is
`ErdosProblems/Erdos686TwoPrimeSecondLift.lean`.  The independent exact
reproduction is `two_prime_second_lift_verify.py`, with regression tests in
`test_two_prime_second_lift_verify.py`.

## Dependency tree

```text
N0  Two-large-prime target-size odd-row solution is impossible       PROVED
 |
 +- N1  Q_i(z)=C_i+D_i*z mod z^2                                    PROVED
 |
 +- N2  Residual a*h^2 and exact block equation imply
 |       h | 3*C_i*a - 4*D_i*(d/h)^2                                PROVED
 |
 +- N3  Banked two-component localization gives positive a,b,
 |       ab<A^2, distinct noncentral i,j, and
 |       a*P^2-b*Q^2=3(i-j)                                         PROVED
 |
 +- N4  Pell substitution gives
 |       P | 3(C_i ab+4D_i(i-j)),
 |       Q | 3(C_j ab-4D_j(i-j))                                    PROVED
 |
 +- N5  For all admissible fixed-row i,j and 1<=ab<A^2,
 |       the two obstruction integers are not simultaneously zero
 |       and each has absolute value below 10^20                     PROVED
 |
 +- N6  One nonzero divisibility bounds one component by 10^20;
         a Pell ratio bounds the other by A*10^20, hence
         d < A*10^40 <= 35*10^40 < 10^120                           PROVED
```

No node is an unproved private lemma.  `N3` is the already kernel-checked
theorem `two_large_prime_support_bounded_pell`; this module proves every new
node above it and composes the chain into unconditional row wrappers.

## Exact algebra audited

For

```text
Q_i(z) = product_{1<=j<=k, j!=i} (z+j-i),
```

the signed coefficients are

```text
C_i = product_{j!=i} (j-i),
D_i = sum_{x!=i} product_{j!=i,x} (j-i).
```

Finite-product induction proves `z^2 | Q_i(z)-C_i-D_i*z`.  The local block
equation is kept in `Int`; the natural interface supplies explicit witnesses
`d=h*m` and `h|(n+i)`, and supplies the residual as an integer equality.  No
truncated subtraction or informal division occurs.

Writing `P=p^e`, `Q=q^f`, the two local lifts are

```text
P | 3*C_i*a - 4*D_i*Q^2,
Q | 3*C_j*b - 4*D_j*P^2.
```

Multiplying the first by `b`, the second by `a`, and using
`a*P^2-b*Q^2=3(i-j)` gives exactly

```text
P | 3*(C_i*a*b + 4*D_i*(i-j)),
Q | 3*(C_j*a*b - 4*D_j*(i-j)).
```

The signs were checked symbolically in Lean and by the exact fixture
`P=2,Q=3,a=3,b=1,i-j=1` in the Python regression test.

## Finite certificate reproduction

The Python verifier uses only integer products, sums, comparisons, and
absolute values.  It exhausts all distinct noncentral indices and every
integer `t=ab` with `1<=t<A^2`.

| k | A | cases | single zeros | max `3*max(abs(X),abs(Y))` |
|---:|---:|---:|---:|---:|
| 5 | 14 | 2,340 | 8 | 13,440 |
| 7 | 17 | 8,640 | 8 | 600,912 |
| 9 | 23 | 29,568 | 8 | 62,551,872 |
| 11 | 26 | 60,750 | 0 | 7,220,776,320 |
| 13 | 29 | 110,880 | 0 | 1,189,246,717,440 |
| 15 | 35 | 222,768 | 0 | 316,717,097,518,080 |

There are no simultaneous zeros.  The Lean certificates do not trust this
output: a 60-entry signed coefficient table is proved equal to the defining
finite products by ordinary kernel `decide`, then `interval_cases`,
`norm_num`, and `omega` prove the uniform variable-`t` statements.  No
`native_decide` is used.

The deliberately loose Lean bound is `M=10^20`; the exact global maximum is
`316717097518080`.  The final bound is

```text
35*M^2 = 350000000000000000000000000000000000000000 < 10^120.
```

## Boundary and falsification audit

- The base boundary `p=k` or `q=k` is included: the hypotheses are `k<=p`
  and `k<=q`, not strict inequalities.
- End indices `i=1,k` are included.  Every distinct noncentral pair is
  covered, including all eight one-component-zero cases in rows 5, 7, and 9.
- The center is not silently discarded.  The banked cubic center conclusion
  gives `d<A^5`; under `A<=35` this contradicts `d>=10^120` before the finite
  certificate is invoked.
- The factor `3` cancellation used to recover `P|(n+i)` and `Q|(n+j)` is
  valid because `p,q>=k>=5`.  Small bases 2 and 3 are explicitly outside this
  clean theorem, not treated by the cancellation.
- Positivity covers `a,b,P,Q`; the finite range starts at `ab=1` and stops at
  the exact strict endpoint `ab=A^2-1`.
- The `k=9,15`, `d=1` telescopes are not contradicted: they are outside the
  two-distinct-prime-power support and target-size regimes.
- The `(k,n,d)=(984,3177026,4480)` and `(244,48502,277)` row-prefix witnesses
  are outside the six odd rows and are not used as equation solutions.
- No congruence-only obstruction, gross log-mass estimate, irrationality
  measure, Baker bound, or fixed-prefix claim is used.

## Lean surfaces and intake

The principal new surfaces are:

- `second_order_local_lift`;
- `second_obstruction_divisibilities`;
- six `second_obstruction_certificate_*` theorems;
- `two_large_prime_support_below_cutoff_of_second_lift`;
- six row wrappers `two_large_prime_support_k*_below_cutoff`.

Focused verification:

```text
python3 -m pytest compute/campaign686/test_two_prime_second_lift_verify.py -q
5 passed

lake env lean ErdosProblems/Erdos686TwoPrimeSecondLift.lean
PASS

lake build ErdosProblems.Erdos686TwoPrimeSecondLift
PASS
```

All audited surfaces report axioms contained in
`[propext, Classical.choice, Quot.sound]`.  The source has no `sorry`,
`admit`, `axiom`, `native_decide`, or `unsafe` declaration.

## Exact remaining gap

Within exactly-two-prime support, the remaining quantified regime is:

```text
For k in {5,7,9,11,13,15}, d=p^e*q^f>=10^120,
p,q distinct primes, e,f>0, and min(p,q)<k,
prove blockProduct k (n+d) != 4*blockProduct k n.
```

For the full odd tail one must additionally cover gaps with at least three
distinct prime divisors.  This module makes no claim that either remaining
statement is equivalent to the original target.
