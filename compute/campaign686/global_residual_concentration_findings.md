# Erdős 686 global-residual concentration

Status: **valuation theorem, third local lift, abstract two-bucket closure,
and complete all-two-prime-support exclusion Lean-banked.**

## Exact input and output

Put

```text
X_i = 3(n+i)-d,                    1 <= i <= k.
```

The independently audited global square lift supplies

```text
d^2 | product_i X_i.                                      (1)
```

In the separated equation range (`k>=5`, `d>=k`) every `X_i` is positive.
For each prime-power component `p^e | d`, the new Lean theorem constructs an
index `i` and

```text
t = e-c_p(k),    h=p^t,
```

with natural subtraction at zero, such that

```text
h | d,        h | n+i,        h^2 | X_i,
p^e <= p^c_p(k) h.                                      (2)
```

The exact loss exponent is

```text
c_p(k) = ceil(v_p((k-1)!)/2)                 if p != 3,
c_3(k) = ceil((k+v_3((k-1)!)-1)/2)
         = floor((k+v_3((k-1)!))/2).         if p = 3.   (3)
```

For `p!=3`, the individual loss factor is at most `64`.  For `p=3` it is at
most `3^10=59049`.  These bounds, and the exact six-row three-exponents
`3,4,5,7,9,10`, are also Lean-proved.

## Proof of concentration for `p != 3`

Choose `i` for which `v_p(X_i)` is maximal.  For every `j!=i`, the common
power `p^v_p(X_j)` divides

```text
|X_i-X_j| = 3|i-j|.
```

Since `p!=3`, it divides `|i-j|`.  Multiplying over the non-owner indices and
using

```text
product_{j!=i}|i-j| = (i-1)!(k-i)! | (k-1)!
```

gives

```text
sum_j v_p(X_j) <= v_p(X_i)+v_p((k-1)!).                  (4)
```

Equation (1) and `p^e|d` give `2e<=sum_j v_p(X_j)`.  With
`c=ceil(v_p((k-1)!)/2)` and `t=e-c`, (4) gives `2t<=v_p(X_i)`, hence
`h^2|X_i`.  Also `h|d`, and from `h|X_i+d=3(n+i)` coprimality with three gives
`h|n+i`.  Finally `e<=c+t`, proving the loss inequality in (2).

## Exact treatment of `p=3`

This branch is not obtained by paying an unexplained extra exponent.  If
`3^e|d`, `e>0`, write `q=d/3`.  Positivity at `i=1` gives `q<=n`, and exactly

```text
X_i = 3(n-q+i),
product_i X_i = 3^k B(k,n-q).                            (5)
```

Thus (1) gives

```text
2e <= k + v_3(B(k,n-q)).                                (6)
```

Ordinary consecutive-block concentration selects `i` with

```text
v_3(B(k,n-q)) <= v_3(n-q+i)+v_3((k-1)!).                (7)
```

For `c=floor((k+v_3((k-1)!))/2)` and `t=e-c`, (6)-(7) imply

```text
2t <= 1+v_3(n-q+i).
```

Since `k>=5`, `c>=1`, so `t<=e-1`.  If `t>0`, the displayed inequality also
gives `t<=v_3(n-q+i)`; at `t=0` divisibility is trivial.  Therefore `3^t`
divides both `q` and `n-q+i`, hence divides `n+i`, while (5) gives its square
dividing `X_i`.  This proves every clause of (2), including the small-exponent
boundary where `t=0`.

## Aggregate loss and bucket grouping

Multiplying the losses over all possible small primes gives the exact row
budgets

| `k` | prime loss exponents | `G_k` |
|---:|:---|---:|
| 5 | `2^2 3^3` | 108 |
| 7 | `2^2 3^4 5` | 1,620 |
| 9 | `2^4 3^5 5 7` | 136,080 |
| 11 | `2^4 3^7 5 7` | 1,224,720 |
| 13 | `2^5 3^9 5 7 11` | 242,494,560 |
| 15 | `2^6 3^10 5 7 11 13` | 18,914,575,680 |

Group the pairwise-coprime cleaned components by their owner indices.  If
there are at most two nontrivial buckets, call their products `P,Q`.  Then

```text
d = g P Q,             1 <= g <= G_k,                  (8)
X_i = a P^2,           X_j = b Q^2,                    (9)
gcd(P,Q)=1.
```

The one-bucket case is immediate from `X_i<A d`: it gives
`d<A G_k^2`, far below `10^120` in every row.

For two distinct buckets, subtracting (9) gives the exact Pell identity

```text
aP^2-bQ^2 = 3(i-j),                                    (10)
```

and the residual bounds give

```text
aP < A g Q,       bQ < A g P,       ab < A^2 g^2.      (11)
```

Here `A=14,17,23,26,29,35` in the six rows.

## Second-order audit and its exact degeneracy

Write the signed local cofactor expansion

```text
Q_i(z)=C_i+D_i z+E_i z^2+O(z^3).
```

The second local lift, with `d/P=gQ` and `d/Q=gP`, and (10) give

```text
P | 3(C_i ab+4D_i g^2(i-j)),
Q | 3(C_j ab-4D_j g^2(i-j)).                            (12)
```

If either obstruction is nonzero, the exact coefficient majorant `M_{k,i,j}`
and (11) give

```text
d < A M_{k,i,j}^2 G_k^6.                               (13)
```

The verifier checks every ordered pair in every row.  The maximum of (13) is
the `k=15` value

```text
217044647287343042885059609316395849093627507558461004041714015187255309475392782336000000000
```

and is below `10^120`.

The two expressions in (12) can vanish simultaneously only if

```text
C_j D_i + C_i D_j = 0.                                 (14)
```

Exact evaluation shows that (14) holds precisely for reflected pairs
`j=k+1-i`.  It is not safe to dismiss them: for such a pair simultaneous
vanishing is arithmetically possible exactly when

```text
ab/g^2 = -4D_i(i-j)/C_i,
```

whose reduced rational values are emitted by the verifier.  For example the
two `k=5` values are `100/3` and `20/3`; all 27 reflected pairs across the six
rows are listed in the JSON report.

## Third-order repair of every reflected pair

The exact Taylor calculation gives the proper local consequence

```text
Z_i = 3C_i a-4D_i(gQ)^2,
P | Z_i,
P^2 | -3Z_i+20E_i P(gQ)^3.                             (15)
```

The coefficient `20` is exact.  It follows from the identity, under
`3x-m=aP`,

```text
9[-C_i a + D_i((x+m)^2-4x^2)
    +P E_i((x+m)^3-4x^3)]
 == -3(3C_i a-4D_i m^2)+20E_i Pm^3          (mod P^2).
```

The verifier checks this identity over a signed integer grid and checks that
the cubic Taylor remainder is divisible by `z^3` for every row and index.
The standalone composition module also proves both facts generically in Lean
before specializing the quadratic coefficient to its exact 60-entry table.

When both second obstructions vanish, multiplying (15) by `b` and using (10)
gives

```text
P | 20 E_i b g^3 Q^3,
Q | 20 E_j a g^3 P^3.                                  (16)
```

Because `gcd(P,Q)=1`, remove the opposite cube.  Moreover (10) implies

```text
gcd(P,b) | 3(i-j),       gcd(Q,a) | 3(i-j).
```

Consequently, since every reflected-pair quadratic coefficient is nonzero,

```text
P <= 60|i-j||E_i|g^3,
Q <= 60|i-j||E_j|g^3,
d <= 3600(i-j)^2|E_iE_j|G_k^7.                         (17)
```

Every exact row-pair bound in (17) is below `10^120`.  The largest is

```text
93984078683194682557325451381987070845762855139556197071318510982175649195251213580361531392000000000
```

for `k=15`, still only 101 digits.

Thus the global concentration theorem plus the second and third local lifts
exclude every target-size gap whose cleaned components occupy at most two
residual buckets at the paper/exact row budgets above.

## Fully composed two-prime-support theorem

For a gap with exactly two distinct prime bases, only two per-component losses
are paid.  Hence the cofactor in (8) satisfies the sharper uniform bound

```text
g <= 59049^2 = 3,486,784,401.                           (18)
```

The Lean composition uses deliberately loose constants to avoid importing a
large reflected-pair certificate into the final arithmetic:

```text
generic branch: d < 35*(10^30)^2*(59049^2)^6 < 10^120,
third branch:   d < 400*(10^12)^2*35^2*(59049^2)^9 < 10^120.
```

The theorem

```text
two_prime_support_below_cutoff_of_global_residual_lifts
```

therefore proves `d<10^120` for every exact gap
`d=p^e*q^f` in the six target rows, for distinct primes `p,q` and positive
exponents, without hypotheses `p>=k` or `q>=k`.  It handles coincident clean
owners by multiplying the coprime square divisors, and distinct owners through
the fully composed second/third obstruction theorem.

The generic valuation core remains isolated in
`ErdosProblems/Erdos686GlobalResidualConcentration.lean`.  The third-order and
composition layer is in
`ErdosProblems/Erdos686GlobalResidualTwoPrime.lean` and records its audited
second-lift dependency SHA
`e4ec6011fa24122072aa35ddba80e12d8d7ab0f9cd37a290610a3b2e4d493dbd`.
Neither module uses `sorry`, `axiom`, or `native_decide`.

## Falsification audit

- The genuine `d=1` telescopes at `k=3,6,9,12,15` have `d<k` and no
  nontrivial prime-power component.  The separated clean-component wrapper
  correctly does not apply.
- The two named large-`k` prefix fixtures `(984,3177026,4480)` and
  `(244,48502,277)` are not complete equation solutions.  The verifier checks
  the equation premise is false and draws no consequence from them.
- `p=3` is not treated as a unit-step progression.  Its common factor is
  removed exactly in (5), and all `k` common valuations are charged in (6).
- Small exponents produce `t=0`; every divisibility conclusion then reduces
  to the unit divisor, with no illegal subtraction or division.
- Reflected second-order zeros are retained and repaired by (15)-(17), not
  silently excluded by a finite scan over `ab`.

## Reproduction

```bash
lake env lean ErdosProblems/Erdos686GlobalResidualConcentration.lean
lake env lean ErdosProblems/Erdos686GlobalResidualTwoPrime.lean
python3 -m pytest compute/campaign686/test_global_residual_concentration_verify.py -q
python3 compute/campaign686/global_residual_concentration_verify.py --pretty
```
