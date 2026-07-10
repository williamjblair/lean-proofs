# Erdős 686 two-prime-support findings

Status: two proper restrictions are Lean-proved in
`ErdosProblems/Erdos686TwoPrimeGap.lean`; exact constants and finite-family
counts are independently reproduced by `two_prime_gap_verify.py`.  This is
not a proof of an odd tail and is not substituted for
`OddThueTailHypothesis`.

## 1. All-prime concentration-location theorem

Let `k=2r+1` with `5<=k<=15`, and suppose

```text
d = p^e q^f,  p and q distinct primes,  e,f>0,
B_k(n+d)=4 B_k(n),  d>=10^120.
```

Use also the already Lean-proved rowwise base window

```text
n+1 < C_k d,
(k,C_k,A_k) = (5,4,14), (7,5,17), (9,7,23),
                (11,8,26), (13,9,29), (15,11,35),
A_k = 3 C_k + 2 <= 35.
```

These are exactly the `hbase`, `hA`, and `hA35` inputs of the parametric Lean
surface; for each of the six rows they follow from the verified ratio window.

The primes may be below `k`; in particular, `2` and `3` are allowed.  For a
primary component `p^e`, valuation concentration supplies an index `i` and
an exponent `t` such that

```text
p^t | d,
p^t | n+i,
p^e <= 4096 p^t.
```

The exact uniform worst-case loss bound over `k<=15`, prime by prime, is

| `p` | `p^(1+v_p(14!))` |
|---:|---:|
| 2 | 4096 |
| 3 | 729 |
| 5 | 125 |
| 7 | 343 |
| 11 | 121 |
| 13 | 169 |

For `p>=k`, the proof chooses `t=e`, so there is no loss.  For `p<k`, the
truncated exponent `t=e-1-v_p((k-1)!)` is used.  The inequality above remains
valid even when this truncates to zero.

Write `h_p=p^t`, `h_q=q^s`, and `L=4096^2=16777216`.  Then

```text
d <= L h_p h_q.
```

The raw local lifts give

```text
h_p^2 < (k-1)! A_k d,
h_q^2 < (k-1)! A_k d,
```

and, if a component concentrates at the center,

```text
h_center^3 < (r!)^2 A_k d.
```

Two elementary combinations now close complete subcases.

1. If both components concentrate at one factor, apply the square lift to
   `h_p h_q`:

   ```text
   d < L^2 (k-1)! A_k
     <= L^2 14! 35
      = 858847761981817541885952000
      < 10^120.
   ```

2. If they concentrate at distinct factors and one is the center, raise the
   cubic inequality to the second power and the other square inequality to
   the third power:

   ```text
   d < L^6 (r!)^4 ((k-1)!)^3 A_k^5
     <= L^6 (7!)^4 (14!)^3 35^5
      = 500733675106336395918545298815399096057504984362231236206385578627747149218985279488000000000000000
      < 10^120.
   ```

Therefore the two concentrated components of any target-size two-prime gap
must land at two distinct noncentral indices.  This is the theorem
`two_prime_support_has_distinct_noncenter_concentrations`.

### Dependency tree and verdicts

```text
A0  two-prime target-size gap
 |- A1  d | 3 B_k(n)                                      Lean-proved
 |- A2  valuation concentration in a consecutive block    Lean-proved
 |- A3  per-prime loss <=4096                              Lean-proved exactly
 |- A4  raw square and center-cubic lifts                  Lean-proved
 |- A5  residual 0<X_i<A_k d                              Lean-proved
 |- A6  same-bucket absolute bound                        Lean-proved
 |- A7  center-plus-other absolute bound                  Lean-proved
 `- A8  two distinct noncentral concentration indices     Lean-proved
```

No node imports a private lemma, analytic estimate, Pell assertion, or
prime-power assertion.

## 2. Clean `p,q>=k` finite-coefficient Pell reduction

Now impose `p,q>=k`, and put `u=p^e`, `v=q^f`, so `d=uv`.  Unique full
localization gives indices `i,j` and positive residuals

```text
u^2 | 3(n+i)-d,
v^2 | 3(n+j)-d,
0 < 3(n+i)-d < A_k d,
0 < 3(n+j)-d < A_k d.
```

Thus there are positive integers `a,b` with

```text
3(n+i)-d = a u^2,
3(n+j)-d = b v^2,
a u < A_k v,
b v < A_k u.
```

Subtracting and multiplying the two strict bounds gives

```text
a u^2 - b v^2 = 3(i-j),
a b < A_k^2.
```

The indices cannot coincide.  If `i=j`, coprimality makes `d^2=u^2v^2`
divide the common residual.  Hence `d^2<A_k d`, so `d<A_k`; but
`d>=pq>=k^2>A_k` for every one of the six rows.

If either localization is the center, the cubic lift and the other square
lift give, with no concentration loss,

```text
d < A_k^5 <= 35^5 < 10^120.
```

The theorem `two_large_prime_support_bounded_pell` records all of these
claims, including the exact integral equation and the cubic divisibility.

Multiplying the equation by `a` produces the conventional generalized Pell
form

```text
(a u)^2 - (a b) v^2 = 3a(i-j),
```

with `a b<A_k^2` and `0<|i-j|<=k-1`.  This is a genuinely finite list of
coefficient families; it is not declared solved.

The remaining exact congruence filters available at paper level are

```text
a == b != 0 (mod 3),
a-b == 3(i-j) (mod 8),
p does not divide b,
q does not divide a.
```

The first two use that `u,v` are odd and prime to three.  The last two use
`0<|i-j|<p,q`.  The coefficient-only enumeration below implements the first
two filters.  The cross-prime filters depend on the actual choices of `p,q`
and are not included in those counts.

## 3. Exact finite-family counts

After `ab<A_k^2` and the mod-3 and mod-8 filters, the exact counts are:

| `k` | `A_k` | raw `(a,b)` | filtered `(a,b)` | filtered `(a,b,i-j)` |
|---:|---:|---:|---:|---:|
| 5 | 14 | 1061 | 246 | 280 |
| 7 | 17 | 1686 | 390 | 668 |
| 9 | 23 | 3402 | 881 | 1762 |
| 11 | 26 | 4509 | 1161 | 2902 |
| 13 | 29 | 5804 | 1491 | 4474 |
| 15 | 35 | 8906 | 2277 | 7970 |

These are enumeration counts, not a proof that any listed Pell family has or
lacks prime-power solutions.

## 4. Hostile boundary audit

- The named `k=9` and `k=15` telescopes have `d=1`; they have neither two
  positive primary components nor `d>=k`.  Both exact identities are
  reproduced by the test file.
- `p=3` is not silently cancelled in the all-prime theorem.  Its possible
  multiplier valuation is the explicit extra exponent in the loss `729`.
- Small exponents are not assumed larger than the factorial loss.  Natural
  subtraction may produce concentration exponent zero, and the bound
  `p^e<=4096 p^t` remains valid.
- Equal primes are excluded exactly by the hypothesis that the gap has two
  distinct prime divisors.  No coprimality stronger than that is assumed.
- The same-bucket and center bounds use strict inequalities; no equality
  boundary is discarded.
- The argument uses neither congruence-only obstruction nor a generic claim
  that Pell equations lack prime powers.

## 5. Exact remaining gap

For the clean large-prime slice, the remaining statement is the following
single quantified lemma:

```text
For k in {5,7,9,11,13,15}, A=A_k, distinct primes p,q>=k,
e,f>=1, distinct noncentral i,j in [1,k], and positive a,b with
ab<A^2 and

    a p^(2e) - b q^(2f) = 3(i-j),

subject to the displayed mod-3, mod-8, and cross-prime filters,
no tuple exists when p^e q^f>=10^120.
```

This is a finite-discriminant Pell/prime-power intersection problem.  Merely
naming it is not counted as progress; the new progress is the proved
coefficient bound, same-index closure, center closure, and the all-prime
concentration-location theorem above.  No squareclass elimination is claimed
in the Lean-banked result.

## Reproduction

```bash
lake env lean ErdosProblems/Erdos686TwoPrimeGap.lean
python3 -m pytest compute/campaign686/test_two_prime_gap_verify.py -q
python3 compute/campaign686/two_prime_gap_verify.py --pretty
```
