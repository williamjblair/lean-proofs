# Odd-tail findings

Status: exact arithmetic reproduced; paper proof complete for the local
prime-power restriction; Lean formalization in progress.  This is not a proof
of `OddThueTailHypothesis`.

## Local Taylor lift

Let

```text
B_k(n) = product_{j=1}^k (n+j),
F_{k,i}(T) = product_{j=1}^k (T+j-i),
c_{k,i} = (-1)^(i-1) (i-1)! (k-i)!.
```

Then `F_{k,i}(n+i)=B_k(n)` and

```text
F_{k,i}(T) = c_{k,i} T + T^2 G_{k,i}(T)
```

for an integer polynomial `G_{k,i}`.  If `h | d`, `h | n+i`, and
`B_k(n+d)=4B_k(n)`, substitution gives

```text
h^2 | c_{k,i} (d - 3(n+i)).
```

For odd `k=2r+1` and the center `i=r+1`,

```text
F_{k,r+1}(T) = (-1)^r (r!)^2 T + T^3 H_k(T),
```

so

```text
h^3 | (r!)^2 (d - 3(n+r+1)).
```

No approximation is used in either statement.

## Prime-power localization

The equation is congruent modulo `d` to `B_k(n)=4B_k(n)`, hence

```text
d | 3 B_k(n).
```

Let `p` be prime, `p >= k >= 5`, `e >= 1`, and `p^e | d`.  Since `p != 3`,
the full power `p^e` divides `B_k(n)`.  At most one of the `k` consecutive
factors is divisible by `p`, because any two indices differ by less than
`p`.  Thus a unique `i` satisfies `p^e | n+i`.  Since `p` divides neither
factorial in `c_{k,i}`, cancellation in the local lift gives

```text
p^(2e) | 3(n+i)-d.
```

At the center the exponent is `3e`.

## Explicit unbounded exclusion

For the six target values use:

| `k` | `C_k` | exact check | `A_k=3C_k+2` |
|---:|---:|---|---:|
| 5 | 4 | `5^5 < 4*4^5` | 14 |
| 7 | 5 | `6^7 < 4*5^7` | 17 |
| 9 | 7 | `8^9 < 4*7^9` | 23 |
| 11 | 8 | `9^11 < 4*8^11` | 26 |
| 13 | 9 | `10^13 < 4*9^13` | 29 |
| 15 | 11 | `12^15 < 4*11^15` | 35 |

The equation gives `d < 3(n+1)`: otherwise the first factor ratio is at
least four and every remaining ratio is greater than one.  It also gives
`n+1 < C_k*d`: if `C_k*d <= n+1`, multiplying

```text
C_k(n+d+j) <= (C_k+1)(n+j)
```

contradicts the exact power check.  Therefore, when `d >= k`,

```text
0 < 3(n+i)-d < A_k*d.
```

Consequently every hypothetical solution satisfies

```text
p^(2e) < A_k*d,
```

and `p^(3e) < A_k*d` if the power lands on the center.  In particular a
solution is impossible if some primary component obeys
`p^(2*v_p(d)) >= A_k*d`.

This is a proper restriction, not a tail closure: it is vacuous for gaps
whose prime support is entirely below `k`, and multiplying it over two or
more large prime components yields no contradiction.

## Exact primitive-scale condition

Write `P_k(T)=sum_j (-1)^j e_j T^(k-2j)`, `X=gu`, `Y=gv`, and
`gcd(u,v)=1`.  Dividing the exact equation by `g` and reducing the resulting
polynomial in `g^2` modulo `g^2` gives

```text
g^2 | (r!)^2 (u-4v).
```

The condition is exact but does not close the primitive branch `g=1`.

## Boundary audit

- `k=9`, `(n,d,X,Y)=(2,1,8,7)`:
  `P_9(8)=79,833,600=4*19,958,400`.
- `k=15`, `(n,d,X,Y)=(4,1,13,12)`:
  `P_15(13)=20,274,183,401,472,000=4*5,068,545,850,368,000`.

Both have `d=1<k`, no nontrivial gap prime power, and primitive scale
`g=1`.  The new restrictions therefore preserve both named telescopes.

Reproduction:

```bash
python3 -m pytest compute/campaign686/test_odd_tail_identities.py -q
```
