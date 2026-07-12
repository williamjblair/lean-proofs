# Erdős 686: an effective tail for every even row

Status: exact uniform paper proof and exact certificate generator.  The
centered-ratio power bound and final integer trap are kernel-banked in
`Erdos686EvenTailRunge.lean`; the arbitrary-`r` polynomial-construction and
coefficient-bound layer is not yet kernel-banked, so the uniform theorem is
not advertised as a Lean theorem yet.

## Theorem

Let `r>=2`, `k=2r`, and

```text
S_r(W) = product_{j=1..r} (W^2-(2j-1)^2).
```

There is an explicitly computable positive integer `M_r` such that, for all
naturals `n,d` with

```text
d >= max(2r,M_r),
```

one has

```text
B(2r,n+d) != 4 B(2r,n).
```

The verifier `even_tail_verify.py` computes `M_r` using only exact rational
and integer arithmetic.  Thus this is a restricted-but-unbounded regime for
every even row in Target 2, not a fixed finite list of rows.

## Exact construction

There is a unique monic `T_r^Q in Q[W]` of degree `r` for which

```text
deg((T_r^Q)^2-S_r) < r.                              (1)
```

It is obtained by descending coefficient recursion: after coefficients above
degree `j` have been fixed, the coefficient of degree `r+j` in the square is
linear in the still-unknown coefficient `T_j`, with coefficient `2`.

Let `C_r` be the least common multiple of the coefficient denominators, put

```text
T_r = C_r T_r^Q in Z[W],
D_r = T_r^2-C_r^2 S_r in Z[W],
q_r = deg D_r < r.                                  (2)
```

The deficit is nonzero: otherwise the polynomial `S_r` would be a square,
although each of its `2r` roots `+-(2j-1)` is simple.  Write

```text
T_r(W) = C_r W^r + lower terms,
D_r(W) = L_r W^q + lower terms,
A_r = sum of absolute lower coefficients of T_r,
E_r = sum of absolute coefficients of D_r,
F_r = sum of absolute lower coefficients of D_r.
```

The exact threshold emitted by the verifier is

```text
M_r = max(2A_r+1, 7F_r+1, 10E_r+1, 2r).             (3)
```

No hidden asymptotic constant occurs.

## Exact ratio bound

Suppose the equation holds.  If `2(n+k)<=kd`, then every factor ratio is at
least `1+2/k`, so

```text
4 >= (1+2/k)^k
  > 1+2+binom(k,2)(2/k)^2
  = 5-2/k > 4,
```

a contradiction.  Hence `kd<2(n+k)`.  For the odd centered arguments

```text
v=2n+k+1,  w=v+2d,
```

integrality gives

```text
v >= k(d-1)+2 = 2r(d-1)+2.
```

Since `d>=2r`, this implies the strict inequality

```text
(r-1)w < rv.                                         (4)
```

For `0<=q<r`, the binomial estimate

```text
(1+1/(r-1))^(r-1) < sum_{j>=0} 1/j! < 3
```

therefore gives

```text
w^q < 3v^q.                                          (5)
```

The first strict inequality uses
`binom(m,j)/m^j <= 1/j!`; the second follows from
`1/j! <= 1/2^(j-1)` for `j>=2`, with strictness already at `j=3` when
needed.  The cases `m=1,2` are immediate from the same finite sum.

## Integer trap

The centered block identity is

```text
S_r(2x+2r+1) = 2^(2r) B(2r,x).
```

Thus the equation gives `S_r(w)=4S_r(v)`.  Set

```text
m = T_r(w)-2T_r(v),
X = T_r(w)+2T_r(v).
```

Equations (1)-(2) give exactly

```text
mX = D_r(w)-4D_r(v).                                 (6)
```

For `W>=M_r`, coefficientwise estimates from (3) give

```text
T_r(W) > W^r/2,
|D_r(W)| <= E_r W^q.
```

As `w>=v>=M_r`, equation (6) yields

```text
|m| < 10 E_r / w <= 10 E_r/M_r < 1.
```

Since `m` is an integer, `m=0`; hence (6) forces
`D_r(w)=4D_r(v)`.

On the other hand, `W>=M_r` also gives the strict leading-term bounds

```text
(6/7)|L_r|W^q < |D_r(W)| < (8/7)|L_r|W^q.
```

Combining these with (5),

```text
|D_r(w)|/|D_r(v)|
  < (4/3)(w/v)^q
  < 4,
```

contradicting `D_r(w)=4D_r(v)`.

Finally, `d>=M_r` and the displayed lower bound on `v` imply `v>=M_r`, so
the proof applies with the explicit statement above.

## Audit boundaries

- `r=1` is deliberately excluded; the ratio-power argument uses `r-1`.
- No smoothness assumption is used, so the result is stronger on its stated
  range than Target 2.
- The proof uses `d>=k`; it does not touch the known `d=1` telescopes.
- The argument is coefficientwise and exact.  The finite test through
  `k=40` checks the generator, not the universal quantifier; universality is
  supplied by the descending recurrence and the inequalities above.
- The threshold is intentionally enormous.  This is a proper effective tail,
  not a claim that the remaining finite strip has been checked.

## Reproduction

```bash
python3 compute/campaign686/agent_t2_even_tail/even_tail_verify.py
python3 -m pytest -q compute/campaign686/agent_t2_even_tail
```
