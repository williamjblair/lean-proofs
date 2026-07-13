# Quadratic-strip / universal-even-tail bridge: hostile audit

Verdict: **the two existing branches do not compose, and parity-aware or
constant-rescaled versions of the current Runge certificate do not repair the
gap.**  This is a structural coefficient-growth obstruction, not merely the
absence of a proved upper bound for the universal threshold.

## 1. Exact first-correction obstruction

For `k=2r`, write

```text
S_r(X) = product_{j=1}^r (X^2-(2j-1)^2).
```

Let `Q_r` be monic of degree `r` and satisfy
`deg(Q_r^2-S_r)<r`, and write `q_i=[X^i]Q_r`.  Comparing the two top
nonleading coefficients gives

```text
[X^(2r-1)] S_r = 0                 => 2 q_(r-1) = 0,
[X^(2r-2)] S_r = -sum (2j-1)^2     => 2 q_(r-2) = -sum (2j-1)^2.
```

Since

```text
sum_{j=1}^r (2j-1)^2 = r(4r^2-1)/3,
```

one has

```text
q_(r-1)=0,
q_(r-2)=-r(4r^2-1)/6.
```

In the current universal certificate, `T=CQ_r` with `C>=1`,
`A=sum_{i<r}|[X^i]T|`, and

```text
M >= 2A+1 > r(4r^2-1)/3.
```

But the new quadratic theorem ends at

```text
d <= k^2/18 = 2r^2/9,
```

and, for every `r>=1`,

```text
r(4r^2-1)/3 - 2r^2/9 = r(12r^2-2r-3)/9 > 0.
```

Therefore the exact threshold constructed in
`Erdos686EvenTailSupply.lean` is strictly above the quadratic cutoff in every
row.  There is no overlap to compose.

## 2. Parity weighting does not fix the decisive node

Parity does improve two crude estimates: lower terms of `T` and `D` fall by
two degrees, so coefficient dominance can use powers of `W^2`.  The fatal
condition is instead the Runge smallness comparison

```text
|D(w)-4D(v)| < lattice_step * (T(w)+2T(v)),
```

where `D=T^2-C^2S`.  If `q=deg D`, its leading contribution requires a scale
of the form

```text
10 |[X^q]D| < lattice_step * C * v^(r-q).
```

Here `r-q=1` for odd `r` and `r-q=2` for even `r`.  The leading coefficient is
the first omitted Laurent coefficient of `sqrt(S)` and grows far faster than
the cubic center supplied at the edge of the quadratic strip.

One live row is already decisive.  For `r=17`, `k=34`, exact
recurrence gives the best denominator-cleared polynomial data

```text
C = 32768,
q = 16,
|[X^16]D| = 188162318421570695167361039564800,
E = sum_{i<=16}|[X^i]D|
  = 6375143223540100100577353665680166719158383844425.
```

The fixed divisor of `T(2a+1)` is exactly `g=255`; the gcd of the first
`18` values suffices by the integer finite-difference expansion for a degree
`17` polynomial.  Even granting this full fixed divisor as the lattice step,
the optimistic leading-only inequality needs

```text
v >= floor(10|[X^16]D|/(C g))+1
  = 225186598141623936273745117.
```

The full coefficient norm needs

```text
v >= floor(10E/(C g))+1
  = 7629565936566640936850578356790181141762389.
```

At the first complementary gap `d=65`, exact integer powers give

```text
1041616^34 < 4*1000000^34 < 1041617^34.
```

Combining this bracket with both necessary equation power windows gives
exactly `1528<=n<=1560`, hence

```text
3091 <= v=2*n+35 <= 3155.
```

The verifier checks the two boundary failures and successes directly with
integer powers, as well as the cross-multiplied linear bounds derived from the
displayed root bracket.  Therefore every possible equation center at this
gap is strictly below the optimistic leading-only threshold by more than
twenty orders of magnitude.  These numbers are a falsifier of that proposed
fixed-divisor-normalized proof route, not an equation counterexample.

## 3. A general interval-lcm estimate cannot change the exponent

For an interval of `m` positive consecutive integers, let `B` be its product
and `L` its lcm.  Prime-power counting gives the reverse divisibility

```text
B | L * (m-1)!.
```

Indeed, if `N_e` is the number of terms divisible by `p^e`, then

```text
v_p(B)-v_p(L)
  = sum_e max(N_e-1,0)
 <= sum_e floor((m-1)/p^e)
  = v_p((m-1)!).
```

For `m=2k-1`, this proves

```text
L_k(d) >= product_{s=-(k-1)}^(k-1)(d+s)/(2k-2)!,
```

so the `d^(2k-1)` exponent in the GPT-Pro lcm upper bound is sharp.  Improving
`Lambda(m)<=4^m` can change only the quadratic constant.  At `k=34`, even the
impossible best monomial coefficient `1/(2k-2)!` would let the resulting size
sandwich exclude only `d<=1204`; it cannot approach the minimal canonical
Runge threshold

```text
63751432235401001005773536656801667191583838444251.
```

Any lcm improvement that crosses the gap must therefore use
equation-specific owner correlation, not a stronger general interval
factorial estimate.

## 4. Narrow next lemma (not proved)

A coherent next Runge node must cancel the first omitted Laurent coefficient
*before* applying an integer-size trap.  For odd `r=2s+1`, write

```text
sqrt(S_r(x)) = Q_r(x) + b_(s+1)/x + O(x^-3).
```

Under `S_r(w)=4S_r(v)`, the usual integer
`m=C(Q_r(w)-2Q_r(v))` has its dominant term proportional to
`b_(s+1)(1/w-2/v)`.  The narrower missing task is to construct a
denominator-cleared integer eliminant that subtracts this term and then prove
a uniform nonzero lattice bound for that eliminant on the exact center window.
The same construction uses the `x^-2` term when `r` is even.

This is strictly more specific than the original equation: it specifies the
canonical Laurent coefficient, the denominator clearing, and the required
integer trap.  It is **not** banked progress.  Clearing `v,w` denominators can
make the next numerator larger, so a successful lemma must include a new gcd
or owner-correlation gain; parity and coefficient weighting alone do not
supply it.

## Reproduction

```sh
PYTHONDONTWRITEBYTECODE=1 python3 \
  compute/campaign686/agent_quadratic_tail_bridge/quadratic_tail_bridge_verify.py
PYTHONDONTWRITEBYTECODE=1 python3 -m pytest -q -p no:cacheprovider \
  compute/campaign686/agent_quadratic_tail_bridge/test_quadratic_tail_bridge_verify.py
```

Every reported number is reconstructed from `Fraction` and integer
arithmetic; no floating point, search for equation solutions, or probabilistic
test is used.
