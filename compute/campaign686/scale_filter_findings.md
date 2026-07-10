# Erdős 686 odd tails: exact scale-filter verdict

Date: 2026-07-10. Status: exact arithmetic and pytest artifact; not yet
formalized in Lean.

Reproduce:

```text
python3 -m pytest -q compute/campaign686/test_scale_filter_counterfamily.py
python3 -m compute.campaign686.scale_filter_counterfamily --t 1
```

The script reads the 341-row files
`compute/artifacts/thue_convergents_k{5,7,9,11,13,15}.json`. Their declared
source is `compute/theory/gen_thue_convergents.py`, and their index range is
exactly `0..340`.

## 1. Scale polynomial and its first two filters

For `k = 5`, write

```text
X = g*u,  Y = g*v,  gcd(u,v) = 1,  z = g^2,
A_j = 4*v^j - u^j.
```

Then `P_5(X) = 4 P_5(Y)` is exactly

```text
Q(z) = A_5*z^2 - 5*A_3*z + 4*A_1 = 0.                 (1)
```

Consequently

```text
z   | 4*A_1,
z^2 | 4*A_1 - 5*z*A_3.                               (2)
```

These are the constant-term and next-coefficient `z`-adic filters. They are
genuine consequences, but the family below proves that they do not bound
`g`, even after imposing coprimality, parity, the correct side of
`4^(1/5)`, and the campaign's rational ratio window.

## 2. An unbounded exact counterfamily

Let

```text
G0 = 204*71*251 = 3,635,484,
g  = G0*t                    for any integer t >= 1,
z  = g^2,
v  = 1 + 19*z^2/51,
u  = 4 + 75*z + 25*z^2/51.
```

Because `51 | z`, both `u` and `v` are integers. Direct expansion gives

```text
A_1 = 4*v-u = z(z-75).                                 (3)
```

### Coprimality

`gcd(z,v)=1`. If a prime divides both `z-75` and `v`, it divides

```text
51*v = 51 + 19*z^2
```

and hence, after substituting `z = 75`, divides

```text
51 + 19*75^2 = 106,926 = 2*3*71*251.
```

None of these primes divides both terms: `z-75` is odd; `v = 1 (mod 3)`;
and `z = 0 (mod 71*251)` makes `z-75` nonzero modulo `71` and `251`.
Thus `gcd(u,v)=gcd(z(z-75),v)=1`.

### Parity and ratio window

Since `4 | g`, `v` is odd and `v_2(u)=2`. The exact margins are

```text
100*u - 131*v = (11*z^2 + 382500*z + 13719)/51 > 0,
211*v - 160*u = 3*(z^2 - 68000*z - 2431)/17 > 0.
```

The second margin is positive already at `z >= G0^2`. Therefore

```text
131/100 < u/v < 211/160 < 4^(1/5),
```

where the algebraic-side comparison is the exact integer inequality

```text
211^5 = 418,227,202,051
      < 419,430,400,000 = 4*160^5.
```

In particular the weaker headline upper bound `u/v < 661/500 = 1.322`
also holds.

### Both congruences

Equation (3) proves the first congruence in (2). Also `v = 1 (mod z)` and
`u = 4v (mod z)`, so

```text
A_3 = 4*v^3-u^3 = -60 (mod z).
```

After division by `z`, the second remainder is

```text
(4*A_1 - 5*z*A_3)/z
  = 4*(z-75) - 5*A_3
  = 0 (mod z).
```

Thus both necessary filters hold for arbitrarily large square `z`.

### Explicit positivity certificate

Substitution into (1) gives

```text
2,255,067*Q(z) = z^2*R(z),
```

where

```text
R(z) = 907*z^10
 - 48,828,125*z^9
 - 14,943,141,610*z^8
 - 2,287,628,906,250*z^7
 - 175,247,492,914,005*z^6
 - 5,388,707,299,519,560*z^5
 - 1,430,018,958,108,645*z^4
 - 152,229,859,332,345*z^3
 - 3,352,908,563,415*z^2
 + 544,813,575,120*z
 + 38,300,057,928.
```

The sum of the absolute values of all negative coefficients is

```text
S = 7,151,859,139,313,955.
```

For `z >= 1`, every negative lower monomial is bounded below by its
coefficient times `z^9`. At the smallest family value

```text
z0       = G0^2 = 13,216,743,914,256,
907*z0   = 11,987,586,730,230,192
         > 7,151,859,139,313,955 = S.
```

Hence `R(z) > z^9(907*z-S) > 0`, and therefore `Q(z) > 0`, for every member
of the family. This is an exact falsification: all filters through the next
coefficient hold, while the full equation does not.

The `t = 1` fixture is

```text
g = 3,635,484
z = 13,216,743,914,256
u = 85,628,588,086,786,850,048,487,604
v = 65,077,726,945,204,651,633,737,985.
```

It has `gcd(u,v)=1`, `v` odd, `v_2(u)=2`, both congruence remainders zero,
the stated ratio inequalities, and `Q(z)>0`.

## 3. A valid stronger lemma: the k=5 floor pin

Suppose

```text
v >= 2, z >= 1, 3*u < 4*v, A_5 > 0, Q(z)=0.
```

Then

```text
z = floor(5*A_3/A_5).                                  (4)
```

Proof. From `3u < 4v`,

```text
27*A_3 = 108*v^3 - 27*u^3 > 44*v^3.
```

Also `A_1 < 4v`, and for `v >= 2`,

```text
220*v^3 > 864*v.
```

Therefore `5*A_3 > 8*A_1`. If `z*A_5 <= 4*A_1`, equation (1) would give

```text
5*z*A_3 = z^2*A_5 + 4*A_1
          <= 4*z*A_1 + 4*A_1
          <= 8*z*A_1,
```

a contradiction. Hence `z*A_5 > 4*A_1`, while (1), divided by `z`, gives

```text
0 < 5*A_3/A_5 - z = 4*A_1/(z*A_5) < 1.
```

This proves (4). Thus the scale is unique for a reduced pair `(u,v)`; the
integer floor must be a perfect square and must divide `4*A_1`.

## 4. Exact 341-convergent reproduction

On all 341 rows of `compute/artifacts/thue_convergents_k5.json`:

```text
A_5 > 0                                      171
positive floor(5*A_3/A_5)                    125
perfect-square floor                          71
perfect-square floor >= 4                      4
square floor also dividing 4*A_1              70
square floor >= 4 also dividing 4*A_1          3
exact Q(root) hits among these floor candidates 0
```

The four nontrivial square-floor rows are

```text
(index,z) = (38,4), (116,4), (204,4), (334,64).
```

The `z=64` row fails `z | 4*A_1`; the three `z=4` rows pass that divisibility
but fail the full equation.

The same script reproduces the successive `z`-adic filter counts for every
stored odd-k artifact, using the exact headline constant and the `Y_min`
from the corresponding banked Lean module:

```text
k=5:  total 161; passes 83,69
k=7:  total 292; passes 182,115,45
k=9:  total 343; passes 274,195,141,89
k=11: total 462; passes 352,242,189,117,27
k=13: total 505; passes 474,411,324,241,230,200
k=15: total 582; passes 564,477,403,317,301,254,111
```

There are zero exact roots in these valid `g >= 2` pure-convergent scale
families.

## 5. Discriminant route and exact blockage

For `k=5`, the discriminant condition is

```text
w^2 = 25*A_3^2 - 16*A_5*A_1
    = 9*u^6 + 64*u^5*v - 200*u^3*v^3
      + 64*u*v^5 + 144*v^6.                           (5)
```

Given a point of (5), the candidate scale is

```text
z = (5*A_3 + w)/(2*A_5)
```

up to the sign of `w`; requiring this rational function to be a square
adjoins a quadratic cover of the genus-2 curve. A connected double cover of
a genus-2 curve has genus

```text
2*2 - 1 + R/2 = 3 + R/2 >= 3
```

by Riemann-Hurwitz, so the square condition does not create a lower-genus
curve. More directly, writing `z=g^2` in (1) gives exactly
`P_5(g*u)=4P_5(g*v)` again. Closing the square cover is therefore a
target-strength restatement, not a new reduction.

The current external computation is evidence only: an exact search through
denominator 3000 found positive ratios only
`0,1,2,4,1/2,2/7,14/11`; Magma 2.29 with height bound 20000 returned
additional negative points but `proved=false`; `RankBounds` was `[3,5]`,
which blocks ordinary genus-2 Chabauty, and the geometric automorphism group
had order 2, exposing no bielliptic quotient.

## 6. Telescope audit and verdict

The exact `d=1` telescopes remain:

```text
k=9:  (Y,X,g,z) = (7,8,1,1),   P_9(8)=4P_9(7),
k=15: (Y,X,g,z) = (12,13,1,1), P_15(13)=4P_15(12).
```

Both have `d=1<k`, so they lie outside the disjoint-block domain. They also
show why no scale argument may silently discard `g=1`.

Verdict:

* **proved:** the floor pin (4), the exact counterfamily, its positivity
  certificate, the 341-row counts, and the telescope checks;
* **refuted:** constant-term, next-coefficient, parity, support-separation,
  sign, and coarse CF-window filters can force `g` into a finite set;
* **open:** excluding the primitive `g=1` branch and proving that the floor
  in (4) is never a square on the infinite continued-fraction tail;
* **not progress by itself:** the discriminant square cover, because it
  reconstructs the original equation and has no lower-genus advantage.

