# Target 2 pure three-owner floor elimination

Status: **a proper equation-level reduction is kernel-banked; the pure
three-owner subcase is not closed.**

Assume the reflection center has no small-prime loss and exactly three
complete, pairwise-coprime large components:

```text
S = P Q R,       h = d+k+1,       e_i = h-2i.
```

At the owner `i` of `P`, clearing the harmless factor two in the reflected
square lift gives

```text
even k:  P^2 | 5S-3e_i,
odd  k:  P^2 | 3S-5e_i.
```

For `k>=220`, the exact product window pins `t=abc` to `15S+r` in an
even row and `3S+r` in an odd row, with `0<r<S`.  Substitution into the
banked reflected third composition, followed by the square lift, eliminates
`S` entirely.  With

```text
C_i = product_{1<=j<=k, j!=i} (j-i),
D_i = coefficient of z in product_{j!=i}(z+j-i),
E_i = coefficient of z^2 in the same product,
Delta_i = (i-j)(i-l),
```

the new exact consequences are

```text
even: P^2 | 5 C_i r + 45 C_i e_i
                 + 60 Delta_i (E_i e_i-D_i),

odd:  P^2 | 3 C_i r + 15 C_i e_i
                 + 60 Delta_i (D_i-E_i e_i).
```

The proof uses no hidden inverse.  It cancels `9` in the even third
composition and `5` in the odd composition only under explicit coprimality
hypotheses.  Those hypotheses are automatic when every prime base of the
component exceeds `k>=220`.

## Exact finite diagnostics

The independent verifier exhausts every prime triple with
`k<p<501` for `k=220` and `k=223`, and every owner representative allowed
by the exact weak target inequalities `9d<n` and `kd<5n`.  This is `33,511`
prime triples.  It finds:

| row | square/floor rows | rows satisfying endpoint window | rows with even one third component zero |
|---:|---:|---:|---:|
| 220 | 71 | 0 | 0 |
| 223 | 2 | 0 | 0 |

The rows form two exact translation families.  Replaying those families for
every `220<=k<=240` gives `981` square/floor rows; none has even one zero
third-composition component.  This finite result is diagnostic only.

The first even row is

```text
k=220, (P,Q,R)=(397,311,353), (i,j,l)=(1,10,150),
S=43583851, h=34541, n=21774655, d=34320,
(a,b,c)=(691,1126,874),
t=680029684=15S+26271919.
```

Its three third residues modulo `(P^2,Q^2,R^2)` are
`(43815,69414,61283)`.  The first odd row is

```text
k=223, (P,Q,R)=(487,293,313), (i,j,l)=(191,1,222),
S=44662283, h=424559, n=22118862, d=424335,
(a,b,c)=(278,768,673),
t=143688192=3S+9701343,
```

with third residues `(73334,74178,48029)`.  Both rows fail the endpoint
window and the block equation; they show only that the square/floor layer is
nonempty under the weaker target inequalities.

## Boundary fixtures for the proposed CRT shortcut

The original third-composition congruences plus the pinned floor and even the
exact endpoint window do not imply the square decompositions or the block
equation.  Two exact fixtures are:

```text
even:
  k=220, (P,Q,R)=(233,239,241), (i,j,l)=(188,71,129),
  S=13420567, h=42505, n=6689031, d=42284,
  t=202928721=15S+1620216;

odd:
  k=223, (P,Q,R)=(227,229,233), (i,j,l)=(76,45,29),
  S=12112039, h=37871, n=6037084, d=37647,
  t=43458456=3S+7122339.
```

For both fixtures all three original `P^2` third-composition residues are
zero, `0<r<S`, `k<=d`, `9d<n`, `kd<5n`, and both exact endpoint inequalities
hold.  Nevertheless their square residues are respectively

```text
(46200,14967,33391),
(38611,33902,49578),
```

and both exact block-product errors are nonzero.  Therefore a resultant or
CRT argument using only the pinned floor and the three affine third rows
cannot close the branch; it must retain the simultaneous square system.

## Exact remaining subcase

The remaining node is the following strictly scoped statement:

> For every `k>=220`, an exact block solution cannot have a reflection center
> `S=PQR` whose complete prime-power components are pairwise coprime, supported
> on primes above `k`, and assigned to exactly three distinct reflected owners,
> while simultaneously satisfying the three component-square decompositions.

Equivalently at the current reduction level, one must rule out the
simultaneous system consisting of the three square congruences, the exact
product identity defining `t=abc`, `0<r<S`, and the three new affine
square-modulus forms.  Dropping either the square layer or the equation layer
is falsified above.  No universal resultant or support contradiction for the
simultaneous system was found.

## Reproduction

```bash
lake env lean ErdosProblems/Erdos686PureThreeOwnerFloor.lean
PYTHONDONTWRITEBYTECODE=1 python3 -m pytest -q \
  compute/campaign686/agent_t2_pure_three_floor
```
