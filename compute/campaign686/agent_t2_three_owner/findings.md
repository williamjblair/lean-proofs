# Target 2 three-owner quotient and reflected third composition

Status: **proper next-order Lean restriction; the proposed uniform floor is
falsified, and the sign/lattice route remains mixed.**

Let `S=2n+d+k+1`.  At an even reflected owner put
`L_i=S+3(n+i)=a_iP_i^2`; at an odd owner put
`M_i=5(n+i)-S=a_iP_i^2`.  If `S=PQR`, then

```text
L_i L_j L_l / S^3 = abc/S,
M_i M_j M_l / S^3 = abc/S.
```

The expected bounds `15<abc/S<16` and `3<abc/S<4` do not follow uniformly
for `k>=16`.  The exact fixture

```text
k = 16
d = 10^120
n = 11048779707016795813821579472468786620154883955085119052786776282417721075083493368730493012989644397541638075075311190921
owners = (1,8,16)
```

satisfies both endpoint ratio-window inequalities, but exact cross
multiplication gives `prod(L)<15*S^3` and `prod(M)<3*S^3` (the decimal
ratios are about `14.4386958966` and `2.6958534947`).  This falsifies a
window-only deduction; it is not asserted to have the three square
decompositions.

There is a correct unbounded range.  The banked inequality `k*d<5*n`, with
`d>=k`, proves for `k>=220`

```text
37*S < 15*L_i,   2*L_i < 5*S,
13*S <  9*M_i,   2*M_i < 3*S.
```

Cubing yields the expected two product windows for every owner triple.

The new kernel-banked next-order composition is in
`Erdos686ReflectedThirdComposition.lean`.  From the raw reflected next lift,
the three residual-difference identities, and `S=gPQR`, it proves

```text
even: P^2 | 9*C*abc - 108*D*g^2*deltaQ*deltaR
                    + 180*E*g^2*deltaQ*deltaR*S,
odd:  P^2 | 5*C*abc + 100*D*g^2*deltaQ*deltaR
                    -  60*E*g^2*deltaQ*deltaR*S.
```

Thus the three cyclic rows are affine in `(abc,S)`.  Their cross product
eliminates both variables and leaves the explicit `D` correction; the exact
lattice identity is also kernel-banked.  A canonical exact scan for every
`k=16,...,200`, using a deep endpoint-window point and owners
`(1,floor((k+1)/2),k)`, finds a mixed weighted sign cell in all 185 rows.
This is an exact counterfamily to any uniform claim that all reflected
third-composition cells are one-sided.  It does not rule out useful
one-sided subcells at other owner placements.

Two synthetic boundary fixtures keep the dependencies honest.  The first
has all three square lifts and `d>=k` but fails the ratio window:

```text
(k,n,d)=(16,8341,4500), S=17*29*43,
owners=(6,11,1), (a,b,c)=(160,55,25).
```

The second also satisfies `9d<n` and the lower window, but fails the upper
window:

```text
(k,n,d)=(16,8547105,847742), S=41*239*1831,
owners=(1,13,3), (a,b,c)=(25927,763,13).
```

Reproduce with:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 -m pytest -q \
  compute/campaign686/agent_t2_three_owner
lake env lean ErdosProblems/Erdos686ReflectedThirdComposition.lean
```
