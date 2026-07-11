# Erdős 686 three-cleaned-bucket attack

Status: **new exact second/third elimination; target-row degeneracy scan
complete; three-bucket closure not proved.**

The machine-checked algebra is in
`ErdosProblems/Erdos686ThreeBucketRestriction.lean`.  The independent
integer reproduction is `three_bucket_attack.py`, with tests in
`test_three_bucket_attack.py`.

## Setup

Let three pairwise-coprime cleaned components occupy distinct residual
indices `i,j,l`.  Write

```text
d = g P Q R,
X_i = 3(n+i)-d = a P^2,
X_j = 3(n+j)-d = b Q^2,
X_l = 3(n+l)-d = c R^2,
```

with `a,b,c,P,Q,R,g>0`.  The concentration theorem supplies this form after
grouping cleaned prime powers by owner.  The bounded loss satisfies
`1 <= g <= G_k`, with

```text
G_5  = 108,             G_7  = 1,620,
G_9  = 136,080,         G_11 = 1,224,720,
G_13 = 242,494,560,     G_15 = 18,914,575,680.
```

Put `C_s,D_s,E_s` for the constant, linear, and quadratic coefficients of
the signed local cofactor at index `s`.

## Exact second-order elimination

At owner `i`, the audited second local lift is

```text
P | 3 C_i a - 4 D_i (g Q R)^2.                         (1)
```

The two residual differences are

```text
a P^2 - b Q^2 = 3(i-j),
a P^2 - c R^2 = 3(i-l).                                (2)
```

Multiply (1) by `bc`.  Modulo `P`, (2) gives

```text
b Q^2 = -3(i-j),       c R^2 = -3(i-l).
```

Therefore

```text
P | O_i,
O_i = 3[C_i abc - 12 D_i g^2 (i-j)(i-l)].              (3)
```

The same argument cyclically gives `Q|O_j` and `R|O_l`.  Lean proves the
generic signed-integer identity, with no primality, positivity, or
coprimality assumption.  In fact it proves the stronger intermediate fact

```text
P^2 | (bQ^2)(cR^2)-9(i-j)(i-l).                        (4)
```

## The finite degeneracy is completely resolved

For fixed `k,i,j,l,g`, obstruction `O_s` vanishes only at the slope

```text
abc/g^2 = 12 D_s (s-u)(s-v) / C_s,                     (5)
```

where `{u,v}` are the other two indices.  Exact rational evaluation checks
all

```text
C(5,3)+C(7,3)+C(9,3)+C(11,3)+C(13,3)+C(15,3) = 1,035
```

unordered index triples.  In every triple the three slopes in (5) are
pairwise distinct.  Consequently at most one of `O_i,O_j,O_l` can vanish.
This includes reflected pairs and the center; neither is discarded.

The minimum pairwise rational slope separations in rows
`5,7,9,11,13,15` are respectively

```text
10, 7, 27/5, 99/35, 117/70, 15/14.
```

Thus the obstruction is not a finite-coefficient degeneracy analogous to
the reflected exception in the two-bucket case.

## Exact third-order composition

The audited third local lift is

```text
P^2 | -3[3 C_i a - 4 D_i(g Q R)^2]
      +20 E_i P(g Q R)^3.                              (6)
```

Multiplying by `bc` and using (4) modulo `P^2` gives the new exact result

```text
P^2 | F_i,
F_i = -3 O_i + 180 E_i g^2(i-j)(i-l)d.                 (7)
```

This is Lean-proved in signed integers.  The verifier checks both (3) and
(7) on **5,216 signed exact fixtures**.

Equation (7) also gives the hostile route verdict.  Modulo `P`, its new term
is already zero because `P|d`, so (7) reduces to `-3O_i`.  It supplies no
second polynomial in `abc` whose resultant with (3) is a fixed nonzero
integer.  The two global cubic moment combinations behave the same way:
localizing either at an owner reproduces the second local residue (1), not an
independent congruence.

## Congruence-only falsifier, stated precisely

The verifier constructs the following **non-solution**:

```text
k = 5,       (i,j,l) = (1,2,4),
P = 101^20,  Q = 103^20,  R = 107^20,  g = 1.
```

Its gap `d=PQR` has 121 decimal digits.  CRT first enforces the three exact
square residuals, then lifts the free parameter modulo `P^2,Q^2,R^2` so that
all three third local congruences hold.  Direct integer evaluation confirms:

```text
P|n+i, Q|n+j, R|n+l;
P^2|X_i, Q^2|X_j, R^2|X_l;
all three second local congruences;
all three third local congruences;
d^3 divides each of the lower and upper global moment combinations.
```

It is not a counterexample to Erdős 686.  The exact block equation is false,
and its largest selected residual is vastly larger than `14d`; equivalently,
the verified short window fails.  This witness falsifies only the proposed
route “derive a bounded resultant from the square, moment, second-local, and
third-local congruences alone.”

## Single remaining quantified gap

The exact unresolved arithmetic core is the following short-CRT lemma.

> **Three-bucket short-CRT lemma.**  For
> `k in {5,7,9,11,13,15}`, let `A_k=14,17,23,26,29,35` and let `G_k` be the
> exact loss budget above.  There do not exist `d>=10^120`,
> `1<=g<=G_k`, pairwise-coprime `P,Q,R>1`, distinct
> `i,j,l in [1,k]`, and positive `a,b,c` such that
> `d=gPQR`, all three residuals `aP^2,bQ^2,cR^2` lie in one step-three
> progression and are `<A_k d`, and the three second and third local
> divisibilities (1) and (6) hold.

This lemma is stronger than the equation-specific three-bucket tail: it no
longer mentions the block equation, only its verified window and exact local
consequences.  It is not proved here.  It is the precise place where a
short-CRT, lattice, or higher Taylor argument must enter.  Returning (7) as
a full closure would be circular because (7) alone admits the target-size
CRT falsifier above.

## Boundary audit

- The genuine `d=1` telescopes at `k=9,15` have no three nontrivial cleaned
  components and are outside the setup.
- Center owners are included in all 1,035 triples.  Their `D_s=0` gives
  slope zero, which cannot equal a positive `abc/g^2`; no cancellation is
  inferred from that fact alone.
- Reflected owners are included; the three-owner slope determinant is still
  nonzero pairwise.
- Small primes `2` and `3` are not treated as units here.  Their exact losses
  remain in `g`; the algebraic identities (3) and (7) do not cancel `g` or
  any prime.
- The CRT witness is labeled a non-solution and is used only to falsify a
  congruence-only closure.

## Reproduction

```bash
lake env lean ErdosProblems/Erdos686ThreeBucketRestriction.lean
python3 -m pytest compute/campaign686/test_three_bucket_attack.py -q
python3 compute/campaign686/three_bucket_attack.py --pretty
```
