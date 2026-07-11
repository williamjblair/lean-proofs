# Hostile audit: Erdős 686 fourth local lift

## Verdict

**PASS as a proper fourth-order necessary restriction.  It does not close the
three-owner branch or Erdős #686.**

The frozen Lean theorems, the denominator-cleared formula, the cyclic
three-owner composition, and the target-size Hensel/CRT falsifier all survive
independent reconstruction.  The fourth lift adds one owner-adic digit beyond
the banked third lift.  The exact `e=20` CRT representative before the fourth
lift has three nonzero fourth quotient residues, while a further CRT step
makes all three fourth residues zero.  The resulting 121-digit-gap tuple fails
all three short-window inequalities and the exact block equation.  Therefore
the new congruence is genuine, but congruence-only closure remains false.

## Frozen producer surface

The audit began by reproducing the supplied SHA-256 values exactly:

```text
22d853c7eac8064aeee977c20757b5f4000006483a2cfade54ef0347c8c4d0be  ErdosProblems/Erdos686FourthLocalLift.lean
22ab5000e33fb6fd4dc6011de76f61165e658d06b8d7efd96139d0133e025068  compute/campaign686/fourth_local_lift_verify.py
99451323a4c12646a62666d6e72ada7da9cbac40ccffd2ca20a8a9e3bdab963f  compute/campaign686/test_fourth_local_lift_verify.py
03b50d019a69760f2b64baa7b57855adae957c2b0cd591383d45b773c432471a  compute/campaign686/fourth_local_lift_findings.md
a162050046ae840a9e520d5c226190cb2ea1676d67e0b7cd256e3951b4930ed0  docs/plans/2026-07-10-erdos686-fourth-local-lift.md
```

No producer file was edited.  The independent audit artifacts are:

```text
deb775c918b4cae356044df75ff9175a592539b9fb0ff57c1160802e5ed63bcd  ErdosProblems/Erdos686FourthLocalLiftAudit.lean
69851c68aea7571e4a344579ea4f1f906a7c1113a02cdd216b63504484404202  compute/campaign686/fourth_local_lift_hostile_verify.py
7ebcb7be06c0670f71f418a23352ca4c233359a02fbe07cc2961344454b4ea21  compute/campaign686/test_fourth_local_lift_hostile_verify.py
3b0a73831bfa59667ef3923318724c08158204a654f9abfdc64f14e1834e7d76  docs/plans/2026-07-10-erdos686-fourth-local-lift-hostile-audit.md
```

The hostile verifier imports no producer or earlier campaign Python module.
It obtains the Taylor coefficients from reciprocal elementary symmetric sums,
whereas the producer uses polynomial multiplication.

## Dependency tree and per-node verdict

```text
exact block equation
  |
  +-- N1  fourth Taylor remainder for the local cofactor
  |     |
  |     +-- N2  cancel H^2 from an H^5 divisibility, H != 0
  |             |
  |             +-- N3  denominator clearing with 3X-M=AH
  |                     |
  |                     +-- N4  local fourth lift H^3 | G4
  |                             |
  |                             +-- N5  two square-residual differences
  |                                     |
  |                                     +-- N6  refined third composition mod P^3
  |                                     +-- N7  fourth correction mod P
  |                                               |
  |                                               +-- N8  cyclic P^3 obstruction
  |
  +-- N9  verified positive short window
          |
          +-- OPEN: combine N8 with N9 to exclude every target-size tuple
```

| Node | Verdict | Exact audit result |
|---|---|---|
| N1 | PASS | All 60 target-row owners passed reciprocal-coefficient reconstruction and 420 fourth-remainder evaluations. |
| N2 | PASS | The Lean proof cancels `H^2` only with `H != 0`; it does not cancel `3`. |
| N3 | PASS | `15,120` signed exact identities passed, including `3,240` with `abs(H)=3` and `3,960` with `abs(H)=1`. |
| N4 | PASS | The natural-number adapter correctly supplies `H>0`, `H|L`, the upper/lower cofactor remainders, and the exact block equation. |
| N5 | PASS | The product of the two residual differences expands with the required linear and constant corrections. |
| N6 | PASS | The term `36*a*D*g^2*P^2*(deltaLeft+deltaRight)` is required modulo `P^3`. |
| N7 | PASS | The coefficient is exactly `6804=84*9^2`; the correction is only reduced modulo `P`, exactly as required after multiplication by `P^2`. |
| N8 | PASS | All 1,035 target-row triples were checked at all 3 cyclic owners in 111,780 signed fixtures; every refined, correction, and final remainder was zero. |
| N9 | NOT DERIVED | The fourth congruence does not imply any short-window inequality.  The exact target-size lifted tuple has all three residuals greater than `10^483*d`. |
| Open composition | OPEN | No audited theorem excludes the short tuple.  Target 1 and #686 remain open. |

No node above is a private unproved lemma.  N1 through N8 are either explicit
kernel theorems or exact integer identities independently replayed here.  N9
is retained as an external verified hypothesis in the remaining lemma; it is
not inferred from the fourth lift.

## 1. Independent denominator clearing

For one owner, let

```text
Q(z) = C + D*z + E*z^2 + F*z^3  (mod z^4),
L = H*X,
d = H*M,
3*X-M = A*H.
```

The block equation and the two fourth-power cofactor remainders give

```text
H^5 | H^2*T4,
```

where

```text
T4 = -C*A
     + D*((X+M)^2-4*X^2)
     + H*E*((X+M)^3-4*X^3)
     + H^2*F*((X+M)^4-4*X^4).
```

Because `H != 0`, cancellation gives `H^3|T4`.  Substitution of
`M=3X-AH` gives the exact integer identity

```text
27*T4 - G4
  = H^3 * (
      80*A*F*M^3
      + H*(-3*A^3*E + 24*A^2*F*M^2)
      - A^4*F*H^3),
```

with

```text
T3 = -3*(3*C*A-4*D*M^2) + 20*E*H*M^3,

G4 = 3*T3
     + H^2*(-9*D*A^2 + 36*E*A*M^2 + 84*F*M^4).
```

Thus `H^3|G4`.  The identity is integral and never divides by `3`, so it
remains valid at `H=3` and at every nonzero multiple of `3`.

The audit checked `15,120` instances over all 60 owners, with

```text
H in {-5,-3,-2,-1,1,2,3,5},
M in [-5,5],
A in [-4,4],
3 | M+A*H.
```

The frozen producer's deliberate fixture `(k,i,H,M,A)=(9,2,11,37,-5)`
also survives.  If one deletes a single correction from `G4`, the resulting
remainders modulo `11^3` are respectively

```text
delete -9*D*A^2       -> 121,
delete 36*E*A*M^2     -> 484,
delete 84*F*M^4       -> 726.
```

All are nonzero.  Setting `A=0` is therefore not a valid simplification of
the cleaned-residual case.

## 2. Independent cyclic composition

At the `P` owner write

```text
a*P^2-b*Q^2 = 3*deltaLeft,
a*P^2-c*R^2 = 3*deltaRight,
M = g*Q*R,
d = g*P*Q*R,
t = a*b*c.
```

Multiplying the two exact differences gives

```text
(b*Q^2)*(c*R^2)
  = a^2*P^4
    - 3*a*P^2*(deltaLeft+deltaRight)
    + 9*deltaLeft*deltaRight.                         (A)
```

Let `Phi` denote the banked composed third obstruction.  The independent
expansion splits into two precise divisibilities:

```text
P^3 | b*c*T3 - Phi
      + 36*a*D*g^2*P^2*(deltaLeft+deltaRight),         (B)

P | (b*c)^2*K - K0,                                   (C)
```

where

```text
K = -9*D*a^2 + 36*E*a*M^2 + 84*F*M^4,

K0 = -9*D*t^2
     + 324*E*t*g^2*deltaLeft*deltaRight
     + 6804*F*g^4*(deltaLeft*deltaRight)^2.
```

The last coefficient follows directly from the last term of (A):

```text
84 * (9*deltaLeft*deltaRight)^2
  = 84*81*(deltaLeft*deltaRight)^2
  = 6804*(deltaLeft*deltaRight)^2.
```

Multiplying (B) by `3bc`, multiplying (C) by `P^2`, and adding yields

```text
P^3 | (b*c)^2*G4 - Psi,
```

where

```text
Psi = 3*b*c*Phi + P^2*J,

J = -9*D*t^2
    -108*D*t*g^2*(deltaLeft+deltaRight)
    +324*E*t*g^2*deltaLeft*deltaRight
    +6804*F*g^4*(deltaLeft*deltaRight)^2.
```

Consequently `P^3|G4` implies `P^3|Psi`.  Relabeling the owners gives the
other two cyclic conclusions.  No coprimality, positivity, or unit
cancellation is used in this algebraic theorem.

The hostile grid checked every target-row triple and every cyclic owner with

```text
P in {-3,-2,2,3},
Q=R=1,
g in {-1,1,2},
a in {-2,0,3},
b=a*P^2-3*deltaLeft,
c=a*P^2-3*deltaRight.
```

This is `1,035*3*4*3*3 = 111,780` exact compositions.  It contains `55,890`
fixtures with `abs(P)=3`, `97,892` fixtures with at least one signed negative
quantity, all 251 center-owner positions, and all 251 triples containing a
reflected pair.

The small sensitivity fixture

```text
(k,owner,P,Q,R,a,b,c,g,deltaLeft,deltaRight)
  = (5,1,11,1,1,-5,-602,-599,2,-1,-2)
```

has correct composed remainder `0 mod 11^3`, but gives

```text
replace (bc)^2 by bc              -> 552 mod 11^3,
replace 6804 by 756=84*9          -> 847 mod 11^3,
delete the -108 refined term      -> 242 mod 11^3.
```

The unit values `Q=R=1` make this a test of the generic integer identity, not
a target short-CRT tuple.  The target-size audit below uses three nonunit,
pairwise-coprime components.

## 3. Independent Hensel/CRT reconstruction

For `k=5`, owners `(1,2,4)`, and

```text
P=101^e, Q=103^e, R=107^e, d=P*Q*R,
```

let `x` be the residual at owner `1`.  First solve

```text
x + 3*(i-1) = 0 mod P_i^2
```

for the three owners, and write the common solution as `x=x0+d^2*s`.
The third residue is affine in `s`; its exact derivative is

```text
-9*C_i*(d/P_i)^2 mod P_i^2.                           (D)
```

After solving (D), write `s=s0+d^2*u`.  Divide the fourth residue by
`P_i^2`.  Its finite-difference derivative modulo `P_i` is exactly

```text
-27*C_i*(d/P_i)^4 mod P_i.                            (E)
```

The local constants are

```text
C_1=24, C_2=-6, C_4=-6.
```

Each base prime is distinct from the other two and from `2` and `3`, so (D)
and (E) are units for every integer `e>=1`.  CRT therefore solves the fourth
condition for every exponent.  Adding `d^3` to `s` changes `x` by `d^5`,
preserves every fourth residue, and cycles through all residues modulo `3`;
one of three choices reconstructs an integer `n`.  Adding `3*d^3*v` for any
positive integer `v` preserves integrality and every congruence while making
the positive residuals arbitrarily large.  Thus no upper bound on `d` can
follow from this congruence package without the short window.

At `e=20`, before the fourth lift the three quotient residues are exactly

```text
439987804685666293694081422867534157888,
7797703725030760165134404338142874334319,
35218501497772032758465410169995205298447.
```

All are nonzero.  This proves that the fourth condition is not already
implied by the third condition on this fixture.

After the fourth CRT step, the independently reconstructed gap is

```text
8528006514942991411329818759017663024603296760011487105481658555774743359211568625230878556970868752918452276874633718401.
```

It has 121 digits and exceeds `10^120`.  The reconstructed `n` has 604
digits.  Direct integer evaluation, without invoking the producer, gives at
all three owners:

```text
P_i | n+i,
P_i^2 | 3(n+i)-d,
P_i | second residue,
P_i^2 | third residue,
P_i^3 | fourth residue,
P_i^3 | cyclic composed fourth obstruction,
P_i^5 | B(5,n+d)-4*B(5,n).
```

Every displayed remainder is exactly zero.  The direct full-block comparison
is nonzero, so this tuple is not an Erdős #686 solution.  All three residuals
are positive, and each satisfies

```text
floor((3(n+i)-d)/d) >= 10^483 > 14.
```

Hence all three verified `k=5` short-window inequalities fail, not merely the
largest one.

The independent verifier also checks

```text
e in {1,2,3,5,8,10,12,16,20,24},
```

with gap digit counts

```text
7,13,19,31,49,61,73,97,121,146.
```

Each checked member is a proper fourth lift, satisfies all local and composed
congruences, fails the short window, and fails the block equation.

## 4. Boundary audit

- **Prime 3.** The local proof never cancels `3`.  The exact denominator grid
  contains 3,240 cases with `abs(H)=3`, and the composition grid contains
  55,890 cases with `abs(P)=3`.  The explicit Hensel family excludes prime 3
  only because it needs the displayed derivatives to be units; that exclusion
  is not imposed on the generic Lean theorem.
- **Signs.** The algebraic theorems are over `Z`.  The hostile grids contain
  negative owner components, losses, and residual cofactors.  Positivity is
  used only when classifying the final target-style CRT tuple.
- **Unit components.** The local identity was checked at `H=+-1`; the cyclic
  identity was checked with `Q=R=1`.  The unresolved target lemma still
  requires `P,Q,R>1`, as it must.
- **Centers.** For centers `3,4,5,6,7,8` in the six target rows, independent
  coefficient reconstruction gives `D=F=0`.  All 251 cyclic center-owner
  positions were included and no division by either coefficient occurs.
- **Reflections.** For every one of the 60 owners,
  `(C,D,E,F)` reflects to `(C,-D,E,-F)`.  All 251 triples containing a
  reflected pair were included in the composition grid.
- **Direct block-difference congruence.** The target witness checks
  `P_i^5 | B(5,n+d)-4B(5,n)` directly at each owner.  It does not infer those
  residues from the fourth formula alone.
- **Short-window scope.** All three positive residual inequalities are checked
  separately.  None holds in the target-size falsifier.
- **The `d=1` telescopes.** The `k=9,15` telescope fixtures do not have three
  nontrivial cleaned components and do not satisfy `d>=10^120`.  No theorem in
  this checkpoint claims to cover them.
- **Target 2 witnesses.** The row-prefix and smoothness falsifiers concern the
  large-`k` target.  This module asserts only a local identity and a
  three-owner cyclic consequence, so it makes no statement contradicted by
  those witnesses.
- **Notation collision.** The cubic Taylor coefficient `F` and the composed
  third obstruction are distinct objects.  The Lean definition expands both;
  the hostile verifier names the latter `Phi` conceptually and never reuses
  `F` for it.

## 5. Kernel and forbidden-token audit

The fresh module `ErdosProblems/Erdos686FourthLocalLiftAudit.lean` independently
kernel-checks the denominator identity, (A), and `6804=84*9^2`, then prints the
axioms of all four public theorems:

```text
localOffsetCofactor_fourth_order
fourth_order_local_algebra
fourth_order_local_lift
three_bucket_fourth_obstruction_dvd_cube
```

Each reports exactly

```text
[propext, Classical.choice, Quot.sound].
```

The source has no `sorry`, `admit`, `native_decide`, `unsafe` declaration, or
new axiom.  The literal word `axioms` occurs only in the required `#print
axioms` commands and documentation.

## 6. Exact remaining quantified gap

The audited result strengthens, but does not solve, the existing three-bucket
short-CRT node.  A sufficient next lemma is:

> For each `k in {5,7,9,11,13,15}`, with the banked constants `A_k` and `G_k`,
> there are no integers/naturals satisfying all of the following:
> `d>=10^120`; `1<=g<=G_k`; pairwise-coprime `P,Q,R>1`; three distinct owners
> `i,j,l in [1,k]`; positive `a,b,c`; `d=gPQR`;
> `aP^2-bQ^2=3(i-j)` and `aP^2-cR^2=3(i-l)`; all three residuals are less than
> `A_k*d`; and, cyclically at each owner, the banked second divisibility, the
> banked third divisibility, and the new fourth local divisibility hold.

Here, in increasing order of `k`,

```text
A_k = (14,17,23,26,29,35),
G_k = (108,1620,136080,1224720,242494560,18914575680),
```

and the new cyclic local condition at an owner with component `H`, cofactor
`A`, and opposite cofactor `M=d/H` is exactly

```text
H^3 |
  3*(-3*(3*C*A-4*D*M^2)+20*E*H*M^3)
  + H^2*(-9*D*A^2+36*E*A*M^2+84*F*M^4).
```

The cyclic composed fourth divisibility proved here follows from the local
fourth divisibility and the two exact square-residual differences, so it may
be included explicitly without changing the quantified content.  Deleting
the three upper-window inequalities makes the statement false by the audited
121-digit tuple.  No theorem-strength gap has been mislabeled as proved.

## Reproduction

```bash
python3 -m pytest \
  compute/campaign686/test_fourth_local_lift_verify.py \
  compute/campaign686/test_fourth_local_lift_hostile_verify.py -q
python3 compute/campaign686/fourth_local_lift_hostile_verify.py --pretty
lake env lean ErdosProblems/Erdos686FourthLocalLift.lean
lake env lean ErdosProblems/Erdos686FourthLocalLiftAudit.lean
```

The audit changed no shared imports, manifest, attestation, frontier, campaign
dashboard, producer file, or git history.
