# Erdős 686 short-window quotient-zero ledger at tail 1000

Date: 2026-07-12

Status: **exact ledger correction and fifth-quotient normalization; no closure of the live joint-nonzero branch.**

## 1. Equation-facing status

The historical short-window quotient package retained cases in which one or
more composed third quotients vanish.  Those cases are no longer live.
`exactRatio_target_three_bucket_all_third_obstructions_nonzero` derives from
the exact block equation and exact ratio window that all three composed third
obstructions are nonzero for every supplied target three-bucket decomposition
at `d >= 10^120`.  The new theorem

```text
exactRatio_target_three_bucket_all_third_quotients_nonzero
```

adds the literal quotient identities `T_s=P_s^2 z_s` and concludes
`z_1 != 0`, `z_2 != 0`, and `z_3 != 0`, without division or primality.
Consequently every one-zero, two-zero, three-zero, center-zero, and
noncentral-zero quotient branch is equation-facing impossible already at
`10^120`, hence also at the current `10^1000` odd-tail boundary.

## 2. Independent historical cutoff reconstruction

The additive verifier reconstructs the local coefficient polynomial,
reduced fourth coefficients, primitive three-row lattice weights, and row
loss bounds without importing the frozen producer.  For noncentral zero
owners it checks

```text
M = L^2 * |Gamma| * G_k^12 < |w_r| * D^2,
L = lcm(|K_1|,|K_2|).
```

The exact placement ledger is:

| `k` | placements | zero-weight contradictions | numerical closures at `10^1000` |
|---:|---:|---:|---:|
| 5 | 18 | 2 | 16 |
| 7 | 75 | 3 | 72 |
| 9 | 196 | 4 | 192 |
| 11 | 405 | 5 | 400 |
| 13 | 726 | 6 | 720 |
| 15 | 1,183 | 7 | 1,176 |
| **total** | **2,603** | **27** | **2,576** |

All 2,603 placements therefore close numerically at `D=10^1000`.  Relative
to the historical `10^120` scan, the only additional placements are the 282
old row-15 survivors.

For every nonzero-weight placement the verifier computes the least positive
integer cutoff

```text
Dmin = isqrt(M // |w_r|) + 1
```

and checks `|w_r|*(Dmin-1)^2 <= M < |w_r|*Dmin^2`.  The global maximum is

```text
15855065204701151051583570030869346558944133017237495757148583758790408893113026893763598192399346355860926337293559495864273423092
```

(131 digits).  It occurs exactly twice, at row 15 placements
`(1,2,15)` with the first two owners zero and `(1,14,15)` with the last two
owners zero.  In both cases

```text
|w_r| = 34756818
L = 3059039240849393713751006665527076990713393190038663069696000
|Gamma| = 445293896574717137525760
G_15 = 18914575680.
```

Thus `10^130` leaves exactly those two historical placements, while
`10^131` closes all 2,603.  This numerical strengthening is recorded only as
an audit of the old package; the equation-facing proof uses nonvanishing.

## 3. Current support and geometry ledger

Unit buckets are retained in `AllOwnerAssemblyThirdNonzeroCertificate`, so a
live owner means an index whose bucket is not one.  The two-owner theorem
excludes support cardinality at most two.  Among three-owner supports, the
tail-1000 reflected determinant closes exactly the 27 center/reflected sets.
The current exact support ledger is:

| `k` | supports of size at least 3 | closed center/reflected | open |
|---:|---:|---:|---:|
| 5 | 16 | 2 | 14 |
| 7 | 99 | 3 | 96 |
| 9 | 466 | 4 | 462 |
| 11 | 1,981 | 5 | 1,976 |
| 13 | 8,100 | 6 | 8,094 |
| 15 | 32,647 | 7 | 32,640 |
| **total** | **43,309** | **27** | **43,282** |

Equivalently, the exactly-three all-nonzero branch contains 1,008
nonreflected triples after the 27 reflected triples are removed.  Every
support of cardinality at least four remains in the joint-nonzero full-owner
problem.

## 4. Exact fifth-order normalization

Let `K4` be `threeBucketReducedFourthCoefficient` and let `R5(d)` be
`threeBucketReducedFifthCoefficient`.  Direct polynomial algebra gives

```text
R5(d) = 27*K4 + d*S1 + d^2*S2,
```

where, for `p=x*y` and `s=x+y`,

```text
S1 = 8748*p*(
  255*C^2*G*p - 120*C*D*E*s + 240*C*D*F*p +
  180*C*E^2*p - 120*D^2*E*p).
```

In particular `R5(0)=27*K4` identically.  Across all 3,105 cyclic target
positions, `S1` is nonzero; its absolute value ranges from `27,818,640` to

```text
277726044983936190440323571987184359571456000.
```

The quadratic coefficient vanishes exactly at the 27 cyclic
center/reflected positions (54 oriented views in the historical ordered
census).

Writing the reduced fourth numerator as `P*w` and the gap as `d=P*M`, the
reduced fifth square congruence is exactly the next Hensel relation

```text
P | 27*w + M*S1*g^4.
```

The third quotient has disappeared.  The three-row lattice controls the
third quotients, not the new fourth quotients `w`, so it supplies no cyclic
resultant here.  This is a proper normalization of the fifth lift, not a
component bound.

The frozen hostile-audited fifth-lift constructor was also replayed at
exponent 166.  Exact integers give a 1,004-digit gap and a 6,023-digit lower
parameter; every local, composed, squared-quotient, and reduced fifth
remainder is zero and every third obstruction is nonzero.  The block equation
and upper residual window are both false.  This is a tail-size route
falsifier, not an Erdős 686 counterexample.

## 5. Exact remaining gap

At `d >= 10^1000`, every third quotient is nonzero.  The 27 supplied
center/reflected triples are impossible.  The remaining odd arm consists of
the 1,008 nonreflected three-owner geometries and all support configurations
of cardinality at least four, with simultaneous nonzero second/third
divisibilities and the exact short window.  The large-row smooth residual is
unchanged.  No theorem in this checkpoint proves either residual arm.
