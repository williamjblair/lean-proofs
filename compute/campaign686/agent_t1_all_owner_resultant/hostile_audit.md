# Hostile audit: Erdős 686 joint all-owner resultant

Verdict: **PASS as an exact negative audit; FAIL as a Target 1 closure.**

No Lean theorem is exported because the only new statement is an
obstruction to this approach family, not a stronger equation-facing
restriction.  No shared registry or frontier file is modified.

## Dependency tree

```text
N0  full solution of Target 1                                      OPEN
|
+- N1 reconstruct C_i,D_i,E_i on all 60 owner rows                PASS
|  `- exact match to Lean coefficient tables                       PASS
|
+- N2 individual full-owner data                                   BANKED INPUT
|  +- X_i=a_i P_i^2 and X_i-X_j=3(i-j)
|  +- d=g product_i P_i, bounded g
|  `- P_i^2|F_i, F_i!=0, sign(F_i)=-sign(C_i)
|
+- N3 form a product-square-divisible determinant                  PASS
|  +- all row entries divisible by P_i^2
|  `- product_{i in S}P_i^2 | C_S L_S(H)
|
+- N4 eliminate the common cofactor A                              FAIL
|  +- annihilator dimension exactly one                            PASS
|  `- sum lambda_i=(-3)^(s-1)/product X_i != 0                     PASS
|
+- N5 alternative four-owner linear circuits                      NEGATIVE
|  +- all 2,576 circuits enumerated                                PASS
|  +- one-sided sign circuits = 0                                  PASS
|  `- sole rank drop k=7,(2,4,6), still mixed                      PASS
|
+- N6 full-grid resultant gives target cutoff                      FAIL
|  +- L(D)=3V e_(k-2), L(E)=9V e_(k-3)                             PASS
|  +- exact third-order block truncation                           PASS
|  `- equation tail begins with d^4, so M^4 divisibility automatic PASS
|
`- N7 proper-subset modulus gives target cutoff                    FAIL
   `- no lower bound on selected bucket product; units permitted   PASS
```

## Quantified scope

The exhaustive set is exactly

```text
{(k,S): k in {5,7,9,11,13,15}, S subset {1,...,k}, 4<=|S|<=k}.
```

Its cardinality is

```text
6 + 64 + 382 + 1816 + 7814 + 32192 = 42274.
```

The four-owner circuit count is

```text
C(5,4)+C(7,4)+C(9,4)+C(11,4)+C(13,4)+C(15,4)=2576.
```

Every one is tested against the exact banked sign cell.  The result is
`2576` mixed and `0` one-sided.  The verifier also records every resultant
degree distribution, every zero coordinate, both endpoint and center rows,
and exact determinant/Vandermonde quotient ranges.

## Per-node verdicts

### N1: coefficient reconstruction — PASS

The verifier multiplies the integer linear factors directly.  It parses the
Lean tables only after reconstruction and compares all 60 triples.  There
are zero mismatches.  No table value is used to produce another value.

### N3: product divisibility — PASS

For row `i`, both the scaled obstruction `(C_S/C_i)F_i` and every auxiliary
entry `i^r X_i` are divisible by `P_i^2`.  Determinant multilinearity gives
the product divisor without pairwise-coprimality or cancellation.

### N4: common-term elimination — FAIL

For nonzero `X_i`, multiplication by `diag(X_i)` preserves the rank `s-1`
of the degree-`<=s-2` Vandermonde matrix.  Its annihilator is therefore
one-dimensional.  The displayed generator has nonzero common-term moment
exactly as quantified in equation (3) of `findings.md`.  No phrase such as
“essentially unique” is used: dimension is exactly `1`.

### N5: raw circuits — NEGATIVE

Four raw equations do eliminate all three global parameters at the level of
a signed linear relation.  That relation gives only

```text
sum_i lambda_i P_i^2 q_i = 0.
```

It does not transfer the product square modulus.  Exact sign enumeration
shows that all such relations permit cancellation.  The k=7 rank drop does
not alter this verdict.

### N6: full-grid cutoff — FAIL

The determinant is not merely of the wrong asymptotic size.  Exact
elementary-symmetric expansion identifies it with the first four
`d`-coefficients of the block equation.  The omitted tail is

```text
R = sum_{r=4}^k (4^r-4)d^r e_(k-r)(X).
```

Every summand is divisible by `d^4=(gM)^4`.  Therefore the strongest
fourth-power divisibility obtained by multiplying the determinant relation
by `M^2` is already true term by term.  This is a structural obstruction,
not a failed numerical optimization.

### N7: proper subsets — FAIL

The exact gap controls only `product_{i in I}P_i=M`.  For `S` proper, the
certificate allows `P_i=1` for every `i in S`.  Hence no quantified lower
bound `product_{i in S}P_i >= d^epsilon` follows.  The frozen k=5 fixture
contains two unit owners and exercises this boundary exactly.

## Adversarial fixture matrix

| Fixture | Result | Scope verdict |
|---|---|---|
| `k=9,n=2,d=1` telescope | exact equation; cutoff false | outside target scale |
| `k=15,n=4,d=1` telescope | exact equation; cutoff false | outside target scale |
| 121-digit three-owner Hensel/CRT | local/composed checks true; upper window and equation false | congruence-only falsifier |
| 130-digit four-owner Hensel/CRT | local/composed checks true; upper window and equation false | congruence-only falsifier |
| k=5 full-grid window fixture | gap, loss, window, all O/F/resultant checks true | equation and cutoff false |
| unit buckets | owners 4 and 5 have `P_i=1` | no improper cancellation |
| bases `2` and `3` | bucket `2` present; powers/signs of `3` retained | no prime cancellation |
| endpoints/centers/reflections | all 60 rows and every subset scanned | no omitted position |

The k=5 fixture is stronger than a congruence-only fixture because it obeys
the exact residual window, bounded loss, gap reconstruction, progression,
and all full-grid obstruction divisibilities.  It is deliberately reported
as below-cutoff and non-equation; no target-scale window fixture was found.

## Overclaim traps

1. A determinant divisor does not imply the determinant vanishes when its
   size grows as `d^(k-2)` and the modulus grows only as `d^2`.
2. A raw parameter circuit is not a product-modulus resultant.
3. Multiplying a valid divisibility by `M^2` does not create information when
   the exact equation remainder already contains `d^4`.
4. The one-dimensionality statement covers the stated polynomial
   Vandermonde auxiliary family.  It does not rule out every conceivable
   nonlinear or arithmetic use of the quotient vector.
5. The boundary fixture is not an Erdős 686 solution and is not presented as
   one.

## Verification record

```text
all_owner_resultant_verify.py --compact
  PASS
  target owner rows: 60
  subsets: 42274
  four-owner circuits: 2576
  one-sided circuits: 0
  L_S(1) identity failures: 0
  report SHA-256:
    2d68ac996adbf8ea8a258556d2f7360eb53d9eb6f6b0f9b71480a5f96d419080

pytest test_all_owner_resultant_verify.py
  8 passed in 17.50s
```

Because no Lean source is added, there is no new axiom surface to attest.
The banked Lean inputs retain their existing kernel gate; this package does
not upgrade the negative audit to a theorem or claim attestation readiness.
