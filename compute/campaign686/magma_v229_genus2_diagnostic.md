# Erdős 686 Magma V2.29 Genus-Two Diagnostic

Date: 2026-07-16

Status: externally computed diagnostic only. Nothing in this file is a
kernel-checked completeness certificate.

## Curve

```magma
Q<x> := PolynomialRing(Rationals());
f := 9*x^6 + 64*x^5 - 200*x^3 + 64*x + 144;
C := HyperellipticCurve(f);
```

The computation used the University of Sydney Magma calculator running
Magma V2.29-8.

## New genus-two driver

```magma
pts, proved, N := RationalPointsGenus2(C);
#pts;
proved;
N;
```

Exact output:

```text
36
false
20000
```

The returned 36 projective points are exactly the already banked point list.
The `false` flag is decisive: Magma did not prove completeness. The final
integer is only the searched multiplicative x-height bound.

## Elliptic-subcover check

The V2.29 driver can sometimes prove completeness through rank-zero degree-2
or degree-3 elliptic subcovers. The direct exact queries were:

```magma
L2 := Degree2Subcovers(C);
#L2;
L3 := Degree3Subcovers(C);
#L3;
```

Exact output:

```text
0
0
```

Thus this curve has no subcover of either supported degree for that fallback.
Since its Jacobian rank is five, ordinary genus-two Chabauty is also
inapplicable. The V2.29 diagnostic therefore adds no rational-point
completeness result and does not change the active symbolic k=5 lanes.

## Documentation

- https://magma.maths.usyd.edu.au/magma/handbook/text/1612
- https://magma.maths.usyd.edu.au/magma/handbook/text/1619
