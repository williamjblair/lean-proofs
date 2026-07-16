Q := Rationals();
R<x> := PolynomialRing(Q);
f := 36*x^6 + 128*x^5 - 100*x^3 + 8*x + 9;
C := HyperellipticCurve(f);
J := Jacobian(C);
K := KummerSurface(J);

print "KUMMER_EXPONENTS",
  [Exponents(monomial) : monomial in Monomials(DefiningPolynomial(K))];
print "KUMMER_COEFFICIENTS", Coefficients(DefiningPolynomial(K));

for index in [1..4] do
  delta := K`Delta[index];
  print "DELTA_INDEX", index;
  print "DELTA_EXPONENTS",
    [Exponents(monomial) : monomial in Monomials(delta)];
  print "DELTA_COEFFICIENTS", Coefficients(delta);
  print "DELTA_L1", &+[Abs(coefficient) : coefficient in Coefficients(delta)];
end for;

F<t> := FunctionField(Q);
S<Z> := PolynomialRing(F);
g := 36*t^6 + 128*t^5 - 100*t^3 + 8*t + 9;
L<z> := ext<F | Z^2 - g>;
RL<u> := PolynomialRing(L);
CL := HyperellipticCurve(
  36*u^6 + 128*u^5 - 100*u^3 + 8*u + 9
);
JL := Jacobian(CL);
KL := KummerSurface(JL);
P := CL![L!t, z, 1];
P0 := CL![0, 3, 1];
D := JL![P, P0];
print "GENERIC_DIVISOR", D;
print "GENERIC_KUMMER", Eltseq(KL!D);

half := Q!1/2;
quarter := Q!1/4;
generators := [
  elt< J | x^2-quarter, 3*half*x-3, 2 >,
  elt< J | x^2+x, -6*x-3, 2 >,
  elt< J | x^2-1, -6*x-3, 2 >,
  elt< J | x+1, -6*x^3-9, 2 >,
  elt< J | x^2+half*x-half, -half*x+5*half, 2 >
];

function RawDouble(point)
  coordinates := Eltseq(point);
  return K![
    Evaluate(K`Delta[index], coordinates) : index in [1..4]
  ];
end function;

print "DELTA_BASIS_AUDIT", [
  RawDouble(K!generator) eq K!(2*generator)
  : generator in generators
];

P0Q := C![0, 3, 1];
known_points := [
  C![-10, 4827, 1],
  C![-19, 13941, 5],
  C![-1, 3, 1],
  C![-1, 30, 2],
  C![2, 75, 1],
  C![0, -3, 1],
  C![1, 6, 0],
  C![1, -6, 0]
];
known_differences := [J![point, P0Q] : point in known_points];
print "DELTA_KNOWN_POINT_AUDIT", [
  RawDouble(K!difference) eq K!(2*difference)
  : difference in known_differences
];

formula_points := known_points[1..5];
print "KUMMER_FORMULA_AUDIT", [
  K!(J![point, P0Q]) eq K![
    point[1]^2*point[3],
    point[1]^3,
    0,
    6*point[2] + 8*point[1]*point[3]^2 + 18*point[3]^3
  ]
  : point in formula_points
];

special_points := [
  C![0, 3, 1],
  C![0, -3, 1],
  C![1, 6, 0],
  C![1, -6, 0]
];
print "SPECIAL_KUMMER", [
  Eltseq(K!(J![point, P0Q])) : point in special_points
];

canonical_g1 := CanonicalHeight(generators[1] : Precision := 40);
pairing_g1 := HeightPairing(
  generators[1], generators[1] : Precision := 40
);
limit_g1 := NaiveHeight((2^7)*generators[1]) / 4^7;
print "CANONICAL_G1", canonical_g1;
print "PAIRING_G1", pairing_g1;
print "LIMIT_G1_R7", limit_g1;
