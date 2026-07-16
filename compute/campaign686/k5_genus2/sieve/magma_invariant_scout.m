Q := Rationals();
RQ<xQ> := PolynomialRing(Q);
fQ := 36*xQ^6 + 128*xQ^5 - 100*xQ^3 + 8*xQ + 9;
candidate_primes := [
  61, 67, 71, 73, 79, 83, 89, 97, 101,
  103, 107, 109, 113, 127, 131, 137, 139, 149
];

for p in candidate_primes do
  F := GF(p);
  R<x> := PolynomialRing(F);
  f := R!fQ;
  if Discriminant(f) eq 0 then
    print "SCOUT_BAD_PRIME", p;
    continue;
  end if;
  C := HyperellipticCurve(f);

  J := Jacobian(C);
  A, m := AbelianGroup(J);
  half := F!1 / (F!2);
  quarter := F!1 / (F!4);
  generators := [
    elt< J | x^2-quarter, (F!3)*half*x-3, 2 >,
    elt< J | x^2+x, -6*x-3, 2 >,
    elt< J | x^2-1, -6*x-3, 2 >,
    elt< J | x+1, -6*x^3-9, 2 >,
    elt< J | x^2+half*x-half, -half*x+(F!5)*half, 2 >
  ];
  print "SCOUT_PRIME", p;
  print "SCOUT_INVARIANTS", Invariants(A);
  print "SCOUT_BASIS", [Eltseq(generator @@ m) : generator in generators];
end for;
