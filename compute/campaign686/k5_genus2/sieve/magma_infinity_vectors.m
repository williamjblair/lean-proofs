Q := Rationals();
R<x> := PolynomialRing(Q);
f := 36*x^6 + 128*x^5 - 100*x^3 + 8*x + 9;
C := HyperellipticCurve(f);
J := Jacobian(C);

G, m, finite, proved, rank_bound :=
  MordellWeilGroupGenus2(
    J : BoundC := 20000, MaxBound := 10000, MaxIndex := 1000
  );

print "MW_INVARIANTS", Invariants(G);
print "FINITE_INDEX", finite;
print "PROVED", proved;
print "RANK_BOUND", rank_bound;
print "GENERATORS", [m(G.i) : i in [1..Ngens(G)]];

P0 := C![0, 3, 1];
Pplus := C![1, 6, 0];
Pminus := C![1, -6, 0];

print "INFINITY_PLUS_COORDINATES",
  Eltseq((J![Pplus, P0]) @@ m);
print "INFINITY_MINUS_COORDINATES",
  Eltseq((J![Pminus, P0]) @@ m);
