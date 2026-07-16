Q := Rationals();
R<x> := PolynomialRing(Q);
f_monic := x^6 + 64/9*x^5 - 200/9*x^3 + 64/9*x + 16;
f_curve := 9*f_monic;
C := HyperellipticCurve(f_curve);

H, AtoH := TwoCoverDescent(C);
A := Domain(AtoH);
theta := A.1;

S<z> := PolynomialRing(Q);
T<t> := PolynomialRing(S);
f_t := t^6 + 64/9*t^5 - 200/9*t^3 + 64/9*t + 16;
pair_resultant := Resultant(f_t, Evaluate(f_t, z-t));
pair_factors := Factorization(pair_resultant);
diagonal_factor :=
  [entry[1] : entry in pair_factors | Degree(entry[1]) eq 6][1];
pair_resolvent :=
  [entry[1] : entry in pair_factors | Degree(entry[1]) eq 15][1];

print "PAIR_RESULTANT_DEGREE", Degree(pair_resultant);
print "DIAGONAL_FACTOR", diagonal_factor;
print "PAIR_RESOLVENT", pair_resolvent;
print "PAIR_RESOLVENT_DEGREE", Degree(pair_resolvent);
print "PAIR_RESOLVENT_IRREDUCIBLE", IsIrreducible(pair_resolvent);

L<s> := NumberField(pair_resolvent);
RL<X> := PolynomialRing(L);
f_L := X^6 + 64/9*X^5 - 200/9*X^3 + 64/9*X + 16;
factorization_L := Factorization(f_L);
q2 := [entry[1] : entry in factorization_L | Degree(entry[1]) eq 2][1];
q4 := [entry[1] : entry in factorization_L | Degree(entry[1]) eq 4][1];

print "FACTOR_DEGREES",
  Sort([Degree(entry[1]) : entry in factorization_L]);
print "TWO_COVER_COUNT", #H;

known_points := Points(C : Bound := 20000);
class_counts := AssociativeArray();
for h in H do
  class_counts[h] := 0;
end for;
for P in known_points do
  coordinates := Eltseq(P);
  if coordinates[3] ne 0 then
    x_coordinate := Q!(coordinates[1]/coordinates[3]);
    class := AtoH(A!x_coordinate - theta);
    class_counts[class] +:= 1;
  end if;
end for;

print "KNOWN_PROJECTIVE_POINT_COUNT", #known_points;
print "KNOWN_AFFINE_POINT_COUNT",
  #[P : P in known_points | Eltseq(P)[3] ne 0];
print "CLASS_POINT_COUNTS_SORTED",
  Sort([class_counts[h] : h in H]);
print "COVER_NORMS_SORTED",
  Sort([Q!Norm(h @@ AtoH) : h in H]);

K<a> := quo<RL | q2>;
AtoK := hom<A -> K | a>;
constructed := 0;
witness_x := [];
for h in H do
  delta := h @@ AtoH;
  gamma := Norm(AtoK(delta));
  found := false;
  for P in known_points do
    coordinates := Eltseq(P);
    if coordinates[3] ne 0 then
      x_coordinate := Q!(coordinates[1]/coordinates[3]);
      if AtoH(A!x_coordinate - theta) eq h then
        square, y_coordinate :=
          IsSquare(Evaluate(gamma*q4, L!x_coordinate));
        if square then
          cover := HyperellipticCurve(gamma*q4);
          cover_point := cover![L!x_coordinate, y_coordinate, 1];
          elliptic_curve, cover_to_elliptic :=
            EllipticCurve(cover, cover_point);
          assert IsNonsingular(elliptic_curve);
          Append(~witness_x, x_coordinate);
          constructed +:= 1;
          found := true;
          break;
        end if;
      end if;
    end if;
  end for;
  assert found;
end for;

print "ELLIPTIC_COVER_WITNESS_X", witness_x;
print "ELLIPTIC_COVERS_CONSTRUCTED", constructed;
