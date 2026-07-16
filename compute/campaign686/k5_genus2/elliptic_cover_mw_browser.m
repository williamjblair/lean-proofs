/*
  Long-running exact Magma source for one of the eight k=5 elliptic covers.

  The public XML calculator currently stops the first cover during the
  2-Selmer computation at its execution cap. Run this source in the
  authenticated browser calculator and change cover_index through 1..8.
  No output from this file is treated as a certificate until it is frozen
  in machine-readable form and independently verified.
*/

cover_index := 1;
assert cover_index in [1..8];

Q := Rationals();
R<x> := PolynomialRing(Q);
f_monic := x^6 + 64/9*x^5 - 200/9*x^3 + 64/9*x + 16;
C := HyperellipticCurve(9*f_monic);
H, AtoH := TwoCoverDescent(C);
A := Domain(AtoH);
theta := A.1;
cover_classes := Setseq(H);
class := cover_classes[cover_index];
delta := class @@ AtoH;

S<z> := PolynomialRing(Q);
T<t> := PolynomialRing(S);
f_t := t^6 + 64/9*t^5 - 200/9*t^3 + 64/9*t + 16;
pair_resultant := Resultant(f_t, Evaluate(f_t, z-t));
pair_resolvent :=
  [entry[1] : entry in Factorization(pair_resultant)
    | Degree(entry[1]) eq 15][1];

L<s> := NumberField(pair_resolvent);
RL<X> := PolynomialRing(L);
f_L := X^6 + 64/9*X^5 - 200/9*X^3 + 64/9*X + 16;
factorization_L := Factorization(f_L);
q2 := [entry[1] : entry in factorization_L
       | Degree(entry[1]) eq 2][1];
q4 := [entry[1] : entry in factorization_L
       | Degree(entry[1]) eq 4][1];

K<a> := quo<RL | q2>;
AtoK := hom<A -> K | a>;
gamma := Norm(AtoK(delta));
cover := HyperellipticCurve(gamma*q4);

known_points := Points(C : Bound := 20000);
found := false;
for P in known_points do
  coordinates := Eltseq(P);
  if coordinates[3] ne 0 then
    x_coordinate := Q!(coordinates[1]/coordinates[3]);
    if AtoH(A!x_coordinate - theta) eq class then
      square, y_coordinate :=
        IsSquare(Evaluate(gamma*q4, L!x_coordinate));
      if square then
        cover_point := cover![L!x_coordinate, y_coordinate, 1];
        found := true;
        break;
      end if;
    end if;
  end if;
end for;
assert found;

elliptic_curve, cover_to_elliptic :=
  EllipticCurve(cover, cover_point);
optimized_field, field_isomorphism := OptimizedRepresentation(L);
optimized_curve := BaseChange(elliptic_curve, field_isomorphism);
integral_curve := IntegralModel(optimized_curve);

print "COVER_INDEX", cover_index;
print "COVER_CLASS", class;
print "REPRESENTATIVE_NORM", Norm(delta);
print "KNOWN_WITNESS_X", x_coordinate;
print "OPTIMIZED_FIELD_POLYNOMIAL",
  DefiningPolynomial(optimized_field);
print "TORSION_INVARIANTS",
  Invariants(TorsionSubgroup(integral_curve));
print "PSEUDO_MW_START";

success, mordell_weil_group, mordell_weil_map :=
  PseudoMordellWeilGroup(
    integral_curve :
      SearchBound := 100,
      UseHomogeneousSpaces := false
  );

print "PSEUDO_MW_SUCCESS", success;
print "PSEUDO_MW_INVARIANTS", Invariants(mordell_weil_group);
print "PSEUDO_MW_GENERATORS",
  [mordell_weil_map(mordell_weil_group.i)
    : i in [1..Ngens(mordell_weil_group)]];
