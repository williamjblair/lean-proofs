\\ PARI/GP 2.17.3 exact certification for the optimized degree-15 pair field.
\\ A successful run must end with CERTIFIED 1 and DONE.

default(parisizemax, 8000000000);

p =
  x^15 + 5*x^14 - 40*x^13 - 370*x^12 + 310*x^11
  + 12646*x^10 + 28620*x^9 - 196560*x^8 - 1018755*x^7
  + 508265*x^6 + 14099572*x^5 + 27417970*x^4
  - 57078960*x^3 - 324899280*x^2 - 528740460*x
  - 311944932;

print("PARI_VERSION ", version());
print("POLDEG ", poldegree(p));
print("IRREDUCIBLE ", polisirreducible(p));

b = bnfinit(p, 1);

print("DISCRIMINANT ", b.disc);
print("CLASS_NUMBER ", b.no);
print("CLASS_GROUP_CYCLIC_FACTORS ", b.cyc);
print("REGULATOR ", b.reg);
print("FUNDAMENTAL_UNIT_COUNT ", #b.fu);
print("FUNDAMENTAL_UNITS ", b.fu);
print("CERTIFY_START");
print("CERTIFIED ", bnfcertify(b));
print("DONE");

quit;
