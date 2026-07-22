import ErdosProblems.Erdos686.EvenK.K16

namespace Erdos686.Erdos686Variant

def evenTable22S {R : Type} [CommRing R] (W : R) : R :=
  (W ^ 2 - 1) * (W ^ 2 - 9) * (W ^ 2 - 25) * (W ^ 2 - 49) *
    (W ^ 2 - 81) * (W ^ 2 - 121) * (W ^ 2 - 169) * (W ^ 2 - 225) *
    (W ^ 2 - 289) * (W ^ 2 - 361) * (W ^ 2 - 441)

def evenTable22T {R : Type} [CommRing R] (W : R) : R :=
  256 * W ^ 11
     - 226688 * W ^ 9
     + 67609696 * W ^ 7
     - 8111362160 * W ^ 5
     + 352497378310 * W ^ 3
     - 6055670906453 * W
end Erdos686.Erdos686Variant
