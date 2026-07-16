from .kummer_height_upper_verify import parse_magma_output


def test_parse_minimal_magma_output() -> None:
    output = """
KUMMER_EXPONENTS [ [ 4, 0, 0, 0 ] ]
KUMMER_COEFFICIENTS [ 1 ]
DELTA_INDEX 1
DELTA_EXPONENTS [ [ 4, 0, 0, 0 ] ]
DELTA_COEFFICIENTS [ 1 ]
DELTA_L1 1
DELTA_INDEX 2
DELTA_EXPONENTS [ [ 0, 4, 0, 0 ] ]
DELTA_COEFFICIENTS [ 1 ]
DELTA_L1 1
DELTA_INDEX 3
DELTA_EXPONENTS [ [ 0, 0, 4, 0 ] ]
DELTA_COEFFICIENTS [ 1 ]
DELTA_L1 1
DELTA_INDEX 4
DELTA_EXPONENTS [ [ 0, 0, 0, 4 ] ]
DELTA_COEFFICIENTS [ 1 ]
DELTA_L1 1
GENERIC_DIVISOR (x^2 - t*x, (1/t*z + 3/t)*x - 3, 2)
GENERIC_KUMMER [
  1,
  t,
  0,
  6/t^2*z + (8*t + 18)/t^2
]
DELTA_BASIS_AUDIT [ true, true, true, true, true ]
DELTA_KNOWN_POINT_AUDIT [ true, true, true, true, true, true, true, true ]
KUMMER_FORMULA_AUDIT [ true, true, true, true, true ]
SPECIAL_KUMMER [ [ 0, 0, 0, 1 ], [ 9, 0, 0, 16 ], [ 0, 1, 0, 36 ], [ 0, 1, 0, -36 ] ]
CANONICAL_G1 0.358295208420105788521564452795191694292896
PAIRING_G1 0.35829520842010578852156445279519169429290
LIMIT_G1_R7 0.358455426362657832650014644423
"""
    parsed = parse_magma_output(output)
    assert parsed["generic_kummer_affine"] == [
        "1", "t", "0", "(6*z+8*t+18)/t^2"
    ]
    assert len(parsed["deltas"]) == 4
