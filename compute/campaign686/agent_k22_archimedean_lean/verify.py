#!/usr/bin/env python3
"""Exact audit data for the ordinary-kernel k=22 Archimedean core.

All arithmetic is over Python integers or ``Fraction``.  This verifier is
deliberately independent of the generated Lean files: the generator consumes
its checked report, while Lean rechecks the resulting identities and finite
certificates in the kernel.
"""

from __future__ import annotations

import hashlib
import json
from fractions import Fraction
from functools import reduce
from math import comb, gcd, lcm


Poly = dict[int, int]
BivariatePoly = dict[tuple[int, int], int]

K = 22
R = 11
SCALE = 256
FIXED_DIVISOR = 33
SPLIT_GAP = 250
RUNGE_BOUND = 125_239_835_548
CANDIDATE_BOUND = 3_795_146_531
V_FLOOR = 7_481
W_FLOOR = 7_981
ROOT_FIXTURES = (
    (28_643_526_033, -3, -1),
    (19_687_413_989, -7, -1),
    (3_809_308_513, 13, 15),
)


def add_term(poly: Poly, degree: int, value: int) -> None:
    poly[degree] = poly.get(degree, 0) + value
    if poly[degree] == 0:
        del poly[degree]


def add_bivariate_term(
    poly: BivariatePoly, degree: tuple[int, int], value: int
) -> None:
    poly[degree] = poly.get(degree, 0) + value
    if poly[degree] == 0:
        del poly[degree]


def mul_poly(left: Poly, right: Poly) -> Poly:
    out: Poly = {}
    for i, ai in left.items():
        for j, bj in right.items():
            add_term(out, i + j, ai * bj)
    return out


def eval_poly(poly: Poly, value: int) -> int:
    return sum(c * value**degree for degree, c in poly.items())


def shift_poly(poly: Poly, shift: int) -> Poly:
    out: Poly = {}
    for degree, coefficient in poly.items():
        for j in range(degree + 1):
            add_term(
                out,
                j,
                coefficient * comb(degree, j) * shift ** (degree - j),
            )
    return out


def shifted_two_variable(poly: Poly, shift: int) -> BivariatePoly:
    out: BivariatePoly = {}
    for degree, coefficient in poly.items():
        for total in range(degree + 1):
            base = coefficient * comb(degree, total) * shift ** (degree - total)
            for i in range(total + 1):
                add_bivariate_term(out, (i, total - i), base * comb(total, i))
    return out


def elementary(values: list[int]) -> list[int]:
    out = [1]
    for value in values:
        out.append(0)
        for j in range(len(out) - 1, 0, -1):
            out[j] += value * out[j - 1]
    return out


def row_data() -> tuple[Poly, Poly, Poly]:
    roots = [(2 * j - 1) ** 2 for j in range(1, R + 1)]
    es = elementary(roots)
    s_poly = {2 * R - 2 * j: (-1) ** j * es[j] for j in range(R + 1)}

    square_root = [Fraction(1)]
    for n in range(1, R // 2 + 1):
        cross = sum(square_root[i] * square_root[n - i] for i in range(1, n))
        square_root.append((Fraction(s_poly[2 * R - 2 * n]) - cross) / 2)
    scale = reduce(lcm, (x.denominator for x in square_root), 1)
    assert scale == SCALE
    t_poly = {
        R - 2 * j: int(scale * coefficient)
        for j, coefficient in enumerate(square_root)
    }
    d_poly = mul_poly(t_poly, t_poly)
    for degree, coefficient in s_poly.items():
        add_term(d_poly, degree, -(SCALE**2) * coefficient)
    return s_poly, t_poly, d_poly


S_POLY, T_POLY, D_POLY = row_data()

EXPECTED_T = {
    11: 256,
    9: -226_688,
    7: 67_609_696,
    5: -8_111_362_160,
    3: 352_497_378_310,
    1: -6_055_670_906_453,
}

EXPECTED_D = {
    10: 463_278_576_995_462_272,
    8: -216_425_162_804_858_318_080,
    6: 31_355_359_404_386_247_301_764,
    4: -1_470_309_582_711_394_865_435_644,
    2: 21_668_018_076_062_298_043_697_209,
    0: 12_389_157_521_837_708_451_840_000,
}


def delta_lower_coefficients(bound: int = RUNGE_BOUND) -> BivariatePoly:
    """Coefficients after v=7481+a and w=7981+a+b."""
    w_poly = dict(D_POLY)
    for degree, coefficient in T_POLY.items():
        add_term(w_poly, degree, bound * coefficient)
    out = shifted_two_variable(w_poly, W_FLOOR)

    v_poly: Poly = {}
    for degree, coefficient in T_POLY.items():
        add_term(v_poly, degree, 2 * bound * coefficient)
    for degree, coefficient in D_POLY.items():
        add_term(v_poly, degree, -4 * coefficient)
    for degree, coefficient in shift_poly(v_poly, V_FLOOR).items():
        add_bivariate_term(out, (degree, 0), coefficient)
    return out


def negative_upper_polynomial() -> Poly:
    """Scaled upper bound for D(w)-4D(v) under 14w <= 15v."""
    denominator = 14
    numerator = 15
    degree = max(D_POLY)
    leading = D_POLY[degree]
    upper: Poly = {
        degree: leading * numerator**degree - 4 * leading * denominator**degree
    }
    for exponent, coefficient in D_POLY.items():
        if exponent in (degree, 0):
            continue
        if coefficient > 0:
            add_term(
                upper,
                exponent,
                coefficient
                * denominator ** (degree - exponent)
                * numerator**exponent,
            )
        else:
            add_term(upper, exponent, -4 * coefficient * denominator**degree)
    return upper


NEGATIVE_UPPER = negative_upper_polynomial()


def finite_strip_report() -> dict[str, object]:
    count = 0
    maximum_offset = 0
    minimum_error: tuple[int, int, int, int] | None = None
    for d in range(27, SPLIT_GAP):
        lower = 15 * d - 21
        upper = (77 * d - 6) // 5
        for n in range(lower, upper + 1):
            v = 2 * n + 23
            w = 2 * (n + d) + 23
            error = eval_poly(S_POLY, w) - 4 * eval_poly(S_POLY, v)
            assert error != 0
            maximum_offset = max(maximum_offset, n - lower)
            record = (abs(error), d, n, error)
            if minimum_error is None or record[0] < minimum_error[0]:
                minimum_error = record
            count += 1
    assert minimum_error is not None
    return {
        "gap_range": [27, 249],
        "pair_count": count,
        "maximum_n": (77 * 249 - 6) // 5,
        "maximum_offset": maximum_offset,
        "minimum_abs_error": minimum_error[0],
        "minimum_at": [minimum_error[1], minimum_error[2]],
        "signed_error": minimum_error[3],
    }


def audit() -> dict[str, object]:
    assert T_POLY == EXPECTED_T
    assert D_POLY == EXPECTED_D
    assert mul_poly(T_POLY, T_POLY) == {
        degree: SCALE**2 * S_POLY.get(degree, 0) + D_POLY.get(degree, 0)
        for degree in set(S_POLY) | set(D_POLY)
        if SCALE**2 * S_POLY.get(degree, 0) + D_POLY.get(degree, 0)
    }

    odd_values = [abs(eval_poly(T_POLY, 2 * a + 1)) for a in range(R + 1)]
    assert reduce(gcd, odd_values, 0) == FIXED_DIVISOR
    assert (
        -72_113_493_154 * eval_poly(T_POLY, 1)
        + 39_309_729_457 * eval_poly(T_POLY, 3)
        == FIXED_DIVISOR
    )
    assert all(eval_poly(T_POLY, 2 * a + 1) % 2 for a in range(-20, 21))

    assert 4 * 15**K < 16**K
    assert 82**K < 4 * 77**K
    assert 18 * 26 <= K**2 < 18 * 27

    shifted_t = shift_poly(T_POLY, V_FLOOR)
    assert min(shifted_t.values()) > 0
    delta = delta_lower_coefficients()
    assert min(delta.values()) > 0
    previous = delta_lower_coefficients(RUNGE_BOUND - 1)
    assert min(previous.values()) <= 0
    shifted_upper = shift_poly(NEGATIVE_UPPER, V_FLOOR)
    assert max(shifted_upper.values()) < 0
    assert (RUNGE_BOUND - 1) // FIXED_DIVISOR == CANDIDATE_BOUND

    root_fixtures: list[dict[str, int]] = []
    for t, w, v in ROOT_FIXTURES:
        assert eval_poly(S_POLY, w) == 4 * eval_poly(S_POLY, v)
        error = eval_poly(T_POLY, w) - 2 * eval_poly(T_POLY, v)
        assert error == -FIXED_DIVISOR * t
        assert t > CANDIDATE_BOUND
        root_fixtures.append({"t": t, "w": w, "v": v, "error": error})

    finite = finite_strip_report()
    assert finite["pair_count"] == 16_859
    assert finite["maximum_n"] == 3_833
    assert finite["maximum_offset"] == 119

    return {
        "row": {
            "k": K,
            "scale": SCALE,
            "fixed_divisor": FIXED_DIVISOR,
            "T": T_POLY,
            "D": D_POLY,
        },
        "quadratic_gaps": [22, 23, 24, 25, 26],
        "ratio_brackets": {
            "upper_margin": 16**K - 4 * 15**K,
            "lower_margin": 4 * 77**K - 82**K,
        },
        "finite_strip": finite,
        "large_gap": {
            "gap_floor": SPLIT_GAP,
            "v_floor": V_FLOOR,
            "w_floor": W_FLOOR,
            "runge_bound": RUNGE_BOUND,
            "candidate_bound": CANDIDATE_BOUND,
            "delta_minimum_coefficient": min(delta.values()),
            "delta_minimum_degree": list(min(delta, key=delta.get)),
            "previous_delta_minimum": min(previous.values()),
            "negative_upper_largest_shifted_coefficient": max(
                shifted_upper.values()
            ),
        },
        "excluded_unrestricted_root_fixtures": root_fixtures,
    }


def main() -> None:
    payload = audit()
    encoded = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    wrapped = {
        "payload_sha256": hashlib.sha256(encoded).hexdigest(),
        "payload": payload,
    }
    print(json.dumps(wrapped, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
