#!/usr/bin/env python3
"""Exact audit for the primitive centered-factor lane at k=5.

No floating point is used.  The file has three deliberately separate jobs.

1. Reproduce the exact factor-matching identities forced by

       u (z u^2-1)(z u^2-4) = 4 v (z v^2-1)(z v^2-4), gcd(u,v)=1.

2. Exhaustively enumerate the *weaker* primitive matching system at z=1
   in the exact 131/100--132/100 ratio strip.  These rows are not solutions
   of the centered equation: the two integral quotient values are unequal.

3. Verify an unbounded, fully explicit family satisfying the scale
   divisibility and the complete upper-to-lower matching direction.  It is
   a boundary fixture showing why both matching directions and the equality
   of the common quotient must be retained.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from math import gcd
from typing import Any


SCAN_BOUND = 200_000


def quadratic_product(z: int, x: int) -> int:
    return (z * x * x - 1) * (z * x * x - 4)


def ratio_strip(u: int, v: int) -> bool:
    return 131 * v < 100 * u < 132 * v


def matching_data(g: int, u: int, v: int) -> dict[str, int | bool]:
    z = g * g
    upper = quadratic_product(z, u)
    lower4 = 4 * quadratic_product(z, v)
    return {
        "g": g,
        "z": z,
        "u": u,
        "v": v,
        "gap": g * (u - v),
        "coprime": gcd(u, v) == 1,
        "ratio_strip": ratio_strip(u, v),
        "scale_remainder": (4 * (4 * v - u)) % z,
        "upper_matching_remainder": upper % v,
        "lower_matching_remainder": lower4 % u,
        "upper_quotient": upper // v,
        "lower_quotient": lower4 // u,
        "equation_residual": u * upper - v * lower4,
        "quadratic_factor_gcd_upper": gcd(z * u * u - 1, z * u * u - 4),
        "quadratic_factor_gcd_lower": gcd(z * v * v - 1, z * v * v - 4),
    }


def _smallest_prime_factors(limit: int) -> list[int]:
    spf = list(range(limit + 1))
    for prime in range(2, int(limit**0.5) + 1):
        if spf[prime] != prime:
            continue
        for value in range(prime * prime, limit + 1, prime):
            if spf[value] == value:
                spf[value] = prime
    return spf


def _prime_powers(value: int, spf: list[int]) -> list[tuple[int, int]]:
    result: list[tuple[int, int]] = []
    while value > 1:
        prime = spf[value]
        power = 1
        while value % prime == 0:
            power *= prime
            value //= prime
        result.append((prime, power))
    return result


def _local_roots(prime: int, power: int) -> list[int]:
    """Roots of (x^2-1)(x^2-4) modulo one prime power."""
    if prime >= 5:
        return sorted({1 % power, (-1) % power, 2 % power, (-2) % power})
    return [
        residue
        for residue in range(power)
        if quadratic_product(1, residue) % power == 0
    ]


def _matching_roots(modulus: int, spf: list[int]) -> list[int]:
    roots = [0]
    accumulated = 1
    for prime, power in _prime_powers(modulus, spf):
        local = _local_roots(prime, power)
        inverse = pow(accumulated, -1, power)
        next_roots: list[int] = []
        for old in roots:
            for new in local:
                correction = ((new - old) * inverse) % power
                next_roots.append(old + accumulated * correction)
        roots = next_roots
        accumulated *= power
    return roots


def primitive_scan(limit: int = SCAN_BOUND) -> list[dict[str, int]]:
    """Enumerate every z=1 two-direction matching row through v=limit."""
    spf = _smallest_prime_factors(limit)
    rows: list[dict[str, int]] = []
    for v in range(2, limit + 1):
        for residue in _matching_roots(v, spf):
            # In the target strip v < u < 2v, hence u=v+residue uniquely.
            u = v + residue
            if not ratio_strip(u, v) or gcd(u, v) != 1:
                continue
            upper = quadratic_product(1, u)
            lower4 = 4 * quadratic_product(1, v)
            if upper % v != 0 or lower4 % u != 0:
                continue
            upper_q = upper // v
            lower_q = lower4 // u
            if upper_q == lower_q:
                raise AssertionError("the scan unexpectedly found an exact k=5 solution")
            rows.append(
                {
                    "u": u,
                    "v": v,
                    "gap": u - v,
                    "upper_quotient": upper_q,
                    "lower_quotient": lower_q,
                    "quotient_difference": upper_q - lower_q,
                }
            )
    return rows


EXPECTED_SCAN_PAIRS = [
    (925, 702),
    (1056, 805),
    (5104, 3885),
    (6775, 5148),
    (7776, 5915),
    (8178, 6205),
    (8721, 6649),
    (9880, 7503),
    (11440, 8721),
    (12276, 9329),
    (12880, 9823),
    (18487, 14040),
    (26543, 20195),
    (26887, 20376),
    (35640, 27161),
    (37584, 28595),
    (38048, 28825),
    (42160, 31993),
    (84783, 64666),
    (91701, 69550),
    (94129, 71640),
    (127127, 96900),
    (145620, 110831),
    (167050, 126699),
    (237888, 180895),
]


@dataclass(frozen=True)
class OneDirectionPoint:
    m: int
    g: int
    H: int
    u: int
    v: int


def one_direction_point(m: int) -> OneDirectionPoint:
    """The m-th point of the exact upper-matching counterfamily."""
    if m < 0:
        raise ValueError("m must be nonnegative")
    g = 2 + 969 * m
    H = 51 * g
    v = 19 * (H * H - 1)
    u = 25 * H * H - 76
    return OneDirectionPoint(m=m, g=g, H=H, u=u, v=v)


def verify_one_direction(point: OneDirectionPoint) -> dict[str, Any]:
    m, g, H, u, v = point.m, point.g, point.H, point.u, point.v
    z = g * g
    if g != 2 + 969 * m or H != 51 * g:
        raise AssertionError("family parametrization changed")
    if v != 19 * (H * H - 1) or u != 25 * H * H - 76:
        raise AssertionError("family coordinates changed")
    if 4 * v - u != 51**3 * z:
        raise AssertionError("exact scale identity failed")
    if not ratio_strip(u, v):
        raise AssertionError("exact target ratio strip failed")
    if gcd(u, v) != 1:
        raise AssertionError("primitive condition failed")

    # H^2 is 11 modulo 19 on g=2 (mod 969), and 11^2+11+1=133.
    if H % 19 != 7 or (H**4 + H * H + 1) % 19 != 0:
        raise AssertionError("cyclotomic congruence failed")
    if (H**6 - 1) % v != 0:
        raise AssertionError("v does not divide H^6-1")

    upper = quadratic_product(z, u)
    if upper % v != 0:
        raise AssertionError("upper-to-lower matching failed")
    data = matching_data(g, u, v)
    if data["scale_remainder"] != 0 or data["upper_matching_remainder"] != 0:
        raise AssertionError("reported matching data changed")
    if data["equation_residual"] == 0:
        raise AssertionError("counterfamily point became an exact solution")
    return data


def affine_resultant_fixture(A: int, B: int, excluded_factor: int) -> dict[str, int]:
    """Reproduce a three-factor affine matching fixture.

    Put v equal to three of |A-B|, A+B, 2B-A, A+2B, require v=-1
    modulo B, then t=(v+1)/B and (u,v)=(A t, B t-1).  The forward
    matching is a direct resultant identity.  The stored rows also pass the
    reverse matching, but their two common-quotient candidates differ.
    """
    factors = (A - B, A + B, 2 * B - A, A + 2 * B)
    v = 1
    for index, factor in enumerate(factors):
        if index != excluded_factor:
            v *= factor
    if v % B != B - 1:
        raise AssertionError("affine integrality congruence failed")
    t = (v + 1) // B
    u = A * t
    data = matching_data(1, u, v)
    for key in (
        "coprime",
        "ratio_strip",
    ):
        if data[key] is not True:
            raise AssertionError(f"affine fixture failed {key}")
    if data["upper_matching_remainder"] or data["lower_matching_remainder"]:
        raise AssertionError("affine two-direction matching failed")
    if data["equation_residual"] == 0:
        raise AssertionError("affine fixture became an exact solution")

    resultant = abs((A * A - B * B) * (A * A - 4 * B * B))
    if resultant % v != 0:
        raise AssertionError("affine resultant divisibility failed")
    return {
        "A": A,
        "B": B,
        "excluded_factor": excluded_factor,
        "t": t,
        "u": u,
        "v": v,
        "resultant": resultant,
        "upper_quotient": int(data["upper_quotient"]),
        "lower_quotient": int(data["lower_quotient"]),
    }


AFFINE_FIXTURE_INPUTS = [
    (59, 45, 2),
    (6751, 5150, 1),
    (15847, 12028, 2),
    (16523, 12554, 2),
    (37499, 28500, 2),
]


def build_report(scan_limit: int = SCAN_BOUND) -> dict[str, Any]:
    rows = primitive_scan(scan_limit)
    if scan_limit == SCAN_BOUND:
        actual = [(row["u"], row["v"]) for row in rows]
        if actual != EXPECTED_SCAN_PAIRS:
            raise AssertionError("primitive scan certificate changed")

    one_direction_indices = [0, 1, 10**6, 10**40]
    one_direction = [
        verify_one_direction(one_direction_point(index))
        for index in one_direction_indices
    ]
    affine = [affine_resultant_fixture(*row) for row in AFFINE_FIXTURE_INPUTS]
    return {
        "status": "proper factor interface and negative boundary fixtures; no k=5 tail closure",
        "primitive_scan": {
            "v_upper_bound": scan_limit,
            "count": len(rows),
            "pairs": [[row["u"], row["v"]] for row in rows],
            "all_common_quotients_unequal": all(
                row["upper_quotient"] != row["lower_quotient"] for row in rows
            ),
            "chain_fixtures": [
                [6649, 8721, 11440],
                [228998, 300375, 394001],
            ],
        },
        "one_direction_unbounded_family": {
            "formula": {
                "g": "2+969*m",
                "H": "51*g",
                "v": "19*(H^2-1)",
                "u": "25*H^2-76",
                "four_v_minus_u": "51^3*g^2",
            },
            "sample_indices": one_direction_indices,
            "samples": one_direction,
            "warning": "lower-to-upper matching deliberately fails; this family falsifies only one-direction arguments",
        },
        "affine_resultant_fixtures": affine,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--scan-limit", type=int, default=SCAN_BOUND)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    report = build_report(args.scan_limit)
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
