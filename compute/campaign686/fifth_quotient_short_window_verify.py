#!/usr/bin/env python3
"""Exact verifier for the Erdős 686 fifth-quotient short-window checkpoint.

This file intentionally reconstructs the Taylor coefficients and every
polynomial used below.  It does not import the earlier campaign verifiers.
All load-bearing comparisons use ``int`` or ``fractions.Fraction``.
"""

from __future__ import annotations

import json
import sys
from fractions import Fraction
from functools import cache
from itertools import combinations
from math import gcd, prod
from typing import Any, Iterable

sys.set_int_max_str_digits(100_000)

ROWS = (5, 7, 9, 11, 13, 15)
RESIDUAL_CEILING = {5: 14, 7: 17, 9: 23, 11: 26, 13: 29, 15: 35}
LOSS_BOUND = {
    5: 108,
    7: 1620,
    9: 136080,
    11: 1224720,
    13: 242494560,
    15: 18914575680,
}
# Adjacent rational brackets A_lo/100000 < 4^(1/k) < A_hi/100000.
ROOT_BRACKETS = {
    5: (131950, 131951),
    7: (121901, 121902),
    9: (116652, 116653),
    11: (113431, 113432),
    13: (111253, 111254),
    15: (109682, 109683),
}
BRACKET_DENOMINATOR = 100000
INTERVAL_PADDING = Fraction(1, 100)
CRT_INDICES = (1, 2, 4)
CRT_BASES = (101, 103, 107)


@cache
def local_coefficients(k: int, owner: int) -> tuple[int, int, int, int, int]:
    """Return C,D,E,F,G in product_{j != owner}(x+j-owner)."""

    if not 1 <= owner <= k:
        raise ValueError("owner outside row")
    coefficients = [1]
    for offset in (j - owner for j in range(1, k + 1) if j != owner):
        updated = [0] * (len(coefficients) + 1)
        for degree, value in enumerate(coefficients):
            updated[degree] += offset * value
            updated[degree + 1] += value
        coefficients = updated
    return tuple(coefficients[:5])  # type: ignore[return-value]


def reduced_fourth_coefficient(
    C: int, D: int, E: int, F: int, left: int, right: int
) -> int:
    p, s = left * right, left + right
    return 108 * p * (
        -108 * D**3 * p
        + C * D * (-108 * D * s + 324 * E * p)
        + 567 * C**2 * F * p
    )


def reduced_fifth_coefficients(
    C: int, D: int, E: int, F: int, G: int, left: int, right: int
) -> tuple[int, int]:
    p, s = left * right, left + right
    linear = 8748 * p * (
        255 * C**2 * G * p
        - 120 * C * D * E * s
        + 240 * C * D * F * p
        + 180 * C * E**2 * p
        - 120 * D**2 * E * p
    )
    quadratic = 8748 * p * (
        -100 * C * E**2 * s
        + 400 * C * E * F * p
        - 100 * D * E**2 * p
    )
    return linear, quadratic


def reduced_fifth_value(
    C: int,
    D: int,
    E: int,
    F: int,
    G: int,
    gap: int,
    left: int,
    right: int,
) -> int:
    k4 = reduced_fourth_coefficient(C, D, E, F, left, right)
    r1, r2 = reduced_fifth_coefficients(C, D, E, F, G, left, right)
    return 27 * k4 + gap * r1 + gap**2 * r2


def nonreflected_triples(k: int) -> Iterable[tuple[int, int, int]]:
    center = (k + 1) // 2
    for triple in combinations(range(1, k + 1), 3):
        others = [x for x in triple if x != center]
        if center in triple and sum(others) == 2 * center:
            continue
        yield triple


def power_window_correction_bound(k: int) -> Fraction:
    """Maximum finite owner correction after exact power-window linearization."""

    lower_root, upper_root = ROOT_BRACKETS[k]
    b = BRACKET_DENOMINATOR
    corrections = []
    for owner in range(1, k + 1):
        corrections.extend(
            (
                Fraction(3 * (b - upper_root * k), upper_root - b) + 3 * owner,
                Fraction(3 * (b * k - lower_root), lower_root - b) + 3 * owner,
            )
        )
    return max(abs(correction) for correction in corrections)


def residual_ratio_interval(k: int) -> tuple[Fraction, Fraction]:
    lower_root, upper_root = ROOT_BRACKETS[k]
    b = BRACKET_DENOMINATOR
    if upper_root != lower_root + 1:
        raise AssertionError("root bracket is not adjacent")
    if not lower_root**k < 4 * b**k < upper_root**k:
        raise AssertionError("root bracket does not contain 4^(1/k)")
    correction = power_window_correction_bound(k)
    if not (
        correction < 1000
        and Fraction(1000, 10**1000) < INTERVAL_PADDING
    ):
        raise AssertionError("padding does not absorb exact finite correction")
    lower = Fraction(4 * b - upper_root, upper_root - b) - INTERVAL_PADDING
    upper = Fraction(4 * b - lower_root, lower_root - b) + INTERVAL_PADDING
    return lower, upper


def leading_coefficients(
    C: int, E: int, delta: int, r1: int
) -> tuple[int, int, int]:
    # f(x) = a*x^5+b*x^2+c.
    return -6561 * C**3, 131220 * C**2 * E * delta, r1


def leading_value(coefficients: tuple[int, int, int], x: Fraction) -> Fraction:
    a, b, c = coefficients
    return a * x**5 + b * x**2 + c


# Sparse bivariate integer polynomials in X,d, keyed by (degree_X, degree_d).
Poly2 = dict[tuple[int, int], int]


def p_add(*polynomials: Poly2) -> Poly2:
    result: Poly2 = {}
    for polynomial in polynomials:
        for monomial, coefficient in polynomial.items():
            result[monomial] = result.get(monomial, 0) + coefficient
    return {key: value for key, value in result.items() if value}


def p_scale(coefficient: int, polynomial: Poly2) -> Poly2:
    return {key: coefficient * value for key, value in polynomial.items() if coefficient * value}


def p_mul(*polynomials: Poly2) -> Poly2:
    result: Poly2 = {(0, 0): 1}
    for polynomial in polynomials:
        updated: Poly2 = {}
        for (ax, ad), av in result.items():
            for (bx, bd), bv in polynomial.items():
                key = (ax + bx, ad + bd)
                updated[key] = updated.get(key, 0) + av * bv
        result = {key: value for key, value in updated.items() if value}
    return result


def p_pow(polynomial: Poly2, exponent: int) -> Poly2:
    result: Poly2 = {(0, 0): 1}
    for _ in range(exponent):
        result = p_mul(result, polynomial)
    return result


PX: Poly2 = {(1, 0): 1}
PD: Poly2 = {(0, 1): 1}


def eliminant_polynomial(
    C: int,
    D: int,
    E: int,
    K: int,
    R1: int,
    left: int,
    right: int,
) -> Poly2:
    """J with d^4*P*N=g^4*J, reconstructed symbolically."""

    delta = left * right
    y = p_add(PX, {(0, 0): -3 * left})
    z = p_add(PX, {(0, 0): -3 * right})
    yz = p_mul(y, z)
    main = p_add(
        p_scale(-9 * C, p_mul(PX, p_pow(yz, 2))),
        p_scale(
            delta,
            p_mul(
                p_pow(PD, 2),
                yz,
                p_add(p_scale(180 * E, PD), {(0, 0): 108 * D}),
            ),
        ),
    )
    tail = p_mul(p_pow(PD, 4), {(0, 0): 27 * K, (0, 1): R1})
    return p_add(p_scale(729 * C**2, main), tail)


def fourth_eliminant_polynomial(
    C: int,
    D: int,
    E: int,
    K: int,
    left: int,
    right: int,
) -> Poly2:
    """J4 with d^4*P*w=g^4*J4, reconstructed symbolically."""

    delta = left * right
    y = p_add(PX, {(0, 0): -3 * left})
    z = p_add(PX, {(0, 0): -3 * right})
    yz = p_mul(y, z)
    main = p_add(
        p_scale(-9 * C, p_mul(PX, p_pow(yz, 2))),
        p_scale(
            delta,
            p_mul(
                p_pow(PD, 2),
                yz,
                p_add(p_scale(180 * E, PD), {(0, 0): 108 * D}),
            ),
        ),
    )
    tail = p_scale(K, p_pow(PD, 4))
    return p_add(p_scale(27 * C**2, main), tail)


def fourth_nonvanishing_certificate() -> dict[str, Any]:
    """Exact finite sign/remainder ledger for the named fourth quotient."""

    critical_points_inside = endpoint_sign_changes = positions = 0
    minimum_margin: tuple[
        Fraction, tuple[int, tuple[int, int, int], int, str]
    ] | None = None
    maximum_remainder: tuple[int, tuple[int, tuple[int, int, int], int] | None] = (
        0,
        None,
    )
    for k in ROWS:
        lower, upper = residual_ratio_interval(k)
        for triple in nonreflected_triples(k):
            for owner in triple:
                positions += 1
                opposite = [index for index in triple if index != owner]
                left, right = owner - opposite[0], owner - opposite[1]
                delta = left * right
                C, D, E, F, _G = local_coefficients(k, owner)
                K = reduced_fourth_coefficient(C, D, E, F, left, right)
                leading = (-243 * C**3, 4860 * C**2 * E * delta, 0)
                endpoint_values = (
                    ("lower", leading_value(leading, lower)),
                    ("upper", leading_value(leading, upper)),
                )
                endpoint_sign_changes += endpoint_values[0][1] * endpoint_values[1][1] <= 0
                for side, value in endpoint_values:
                    item = (abs(value), (k, triple, owner, side))
                    if minimum_margin is None or item[0] < minimum_margin[0]:
                        minimum_margin = item
                a, b, _zero = leading
                critical_cube = Fraction(-2 * b, 5 * a)
                if critical_cube > 0 and lower**3 <= critical_cube <= upper**3:
                    critical_points_inside += 1

                polynomial = fourth_eliminant_polynomial(
                    C, D, E, K, left, right
                )
                homogeneous = {
                    degree_x: coefficient
                    for (degree_x, degree_d), coefficient in polynomial.items()
                    if degree_x + degree_d == 5
                }
                expected = {5: leading[0], 2: leading[1]}
                if homogeneous != expected:
                    raise AssertionError((k, triple, owner, homogeneous, expected))
                remainder = sum(
                    abs(coefficient) * 36**degree_x
                    for (degree_x, degree_d), coefficient in polynomial.items()
                    if degree_x + degree_d < 5
                )
                if remainder > maximum_remainder[0]:
                    maximum_remainder = (remainder, (k, triple, owner))

    if minimum_margin is None or maximum_remainder[1] is None:
        raise AssertionError("empty fourth-quotient ledger")
    if minimum_margin[0] <= 1:
        raise AssertionError("fourth leading margin is not uniformly above one")
    if not minimum_margin[0] * 10**1000 > maximum_remainder[0]:
        raise AssertionError("fourth remainder is not dominated at target cutoff")
    return {
        "cyclic_positions": positions,
        "critical_points_inside": critical_points_inside,
        "endpoint_sign_changes": endpoint_sign_changes,
        "minimum_endpoint_margin": {
            "numerator": minimum_margin[0].numerator,
            "denominator": minimum_margin[0].denominator,
            "case": minimum_margin[1],
        },
        "minimum_endpoint_margin_gt_one": True,
        "maximum_remainder_majorant": {
            "value": maximum_remainder[0],
            "case": maximum_remainder[1],
            "below_10_pow_46": maximum_remainder[0] < 10**46,
        },
        "target_cutoff_dominates_remainder": True,
    }


def coefficient_ledger() -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    all_w: list[tuple[int, tuple[int, tuple[int, int, int], int]]] = []
    all_v: list[tuple[int, tuple[int, tuple[int, int, int], int]]] = []
    minimum_margin: tuple[Fraction, tuple[int, tuple[int, int, int], int, str]] | None = None
    maximum_remainder = (0, None)
    total_triples = total_positions = total_r1_zero = total_r2_zero = 0
    total_critical_inside = total_sign_changes = 0
    decomposition_checks = 0

    for k in ROWS:
        row_triples = row_positions = row_r1_zero = row_r2_zero = 0
        row_w: list[tuple[int, tuple[int, tuple[int, int, int], int]]] = []
        row_v: list[tuple[int, tuple[int, tuple[int, int, int], int]]] = []
        row_critical_inside = row_sign_changes = 0
        lower, upper = residual_ratio_interval(k)
        correction = power_window_correction_bound(k)
        for triple in nonreflected_triples(k):
            row_triples += 1
            for owner in triple:
                opposite = [index for index in triple if index != owner]
                dl, dr = owner - opposite[0], owner - opposite[1]
                delta = dl * dr
                C, D, E, F, G = local_coefficients(k, owner)
                K = reduced_fourth_coefficient(C, D, E, F, dl, dr)
                R1, R2 = reduced_fifth_coefficients(C, D, E, F, G, dl, dr)
                for gap in (0, 1, -7, 10**1000 + 123):
                    if reduced_fifth_value(C, D, E, F, G, gap, dl, dr) != (
                        27 * K + gap * R1 + gap**2 * R2
                    ):
                        raise AssertionError("reduced fifth decomposition")
                    decomposition_checks += 1

                U = RESIDUAL_CEILING[k]
                B = 9 * abs(C) * U**3 + 108 * abs(D * delta) + 180 * abs(E * delta)
                W = 27 * C**2 * U**2 * B + abs(K)
                V = 27 * W + abs(R1)
                case = (k, triple, owner)
                row_w.append((W, case))
                row_v.append((V, case))
                all_w.append((W, case))
                all_v.append((V, case))

                row_positions += 1
                row_r1_zero += R1 == 0
                row_r2_zero += R2 == 0
                leading = leading_coefficients(C, E, delta, R1)
                endpoint_values = (
                    ("lower", leading_value(leading, lower)),
                    ("upper", leading_value(leading, upper)),
                )
                if endpoint_values[0][1] * endpoint_values[1][1] <= 0:
                    row_sign_changes += 1
                for side, value in endpoint_values:
                    item = (abs(value), (k, triple, owner, side))
                    if minimum_margin is None or item[0] < minimum_margin[0]:
                        minimum_margin = item

                a, b, _c = leading
                if a:
                    critical_cube = Fraction(-2 * b, 5 * a)
                    if critical_cube > 0 and lower**3 <= critical_cube <= upper**3:
                        row_critical_inside += 1

                polynomial = eliminant_polynomial(C, D, E, K, R1, dl, dr)
                # Independently match the degree-five homogeneous part.
                homogeneous = {
                    ax: coefficient
                    for (ax, ad), coefficient in polynomial.items()
                    if ax + ad == 5
                }
                expected = {5: leading[0], 2: leading[1], 0: leading[2]}
                if homogeneous != {key: value for key, value in expected.items() if value}:
                    raise AssertionError((case, homogeneous, expected))
                remainder = sum(
                    abs(coefficient) * 36**degree_x
                    for (degree_x, degree_d), coefficient in polynomial.items()
                    if degree_x + degree_d < 5
                )
                if remainder > maximum_remainder[0]:
                    maximum_remainder = (remainder, case)

        rows.append(
            {
                "k": k,
                "nonreflected_triples": row_triples,
                "cyclic_positions": row_positions,
                "r1_zero": row_r1_zero,
                "r2_zero": row_r2_zero,
                "critical_points_inside": row_critical_inside,
                "endpoint_sign_changes": row_sign_changes,
                "w_min": min(row_w),
                "w_max": max(row_w),
                "v_min": min(row_v),
                "v_max": max(row_v),
                "interval": {
                    "lower": [lower.numerator, lower.denominator],
                    "upper": [upper.numerator, upper.denominator],
                    "root_bracket_adjacent_and_exact": True,
                    "padding_dominates_exact_finite_correction": True,
                    "maximum_power_window_correction": [
                        correction.numerator,
                        correction.denominator,
                    ],
                },
            }
        )
        total_triples += row_triples
        total_positions += row_positions
        total_r1_zero += row_r1_zero
        total_r2_zero += row_r2_zero
        total_critical_inside += row_critical_inside
        total_sign_changes += row_sign_changes

    if minimum_margin is None:
        raise AssertionError("empty coefficient ledger")
    if minimum_margin[0] <= 1:
        raise AssertionError("normalized leading margin is not uniformly above one")
    if not minimum_margin[0] * 10**1000 > maximum_remainder[0]:
        raise AssertionError("normalized remainder is not dominated at target cutoff")
    return {
        "rows": rows,
        "totals": {
            "nonreflected_triples": total_triples,
            "cyclic_positions": total_positions,
            "r1_zero": total_r1_zero,
            "r2_zero": total_r2_zero,
            "critical_points_inside": total_critical_inside,
            "endpoint_sign_changes": total_sign_changes,
            "decomposition_checks": decomposition_checks,
        },
        "global_w_min": min(all_w),
        "global_w_max": max(all_w),
        "global_v_min": min(all_v),
        "global_v_max": max(all_v),
        "minimum_endpoint_margin": {
            "numerator": minimum_margin[0].numerator,
            "denominator": minimum_margin[0].denominator,
            "case": minimum_margin[1],
        },
        "minimum_endpoint_margin_gt_one": True,
        "maximum_remainder_majorant": {
            "value": maximum_remainder[0],
            "case": maximum_remainder[1],
            "below_10_pow_46": maximum_remainder[0] < 10**46,
        },
        "target_cutoff_dominates_remainder": True,
    }


def crt(residues: tuple[int, ...], moduli: tuple[int, ...]) -> tuple[int, int]:
    value, modulus = 0, 1
    for residue, next_modulus in zip(residues, moduli, strict=True):
        if next_modulus <= 0 or gcd(modulus, next_modulus) != 1:
            raise ValueError("CRT moduli must be positive and coprime")
        step = ((residue - value) * pow(modulus, -1, next_modulus)) % next_modulus
        value = (value + modulus * step) % (modulus * next_modulus)
        modulus *= next_modulus
    return value, modulus


def third_local(C: int, D: int, E: int, P: int, M: int, a: int) -> int:
    return -3 * (3 * C * a - 4 * D * M**2) + 20 * E * P * M**3


def fourth_local(C: int, D: int, E: int, F: int, P: int, M: int, a: int) -> int:
    return 3 * third_local(C, D, E, P, M, a) + P**2 * (
        -9 * D * a**2 + 36 * E * a * M**2 + 84 * F * M**4
    )


def fifth_local(
    C: int, D: int, E: int, F: int, G: int, P: int, M: int, a: int
) -> int:
    return 3 * fourth_local(C, D, E, F, P, M, a) + 20 * P**3 * M**3 * (
        12 * a * F + 17 * G * M**2
    )


def block_product(k: int, n: int) -> int:
    return prod(n + index for index in range(1, k + 1))


def fifth_hensel_fixture(exponent: int = 166) -> dict[str, Any]:
    k, anchor = 5, CRT_INDICES[0]
    components = tuple(base**exponent for base in CRT_BASES)
    gap = prod(components)
    moduli = tuple(component**2 for component in components)
    residues = tuple(
        (-3 * (index - anchor)) % modulus
        for index, modulus in zip(CRT_INDICES, moduli, strict=True)
    )
    base_x, modulus = crt(residues, moduli)
    if modulus != gap**2:
        raise AssertionError("square CRT modulus")

    def cofactor(parameter: int, index: int, component: int) -> int:
        numerator = base_x + gap**2 * parameter + 3 * (index - anchor)
        if numerator % component**2:
            raise AssertionError("square residual")
        return numerator // component**2

    third_targets = []
    for index, component in zip(CRT_INDICES, components, strict=True):
        C, D, E, _F, _G = local_coefficients(k, index)
        M, a = gap // component, cofactor(0, index, component)
        value = third_local(C, D, E, component, M, a)
        derivative = -9 * C * M**2
        third_targets.append((-value * pow(derivative, -1, component**2)) % component**2)
    third_parameter, _ = crt(tuple(third_targets), moduli)

    fourth_targets = []
    for index, component in zip(CRT_INDICES, components, strict=True):
        C, D, E, F, _G = local_coefficients(k, index)
        M, a = gap // component, cofactor(third_parameter, index, component)
        value = fourth_local(C, D, E, F, component, M, a)
        derivative = (-27 * C * M**4) % component
        fourth_targets.append((-(value // component**2) * pow(derivative, -1, component)) % component)
    fourth_lift, _ = crt(tuple(fourth_targets), components)
    fourth_parameter = third_parameter + gap**2 * fourth_lift

    fifth_targets = []
    for index, component in zip(CRT_INDICES, components, strict=True):
        C, D, E, F, G = local_coefficients(k, index)
        M, a = gap // component, cofactor(fourth_parameter, index, component)
        value = fifth_local(C, D, E, F, G, component, M, a)
        shifted = fifth_local(C, D, E, F, G, component, M, a + component**3 * M**5)
        derivative = ((shifted - value) // component**3) % component
        fifth_targets.append((-(value // component**3) * pow(derivative, -1, component)) % component)
    fifth_lift, _ = crt(tuple(fifth_targets), components)
    parameter = fourth_parameter + gap**3 * fifth_lift
    for integrality_lift in range(3):
        candidate = parameter + gap**4 * integrality_lift
        x_anchor = base_x + gap**2 * candidate
        if (x_anchor + gap) % 3 == 0:
            n = (x_anchor + gap) // 3 - anchor
            break
    else:
        raise AssertionError("integrality lift")

    residuals = [3 * (n + index) - gap for index in CRT_INDICES]
    cofactors = [
        residual // component**2
        for residual, component in zip(residuals, components, strict=True)
    ]
    local_remainders = []
    reduced_remainders = []
    normalized_remainders = []
    z_nonzero = []
    w_nonzero = []
    n5_nonzero = []
    for position, owner in enumerate(CRT_INDICES):
        other = [index for index in range(3) if index != position]
        left, right = other
        P, Q, R = components[position], components[left], components[right]
        a, b, c = cofactors[position], cofactors[left], cofactors[right]
        dl, dr = owner - CRT_INDICES[left], owner - CRT_INDICES[right]
        C, D, E, F, G = local_coefficients(k, owner)
        M = gap // P
        local5 = fifth_local(C, D, E, F, G, P, M, a)
        t, delta = a * b * c, dl * dr
        third = -9 * C * t + 108 * D * delta + 180 * E * delta * gap
        if third % P**2:
            raise AssertionError("third quotient")
        z = third // P**2
        K = reduced_fourth_coefficient(C, D, E, F, dl, dr)
        R1, R2 = reduced_fifth_coefficients(C, D, E, F, G, dl, dr)
        fourth_numerator = 27 * C**2 * b * c * z + K
        if fourth_numerator % P:
            raise AssertionError("fourth quotient")
        w = fourth_numerator // P
        normalized = 27 * w + M * R1
        reduced = 729 * C**2 * b * c * z + reduced_fifth_value(
            C, D, E, F, G, gap, dl, dr
        )
        local_remainders.append(local5 % P**4)
        reduced_remainders.append(reduced % P**2)
        normalized_remainders.append(normalized % P)
        z_nonzero.append(z != 0)
        w_nonzero.append(w != 0)
        n5_nonzero.append(normalized != 0)

    return {
        "exponent": exponent,
        "gap_digits": len(str(gap)),
        "n_digits": len(str(n)),
        "local_fifth_remainders": local_remainders,
        "reduced_remainders": reduced_remainders,
        "normalized_remainders": normalized_remainders,
        "all_z_nonzero": all(z_nonzero),
        "all_w_nonzero": all(w_nonzero),
        "all_normalized_nonzero": all(n5_nonzero),
        "upper_window": all(0 < residual < RESIDUAL_CEILING[k] * gap for residual in residuals),
        "block_equation": block_product(k, n + gap) == 4 * block_product(k, n),
    }


@cache
def report() -> dict[str, Any]:
    ledger = coefficient_ledger()
    fourth_certificate = fourth_nonvanishing_certificate()
    fixture = fifth_hensel_fixture()
    return {
        "arithmetic": "exact Python integers and fractions.Fraction",
        "ledger": ledger,
        "fourth_nonvanishing": fourth_certificate,
        "hensel_fixture": fixture,
        "verdict": (
            "W/V bounds and the fifth-numerator nonzero certificate are proper; "
            "cyclic multiplication remains exponent-wrong"
        ),
    }


def main() -> None:
    print(json.dumps(report(), sort_keys=True))


if __name__ == "__main__":
    main()
