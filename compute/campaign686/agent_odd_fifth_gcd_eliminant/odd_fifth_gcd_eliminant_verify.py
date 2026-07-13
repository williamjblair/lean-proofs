#!/usr/bin/env python3
"""Exact simultaneous gcd/eliminant audit for the odd three-bucket core.

The script reconstructs the normalized fifth eliminant from integer
arithmetic.  It scans all 1,008 nonreflected triples in the six target rows,
all three cyclic owner positions, all three natural leading-term cross
lattices, and three pairwise-coprime packing patterns.

All load-bearing arithmetic uses ``int`` or ``fractions.Fraction``.  The two
historical Hensel fixtures are replayed through their separately frozen exact
constructors.  No floating point value is used in a verdict.
"""

from __future__ import annotations

import hashlib
import json
from collections import Counter
from fractions import Fraction
from functools import cache, reduce
from itertools import combinations
from math import comb, gcd, prod
from typing import Any, Iterable

from compute.campaign686.fifth_quotient_short_window_verify import (
    fifth_hensel_fixture,
)
from compute.campaign686.short_window_quotient_attack import (
    target_size_congruence_family,
)


ROWS = (5, 7, 9, 11, 13, 15)
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
TARGET_CUTOFF = 10**1000
DIRECT_RESIDUAL_BOUND = 36
COMMON_RESIDUAL_BOUND = 81


Poly2 = dict[tuple[int, int], int]


def sign(value: int | Fraction) -> int:
    if value == 0:
        raise AssertionError("unexpected zero")
    return 1 if value > 0 else -1


def local_coefficients(k: int, owner: int) -> tuple[int, int, int, int, int]:
    """First five coefficients of product_(j != owner)(x+j-owner)."""

    coefficients = [1]
    for index in range(1, k + 1):
        if index == owner:
            continue
        offset = index - owner
        updated = [0] * (len(coefficients) + 1)
        for degree, coefficient in enumerate(coefficients):
            updated[degree] += offset * coefficient
            updated[degree + 1] += coefficient
        coefficients = updated
    return tuple(coefficients[:5])  # type: ignore[return-value]


def reduced_fourth_coefficient(
    C: int, D: int, E: int, F: int, left: int, right: int
) -> int:
    delta, sigma = left * right, left + right
    return 108 * delta * (
        -108 * D**3 * delta
        + C * D * (-108 * D * sigma + 324 * E * delta)
        + 567 * C**2 * F * delta
    )


def reduced_fifth_linear_coefficient(
    C: int, D: int, E: int, F: int, G: int, left: int, right: int
) -> int:
    delta, sigma = left * right, left + right
    return 8748 * delta * (
        255 * C**2 * G * delta
        - 120 * C * D * E * sigma
        + 240 * C * D * F * delta
        + 180 * C * E**2 * delta
        - 120 * D**2 * E * delta
    )


def nonreflected_triples(k: int) -> Iterable[tuple[int, int, int]]:
    center = (k + 1) // 2
    for triple in combinations(range(1, k + 1), 3):
        others = [owner for owner in triple if owner != center]
        if center in triple and sum(others) == 2 * center:
            continue
        yield triple


def p_add(*polynomials: Poly2) -> Poly2:
    result: Poly2 = {}
    for polynomial in polynomials:
        for monomial, coefficient in polynomial.items():
            result[monomial] = result.get(monomial, 0) + coefficient
    return {key: value for key, value in result.items() if value}


def p_scale(coefficient: int, polynomial: Poly2) -> Poly2:
    return {
        key: coefficient * value
        for key, value in polynomial.items()
        if coefficient * value
    }


def p_mul(*polynomials: Poly2) -> Poly2:
    result: Poly2 = {(0, 0): 1}
    for polynomial in polynomials:
        updated: Poly2 = {}
        for (left_x, left_d), left_value in result.items():
            for (right_x, right_d), right_value in polynomial.items():
                key = (left_x + right_x, left_d + right_d)
                updated[key] = updated.get(key, 0) + left_value * right_value
        result = {key: value for key, value in updated.items() if value}
    return result


def p_pow(polynomial: Poly2, exponent: int) -> Poly2:
    result: Poly2 = {(0, 0): 1}
    for _ in range(exponent):
        result = p_mul(result, polynomial)
    return result


def p_eval(polynomial: Poly2, x: int, d: int) -> int:
    return sum(
        coefficient * x**degree_x * d**degree_d
        for (degree_x, degree_d), coefficient in polynomial.items()
    )


PX: Poly2 = {(1, 0): 1}
PD: Poly2 = {(0, 1): 1}


def fifth_eliminant(
    C: int,
    D: int,
    E: int,
    K: int,
    R1: int,
    left: int,
    right: int,
) -> Poly2:
    """J with d^4*P*N=g^4*J, reconstructed from the Lean formula."""

    delta = left * right
    y = p_add(PX, {(0, 0): -3 * left})
    z = p_add(PX, {(0, 0): -3 * right})
    yz = p_mul(y, z)
    core = p_add(
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
    return p_add(p_scale(729 * C**2, core), tail)


def shift_x(polynomial: Poly2, shift: int) -> Poly2:
    """Substitute X+shift for X exactly."""

    result: Poly2 = {}
    for (degree_x, degree_d), coefficient in polynomial.items():
        for remaining_x in range(degree_x + 1):
            key = (remaining_x, degree_d)
            result[key] = result.get(key, 0) + (
                coefficient
                * comb(degree_x, remaining_x)
                * shift ** (degree_x - remaining_x)
            )
    return {key: value for key, value in result.items() if value}


def residual_ratio_interval(k: int) -> tuple[Fraction, Fraction]:
    lower_root, upper_root = ROOT_BRACKETS[k]
    denominator = BRACKET_DENOMINATOR
    if upper_root != lower_root + 1:
        raise AssertionError("root bracket is not adjacent")
    if not lower_root**k < 4 * denominator**k < upper_root**k:
        raise AssertionError("root bracket failed")
    lower = (
        Fraction(4 * denominator - upper_root, upper_root - denominator)
        - INTERVAL_PADDING
    )
    upper = (
        Fraction(4 * denominator - lower_root, lower_root - denominator)
        + INTERVAL_PADDING
    )
    return lower, upper


def leading_coefficients(
    C: int, E: int, delta: int, R1: int
) -> tuple[int, int, int]:
    return -6561 * C**3, 131220 * C**2 * E * delta, R1


def leading_value(coefficients: tuple[int, int, int], x: Fraction) -> Fraction:
    a, b, c = coefficients
    return a * x**5 + b * x**2 + c


def certified_eliminant_sign(
    polynomial: Poly2,
    leading: tuple[int, int, int],
    lower: Fraction,
    upper: Fraction,
) -> int:
    """Certify the sign of J throughout the target residual window."""

    a, b, c = leading
    endpoints = (leading_value(leading, lower), leading_value(leading, upper))
    if sign(endpoints[0]) != sign(endpoints[1]):
        raise AssertionError("leading endpoint sign change")
    critical_cube = Fraction(-2 * b, 5 * a)
    if critical_cube > 0 and lower**3 <= critical_cube <= upper**3:
        raise AssertionError("leading critical point inside interval")

    homogeneous = {
        degree_x: coefficient
        for (degree_x, degree_d), coefficient in polynomial.items()
        if degree_x + degree_d == 5
    }
    expected = {
        degree: coefficient
        for degree, coefficient in enumerate((c, 0, b, 0, 0, a))
        if coefficient
    }
    if homogeneous != expected:
        raise AssertionError(("homogeneous mismatch", homogeneous, expected))

    remainder = sum(
        abs(coefficient) * DIRECT_RESIDUAL_BOUND**degree_x
        for (degree_x, degree_d), coefficient in polynomial.items()
        if degree_x + degree_d < 5
    )
    margin = min(abs(value) for value in endpoints)
    if margin * TARGET_CUTOFF <= remainder:
        raise AssertionError("target cutoff does not dominate remainder")
    return sign(endpoints[0])


def cross(left: list[int], right: list[int]) -> tuple[int, int, int]:
    return (
        left[1] * right[2] - left[2] * right[1],
        left[2] * right[0] - left[0] * right[2],
        left[0] * right[1] - left[1] * right[0],
    )


def primitive(vector: tuple[int, int, int]) -> tuple[int, int, int]:
    common = reduce(gcd, (abs(value) for value in vector))
    if common == 0:
        raise AssertionError("zero cross product")
    return tuple(value // common for value in vector)  # type: ignore[return-value]


def determinant(rows: list[tuple[int, int, int]]) -> int:
    (a, b, c), (d, e, f), (g, h, i) = rows
    return a * (e * i - f * h) - b * (d * i - f * g) + c * (d * h - e * g)


def matrix_rank(matrix: list[list[int]]) -> int:
    work = [[Fraction(value) for value in row] for row in matrix]
    row_count = len(work)
    column_count = len(work[0]) if work else 0
    pivot_row = 0
    for column in range(column_count):
        candidate = next(
            (row for row in range(pivot_row, row_count) if work[row][column]),
            None,
        )
        if candidate is None:
            continue
        work[pivot_row], work[candidate] = work[candidate], work[pivot_row]
        pivot = work[pivot_row][column]
        work[pivot_row] = [value / pivot for value in work[pivot_row]]
        for row in range(pivot_row + 1, row_count):
            if work[row][column]:
                multiplier = work[row][column]
                work[row] = [
                    value - multiplier * pivot_value
                    for value, pivot_value in zip(
                        work[row], work[pivot_row], strict=True
                    )
                ]
        pivot_row += 1
    return pivot_row


def high_degree_rank(polynomials: list[Poly2], cutoff: int) -> tuple[int, int]:
    monomials = sorted(
        {
            monomial
            for polynomial in polynomials
            for monomial in polynomial
            if sum(monomial) >= cutoff
        }
    )
    matrix = [
        [polynomial.get(monomial, 0) for polynomial in polynomials]
        for monomial in monomials
    ]
    return matrix_rank(matrix), len(monomials)


@cache
def block_equation_polynomial(k: int) -> Poly2:
    """Exact 3^k-cleared block difference in U=3n-d and d."""

    upper: Poly2 = {(0, 0): 1}
    lower: Poly2 = {(0, 0): 1}
    for index in range(1, k + 1):
        upper = p_mul(
            upper, {(1, 0): 1, (0, 1): 4, (0, 0): 3 * index}
        )
        lower = p_mul(
            lower, {(1, 0): 1, (0, 1): 1, (0, 0): 3 * index}
        )
    return p_add(upper, p_scale(-4, lower))


def monomial_polynomials_at_most(degree: int) -> list[Poly2]:
    return [
        {(degree_x, degree_d): 1}
        for degree_x in range(degree + 1)
        for degree_d in range(degree + 1 - degree_x)
    ]


def equation_quotient_kernel_dimension(
    polynomials: list[Poly2],
    *,
    k: int,
    polynomial_degree: int,
    closing_cutoff: int,
) -> int:
    """Kernel after quotienting high terms by the exact block equation.

    A nonzero kernel vector would give constant weights on ``polynomials``
    and a polynomial multiplier Q such that the weighted sum minus
    Q*blockDifference has degree below ``closing_cutoff``.
    """

    if polynomial_degree < k:
        equation_multiples: list[Poly2] = []
    else:
        equation = block_equation_polynomial(k)
        equation_multiples = [
            p_mul(equation, monomial)
            for monomial in monomial_polynomials_at_most(polynomial_degree - k)
        ]
    generators = equation_multiples + polynomials
    monomials = sorted(
        {
            monomial
            for polynomial in generators
            for monomial in polynomial
            if sum(monomial) >= closing_cutoff
        }
    )

    def projected_rank(items: list[Poly2]) -> int:
        if not items:
            return 0
        return matrix_rank(
            [
                [item.get(monomial, 0) for item in items]
                for monomial in monomials
            ]
        )

    equation_rank = projected_rank(equation_multiples)
    combined_rank = projected_rank(generators)
    image_rank_mod_equation = combined_rank - equation_rank
    return len(polynomials) - image_rank_mod_equation


def sum_polynomials(polynomials: list[Poly2], weights: tuple[int, int, int]) -> Poly2:
    return p_add(
        *(p_scale(weight, polynomial) for weight, polynomial in zip(weights, polynomials))
    )


def common_window_majorant(polynomial: Poly2) -> int:
    """H with |S(U,d)| <= H*d^5 for d>=1 and |U|<=81d."""

    if any(sum(monomial) > 5 for monomial in polynomial):
        raise AssertionError("unexpected degree above five")
    return sum(
        abs(coefficient) * COMMON_RESIDUAL_BOUND**degree_x
        for (degree_x, _degree_d), coefficient in polynomial.items()
    )


def position_polynomials(
    k: int, triple: tuple[int, int, int]
) -> tuple[list[Poly2], list[Poly2], list[tuple[int, int, int]], list[int]]:
    """Return direct/common J, leading rows, and certified N signs."""

    direct: list[Poly2] = []
    common: list[Poly2] = []
    leading_rows: list[tuple[int, int, int]] = []
    signs: list[int] = []
    lower, upper = residual_ratio_interval(k)
    for owner in triple:
        opposite = [index for index in triple if index != owner]
        left, right = owner - opposite[0], owner - opposite[1]
        C, D, E, F, G = local_coefficients(k, owner)
        K = reduced_fourth_coefficient(C, D, E, F, left, right)
        R1 = reduced_fifth_linear_coefficient(C, D, E, F, G, left, right)
        polynomial = fifth_eliminant(C, D, E, K, R1, left, right)
        leading = leading_coefficients(C, E, left * right, R1)
        direct.append(polynomial)
        common.append(shift_x(polynomial, 3 * owner))
        leading_rows.append(leading)
        signs.append(certified_eliminant_sign(polynomial, leading, lower, upper))
    return direct, common, leading_rows, signs


def leading_and_packing_scan() -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    totals = Counter()
    global_rank_failures = 0
    determinant_positive = determinant_negative = 0

    for k in ROWS:
        row = Counter()
        row_majorant = -1
        row_majorant_case: dict[str, Any] | None = None
        row_minimum_weight: int | None = None
        for triple in nonreflected_triples(k):
            _direct, common, leading_rows, n_signs = position_polynomials(k, triple)
            columns = [
                [leading_rows[row_index][column] for row_index in range(3)]
                for column in range(3)
            ]
            det = determinant(leading_rows)
            if det > 0:
                determinant_positive += 1
                row["determinant_positive"] += 1
            elif det < 0:
                determinant_negative += 1
                row["determinant_negative"] += 1
            else:
                raise AssertionError(("zero leading determinant", k, triple))

            orientations = {
                "ab": (columns[0], columns[1], columns[2]),
                "ac": (columns[0], columns[2], columns[1]),
                "bc": (columns[1], columns[2], columns[0]),
            }
            for name, (first, second, remaining) in orientations.items():
                weights = primitive(cross(first, second))
                gamma = sum(
                    weight * coefficient
                    for weight, coefficient in zip(weights, remaining, strict=True)
                )
                if gamma == 0 or any(weight == 0 for weight in weights):
                    raise AssertionError(("degenerate cross lattice", k, triple, name))
                weighted_signs = {
                    sign(weight) * n_sign
                    for weight, n_sign in zip(weights, n_signs, strict=True)
                }
                if weighted_signs == {-1, 1}:
                    row[f"{name}_mixed"] += 1
                elif weighted_signs == {1}:
                    row[f"{name}_one_sided_positive"] += 1
                elif weighted_signs == {-1}:
                    row[f"{name}_one_sided_negative"] += 1
                else:
                    raise AssertionError(("bad sign cell", weighted_signs))

                if name == "bc" and len(weighted_signs) == 1:
                    combination = sum_polynomials(common, weights)
                    majorant = common_window_majorant(combination)
                    if majorant > row_majorant:
                        row_majorant = majorant
                        row_majorant_case = {
                            "triple": list(triple),
                            "primitive_weights": list(weights),
                        }
                    minimum_weight = min(abs(weight) for weight in weights)
                    row_minimum_weight = (
                        minimum_weight
                        if row_minimum_weight is None
                        else min(row_minimum_weight, minimum_weight)
                    )

            owner_residuals = [
                {(1, 0): 1, (0, 0): 3 * owner} for owner in triple
            ]
            opposite_packed = [
                p_mul(
                    owner_residuals[(position + 1) % 3],
                    owner_residuals[(position + 2) % 3],
                    common[position],
                )
                for position in range(3)
            ]
            pair_packed = [
                p_mul(
                    owner_residuals[position],
                    common[(position + 1) % 3],
                    common[(position + 2) % 3],
                )
                for position in range(3)
            ]
            triple_product = [p_mul(*common)]
            ranks = {
                "raw_rank_at_closing_cutoff": high_degree_rank(common, 4),
                "opposite_packed_rank_at_closing_cutoff": high_degree_rank(
                    opposite_packed, 6
                ),
                "pair_packed_rank_at_closing_cutoff": high_degree_rank(
                    pair_packed, 10
                ),
            }
            expected = {
                "raw_rank_at_closing_cutoff": (3, 7),
                "opposite_packed_rank_at_closing_cutoff": (3, 8),
                "pair_packed_rank_at_closing_cutoff": (3, 16),
            }
            if ranks != expected:
                global_rank_failures += 1
                raise AssertionError((k, triple, ranks))
            equation_kernels = {
                "raw": equation_quotient_kernel_dimension(
                    common,
                    k=k,
                    polynomial_degree=5,
                    closing_cutoff=4,
                ),
                "opposite_packed": equation_quotient_kernel_dimension(
                    opposite_packed,
                    k=k,
                    polynomial_degree=7,
                    closing_cutoff=6,
                ),
                "pair_packed": equation_quotient_kernel_dimension(
                    pair_packed,
                    k=k,
                    polynomial_degree=11,
                    closing_cutoff=10,
                ),
                "triple_product": equation_quotient_kernel_dimension(
                    triple_product,
                    k=k,
                    polynomial_degree=15,
                    closing_cutoff=14,
                ),
            }
            if any(equation_kernels.values()):
                raise AssertionError(
                    ("equation quotient kernel", k, triple, equation_kernels)
                )
            for family in equation_kernels:
                row[f"{family}_equation_quotient_kernel_zero"] += 1
            row["full_rank_packing_geometries"] += 1
            row["nonreflected_triples"] += 1

        one_sided = (
            row["bc_one_sided_positive"] + row["bc_one_sided_negative"]
        )
        row_result = {
            "k": k,
            "nonreflected_triples": row["nonreflected_triples"],
            "leading_determinant_positive": row["determinant_positive"],
            "leading_determinant_negative": row["determinant_negative"],
            "ab_mixed": row["ab_mixed"],
            "ac_mixed": row["ac_mixed"],
            "bc_mixed": row["bc_mixed"],
            "bc_one_sided_positive": row["bc_one_sided_positive"],
            "bc_one_sided_negative": row["bc_one_sided_negative"],
            "bc_one_sided_total": one_sided,
            "full_rank_packing_geometries": row[
                "full_rank_packing_geometries"
            ],
            "exact_block_equation_quotient_kernel_zero": {
                family: row[f"{family}_equation_quotient_kernel_zero"]
                for family in (
                    "raw",
                    "opposite_packed",
                    "pair_packed",
                    "triple_product",
                )
            },
            "one_sided_uniform_H": row_majorant,
            "one_sided_uniform_H_digits": len(str(row_majorant)),
            "one_sided_H_maximizer": row_majorant_case,
            "one_sided_minimum_abs_weight": row_minimum_weight,
        }
        rows.append(row_result)
        totals.update(
            {
                "nonreflected_triples": row["nonreflected_triples"],
                "ab_mixed": row["ab_mixed"],
                "ac_mixed": row["ac_mixed"],
                "bc_mixed": row["bc_mixed"],
                "bc_one_sided_positive": row["bc_one_sided_positive"],
                "bc_one_sided_negative": row["bc_one_sided_negative"],
                "bc_one_sided_total": one_sided,
                "full_rank_packing_geometries": row[
                    "full_rank_packing_geometries"
                ],
                **{
                    f"{family}_equation_quotient_kernel_zero": row[
                        f"{family}_equation_quotient_kernel_zero"
                    ]
                    for family in (
                        "raw",
                        "opposite_packed",
                        "pair_packed",
                        "triple_product",
                    )
                },
            }
        )

    return {
        "rows": rows,
        "totals": dict(totals),
        "leading_determinant_positive": determinant_positive,
        "leading_determinant_negative": determinant_negative,
        "rank_failures": global_rank_failures,
        "rank_certificate": {
            "raw": {
                "known_divisor_exponent": 4,
                "polynomial_degree": 5,
                "closing_degree_cutoff": 3,
                "rank_on_terms_degree_at_least_4": 3,
            },
            "opposite_packed_Xt_Xu_Js": {
                "known_divisor_exponent": 6,
                "polynomial_degree": 7,
                "closing_degree_cutoff": 5,
                "rank_on_terms_degree_at_least_6": 3,
            },
            "pair_packed_Xs_Jt_Ju": {
                "known_divisor_exponent": 10,
                "polynomial_degree": 11,
                "closing_degree_cutoff": 9,
                "rank_on_terms_degree_at_least_10": 3,
            },
            "triple_product": {
                "known_divisor_exponent": 14,
                "polynomial_degree": 15,
                "uncancelled_degree_deficit": 1,
            },
            "exact_block_equation_quotient": {
                "method": (
                    "allow every multiplier monomial through degree "
                    "polynomial_degree-k and project away the exact cleared "
                    "block-difference polynomial"
                ),
                "raw_kernel_zero_geometries": totals[
                    "raw_equation_quotient_kernel_zero"
                ],
                "opposite_packed_kernel_zero_geometries": totals[
                    "opposite_packed_equation_quotient_kernel_zero"
                ],
                "pair_packed_kernel_zero_geometries": totals[
                    "pair_packed_equation_quotient_kernel_zero"
                ],
                "triple_product_kernel_zero_geometries": totals[
                    "triple_product_equation_quotient_kernel_zero"
                ],
            },
        },
    }


def block_product(k: int, n: int) -> int:
    return prod(n + index for index in range(1, k + 1))


def block_equation_polynomial_audit() -> dict[str, Any]:
    checks = 0
    for k in ROWS:
        polynomial = block_equation_polynomial(k)
        for n in (0, 1, 7):
            for d in (1, 2, 11):
                common_residual = 3 * n - d
                expected = 3**k * (
                    block_product(k, n + d) - 4 * block_product(k, n)
                )
                if p_eval(polynomial, common_residual, d) != expected:
                    raise AssertionError(("block polynomial", k, n, d))
                checks += 1
    return {
        "signed_integer_grid_checks": checks,
        "all_equal_3_pow_k_times_block_difference": True,
    }


def local_lifts(
    C: int, D: int, E: int, F: int, G: int, P: int, M: int, a: int
) -> tuple[int, int, int, int]:
    second = 3 * C * a - 4 * D * M**2
    third = -3 * second + 20 * E * P * M**3
    fourth = 3 * third + P**2 * (
        -9 * D * a**2 + 36 * E * a * M**2 + 84 * F * M**4
    )
    fifth = 3 * fourth + 20 * P**3 * M**3 * (12 * a * F + 17 * G * M**2)
    return second, third, fourth, fifth


def fourth_correction(
    D: int,
    E: int,
    F: int,
    t: int,
    g: int,
    left: int,
    right: int,
) -> int:
    delta, sigma = left * right, left + right
    return (
        -9 * D * t**2
        - 108 * D * t * g**2 * sigma
        + 324 * E * t * g**2 * delta
        + 6804 * F * g**4 * delta**2
    )


def small_short_fifth_fixture() -> dict[str, Any]:
    """Exact coarse-short fixture satisfying all cyclic lifts through fifth."""

    k = 5
    owners = (1, 2, 3)
    components = (2, 5, 3)
    g = 30
    d = g * prod(components)
    anchor_residual = 9372
    residuals = tuple(
        anchor_residual + 3 * (owner - owners[0]) for owner in owners
    )
    cofactors = tuple(
        residual // component**2
        for residual, component in zip(residuals, components, strict=True)
    )
    if any(
        residual != cofactor * component**2
        for residual, cofactor, component in zip(
            residuals, cofactors, components, strict=True
        )
    ):
        raise AssertionError("bad square residual fixture")
    n = (anchor_residual + d) // 3 - owners[0]
    if 3 * (n + owners[0]) - d != anchor_residual:
        raise AssertionError("bad n reconstruction")
    if any((n + owner) % component for owner, component in zip(owners, components)):
        raise AssertionError("owner divisibility failed")

    t = prod(cofactors)
    cyclic: list[dict[str, Any]] = []
    for position, owner in enumerate(owners):
        other_positions = [index for index in range(3) if index != position]
        left_position, right_position = other_positions
        left_owner, right_owner = (
            owners[left_position],
            owners[right_position],
        )
        left, right = owner - left_owner, owner - right_owner
        delta = left * right
        P = components[position]
        M = d // P
        a = cofactors[position]
        b = cofactors[left_position]
        c = cofactors[right_position]
        C, D, E, F, G = local_coefficients(k, owner)
        second_local, third_local, fourth_local, fifth_local = local_lifts(
            C, D, E, F, G, P, M, a
        )
        second = 3 * (C * t - 12 * D * g**2 * delta)
        third = -3 * second + 180 * E * g**2 * delta * d
        if third % P**2:
            raise AssertionError("third quotient failed")
        z = third // P**2
        correction = fourth_correction(D, E, F, t, g, left, right)
        composed_fourth = 3 * b * c * third + P**2 * correction
        K = reduced_fourth_coefficient(C, D, E, F, left, right)
        R1 = reduced_fifth_linear_coefficient(C, D, E, F, G, left, right)
        fourth_numerator = 27 * C**2 * b * c * z + K * g**4
        if fourth_numerator % P:
            raise AssertionError("fourth quotient failed")
        w = fourth_numerator // P
        normalized = 27 * w + M * R1 * g**4
        cyclic.append(
            {
                "owner": owner,
                "component": P,
                "local_second_remainder": second_local % P,
                "local_third_remainder": third_local % P**2,
                "local_fourth_remainder": fourth_local % P**3,
                "local_fifth_remainder": fifth_local % P**4,
                "composed_second_remainder": second % P,
                "composed_third_remainder": third % P**2,
                "composed_fourth_remainder": composed_fourth % P**3,
                "third_quotient": z,
                "fourth_quotient": w,
                "normalized_numerator": normalized,
                "normalized_remainder": normalized % P,
                "all_named_nonzero": z != 0 and w != 0 and normalized != 0,
            }
        )

    difference = block_product(k, n + d) - 4 * block_product(k, n)
    lower, upper = residual_ratio_interval(k)
    return {
        "k": k,
        "owners": list(owners),
        "components": list(components),
        "pairwise_coprime": all(
            gcd(components[left], components[right]) == 1
            for left, right in combinations(range(3), 2)
        ),
        "g": g,
        "d": d,
        "n": n,
        "residuals": list(residuals),
        "cofactors": list(cofactors),
        "anchor_residual_ratio": [
            Fraction(anchor_residual, d).numerator,
            Fraction(anchor_residual, d).denominator,
        ],
        "coarse_window": all(5 * d < residual < 14 * d for residual in residuals),
        "target_ratio_window": all(
            lower < Fraction(residual, d) < upper for residual in residuals
        ),
        "cyclic": cyclic,
        "all_lifts_through_fifth": all(
            all(
                row[key] == 0
                for key in (
                    "local_second_remainder",
                    "local_third_remainder",
                    "local_fourth_remainder",
                    "local_fifth_remainder",
                    "composed_second_remainder",
                    "composed_third_remainder",
                    "composed_fourth_remainder",
                    "normalized_remainder",
                )
            )
            and row["all_named_nonzero"]
            for row in cyclic
        ),
        "block_equation": difference == 0,
        "block_difference_sign": sign(difference),
        "block_difference_decimal_sha256": hashlib.sha256(
            str(difference).encode()
        ).hexdigest(),
    }


def historical_fixture_replay() -> dict[str, Any]:
    fourth_121 = target_size_congruence_family(20)
    fifth_121 = fifth_hensel_fixture(20)
    fifth_1004 = fifth_hensel_fixture(166)
    if not (
        fourth_121["gap_digits"] == 121
        and fourth_121["all_local_lifts"]
        and fourth_121["all_composed_lifts"]
        and not fourth_121["upper_window"]
        and not fourth_121["block_equation"]
    ):
        raise AssertionError("121-digit fourth fixture failed")
    for expected_digits, fixture in ((121, fifth_121), (1004, fifth_1004)):
        if not (
            fixture["gap_digits"] == expected_digits
            and fixture["local_fifth_remainders"] == [0, 0, 0]
            and fixture["reduced_remainders"] == [0, 0, 0]
            and fixture["normalized_remainders"] == [0, 0, 0]
            and fixture["all_z_nonzero"]
            and fixture["all_w_nonzero"]
            and fixture["all_normalized_nonzero"]
            and not fixture["upper_window"]
            and not fixture["block_equation"]
        ):
            raise AssertionError(("fifth Hensel fixture failed", expected_digits))
    return {
        "fourth_order_121_digit": fourth_121,
        "fifth_order_121_digit": fifth_121,
        "fifth_order_1004_digit": fifth_1004,
        "verdict": (
            "all congruence packages reproduce, but every historical large "
            "fixture fails the target residual window and the block equation"
        ),
    }


@cache
def report() -> dict[str, Any]:
    scan = leading_and_packing_scan()
    return {
        "arithmetic": "exact Python integers and fractions.Fraction",
        "scan": scan,
        "block_equation_polynomial_audit": block_equation_polynomial_audit(),
        "small_short_fifth_fixture": small_short_fifth_fixture(),
        "historical_fixtures": historical_fixture_replay(),
        "proved_bound_schema": {
            "covered_geometries": scan["totals"]["bc_one_sided_total"],
            "statement": (
                "For a one-sided bc-cross geometry with primitive weights mu "
                "and row constant H, the exact eliminant identities imply "
                "sum_s |mu_s| P_s^2 <= H g^4 d."
            ),
            "derivation": (
                "J_s=(PQR)^4 P_s N_s; P_s divides nonzero N_s; the weighted "
                "N_s signs agree; and |sum mu_s J_s|<=H d^5."
            ),
            "exponent_audit": (
                "Weighted AM-GM turns this into a lower bound proportional to "
                "1 <= constant*g^14*d, not an upper bound on d."
            ),
        },
        "verdict": (
            "A new simultaneous one-sided component-square bound holds in 442 "
            "of 1,008 geometries, but it retains one full factor of d.  The "
            "remaining 566 cells are sign-mixed.  Every natural constant-weight "
            "gcd/resultant packing tested has full rank at the degree that would "
            "need to cancel, including after quotienting by every relevant "
            "polynomial multiple of the full exact block equation; the triple "
            "product has divisor degree 14 versus polynomial degree 15.  Fifth "
            "order therefore does not close the exactly-three branch without a "
            "new d-saving or sixth-order coupling."
        ),
    }


def main() -> None:
    print(json.dumps(report(), sort_keys=True))


if __name__ == "__main__":
    main()
