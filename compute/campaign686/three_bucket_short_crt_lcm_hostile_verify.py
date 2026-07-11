#!/usr/bin/env python3
"""Independent hostile verifier for the three-bucket short-CRT LCM filter.

This implementation imports no producer or prior audit module.  Taylor
coefficients are reconstructed through elementary reciprocal sums rather
than polynomial multiplication.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from functools import cache
from itertools import combinations
from math import gcd, prod
from typing import Any, Iterable, Sequence


TARGET = 10**120
ROWS = {
    5: (14, 108),
    7: (17, 1_620),
    9: (23, 136_080),
    11: (26, 1_224_720),
    13: (29, 242_494_560),
    15: (35, 18_914_575_680),
}


def gcd_lcm(*values: int) -> int:
    result = 1
    for value in values:
        if value <= 0:
            raise ValueError
        result = result // gcd(result, value) * value
    return result


@cache
def coefficients(k: int, owner: int) -> tuple[int, int, int]:
    offsets = [column - owner for column in range(1, k + 1) if column != owner]
    constant = prod(offsets)
    linear_q = constant * sum((Fraction(1, offset) for offset in offsets), Fraction())
    quadratic_q = constant * sum(
        (
            Fraction(1, offsets[first] * offsets[second])
            for first, second in combinations(range(len(offsets)), 2)
        ),
        Fraction(),
    )
    if linear_q.denominator != 1 or quadratic_q.denominator != 1:
        raise AssertionError("integer Taylor coefficient lost")
    return constant, linear_q.numerator, quadratic_q.numerator


def triples(k: int) -> Iterable[tuple[int, int, int]]:
    return combinations(range(1, k + 1), 3)


def delta(owner: int, indices: Sequence[int]) -> int:
    others = [index for index in indices if index != owner]
    if len(others) != 2:
        raise ValueError
    return (owner - others[0]) * (owner - others[1])


def slope(k: int, owner: int, indices: Sequence[int]) -> Fraction:
    constant, linear, _ = coefficients(k, owner)
    return Fraction(12 * linear * delta(owner, indices), constant)


def zero_record(k: int, indices: tuple[int, int, int], zero_owner: int) -> dict[str, Any]:
    slopes = {owner: slope(k, owner, indices) for owner in indices}
    zero_slope = slopes[zero_owner]
    if zero_slope <= 0:
        raise ValueError
    zero_constant, zero_linear, zero_quadratic = coefficients(k, zero_owner)
    zero_delta = delta(zero_owner, indices)
    numerators: list[int] = []
    denominators: list[int] = []
    raw_crosses: list[int] = []
    for owner in indices:
        if owner == zero_owner:
            continue
        constant, linear, _ = coefficients(k, owner)
        owner_delta = delta(owner, indices)
        rational_coefficient = 3 * constant * (zero_slope - slopes[owner])
        numerator = abs(rational_coefficient.numerator)
        denominator = rational_coefficient.denominator
        raw_cross = abs(
            36
            * (
                constant * zero_linear * zero_delta
                - linear * owner_delta * zero_constant
            )
        )
        if numerator == 0 or raw_cross == 0 or raw_cross % numerator != 0:
            raise AssertionError("cross determinant reduction failed")
        # D*O=N*g^2 after substituting t=zero_slope*g^2.
        left_factor = denominator * 3 * (
            constant * zero_slope - 12 * linear * owner_delta
        )
        if left_factor != rational_coefficient.numerator:
            raise AssertionError("denominator-cleared identity failed")
        numerators.append(numerator)
        denominators.append(denominator)
        raw_crosses.append(raw_cross)
    third = abs(180 * zero_quadratic * zero_delta)
    if third == 0:
        raise AssertionError("zero-owner third coefficient vanished")
    common = gcd_lcm(numerators[0], numerators[1], third)
    return {
        "indices": list(indices),
        "zero_owner": zero_owner,
        "zero_slope": [zero_slope.numerator, zero_slope.denominator],
        "numerators": numerators,
        "denominators": denominators,
        "raw_crosses": raw_crosses,
        "third": third,
        "lcm": common,
    }


def obstruction_majorant(k: int, indices: Sequence[int], abc: int, G: int) -> int:
    result = G
    for owner in indices:
        constant, linear, _ = coefficients(k, owner)
        result *= (
            3 * abs(constant) * abc
            + 36 * abs(linear) * G**2 * abs(delta(owner, indices))
        )
    return result


def maximum_majorant(k: int, abc: int, G: int) -> tuple[int, tuple[int, int, int]]:
    records = [
        (obstruction_majorant(k, indices, abc, G), indices)
        for indices in triples(k)
    ]
    return max(records, key=lambda record: record[0])


def abc_threshold(k: int, G: int) -> tuple[int, int, int, tuple[int, int, int]]:
    low, high = 0, TARGET
    while low + 1 < high:
        middle = (low + high) // 2
        if maximum_majorant(k, middle, G)[0] < TARGET:
            low = middle
        else:
            high = middle
    before = maximum_majorant(k, high - 1, G)[0]
    at, indices = maximum_majorant(k, high, G)
    if not before < TARGET <= at:
        raise AssertionError
    return high, before, at, indices


@cache
def row_certificate(k: int) -> dict[str, Any]:
    A, G = ROWS[k]
    positive: list[dict[str, Any]] = []
    nonpositive = 0
    center_occurrences = 0
    reflected_occurrences = 0
    for indices in triples(k):
        center = (k + 1) // 2
        if center in indices:
            center_occurrences += 1
        if any(first + second == k + 1 for first, second in combinations(indices, 2)):
            reflected_occurrences += 1
        for owner in indices:
            if slope(k, owner, indices) > 0:
                positive.append(zero_record(k, indices, owner))
            else:
                nonpositive += 1
    maximum = max(positive, key=lambda record: record["lcm"])
    threshold, before, at, threshold_indices = abc_threshold(k, G)
    zero_bound = maximum["lcm"] * G**4
    if zero_bound >= TARGET:
        raise AssertionError
    return {
        "k": k,
        "A": A,
        "G": G,
        "triples": sum(1 for _ in triples(k)),
        "positive_zero_cases": len(positive),
        "nonpositive_zero_cases": nonpositive,
        "center_triples": center_occurrences,
        "reflected_pair_triples": reflected_occurrences,
        "nonintegral_denominator_cases": sum(
            1 for record in positive if any(d > 1 for d in record["denominators"])
        ),
        "maximum_denominator": max(
            denominator
            for record in positive
            for denominator in record["denominators"]
        ),
        "maximum_lcm": maximum["lcm"],
        "maximum_lcm_case": maximum,
        "zero_bound": zero_bound,
        "abc_threshold": threshold,
        "abc_before": before,
        "abc_at": at,
        "abc_threshold_indices": list(threshold_indices),
        "equation_context_minimum_abc": 125 * TARGET + 1,
        "equation_context_to_new_threshold_floor": (125 * TARGET + 1) // threshold,
    }


def coarse_bound_audit() -> dict[str, int]:
    all_coefficients = [
        coefficients(k, owner)
        for k in ROWS
        for owner in range(1, k + 1)
    ]
    cmax = max(abs(record[0]) for record in all_coefficients)
    dmax = max(abs(record[1]) for record in all_coefficients)
    emax = max(abs(record[2]) for record in all_coefficients)
    delta_max = 14**2
    second = 72 * cmax * dmax * delta_max
    third = 180 * emax * delta_max
    G = max(data[1] for data in ROWS.values())
    product_bound = second**2 * third * G**4
    if (cmax, dmax, emax) != (
        87_178_291_200,
        283_465_647_360,
        392_156_797_824,
    ):
        raise AssertionError((cmax, dmax, emax))
    if product_bound >= TARGET:
        raise AssertionError
    return {
        "Cmax": cmax,
        "Dmax": dmax,
        "Emax": emax,
        "second_numerator_bound": second,
        "third_coefficient_bound": third,
        "coarse_product_bound": product_bound,
        "coarse_cutoff_margin": TARGET - product_bound,
    }


def crt(residues: Sequence[int], moduli: Sequence[int]) -> tuple[int, int]:
    value, modulus = 0, 1
    for residue, next_modulus in zip(residues, moduli, strict=True):
        if gcd(modulus, next_modulus) != 1:
            raise ValueError
        correction = (
            (residue - value) * pow(modulus, -1, next_modulus)
        ) % next_modulus
        value = (value + modulus * correction) % (modulus * next_modulus)
        modulus *= next_modulus
    return value, modulus


def local_second(k: int, owner: int, cofactor: int, opposite: int) -> int:
    constant, linear, _ = coefficients(k, owner)
    return 3 * constant * cofactor - 4 * linear * opposite**2


def local_third(
    k: int, owner: int, component: int, cofactor: int, opposite: int
) -> int:
    _, _, quadratic = coefficients(k, owner)
    return (
        -3 * local_second(k, owner, cofactor, opposite)
        + 20 * quadratic * component * opposite**3
    )


def composed_obstructions(
    k: int,
    indices: Sequence[int],
    owner: int,
    abc: int,
    g: int,
    d: int,
) -> tuple[int, int]:
    constant, linear, quadratic = coefficients(k, owner)
    owner_delta = delta(owner, indices)
    second = 3 * (
        constant * abc - 12 * linear * g**2 * owner_delta
    )
    third = -3 * second + 180 * quadratic * g**2 * owner_delta * d
    return second, third


def crt_pseudo_witness() -> dict[str, Any]:
    k = 5
    indices = (1, 2, 4)
    components = (101**20, 103**20, 107**20)
    squares = tuple(component**2 for component in components)
    anchor = indices[0]
    base, modulus = crt(
        tuple(
            (-3 * (index - anchor)) % square
            for index, square in zip(indices, squares, strict=True)
        ),
        squares,
    )
    d = prod(components)
    if modulus != d**2:
        raise AssertionError
    parameter_residues = []
    for index, component in zip(indices, components, strict=True):
        base_cofactor = (base + 3 * (index - anchor)) // component**2
        coefficient = d**2 // component**2
        constant, linear, quadratic = coefficients(k, index)
        opposite = d // component
        third_constant = (
            -3 * (3 * constant * base_cofactor - 4 * linear * opposite**2)
            + 20 * quadratic * component * opposite**3
        )
        third_linear = -9 * constant * coefficient
        parameter_residues.append(
            (-third_constant * pow(third_linear, -1, component**2))
            % component**2
        )
    parameter, parameter_modulus = crt(parameter_residues, squares)
    if parameter_modulus != d**2:
        raise AssertionError
    candidates = []
    for lift in range(3):
        candidate = parameter + lift * d**2
        x = base + d**2 * candidate
        if (x + d) % 3 == 0:
            candidates.append((lift, x))
    if len(candidates) != 1:
        raise AssertionError(candidates)
    lift, x_anchor = candidates[0]
    n = (x_anchor + d) // 3 - anchor
    cofactors = []
    local_ok = True
    composed_ok = True
    nonzero = True
    residuals = []
    for position, (index, component) in enumerate(zip(indices, components, strict=True)):
        residual = 3 * (n + index) - d
        cofactor = residual // component**2
        opposite = d // component
        local_ok &= local_second(k, index, cofactor, opposite) % component == 0
        local_ok &= local_third(k, index, component, cofactor, opposite) % component**2 == 0
        cofactors.append(cofactor)
        residuals.append(residual)
    abc = prod(cofactors)
    for position, (index, component) in enumerate(zip(indices, components, strict=True)):
        second, third = composed_obstructions(k, indices, index, abc, 1, d)
        composed_ok &= second % component == 0 and third % component**2 == 0
        nonzero &= second != 0
    window = max(residuals) < ROWS[k][0] * d
    equation = block_product(k, n + d) == 4 * block_product(k, n)
    return {
        "gap_digits": len(str(d)),
        "gap_at_least_target": d >= TARGET,
        "integrality_lift": lift,
        "local_divisibilities": local_ok,
        "composed_divisibilities": composed_ok,
        "all_second_obstructions_nonzero": nonzero,
        "abc_above_new_threshold": abc >= row_certificate(5)["abc_threshold"],
        "short_window": window,
        "equation": equation,
    }


def block_product(k: int, n: int) -> int:
    return prod(n + index for index in range(1, k + 1))


def below_threshold_fixture() -> dict[str, Any]:
    k = 5
    indices = (1, 2, 3)
    components = (2, 7, 5)
    g, d, n = 97, 6_790, 25_177
    residuals = (68_744, 68_747, 68_750)
    if residuals != tuple(3 * (n + index) - d for index in indices):
        raise AssertionError("fixture progression drifted")
    if any(
        residual % component**2
        for residual, component in zip(residuals, components, strict=True)
    ):
        raise AssertionError("fixture square divisibility drifted")
    cofactors = tuple(
        residual // component**2
        for residual, component in zip(residuals, components, strict=True)
    )
    abc = prod(cofactors)
    local_ok = True
    composed_ok = True
    for position, (index, component, cofactor) in enumerate(
        zip(indices, components, cofactors, strict=True)
    ):
        opposite = g * prod(
            components[other] for other in range(3) if other != position
        )
        local_ok &= local_second(k, index, cofactor, opposite) % component == 0
        local_ok &= local_third(k, index, component, cofactor, opposite) % component**2 == 0
        second, third = composed_obstructions(k, indices, index, abc, g, d)
        composed_ok &= second % component == 0 and third % component**2 == 0
    return {
        "d": d,
        "abc": abc,
        "below_target": d < TARGET,
        "below_new_abc_threshold": abc < row_certificate(5)["abc_threshold"],
        "short_window": max(residuals) < ROWS[k][0] * d,
        "local_divisibilities": local_ok,
        "composed_divisibilities": composed_ok,
        "equation": block_product(k, n + d) == 4 * block_product(k, n),
    }


def generic_packing_boundaries() -> dict[str, Any]:
    fixtures = []
    for P, Q, R, g in ((2, 3, 5, 30), (1, 2, 3, 6), (1, 1, 1, 7)):
        d = g * P * Q * R
        A, B, K = max(P, 1), max(Q, 1), max(R, 1)
        L = gcd_lcm(A, B, K)
        premises = (
            gcd(P, Q) == gcd(P, R) == gcd(Q, R) == 1
            and (A * g**2) % P == 0
            and (B * g**2) % Q == 0
            and (K * g**2 * d) % (R**2) == 0
        )
        conclusion = (L * g**4) % d == 0
        if not premises or not conclusion:
            raise AssertionError((P, Q, R, g))
        fixtures.append(
            {
                "components": [P, Q, R],
                "g": g,
                "g_shares_component_prime": any(
                    gcd(g, component) > 1 for component in (P, Q, R) if component > 1
                ),
                "unit_component": 1 in (P, Q, R),
            }
        )
    # The fourth power cannot be replaced by a cube under the generic
    # hypotheses: all three components are nonunits and pairwise coprime.
    P, Q, R, g, A, B, K, L = 2, 5, 27, 3, 2, 5, 1, 10
    d = g * P * Q * R
    if not (
        gcd(P, Q) == gcd(P, R) == gcd(Q, R) == 1
        and (A * g**2) % P == 0
        and (B * g**2) % Q == 0
        and (K * g**2 * d) % R**2 == 0
        and (L * g**4) % d == 0
        and (L * g**3) % d != 0
    ):
        raise AssertionError("g^4 sharpness fixture failed")
    return {
        "fixtures": fixtures,
        "g_fourth_power_confirmed": True,
        "g_fourth_power_sharp_fixture": {
            "P": P,
            "Q": Q,
            "R": R,
            "g": g,
            "A": A,
            "B": B,
            "K": K,
            "L": L,
            "d": d,
            "d_divides_Lg4": True,
            "d_divides_Lg3": False,
        },
    }


def boundary_report() -> dict[str, Any]:
    telescopes = []
    for point in ((9, 2, 1), (15, 4, 1)):
        k, n, d = point
        if block_product(k, n + d) != 4 * block_product(k, n):
            raise AssertionError(point)
        telescopes.append(list(point))
    return {
        "packing": generic_packing_boundaries(),
        "d_eq_one_telescopes": telescopes,
        "below_threshold_fixture": below_threshold_fixture(),
        "crt_pseudo_witness": crt_pseudo_witness(),
    }


def report() -> dict[str, Any]:
    rows = [row_certificate(k) for k in ROWS]
    return {
        "rows": rows,
        "total_positive_zero_cases": sum(row["positive_zero_cases"] for row in rows),
        "total_nonpositive_zero_cases": sum(
            row["nonpositive_zero_cases"] for row in rows
        ),
        "coarse": coarse_bound_audit(),
        "boundaries": boundary_report(),
        "claim_boundary": {
            "new_information": "all three composed second obstructions are nonzero",
            "abc_thresholds_redundant_for_equation_solutions": True,
            "remaining_gap_requires": [
                "d>=10^120 and 1<=g<=G_k",
                "pairwise-coprime P,Q,R>1 and d=gPQR",
                "positive cofactors and exact step-three progression",
                "all three residual windows",
                "all O_s nonzero and H_s divides O_s",
                "all H_s^2 divides F_s",
                "abc>=T_k (but actual equations already imply abc>125*g^2*d)",
            ],
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args()
    print(json.dumps(report(), indent=2 if args.pretty else None, sort_keys=True))


if __name__ == "__main__":
    main()
