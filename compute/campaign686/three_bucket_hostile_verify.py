#!/usr/bin/env python3
"""Independent hostile verifier for the Erdős 686 three-bucket artifacts.

This verifier deliberately imports nothing from ``three_bucket_attack.py``.
It reconstructs the Taylor coefficients, finite slope scan, signed
elimination grid, global-moment localization, and the target-size CRT
pseudo-witness from the definitions.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from fractions import Fraction
from itertools import combinations, product
from math import gcd, prod
from typing import Any, Iterable, Sequence


ROWS = {5: 14, 7: 17, 9: 23, 11: 26, 13: 29, 15: 35}
TARGET = 10**120


def decimal_sha256(value: int) -> str:
    return hashlib.sha256(str(value).encode("ascii")).hexdigest()


def multiply_by_affine(coefficients: Sequence[int], offset: int) -> list[int]:
    result = [0] * (len(coefficients) + 1)
    for degree, coefficient in enumerate(coefficients):
        result[degree] += offset * coefficient
        result[degree + 1] += coefficient
    return result


def coefficients(k: int, owner: int) -> tuple[int, ...]:
    if owner < 1 or owner > k:
        raise ValueError("owner outside row")
    result = [1]
    for index in range(1, k + 1):
        if index != owner:
            result = multiply_by_affine(result, index - owner)
    return tuple(result)


def obstruction_two(
    k: int,
    owner: int,
    left: int,
    right: int,
    abc: int,
    g: int,
) -> int:
    constant, linear = coefficients(k, owner)[:2]
    delta = (owner - left) * (owner - right)
    return 3 * (constant * abc - 12 * linear * g**2 * delta)


def obstruction_three(
    k: int,
    owner: int,
    left: int,
    right: int,
    abc: int,
    g: int,
    d: int,
) -> int:
    quadratic = coefficients(k, owner)[2]
    delta = (owner - left) * (owner - right)
    return (
        -3 * obstruction_two(k, owner, left, right, abc, g)
        + 180 * quadratic * g**2 * delta * d
    )


def slope(k: int, owner: int, left: int, right: int) -> Fraction:
    constant, linear = coefficients(k, owner)[:2]
    if constant == 0:
        raise AssertionError("local constant unexpectedly vanished")
    return Fraction(
        12 * linear * (owner - left) * (owner - right), constant
    )


def independent_slope_scan() -> dict[str, Any]:
    total_unordered = 0
    total_ordered = 0
    row_reports: list[dict[str, Any]] = []
    for k in ROWS:
        row_count = 0
        minimum: Fraction | None = None
        positive = 0
        for indices in combinations(range(1, k + 1), 3):
            row_count += 1
            values = []
            for owner in indices:
                others = [index for index in indices if index != owner]
                values.append(slope(k, owner, others[0], others[1]))
            if len(set(values)) != 3:
                raise AssertionError((k, indices, values))
            positive += sum(value > 0 for value in values)
            for first, second in combinations(values, 2):
                separation = abs(first - second)
                if separation == 0:
                    raise AssertionError((k, indices, first, second))
                minimum = separation if minimum is None else min(minimum, separation)
        if minimum is None:
            raise AssertionError("empty row scan")
        expected = k * (k - 1) * (k - 2) // 6
        if row_count != expected:
            raise AssertionError((k, row_count, expected))
        ordered = 6 * row_count
        total_unordered += row_count
        total_ordered += ordered
        row_reports.append(
            {
                "k": k,
                "unordered_triples": row_count,
                "ordered_triples": ordered,
                "positive_slope_entries": positive,
                "minimum_separation": [minimum.numerator, minimum.denominator],
            }
        )
    if total_unordered != 1_035:
        raise AssertionError(total_unordered)
    return {
        "total_unordered_triples": total_unordered,
        "total_ordered_triples": total_ordered,
        "rows": row_reports,
    }


def block_product(k: int, n: int) -> int:
    return prod(n + index for index in range(1, k + 1))


def boundary_checks() -> dict[str, Any]:
    telescopes = []
    for k, n in ((9, 2), (15, 4)):
        if block_product(k, n + 1) != 4 * block_product(k, n):
            raise AssertionError((k, n))
        telescopes.append({"k": k, "n": n, "d": 1})

    center_occurrences = 0
    reflected_pair_occurrences = 0
    for k in ROWS:
        center = (k + 1) // 2
        if coefficients(k, center)[1] != 0:
            raise AssertionError("center linear coefficient is nonzero")
        for indices in combinations(range(1, k + 1), 3):
            if center in indices:
                center_occurrences += 1
            if any(
                first + second == k + 1
                for first, second in combinations(indices, 2)
            ):
                reflected_pair_occurrences += 1
    if center_occurrences == 0 or reflected_pair_occurrences == 0:
        raise AssertionError("boundary family omitted")

    # The integer identities do not invert 2, 3, or g.  Exercise both small
    # owner components directly on exact residual triples.
    small_prime_checks = 0
    for p in (2, 3):
        for q, r, a in product((1, 2, 3, 4), (1, 2, 3, 4), range(-40, 41)):
            owner, left, right = 1, 2, 4
            x_owner = a * p**2
            x_left = x_owner - 3 * (owner - left)
            x_right = x_owner - 3 * (owner - right)
            if x_left % q**2 != 0 or x_right % r**2 != 0:
                continue
            b = x_left // q**2
            c = x_right // r**2
            g = 6
            constant, linear, quadratic = coefficients(5, owner)[:3]
            opposite = g * q * r
            local_two = 3 * constant * a - 4 * linear * opposite**2
            local_three = -3 * local_two + 20 * quadratic * p * opposite**3
            abc = a * b * c
            d = g * p * q * r
            composed_two = obstruction_two(5, owner, left, right, abc, g)
            composed_three = obstruction_three(
                5, owner, left, right, abc, g, d
            )
            if (b * c * local_two - composed_two) % p != 0:
                raise AssertionError("small-prime second identity failed")
            if (b * c * local_three - composed_three) % p**2 != 0:
                raise AssertionError("small-prime third identity failed")
            small_prime_checks += 1
    if small_prime_checks == 0:
        raise AssertionError("small-prime grid empty")
    return {
        "d_eq_one_telescopes": telescopes,
        "center_triple_occurrences": center_occurrences,
        "reflected_pair_triple_occurrences": reflected_pair_occurrences,
        "small_prime_owner_fixtures": small_prime_checks,
    }


def below_threshold_short_crt_fixture() -> dict[str, Any]:
    """A short-window fixture showing that the 10^120 cutoff is substantive.

    This tuple satisfies the explicitly quantified progression, window, and
    all cyclic second/third local divisibilities, but it is below the target
    threshold and does not solve the block equation.
    """

    k = 5
    window_constant = ROWS[k]
    loss_budget = 108
    indices = (1, 2, 3)
    components = (2, 7, 5)
    g = 97
    d = g * prod(components)
    residuals = (68_744, 68_747, 68_750)
    cofactors = tuple(
        residual // component**2
        for residual, component in zip(residuals, components, strict=True)
    )
    if cofactors != (17_186, 1_403, 2_750):
        raise AssertionError(cofactors)
    if d != 6_790 or not (1 <= g <= loss_budget) or d >= TARGET:
        raise AssertionError
    if gcd(g, prod(components)) != 1:
        raise AssertionError("fixture even has coprime loss")
    if any(
        gcd(components[first], components[second]) != 1
        for first, second in combinations(range(3), 2)
    ):
        raise AssertionError
    anchor = indices[0]
    if [residual - residuals[0] for residual in residuals] != [
        3 * (index - anchor) for index in indices
    ]:
        raise AssertionError("step-three progression failed")
    if not all(0 < residual < window_constant * d for residual in residuals):
        raise AssertionError("short window failed")

    local_remainders = []
    for position, (index, component, cofactor) in enumerate(
        zip(indices, components, cofactors, strict=True)
    ):
        constant, linear, quadratic = coefficients(k, index)[:3]
        opposite = g * prod(
            components[other] for other in range(3) if other != position
        )
        second = 3 * constant * cofactor - 4 * linear * opposite**2
        third = -3 * second + 20 * quadratic * component * opposite**3
        if second % component != 0 or third % component**2 != 0:
            raise AssertionError("local divisibility failed")
        local_remainders.append([second % component, third % component**2])

    if (residuals[0] + d) % 3 != 0:
        raise AssertionError("no integral n")
    n = (residuals[0] + d) // 3 - anchor
    equation_difference = block_product(k, n + d) - 4 * block_product(k, n)
    if n != 25_177 or equation_difference == 0:
        raise AssertionError
    return {
        "k": k,
        "indices": list(indices),
        "components": list(components),
        "g": g,
        "d": d,
        "n": n,
        "residuals": list(residuals),
        "cofactors": list(cofactors),
        "local_remainders": local_remainders,
        "short_window_holds": True,
        "target_threshold_holds": False,
        "block_equation_holds": False,
        "block_difference": equation_difference,
    }


def signed_elimination_grid() -> dict[str, int]:
    checks = 0
    intermediate_square_checks = 0
    for k in (5, 7):
        for owner, left, right in ((1, 2, 4), (4, 1, 5), (3, 1, 5)):
            constant, linear, quadratic = coefficients(k, owner)[:3]
            delta_left = owner - left
            delta_right = owner - right
            for p, q, r in product((-2, -1, 1, 2), repeat=3):
                for a in range(-20, 21):
                    x_owner = a * p**2
                    x_left = x_owner - 3 * delta_left
                    x_right = x_owner - 3 * delta_right
                    if x_left % q**2 != 0 or x_right % r**2 != 0:
                        continue
                    b = x_left // q**2
                    c = x_right // r**2
                    g = 3
                    opposite = g * q * r
                    local_two = 3 * constant * a - 4 * linear * opposite**2
                    local_three = (
                        -3 * local_two
                        + 20 * quadratic * p * opposite**3
                    )
                    abc = a * b * c
                    d = g * p * q * r
                    composed_two = 3 * (
                        constant * abc
                        - 12 * linear * g**2 * delta_left * delta_right
                    )
                    composed_three = (
                        -3 * composed_two
                        + 180
                        * quadratic
                        * g**2
                        * delta_left
                        * delta_right
                        * d
                    )
                    intermediate = (
                        (b * q**2) * (c * r**2)
                        - 9 * delta_left * delta_right
                    )
                    if intermediate % p**2 != 0:
                        raise AssertionError("intermediate square identity failed")
                    if (b * c * local_two - composed_two) % p != 0:
                        raise AssertionError("second elimination failed")
                    if (b * c * local_three - composed_three) % p**2 != 0:
                        raise AssertionError("third elimination failed")
                    checks += 1
                    intermediate_square_checks += 1
    if checks != 5_216:
        raise AssertionError(checks)
    return {
        "signed_elimination_fixtures": checks,
        "intermediate_square_fixtures": intermediate_square_checks,
    }


def coefficient_one_by_convolution(values: Sequence[int]) -> int:
    polynomial = [1]
    for value in values:
        polynomial = multiply_by_affine(polynomial, value)
    return polynomial[1] if len(polynomial) > 1 else 0


def coefficient_one_by_omission(values: Sequence[int]) -> int:
    return sum(
        prod(values[:index] + values[index + 1 :])
        for index in range(len(values))
    )


def moment_combinations(k: int, n: int, d: int) -> tuple[int, int]:
    lower_values = [n + index - d for index in range(1, k + 1)]
    upper_values = [3 * (n + index) + d for index in range(1, k + 1)]
    lower_coefficient = coefficient_one_by_convolution(lower_values)
    upper_coefficient = coefficient_one_by_convolution(upper_values)
    if lower_coefficient != coefficient_one_by_omission(lower_values):
        raise AssertionError("lower coefficient reproduction failed")
    if upper_coefficient != coefficient_one_by_omission(upper_values):
        raise AssertionError("upper coefficient reproduction failed")
    lower = 3 * prod(lower_values) + 2 * d * lower_coefficient
    upper = 3 * prod(upper_values) - 6 * d * upper_coefficient
    return lower, upper


def global_moment_localization_grid() -> dict[str, int]:
    """Check that both cubic moments reduce to the second local residue.

    If ``d=P*m``, ``n+i=P*x``, and ``3*x-m=a*P``, direct expansion gives

      3*(lowerMoment/P^2) = secondLocal             (mod P),
      upperMoment/P^2 = 3^(k-1)*secondLocal         (mod P).

    The chosen P are coprime to three, so each is equivalent to the same
    second-local divisibility and is not an independent obstruction.
    """

    checks = 0
    for k in ROWS:
        for owner in range(1, k + 1):
            constant, linear = coefficients(k, owner)[:2]
            for p, x, a in product((17, 19, 23), (-5, -1, 1, 4), (-3, -1, 1, 2)):
                if gcd(p, 3) != 1:
                    raise AssertionError
                m = 3 * x - a * p
                d = p * m
                n = p * x - owner
                if 3 * (n + owner) - d != a * p**2:
                    raise AssertionError("residual identity failed")
                lower, upper = moment_combinations(k, n, d)
                if lower % p**2 != 0 or upper % p**2 != 0:
                    raise AssertionError("moment lacks forced square factor")
                second = 3 * constant * a - 4 * linear * m**2
                if (3 * (lower // p**2) - second) % p != 0:
                    raise AssertionError("lower moment localization failed")
                if (upper // p**2 - 3 ** (k - 1) * second) % p != 0:
                    raise AssertionError("upper moment localization failed")
                checks += 1
    if checks != 2_880:
        raise AssertionError(checks)
    return {"signed_global_moment_localizations": checks}


def crt_iterative(residues: Sequence[int], moduli: Sequence[int]) -> tuple[int, int]:
    if not residues or len(residues) != len(moduli):
        raise ValueError("bad CRT input")
    value = 0
    modulus = 1
    for residue, next_modulus in zip(residues, moduli, strict=True):
        if gcd(modulus, next_modulus) != 1:
            raise ValueError("noncoprime CRT moduli")
        correction = (
            (residue - value) * pow(modulus, -1, next_modulus)
        ) % next_modulus
        value += modulus * correction
        modulus *= next_modulus
        value %= modulus
    return value, modulus


def independent_crt_witness(exponent: int = 20) -> dict[str, Any]:
    if exponent < 1:
        raise ValueError("positive exponent required")
    k = 5
    indices = (1, 2, 4)
    components = (101**exponent, 103**exponent, 107**exponent)
    anchor = indices[0]
    squares = tuple(component**2 for component in components)
    residues = tuple(
        (-3 * (index - anchor)) % square
        for index, square in zip(indices, squares, strict=True)
    )
    base_x, square_product = crt_iterative(residues, squares)
    d = prod(components)
    if square_product != d**2:
        raise AssertionError

    parameter_residues: list[int] = []
    for index, component in zip(indices, components, strict=True):
        shifted = base_x + 3 * (index - anchor)
        if shifted % component**2 != 0:
            raise AssertionError("base square CRT failed")
        a0 = shifted // component**2
        parameter_coefficient = d**2 // component**2
        constant, linear, quadratic = coefficients(k, index)[:3]
        opposite = d // component
        local_three_constant = (
            -3 * (3 * constant * a0 - 4 * linear * opposite**2)
            + 20 * quadratic * component * opposite**3
        )
        local_three_linear = -9 * constant * parameter_coefficient
        modulus = component**2
        if gcd(local_three_linear, modulus) != 1:
            raise AssertionError("local coefficient is not invertible")
        parameter_residues.append(
            (-local_three_constant * pow(local_three_linear, -1, modulus))
            % modulus
        )

    parameter, parameter_modulus = crt_iterative(parameter_residues, squares)
    if parameter_modulus != d**2:
        raise AssertionError
    valid_integral_lifts: list[int] = []
    for lift in range(3):
        candidate = parameter + lift * d**2
        candidate_x = base_x + d**2 * candidate
        if (candidate_x + d) % 3 == 0:
            valid_integral_lifts.append(lift)
    if len(valid_integral_lifts) != 1:
        raise AssertionError(valid_integral_lifts)
    lift = valid_integral_lifts[0]
    parameter_lifted = parameter + lift * d**2
    x_anchor = base_x + d**2 * parameter_lifted
    n = (x_anchor + d) // 3 - anchor
    if n < 0:
        raise AssertionError

    local_checks: list[dict[str, Any]] = []
    selected_residuals: list[int] = []
    lower_moment, upper_moment = moment_combinations(k, n, d)
    for index, component in zip(indices, components, strict=True):
        residual = 3 * (n + index) - d
        if residual <= 0 or residual % component**2 != 0:
            raise AssertionError("selected square residual failed")
        a = residual // component**2
        constant, linear, quadratic = coefficients(k, index)[:3]
        opposite = d // component
        second = 3 * constant * a - 4 * linear * opposite**2
        third = -3 * second + 20 * quadratic * component * opposite**3
        if (n + index) % component != 0:
            raise AssertionError("localized lower factor failed")
        if second % component != 0 or third % component**2 != 0:
            raise AssertionError("local congruence failed")
        if lower_moment % component**2 != 0 or upper_moment % component**2 != 0:
            raise AssertionError("moment square factor failed")
        if (3 * (lower_moment // component**2) - second) % component != 0:
            raise AssertionError("witness lower localization mismatch")
        if (
            upper_moment // component**2 - 3 ** (k - 1) * second
        ) % component != 0:
            raise AssertionError("witness upper localization mismatch")
        selected_residuals.append(residual)
        local_checks.append(
            {
                "index": index,
                "component_digits": len(str(component)),
                "cofactor_digits": len(str(a)),
                "second_remainder": second % component,
                "third_remainder": third % component**2,
                "lower_factor_remainder": (n + index) % component,
            }
        )

    progression_differences = [
        selected_residuals[index] - selected_residuals[0]
        for index in range(3)
    ]
    expected_differences = [3 * (index - anchor) for index in indices]
    if progression_differences != expected_differences:
        raise AssertionError((progression_differences, expected_differences))

    if lower_moment % d**3 != 0 or upper_moment % d**3 != 0:
        raise AssertionError("global cubic moment failed")
    all_residuals = [3 * (n + index) - d for index in range(1, k + 1)]
    if prod(all_residuals) % d**2 != 0:
        raise AssertionError("global square congruence failed")

    left_block = prod(n + d + index for index in range(1, k + 1))
    right_block = 4 * prod(n + index for index in range(1, k + 1))
    equation_difference = left_block - right_block
    if equation_difference == 0:
        raise AssertionError("pseudo-witness unexpectedly solves equation")
    residual_max = max(selected_residuals)
    window_excess = residual_max - ROWS[k] * d
    if window_excess < 0:
        raise AssertionError("pseudo-witness unexpectedly meets short window")

    return {
        "parameters": {
            "k": k,
            "indices": list(indices),
            "components": [
                f"101^{exponent}",
                f"103^{exponent}",
                f"107^{exponent}",
            ],
            "integrality_lift": lift,
        },
        "gap": {
            "digits": len(str(d)),
            "at_least_10_pow_120": d >= TARGET,
            "decimal_sha256": decimal_sha256(d),
        },
        "n": {
            "digits": len(str(n)),
            "decimal_sha256": decimal_sha256(n),
        },
        "local_checks": local_checks,
        "progression_differences": progression_differences,
        "global_square_remainder": prod(all_residuals) % d**2,
        "lower_global_moment_remainder": lower_moment % d**3,
        "upper_global_moment_remainder": upper_moment % d**3,
        "lower_global_moment_quotient_sha256": decimal_sha256(lower_moment // d**3),
        "upper_global_moment_quotient_sha256": decimal_sha256(upper_moment // d**3),
        "block_equation": {
            "holds": False,
            "difference_sign": 1 if equation_difference > 0 else -1,
            "difference_digits": len(str(abs(equation_difference))),
            "difference_decimal_sha256": decimal_sha256(equation_difference),
        },
        "short_window": {
            "holds": False,
            "excess_digits": len(str(window_excess)),
            "excess_decimal_sha256": decimal_sha256(window_excess),
            "residual_to_gap_floor": residual_max // d,
        },
    }


def crt_family_prefix_scan() -> dict[str, Any]:
    """Exercise a prefix of the parameterized, unbounded CRT family."""

    gaps: list[int] = []
    for exponent in range(1, 25):
        result = independent_crt_witness(exponent)
        d = (101 * 103 * 107) ** exponent
        if result["gap"]["decimal_sha256"] != decimal_sha256(d):
            raise AssertionError("family gap mismatch")
        if result["global_square_remainder"] != 0:
            raise AssertionError
        if result["lower_global_moment_remainder"] != 0:
            raise AssertionError
        if result["upper_global_moment_remainder"] != 0:
            raise AssertionError
        if any(
            check["second_remainder"] != 0
            or check["third_remainder"] != 0
            or check["lower_factor_remainder"] != 0
            for check in result["local_checks"]
        ):
            raise AssertionError
        gaps.append(d)
    if any(left >= right for left, right in zip(gaps, gaps[1:])):
        raise AssertionError("family gaps do not increase")
    return {
        "exponents_checked": [1, 24],
        "fixtures": len(gaps),
        "gap_formula": "(101*103*107)^t",
        "first_gap_digits": len(str(gaps[0])),
        "last_gap_digits": len(str(gaps[-1])),
    }


def report() -> dict[str, Any]:
    return {
        "boundaries": boundary_checks(),
        "below_threshold_short_crt_fixture": below_threshold_short_crt_fixture(),
        "slope_scan": independent_slope_scan(),
        "signed_grid": signed_elimination_grid(),
        "global_moment_localization": global_moment_localization_grid(),
        "crt_pseudo_witness": independent_crt_witness(),
        "crt_family_prefix": crt_family_prefix_scan(),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args()
    print(json.dumps(report(), indent=2 if args.pretty else None, sort_keys=True))


if __name__ == "__main__":
    main()
