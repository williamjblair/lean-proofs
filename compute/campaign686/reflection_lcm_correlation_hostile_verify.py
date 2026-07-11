#!/usr/bin/env python3
"""Independent verifier for the Erdős 686 reflection-owner correlation.

This file imports none of the producer diagnostics.  It reconstructs all
valuations, owner choices, fixture predicates, and lcms with exact integers.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from math import factorial, gcd, isqrt, prod
from typing import Any


DEEP_17 = (984, 3_177_026, 4_480)
DEEP_16 = (244, 48_502, 277)
SMOOTH_REFLECTION_984 = (984, 3_177_027, 4_480)
EVEN_SYNTHETIC = (16, 582_087, 52_684)
ODD_SYNTHETIC = (17, 996_082, 84_632)


def factor(value: int) -> list[tuple[int, int]]:
    if value <= 0:
        raise ValueError
    result: list[tuple[int, int]] = []
    exponent = 0
    while value % 2 == 0:
        value //= 2
        exponent += 1
    if exponent:
        result.append((2, exponent))
    prime = 3
    while prime <= isqrt(value):
        exponent = 0
        while value % prime == 0:
            value //= prime
            exponent += 1
        if exponent:
            result.append((prime, exponent))
        prime += 2
    if value > 1:
        result.append((value, 1))
    return result


def valuation(value: int, prime: int) -> int:
    if value <= 0 or prime < 2:
        raise ValueError
    exponent = 0
    while value % prime == 0:
        value //= prime
        exponent += 1
    return exponent


def factorial_valuation(bound: int, prime: int) -> int:
    total = 0
    while bound:
        bound //= prime
        total += bound
    return total


def lcm(values: list[int]) -> int:
    result = 1
    for value in values:
        if value <= 0:
            raise ValueError
        result = result // gcd(result, value) * value
    return result


def coefficient(k: int) -> int:
    return 3 if k % 2 == 0 else 5


def center(k: int, n: int, d: int) -> int:
    return 2 * n + d + k + 1


def terms(k: int, start: int) -> list[int]:
    return [start + index for index in range(1, k + 1)]


def block(k: int, start: int) -> int:
    return prod(terms(k, start))


def exact_equation(k: int, n: int, d: int) -> bool:
    return block(k, n + d) == 4 * block(k, n)


def row_passes(k: int, n: int, d: int, row: int) -> bool:
    modulus = n + row
    residue = 1 % modulus
    for value in range(d + 1 - row, d + k - row + 1):
        residue = residue * (value % modulus) % modulus
    return residue == 0


def reflection_values(k: int, d: int) -> list[int]:
    if k < 1 or d < k:
        raise ValueError
    values = [d + k + 1 - 2 * index for index in range(1, k + 1)]
    if min(values) <= 0:
        raise AssertionError
    return values


def reflection_lcm(k: int, d: int) -> int:
    return lcm(reflection_values(k, d))


def reflection_product(k: int, d: int) -> int:
    return prod(reflection_values(k, d))


def small_lcm(k: int) -> int:
    if k < 2:
        raise ValueError
    return lcm(list(range(1, k)))


def first_max_owner(k: int, start: int, prime: int) -> tuple[int, int]:
    exponents = [valuation(value, prime) for value in terms(k, start)]
    maximum = max(exponents)
    return exponents.index(maximum) + 1, maximum


@dataclass(frozen=True)
class OwnerRow:
    prime: int
    center_exponent: int
    coefficient_exponent: int
    loss_exponent: int
    residual_exponent: int
    residual_power: int
    lower_block_exponent: int
    upper_block_exponent: int
    lower_owner: int
    upper_owner: int
    lower_owner_exponent: int
    upper_owner_exponent: int
    reflection_difference: int
    centered_difference: int
    signed_offset: int

    @property
    def reflected(self) -> bool:
        return self.signed_offset == 0


def owner_rows(k: int, n: int, d: int) -> list[OwnerRow]:
    s = center(k, n, d)
    c = coefficient(k)
    rows = []
    for prime, center_exponent in factor(s):
        loss = factorial_valuation(k - 1, prime)
        residual_exponent = max(
            center_exponent - valuation(c, prime) - loss, 0
        )
        lower_owner, lower_owner_exponent = first_max_owner(k, n, prime)
        upper_owner, upper_owner_exponent = first_max_owner(k, n + d, prime)
        rows.append(
            OwnerRow(
                prime=prime,
                center_exponent=center_exponent,
                coefficient_exponent=valuation(c, prime),
                loss_exponent=loss,
                residual_exponent=residual_exponent,
                residual_power=prime**residual_exponent,
                lower_block_exponent=sum(
                    valuation(value, prime) for value in terms(k, n)
                ),
                upper_block_exponent=sum(
                    valuation(value, prime) for value in terms(k, n + d)
                ),
                lower_owner=lower_owner,
                upper_owner=upper_owner,
                lower_owner_exponent=lower_owner_exponent,
                upper_owner_exponent=upper_owner_exponent,
                reflection_difference=d + k + 1 - 2 * lower_owner,
                centered_difference=d + upper_owner - lower_owner,
                signed_offset=lower_owner + upper_owner - (k + 1),
            )
        )
    return rows


def concentration_grid() -> dict[str, int]:
    checks = 0
    for k in range(2, 21):
        for start in range(0, 101):
            for prime in (2, 3, 5, 7, 11, 13, 17, 19, 23):
                owner, owner_exponent = first_max_owner(k, start, prime)
                block_exponent = sum(
                    valuation(value, prime) for value in terms(k, start)
                )
                loss = factorial_valuation(k - 1, prime)
                if block_exponent > owner_exponent + loss:
                    raise AssertionError((k, start, prime, owner))
                checks += 1
    return {"maximum_owner_concentration_checks": checks}


def conditional_composition_scan() -> dict[str, int]:
    """Check the theorem from exactly its two equation-supplied consequences."""

    premise_points = 0
    prime_rows = 0
    nonzero_rows = 0
    nonreflected_rows = 0
    for k in range(2, 13):
        for n in range(0, 101):
            lower = block(k, n)
            for d in range(k, k + 31):
                upper = block(k, n + d)
                s = center(k, n, d)
                c = coefficient(k)
                if (c * lower) % s != 0 or upper % lower != 0:
                    continue
                premise_points += 1
                for row in owner_rows(k, n, d):
                    prime_rows += 1
                    q = row.residual_power
                    if row.center_exponent < row.residual_exponent:
                        raise AssertionError
                    if row.lower_block_exponent > (
                        row.lower_owner_exponent + row.loss_exponent
                    ):
                        raise AssertionError("lower concentration failed")
                    if row.upper_block_exponent > (
                        row.upper_owner_exponent + row.loss_exponent
                    ):
                        raise AssertionError("upper concentration failed")
                    if row.lower_block_exponent > row.upper_block_exponent:
                        raise AssertionError("block divisibility valuation failed")
                    if row.lower_owner_exponent < row.residual_exponent:
                        raise AssertionError("lower landing failed")
                    if row.upper_owner_exponent < row.residual_exponent:
                        raise AssertionError("upper landing failed")
                    if row.reflection_difference % q != 0:
                        raise AssertionError("reflection landing failed")
                    if row.centered_difference % q != 0:
                        raise AssertionError("centered landing failed")
                    offset = abs(row.signed_offset)
                    if offset % q != 0:
                        raise AssertionError("offset landing failed")
                    if row.residual_exponent:
                        nonzero_rows += 1
                    if row.residual_exponent and not row.reflected:
                        nonreflected_rows += 1
                        if not 1 <= offset <= k - 1:
                            raise AssertionError("offset outside lcm interval")
                        if small_lcm(k) % q != 0:
                            raise AssertionError("small lcm absorption failed")
    if premise_points != 499:
        raise AssertionError(premise_points)
    return {
        "premise_points": premise_points,
        "prime_rows": prime_rows,
        "nonzero_residual_rows": nonzero_rows,
        "nonreflected_nonzero_rows": nonreflected_rows,
    }


def named_fixture_report() -> dict[str, Any]:
    deep17 = {
        "rows_1_through_16": all(
            row_passes(*DEEP_17, row) for row in range(1, 17)
        ),
        "row_17": row_passes(*DEEP_17, 17),
        "equation": exact_equation(*DEEP_17),
        "center": center(*DEEP_17),
    }
    deep16 = {
        "rows_1_through_15": all(
            row_passes(*DEEP_16, row) for row in range(1, 16)
        ),
        "row_16": row_passes(*DEEP_16, 16),
        "equation": exact_equation(*DEEP_16),
        "center": center(*DEEP_16),
    }
    aligned = []
    for point in (SMOOTH_REFLECTION_984, EVEN_SYNTHETIC, ODD_SYNTHETIC):
        rows = [row for row in owner_rows(*point) if row.residual_exponent]
        for row in rows:
            q = row.residual_power
            if not row.reflected:
                raise AssertionError((point, row))
            if row.reflection_difference % q or row.centered_difference % q:
                raise AssertionError((point, row))
        aligned.append(
            {
                "point": list(point),
                "equation": exact_equation(*point),
                "rows": [
                    [row.prime, row.lower_owner, row.upper_owner]
                    for row in rows
                ],
            }
        )
    telescopes = []
    for point in ((9, 2, 1), (15, 4, 1)):
        if not exact_equation(*point):
            raise AssertionError(point)
        rows = owner_rows(*point)
        if any(row.residual_exponent for row in rows):
            raise AssertionError(point)
        telescopes.append({"point": list(point), "residual_rows": 0})
    return {
        "deep17": deep17,
        "deep16": deep16,
        "aligned": aligned,
        "d_eq_one_telescopes": telescopes,
    }


def compression_flags(point: tuple[int, int, int]) -> dict[str, bool]:
    k, n, d = point
    s = center(k, n, d)
    c = coefficient(k)
    lower = block(k, n)
    product_rhs = c * reflection_product(k, d)
    lcm_rhs = c * factorial(k - 1) * reflection_lcm(k, d)
    return {
        "equation": exact_equation(k, n, d),
        "reflection_congruence": (c * lower) % s == 0,
        "product_compression": product_rhs % s == 0,
        "lcm_compression": lcm_rhs % s == 0,
        "lcm_rhs_lt_product_rhs": lcm_rhs < product_rhs,
        "lcm_rhs_divides_product_rhs": product_rhs % lcm_rhs == 0,
        "product_rhs_divides_lcm_rhs": lcm_rhs % product_rhs == 0,
    }


def structural_report() -> dict[str, Any]:
    points = (DEEP_16, SMOOTH_REFLECTION_984, EVEN_SYNTHETIC, ODD_SYNTHETIC)
    flags = {str(point): compression_flags(point) for point in points}
    directions = [entry["lcm_rhs_lt_product_rhs"] for entry in flags.values()]
    if not any(directions) or all(directions):
        raise AssertionError("raw RHS comparison is not bidirectional")
    if not any(
        not entry["lcm_rhs_divides_product_rhs"]
        and not entry["product_rhs_divides_lcm_rhs"]
        for entry in flags.values()
    ):
        raise AssertionError("no divisibility-incomparable fixture")
    exact16_numerator = 3 * factorial(15) * small_lcm(16)
    uniform16_numerator = 5 * factorial(15) * small_lcm(16)
    exact16 = (exact16_numerator + 18) // 19
    uniform16 = (uniform16_numerator + 18) // 19
    if small_lcm(16) != 360_360:
        raise AssertionError
    if not 19 * (exact16 - 1) < exact16_numerator <= 19 * exact16:
        raise AssertionError
    return {
        "flags": flags,
        "small_lcm_16": small_lcm(16),
        "exact_threshold_16": exact16,
        "uniform_threshold_16": uniform16,
        "raw_rhs_both_directions": True,
    }


def report() -> dict[str, Any]:
    return {
        "concentration": concentration_grid(),
        "conditional_composition": conditional_composition_scan(),
        "named_fixtures": named_fixture_report(),
        "structure": structural_report(),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args()
    print(json.dumps(report(), indent=2 if args.pretty else None, sort_keys=True))


if __name__ == "__main__":
    main()
