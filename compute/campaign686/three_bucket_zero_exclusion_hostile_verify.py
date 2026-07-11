#!/usr/bin/env python3
"""Independent hostile verifier for the target-row zero-obstruction wrapper.

This module imports no producer verifier and no earlier audit module.  The
three Taylor coefficients are reconstructed as elementary-symmetric sums by
directly omitting zero, one, or two offsets from the local product.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from functools import cache
from itertools import combinations, permutations
from math import gcd, prod
from pathlib import Path
from typing import Any, Iterable, Sequence


ROWS = (5, 7, 9, 11, 13, 15)
CROSS_BOUND = 10**30
THIRD_BOUND = 10**18
LOSS_BOUND = 18_914_575_680
CUTOFF = 10**120

FROZEN_HASHES = {
    "ErdosProblems/Erdos686ThreeBucketZeroExclusion.lean":
        "5b802dd3db2d63254b251465f96093358389c0eca4d72cdd7608d2238e549ff2",
    "compute/campaign686/three_bucket_zero_exclusion_verify.py":
        "106f7686c30eed5150d922fa1e0acbd1b7439f1bc000a356df541af724fb4c78",
    "compute/campaign686/test_three_bucket_zero_exclusion_verify.py":
        "6d7f2aa138e344fed21700b86a58e98a50ebbbbb3976c2d42fd95c9a66ae4810",
    "compute/campaign686/three_bucket_zero_exclusion_findings.md":
        "459f43e1d11c02186635bfe617a8bfe372acdcc5c3cc407fc7bfb7f1d78a3f20",
    "docs/plans/2026-07-10-erdos686-three-bucket-zero-exclusion.md":
        "0ba5ac8c350406eeccc5e4f134f392487dd3045c4de5dd685964d49c6d22c330",
}


def repository_root() -> Path:
    return Path(__file__).resolve().parents[2]


@cache
def frozen_hash_report() -> dict[str, Any]:
    root = repository_root()
    actual = {
        relative: hashlib.sha256((root / relative).read_bytes()).hexdigest()
        for relative in FROZEN_HASHES
    }
    drifted = [
        relative
        for relative, expected in FROZEN_HASHES.items()
        if actual[relative] != expected
    ]
    return {
        "expected": FROZEN_HASHES,
        "actual": actual,
        "drifted_paths_since_audit": drifted,
        "all_match": not drifted,
    }


def _product_without(values: Sequence[int], omitted: frozenset[int]) -> int:
    return prod(value for index, value in enumerate(values) if index not in omitted)


@cache
def local_coefficients(k: int, owner: int) -> tuple[int, int, int]:
    if k not in ROWS or not 1 <= owner <= k:
        raise ValueError((k, owner))
    offsets = tuple(column - owner for column in range(1, k + 1) if column != owner)
    constant = prod(offsets)
    linear = sum(
        _product_without(offsets, frozenset((omitted,)))
        for omitted in range(len(offsets))
    )
    quadratic = sum(
        _product_without(offsets, frozenset((first, second)))
        for first, second in combinations(range(len(offsets)), 2)
    )
    return constant, linear, quadratic


def owner_delta(owner: int, left: int, right: int) -> int:
    return (owner - left) * (owner - right)


def second_obstruction(
    k: int,
    owner: int,
    left: int,
    right: int,
    t: int,
    g: int,
) -> int:
    constant, linear, _ = local_coefficients(k, owner)
    return 3 * (
        constant * t
        - 12 * linear * g**2 * owner_delta(owner, left, right)
    )


def third_obstruction(
    k: int,
    owner: int,
    left: int,
    right: int,
    t: int,
    g: int,
    d: int,
) -> int:
    _, _, quadratic = local_coefficients(k, owner)
    second = second_obstruction(k, owner, left, right, t, g)
    return (
        -3 * second
        + 180 * quadratic * g**2 * owner_delta(owner, left, right) * d
    )


def cross_numerator(k: int, owner: int, zero: int, other: int) -> int:
    owner_constant, owner_linear, _ = local_coefficients(k, owner)
    zero_constant, zero_linear, _ = local_coefficients(k, zero)
    return 36 * (
        owner_constant
        * zero_linear
        * owner_delta(zero, owner, other)
        - owner_linear
        * owner_delta(owner, zero, other)
        * zero_constant
    )


def zero_third_coefficient(k: int, zero: int, owner: int, other: int) -> int:
    _, _, quadratic = local_coefficients(k, zero)
    return 180 * quadratic * owner_delta(zero, owner, other)


def _designated_view(
    k: int,
    first: int,
    second: int,
    zero: int,
    t: int,
    g: int,
    d: int,
) -> tuple[int, int, int, int]:
    return (
        second_obstruction(k, first, zero, second, t, g),
        second_obstruction(k, second, zero, first, t, g),
        second_obstruction(k, zero, first, second, t, g),
        third_obstruction(k, zero, first, second, t, g, d),
    )


def _cyclic_views(
    k: int,
    i: int,
    j: int,
    l: int,
    t: int,
    g: int,
    d: int,
) -> Iterable[tuple[tuple[int, int, int, int], tuple[int, int, int, int]]]:
    oi = second_obstruction(k, i, j, l, t, g)
    oj = second_obstruction(k, j, i, l, t, g)
    ol = second_obstruction(k, l, i, j, t, g)
    fi = third_obstruction(k, i, j, l, t, g, d)
    fj = third_obstruction(k, j, i, l, t, g, d)
    fl = third_obstruction(k, l, i, j, t, g, d)
    # Each pair is (the theorem's designated view, its expected original view).
    yield _designated_view(k, j, l, i, t, g, d), (oj, ol, oi, fi)
    yield _designated_view(k, i, l, j, t, g, d), (oi, ol, oj, fj)
    yield _designated_view(k, i, j, l, t, g, d), (oi, oj, ol, fl)


@cache
def finite_certificate_report() -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    cross_checks = 0
    third_checks = 0
    cyclic_checks = 0
    for k in ROWS:
        count = 0
        zero_cross_cases = 0
        zero_third_cases = 0
        maximum_cross = -1
        maximum_cross_case: tuple[int, int, int] | None = None
        maximum_third = -1
        maximum_third_case: tuple[int, int, int] | None = None
        for owner, zero, other in permutations(range(1, k + 1), 3):
            count += 1
            cross = cross_numerator(k, owner, zero, other)
            third_coefficient = zero_third_coefficient(k, zero, owner, other)
            zero_cross_cases += cross == 0
            zero_third_cases += third_coefficient == 0
            if not 0 < abs(cross) < CROSS_BOUND:
                raise AssertionError(("cross certificate", k, owner, zero, other, cross))
            if not 0 < abs(third_coefficient) < THIRD_BOUND:
                raise AssertionError(
                    ("third certificate", k, owner, zero, other, third_coefficient)
                )
            if abs(cross) > maximum_cross:
                maximum_cross = abs(cross)
                maximum_cross_case = (owner, zero, other)
            if abs(third_coefficient) > maximum_third:
                maximum_third = abs(third_coefficient)
                maximum_third_case = (owner, zero, other)

            # Check the exact denominator-free elimination independently of
            # the producer theorem.  The chosen values merely instantiate a
            # polynomial identity whose t-coefficient cancels identically.
            t = (k + owner) * (zero + 2 * other + 1)
            g = 1 + (owner * zero + other) % 19
            d = 1 + k * owner * zero * other
            owner_second = second_obstruction(k, owner, zero, other, t, g)
            zero_second = second_obstruction(k, zero, owner, other, t, g)
            owner_constant, _, _ = local_coefficients(k, owner)
            zero_constant, _, _ = local_coefficients(k, zero)
            if (
                zero_constant * owner_second - owner_constant * zero_second
                != cross * g**2
            ):
                raise AssertionError(("cross identity", k, owner, zero, other))
            cross_checks += 1

            zero_third = third_obstruction(k, zero, owner, other, t, g, d)
            if zero_third + 3 * zero_second != third_coefficient * g**2 * d:
                raise AssertionError(("third identity", k, owner, zero, other))
            third_checks += 1

            for actual, expected in _cyclic_views(k, owner, zero, other, t, g, d):
                if actual != expected:
                    raise AssertionError(("cyclic view", k, owner, zero, other))
                cyclic_checks += 1

        rows.append(
            {
                "k": k,
                "ordered_distinct_owner_triples": count,
                "maximum_cross_numerator": maximum_cross,
                "maximum_cross_case": list(maximum_cross_case or ()),
                "maximum_third_coefficient": maximum_third,
                "maximum_third_case": list(maximum_third_case or ()),
                "zero_cross_cases": zero_cross_cases,
                "zero_third_cases": zero_third_cases,
            }
        )
    return {
        "rows": rows,
        "ordered_distinct_owner_triples": sum(
            row["ordered_distinct_owner_triples"] for row in rows
        ),
        "cross_identity_checks": cross_checks,
        "third_identity_checks": third_checks,
        "cyclic_designated_zero_checks": cyclic_checks,
    }


def numeric_cutoff_report() -> dict[str, int | bool]:
    majorant = CROSS_BOUND**2 * THIRD_BOUND * LOSS_BOUND**4
    return {
        "cross_bound": CROSS_BOUND,
        "third_bound": THIRD_BOUND,
        "loss_bound": LOSS_BOUND,
        "majorant": majorant,
        "cutoff": CUTOFF,
        "strict": majorant < CUTOFF,
        "cutoff_margin": CUTOFF - majorant,
        "cutoff_margin_floor": CUTOFF // majorant,
    }


def _packing_fixture(
    P: int,
    Q: int,
    R: int,
    g: int,
    A: int,
    B: int,
    K: int,
) -> dict[str, Any]:
    d = g * P * Q * R
    coefficient_product = A * B * K
    premises = (
        R > 0
        and gcd(P, Q) == gcd(P, R) == gcd(Q, R) == 1
        and (A * g**2) % P == 0
        and (B * g**2) % Q == 0
        and (K * g**2 * d) % R**2 == 0
    )
    conclusion = (coefficient_product * g**4) % d == 0
    if not premises or not conclusion:
        raise AssertionError((P, Q, R, g, A, B, K))
    return {
        "components": [P, Q, R],
        "g": g,
        "A": A,
        "B": B,
        "K": K,
        "d": d,
        "coefficient_product": coefficient_product,
        "premises_hold": premises,
        "conclusion_holds": conclusion,
    }


def packing_boundary_report() -> dict[str, Any]:
    shared = _packing_fixture(2, 3, 5, 30, 2, 3, 5)
    shared["gcds_with_g"] = [gcd(shared["g"], value) for value in (2, 3, 5)]
    units = (
        _packing_fixture(1, 2, 3, 6, 1, 2, 3),
        _packing_fixture(1, 1, 1, 7, 1, 1, 1),
    )
    sharp = _packing_fixture(2, 5, 27, 3, 2, 5, 1)
    sharp["d_divides_product_g4"] = True
    sharp["d_divides_product_g3"] = (
        sharp["coefficient_product"] * sharp["g"] ** 3
    ) % sharp["d"] == 0
    if sharp["d_divides_product_g3"]:
        raise AssertionError("the g^4 sharpness fixture unexpectedly paid only g^3")
    return {
        "small_primes_shared_with_g": shared,
        "unit_fixtures": list(units),
        "g_fourth_power_sharp_fixture": sharp,
    }


def _crt_pairwise(congruences: Sequence[tuple[int, int]]) -> tuple[int, int]:
    modulus = prod(modulus for _, modulus in congruences)
    value = 0
    for residue, component_modulus in congruences:
        complement = modulus // component_modulus
        value += (
            residue
            * complement
            * pow(complement, -1, component_modulus)
        )
    value %= modulus
    if any(value % modulus_i != residue % modulus_i for residue, modulus_i in congruences):
        raise AssertionError("CRT reconstruction failed")
    return value, modulus


def local_second_lift(
    k: int,
    owner: int,
    cofactor: int,
    opposite: int,
) -> int:
    constant, linear, _ = local_coefficients(k, owner)
    return 3 * constant * cofactor - 4 * linear * opposite**2


def local_third_lift(
    k: int,
    owner: int,
    component: int,
    cofactor: int,
    opposite: int,
) -> int:
    _, _, quadratic = local_coefficients(k, owner)
    return (
        -3 * local_second_lift(k, owner, cofactor, opposite)
        + 20 * quadratic * component * opposite**3
    )


def block_product(k: int, n: int) -> int:
    return prod(n + index for index in range(1, k + 1))


@cache
def crt_pseudo_witness() -> dict[str, Any]:
    k = 5
    indices = (1, 2, 4)
    components = (101**20, 103**20, 107**20)
    component_squares = tuple(component**2 for component in components)
    d = prod(components)
    anchor = indices[0]

    base, base_modulus = _crt_pairwise(
        tuple(
            ((-3 * (index - anchor)) % square, square)
            for index, square in zip(indices, component_squares, strict=True)
        )
    )
    if base_modulus != d**2:
        raise AssertionError("base CRT modulus is not d^2")

    parameter_congruences: list[tuple[int, int]] = []
    for index, component, square in zip(
        indices, components, component_squares, strict=True
    ):
        base_cofactor = (base + 3 * (index - anchor)) // square
        cofactor_step = d**2 // square
        constant, _, quadratic = local_coefficients(k, index)
        opposite = d // component
        third_at_zero = (
            -3 * local_second_lift(k, index, base_cofactor, opposite)
            + 20 * quadratic * component * opposite**3
        )
        third_step = -9 * constant * cofactor_step
        parameter_residue = (
            -third_at_zero * pow(third_step, -1, square)
        ) % square
        parameter_congruences.append((parameter_residue, square))

    parameter, parameter_modulus = _crt_pairwise(tuple(parameter_congruences))
    if parameter_modulus != d**2:
        raise AssertionError("parameter CRT modulus is not d^2")

    integral_candidates: list[tuple[int, int]] = []
    for lift in range(3):
        lifted_parameter = parameter + lift * d**2
        x_anchor = base + d**2 * lifted_parameter
        if (x_anchor + d) % 3 == 0:
            integral_candidates.append((lift, x_anchor))
    if len(integral_candidates) != 1:
        raise AssertionError(integral_candidates)
    integrality_lift, x_anchor = integral_candidates[0]
    n = (x_anchor + d) // 3 - anchor

    residuals = tuple(3 * (n + index) - d for index in indices)
    cofactors = tuple(
        residual // square
        for residual, square in zip(residuals, component_squares, strict=True)
    )
    if any(cofactor <= 0 for cofactor in cofactors):
        raise AssertionError("nonpositive CRT cofactor")
    t = prod(cofactors)

    local_ok = True
    composed_ok = True
    nonzero = True
    for index, component, cofactor in zip(indices, components, cofactors, strict=True):
        opposite = d // component
        local_ok &= local_second_lift(k, index, cofactor, opposite) % component == 0
        local_ok &= (
            local_third_lift(k, index, component, cofactor, opposite)
            % component**2
            == 0
        )
        other_indices = tuple(other for other in indices if other != index)
        second = second_obstruction(k, index, *other_indices, t, 1)
        third = third_obstruction(k, index, *other_indices, t, 1, d)
        composed_ok &= second % component == 0
        composed_ok &= third % component**2 == 0
        nonzero &= second != 0

    progression = all(
        residuals[right] - residuals[left]
        == 3 * (indices[right] - indices[left])
        for left, right in combinations(range(3), 2)
    )
    return {
        "k": k,
        "indices": list(indices),
        "components": list(components),
        "g": 1,
        "d": d,
        "gap_digits": len(str(d)),
        "gap_at_least_cutoff": d >= CUTOFF,
        "pairwise_coprime_components": all(
            gcd(components[left], components[right]) == 1
            for left, right in combinations(range(3), 2)
        ),
        "integrality_lift": integrality_lift,
        "exact_step_three_progression": progression,
        "local_divisibilities": local_ok,
        "composed_divisibilities": composed_ok,
        "all_second_obstructions_nonzero": nonzero,
        "zero_exclusion_conclusion_holds": nonzero,
        "short_window": max(residuals) < 14 * d,
        "equation": block_product(k, n + d) == 4 * block_product(k, n),
    }


@cache
def boundary_report() -> dict[str, Any]:
    telescopes = []
    for k, n in ((9, 2), (15, 4)):
        d = 1
        equation = block_product(k, n + d) == 4 * block_product(k, n)
        if not equation:
            raise AssertionError((k, n, d))
        telescopes.append(
            {
                "k": k,
                "n": n,
                "d": d,
                "equation": equation,
                "large_gap_hypothesis": CUTOFF <= d,
            }
        )
    return {
        "packing": packing_boundary_report(),
        "d_eq_one_telescopes": telescopes,
        "crt_pseudo_witness": crt_pseudo_witness(),
    }


def forbidden_construct_report() -> dict[str, Any]:
    root = repository_root()
    files = (
        "ErdosProblems/Erdos686ThreeBucketZeroExclusion.lean",
        "compute/campaign686/three_bucket_zero_exclusion_verify.py",
        "compute/campaign686/test_three_bucket_zero_exclusion_verify.py",
    )
    pattern = re.compile(
        r"\b(?:sorry|admit|native_decide|of_decide|unsafe|implemented_by|extern)\b"
        r"|^\s*(?:private\s+)?axiom\b",
        re.MULTILINE,
    )
    hits = {
        relative: pattern.findall((root / relative).read_text())
        for relative in files
    }
    hits = {relative: matches for relative, matches in hits.items() if matches}
    return {"files": list(files), "hits": hits, "clean": not hits}


@cache
def report() -> dict[str, Any]:
    finite = finite_certificate_report()
    return {
        **finite,
        "frozen_hashes": frozen_hash_report(),
        "numeric_cutoff": numeric_cutoff_report(),
        "boundaries": boundary_report(),
        "forbidden_constructs": forbidden_construct_report(),
        "scope": {
            "proved": (
                "conditional exclusion of a zero composed second obstruction "
                "for the six target rows above the cutoff"
            ),
            "assumes_three_owner_factorization_and_six_divisibilities": True,
            "closes_nonzero_branch": False,
            "closes_exactly_three_owner_slice": False,
            "closes_erdos_686": False,
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args()
    print(json.dumps(report(), indent=2 if args.pretty else None, sort_keys=True))


if __name__ == "__main__":
    main()
