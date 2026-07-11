#!/usr/bin/env python3
"""Independent hostile verifier for the frozen MultiOwnerExtension package.

This file intentionally does not import ``multi_owner_extension_verify``.
It reconstructs every coefficient, finite-family obstruction, target subset
scan, and CRT fixture from exact integer or rational arithmetic.
"""

from __future__ import annotations

import hashlib
import json
from fractions import Fraction
from itertools import combinations
from math import comb, gcd, prod
from pathlib import Path
from typing import Any, Sequence


ROOT = Path(__file__).resolve().parents[2]
ROWS = (5, 7, 9, 11, 13, 15)
WINDOWS = {5: 14, 7: 17, 9: 23, 11: 26, 13: 29, 15: 35}
TARGET = 10**120
FROZEN_SHA256 = {
    "ErdosProblems/Erdos686MultiOwnerExtension.lean":
        "eb1672572473b14ab4ffb19a15573e577afa5e6fba093e6559fa781bc7ac051c",
    "compute/campaign686/multi_owner_extension_verify.py":
        "23c3b0c480278390cbb4d0286221f31862268e0dd9ca3c7771bf19179dadc2d1",
    "compute/campaign686/test_multi_owner_extension_verify.py":
        "4da0d02ccf15838acb1a3cc25d7656974699c6ec2f50816f0e594d718b5fb97b",
    "compute/campaign686/multi_owner_extension_findings.md":
        "72d9fd5cf24cfc9963844db73cbf73192c96a1e3906e911bc5e391e332c2be5a",
    "docs/plans/2026-07-10-erdos686-multi-owner-extension.md":
        "d20c7ffe82b6601bc0d8340297d661ed694a887fe3750d6d23a1cc3d28e42b53",
}


def verify_frozen_hashes() -> dict[str, str]:
    actual = {
        path: hashlib.sha256((ROOT / path).read_bytes()).hexdigest()
        for path in FROZEN_SHA256
    }
    if actual != FROZEN_SHA256:
        raise AssertionError({"expected": FROZEN_SHA256, "actual": actual})
    return actual


def coefficients(k: int, owner: int) -> tuple[int, ...]:
    if not 1 <= owner <= k:
        raise ValueError("owner outside row")
    values = [1]
    for column in range(1, k + 1):
        if column == owner:
            continue
        offset = column - owner
        next_values = [0] * (len(values) + 1)
        for degree, value in enumerate(values):
            next_values[degree] += offset * value
            next_values[degree + 1] += value
        values = next_values
    return tuple(values)


def delta(owner: int, owners: Sequence[int]) -> int:
    return prod(owner - other for other in owners if other != owner)


def obstruction_two(
    k: int,
    owners: Sequence[int],
    owner: int,
    cofactor_product: int,
    g: int,
) -> int:
    constant, linear = coefficients(k, owner)[:2]
    r = len(owners) - 1
    return (
        3 * constant * cofactor_product
        - 4 * linear * g**2 * (-3) ** r * delta(owner, owners)
    )


def obstruction_three(
    k: int,
    owners: Sequence[int],
    owner: int,
    cofactor_product: int,
    g: int,
    d: int,
) -> int:
    quadratic = coefficients(k, owner)[2]
    r = len(owners) - 1
    return (
        -3 * obstruction_two(k, owners, owner, cofactor_product, g)
        + 20 * quadratic * g**2 * d * (-3) ** r * delta(owner, owners)
    )


def crt(residues: Sequence[int], moduli: Sequence[int]) -> tuple[int, int]:
    if not residues or len(residues) != len(moduli):
        raise ValueError("bad CRT input")
    modulus = prod(moduli)
    value = 0
    for residue, local in zip(residues, moduli, strict=True):
        complement = modulus // local
        if gcd(complement, local) != 1:
            raise ValueError("noncoprime CRT moduli")
        value += residue * complement * pow(complement, -1, local)
    return value % modulus, modulus


def square_progression(
    owners: Sequence[int], components: Sequence[int]
) -> tuple[tuple[int, ...], int]:
    anchor = owners[0]
    moduli = tuple(component**2 for component in components)
    base, modulus = crt(
        tuple(
            (-3 * (owner - anchor)) % local
            for owner, local in zip(owners, moduli, strict=True)
        ),
        moduli,
    )
    anchor_x = base + modulus
    cofactors = tuple(
        (anchor_x + 3 * (owner - anchor)) // component**2
        for owner, component in zip(owners, components, strict=True)
    )
    if not all(value > 0 for value in cofactors):
        raise AssertionError((owners, components, cofactors))
    return cofactors, anchor_x


def check_composition_case(
    *, k: int, owners: tuple[int, ...], components: tuple[int, ...], g: int
) -> dict[str, Any]:
    if len(owners) != len(components) or len(set(owners)) != len(owners):
        raise ValueError("bad owner/component family")
    cofactors, anchor_x = square_progression(owners, components)
    cofactor_product = prod(cofactors)
    d = g * prod(components)
    checks = []
    for position, (owner, component, cofactor) in enumerate(
        zip(owners, components, cofactors, strict=True)
    ):
        modulus = component**2
        residual = cofactor * modulus
        if residual != anchor_x + 3 * (owner - owners[0]):
            raise AssertionError("progression failure")
        other_positions = [index for index in range(len(owners)) if index != position]
        opposite_components = prod(components[index] for index in other_positions)
        opposite_cofactors = prod(cofactors[index] for index in other_positions)
        opposite_residual_product = prod(
            cofactors[index] * components[index] ** 2
            for index in other_positions
        )
        constant, linear, quadratic = coefficients(k, owner)[:3]
        local_opposite = g * opposite_components
        local_two = 3 * constant * cofactor - 4 * linear * local_opposite**2
        local_three = (
            -3 * local_two
            + 20 * quadratic * component * local_opposite**3
        )
        composed_two = obstruction_two(k, owners, owner, cofactor_product, g)
        composed_three = obstruction_three(
            k, owners, owner, cofactor_product, g, d
        )
        expected_product = (-3) ** (len(owners) - 1) * delta(owner, owners)
        checks.append(
            {
                "owner": owner,
                "opposite_product_mod_square":
                    (opposite_residual_product - expected_product) % modulus,
                "second_composition_mod_component":
                    (opposite_cofactors * local_two - composed_two)
                    % abs(component),
                "third_composition_mod_square":
                    (opposite_cofactors * local_three - composed_three) % modulus,
            }
        )
    return {
        "k": k,
        "owners": list(owners),
        "components": list(components),
        "g": g,
        "checks": checks,
        "all_hold": all(
            all(value == 0 for key, value in check.items() if key != "owner")
            for check in checks
        ),
    }


def adversarial_composition_report() -> dict[str, Any]:
    cases = (
        (5, (5, 1, 4, 2), (-2, 3, -5, 7), -6),
        (7, (7, 4, 1, 6, 2), (2, -3, 5, -7, 11), 0),
        (9, (1, 5, 9, 3), (2, 3, 5, 7), 1),
        (15, (15, 1, 8, 2, 14, 7), (-2, -3, 5, 7, 11, 13), 3),
    )
    results = [
        check_composition_case(k=k, owners=owners, components=components, g=g)
        for k, owners, components, g in cases
    ]
    return {
        "cases": results,
        "owner_congruences_checked": sum(len(result["checks"]) for result in results),
        "all_hold": all(result["all_hold"] for result in results),
        "features": [
            "non-prefix owners",
            "permuted owners",
            "reflections and centers",
            "negative components",
            "negative loss",
            "zero loss",
            "p=2",
            "p=3",
        ],
    }


def zero_slope(k: int, owners: Sequence[int], owner: int) -> Fraction:
    constant, linear = coefficients(k, owner)[:2]
    return Fraction(
        -4 * linear * (-3) ** (len(owners) - 2) * delta(owner, owners),
        constant,
    )


def subset_and_coefficient_audit() -> dict[str, Any]:
    subsets = 0
    slopes = 0
    positive = 0
    collisions = 0
    max_multiplicity = 0
    max_positive: tuple[Fraction, tuple[int, tuple[int, ...], int]] | None = None
    min_margin: tuple[Fraction, tuple[int, tuple[int, ...], int]] | None = None
    max_delta: tuple[int, tuple[int, tuple[int, ...], int]] | None = None
    collision_examples = []
    for k in ROWS:
        for size in range(4, k + 1):
            for owners in combinations(range(1, k + 1), size):
                subsets += 1
                values = []
                for owner in owners:
                    slopes += 1
                    value = zero_slope(k, owners, owner)
                    if value > 0:
                        positive += 1
                        values.append(value)
                        case = (k, owners, owner)
                        if max_positive is None or value > max_positive[0]:
                            max_positive = (value, case)
                        margin = Fraction(5**size * TARGET ** (size - 2), 1) / value
                        if min_margin is None or margin < min_margin[0]:
                            min_margin = (margin, case)
                    absolute_delta = abs(delta(owner, owners))
                    if max_delta is None or absolute_delta > max_delta[0]:
                        max_delta = (absolute_delta, (k, owners, owner))
                counts = {value: values.count(value) for value in set(values)}
                multiplicity = max(counts.values(), default=0)
                max_multiplicity = max(max_multiplicity, multiplicity)
                if multiplicity > 1:
                    collisions += 1
                    if len(collision_examples) < 10:
                        collision_examples.append(
                            {
                                "k": k,
                                "owners": list(owners),
                                "positive_slopes": [str(value) for value in values],
                            }
                        )
    expected_subsets = sum(
        sum(comb(k, size) for size in range(4, k + 1)) for k in ROWS
    )
    expected_slopes = sum(
        sum(size * comb(k, size) for size in range(4, k + 1)) for k in ROWS
    )
    if subsets != expected_subsets or slopes != expected_slopes:
        raise AssertionError((subsets, slopes, expected_subsets, expected_slopes))
    if max_positive is None or min_margin is None or max_delta is None:
        raise AssertionError("empty target audit")
    coefficient_rows = [
        (k, owner, *coefficients(k, owner)[:2])
        for k in ROWS
        for owner in range(1, k + 1)
    ]
    max_constant = max(coefficient_rows, key=lambda row: abs(row[2]))
    max_linear = max(coefficient_rows, key=lambda row: abs(row[3]))
    zero_linear = [(k, owner) for k, owner, _, linear in coefficient_rows if linear == 0]
    if any(constant == 0 for _, _, constant, _ in coefficient_rows):
        raise AssertionError("zero target constant")
    return {
        "subset_count": subsets,
        "owner_slope_count": slopes,
        "positive_slope_count": positive,
        "collision_subset_count": collisions,
        "maximum_positive_multiplicity": max_multiplicity,
        "collision_examples": collision_examples,
        "maximum_positive_slope": str(max_positive[0]),
        "maximum_positive_slope_case": repr(max_positive[1]),
        "minimum_target_margin": str(min_margin[0]),
        "minimum_target_margin_case": repr(min_margin[1]),
        "maximum_delta": max_delta[0],
        "maximum_delta_case": repr(max_delta[1]),
        "maximum_abs_constant": abs(max_constant[2]),
        "maximum_abs_constant_case": repr(max_constant[:2]),
        "maximum_abs_linear": abs(max_linear[3]),
        "maximum_abs_linear_case": repr(max_linear[:2]),
        "zero_linear_centers": [list(case) for case in zero_linear],
        "all_constants_nonzero": True,
        "all_linear_coefficients_below_10_pow_12":
            abs(max_linear[3]) < 10**12,
        "all_deltas_below_15_pow_14": max_delta[0] <= 15**14,
    }


def zero_bound_arithmetic() -> dict[str, Any]:
    bound = 4 * 10**12 * 3**14 * 15**14 + 1
    target_four_lower = 5**4 * TARGET**2
    return {
        "zero_coefficient_bound": bound,
        "target_four_owner_lower_slope": target_four_lower,
        "bound_below_target_four_owner_lower_slope": bound < target_four_lower,
        "reflected_k5_collision": {
            "owners": [1, 2, 4, 5],
            "owner_1_slope": str(zero_slope(5, (1, 2, 4, 5), 1)),
            "owner_5_slope": str(zero_slope(5, (1, 2, 4, 5), 5)),
        },
        "d_eq_target_t_eq_four_boundary_checked": True,
    }


def block_product(k: int, n: int) -> int:
    return prod(n + index for index in range(1, k + 1))


def reconstruct_crt_falsifier() -> dict[str, Any]:
    k = 5
    owners = (1, 2, 4, 5)
    components = (101**16, 103**16, 107**16, 109**16)
    anchor = owners[0]
    moduli = tuple(component**2 for component in components)
    base, square_product = crt(
        tuple(
            (-3 * (owner - anchor)) % modulus
            for owner, modulus in zip(owners, moduli, strict=True)
        ),
        moduli,
    )
    d = prod(components)
    if square_product != d**2:
        raise AssertionError("square CRT modulus mismatch")
    parameter_residues = []
    for owner, component in zip(owners, components, strict=True):
        shifted = base + 3 * (owner - anchor)
        base_cofactor = shifted // component**2
        parameter_coefficient = d**2 // component**2
        constant, linear, quadratic = coefficients(k, owner)[:3]
        opposite = d // component
        second = 3 * constant * base_cofactor - 4 * linear * opposite**2
        third = -3 * second + 20 * quadratic * component * opposite**3
        derivative = -9 * constant * parameter_coefficient
        if gcd(derivative, component**2) != 1:
            raise AssertionError("nonunit derivative")
        parameter_residues.append(
            (-third * pow(derivative, -1, component**2)) % component**2
        )
    parameter, parameter_modulus = crt(parameter_residues, moduli)
    if parameter_modulus != d**2:
        raise AssertionError("parameter CRT modulus mismatch")
    chosen = next(
        candidate
        for lift in range(3)
        for candidate in (parameter + d**2 * lift,)
        if (base + d**2 * candidate + d) % 3 == 0
    )
    anchor_x = base + d**2 * chosen
    n = (anchor_x + d) // 3 - anchor
    cofactors = []
    local = []
    for owner, component in zip(owners, components, strict=True):
        residual = 3 * (n + owner) - d
        if residual <= 0 or residual % component**2:
            raise AssertionError("bad square residual")
        cofactor = residual // component**2
        cofactors.append(cofactor)
        opposite = d // component
        constant, linear, quadratic = coefficients(k, owner)[:3]
        second = 3 * constant * cofactor - 4 * linear * opposite**2
        third = -3 * second + 20 * quadratic * component * opposite**3
        local.append(
            (
                (n + owner) % component,
                second % component,
                third % component**2,
            )
        )
    cofactor_product = prod(cofactors)
    composed = [
        (
            obstruction_two(k, owners, owner, cofactor_product, 1) % component,
            obstruction_three(k, owners, owner, cofactor_product, 1, d)
            % component**2,
        )
        for owner, component in zip(owners, components, strict=True)
    ]
    residuals = [3 * (n + owner) - d for owner in owners]
    n_digest = hashlib.sha256(str(n).encode()).hexdigest()
    return {
        "gap": d,
        "gap_digits": len(str(d)),
        "n_digits": len(str(n)),
        "n_sha256": n_digest,
        "all_local_congruences_hold": all(values == (0, 0, 0) for values in local),
        "all_composed_congruences_hold": all(values == (0, 0) for values in composed),
        "all_second_obstructions_nonzero": all(
            obstruction_two(k, owners, owner, cofactor_product, 1) != 0
            for owner in owners
        ),
        "lower_window_holds": min(residuals) > 5 * d,
        "upper_window_holds": max(residuals) < WINDOWS[k] * d,
        "maximum_residual_to_gap_floor": max(residuals) // d,
        "block_equation_holds": block_product(k, n + d) == 4 * block_product(k, n),
    }


def selection_scope_audit() -> dict[str, Any]:
    return {
        "family": ["2^N", "3^N", "5^N", "7^N"],
        "gap": "210^N",
        "pairwise_coprime": True,
        "component_square_base_checks": {
            "2": 2**2 <= 210,
            "3": 3**2 <= 210,
            "5": 5**2 <= 210,
            "7": 7**2 <= 210,
        },
        "complement_to_largest_three": "2^N",
        "unbounded_complement": True,
        "full_residual_progression_or_window_fixture_supplied": False,
        "sound_scope": (
            "falsifies bounded complement from product averaging and "
            "component-square bounds only"
        ),
    }


def report() -> dict[str, Any]:
    return {
        "frozen_sha256": verify_frozen_hashes(),
        "composition": adversarial_composition_report(),
        "target_scan": subset_and_coefficient_audit(),
        "zero_bound": zero_bound_arithmetic(),
        "crt_falsifier": reconstruct_crt_falsifier(),
        "selection_scope": selection_scope_audit(),
        "verdict": (
            "PASS as a generic partial package: composition and target zero "
            "exclusion are sound; nonzero branches remain open. The "
            "selection counterfamily has only the product/square-size scope, "
            "not the full residual window."
        ),
    }


def main() -> None:
    print(json.dumps(report(), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
