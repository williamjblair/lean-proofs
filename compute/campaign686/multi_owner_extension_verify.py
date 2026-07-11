#!/usr/bin/env python3
"""Exact audit of the four-or-more cleaned-owner route for Erdős 686.

This file deliberately keeps the original bounded loss ``g``.  For a finite
owner family ``S`` with pairwise-coprime cleaned components ``P_s``, write

    d = g * product(P_s),
    X_s = a_s * P_s^2,
    X_s - X_u = 3 * (s-u).

Multiplying one local lift by every opposite cofactor gives exact second and
third composed obstructions for arbitrary ``len(S)``.  The target-row scan
also checks the only apparently bounded degeneracy, a zero second
obstruction.  It does not claim that nonzero obstructions close the equation.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from functools import lru_cache
from itertools import combinations
from math import comb, gcd, prod
from typing import Any, Sequence


ROWS = {5: 14, 7: 17, 9: 23, 11: 26, 13: 29, 15: 35}
LOSS_BUDGETS = {
    5: 108,
    7: 1_620,
    9: 136_080,
    11: 1_224_720,
    13: 242_494_560,
    15: 18_914_575_680,
}
TARGET = 10**120
COMPONENT_BASES = (2, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53)


def local_taylor_coefficients(k: int, owner: int) -> tuple[int, ...]:
    """Coefficients of ``prod_{1<=j<=k,j!=owner}(z+j-owner)``."""

    if not 1 <= owner <= k:
        raise ValueError("owner outside the row")
    coefficients = [1]
    for column in range(1, k + 1):
        if column == owner:
            continue
        offset = column - owner
        updated = [0] * (len(coefficients) + 1)
        for degree, coefficient in enumerate(coefficients):
            updated[degree] += offset * coefficient
            updated[degree + 1] += coefficient
        coefficients = updated
    return tuple(coefficients)


def crt(residues: Sequence[int], moduli: Sequence[int]) -> tuple[int, int]:
    """Pairwise-coprime Chinese remainder theorem, using exact integers."""

    if len(residues) != len(moduli) or not residues:
        raise ValueError("CRT expects equal nonempty lists")
    modulus = prod(moduli)
    value = 0
    for residue, local_modulus in zip(residues, moduli, strict=True):
        complement = modulus // local_modulus
        if gcd(complement, local_modulus) != 1:
            raise ValueError("CRT moduli are not pairwise coprime")
        value += residue * complement * pow(complement, -1, local_modulus)
    return value % modulus, modulus


def owner_delta(owner: int, owners: Sequence[int]) -> int:
    return prod(owner - other for other in owners if other != owner)


def multi_owner_second_obstruction(
    *, k: int, owners: Sequence[int], owner: int, cofactor_product: int, loss: int
) -> int:
    """Second obstruction after eliminating every opposite square residual."""

    constant, linear = local_taylor_coefficients(k, owner)[:2]
    size = len(owners)
    delta = owner_delta(owner, owners)
    return 3 * (
        constant * cofactor_product
        + 4 * linear * loss**2 * (-3) ** (size - 2) * delta
    )


def multi_owner_third_obstruction(
    *,
    k: int,
    owners: Sequence[int],
    owner: int,
    cofactor_product: int,
    loss: int,
    gap: int,
) -> int:
    """Third obstruction after the same finite-family elimination."""

    quadratic = local_taylor_coefficients(k, owner)[2]
    size = len(owners)
    delta = owner_delta(owner, owners)
    second = multi_owner_second_obstruction(
        k=k,
        owners=owners,
        owner=owner,
        cofactor_product=cofactor_product,
        loss=loss,
    )
    return (
        -3 * second
        + 20 * quadratic * loss**2 * gap * (-3) ** (size - 1) * delta
    )


def square_progression_fixture(
    owners: Sequence[int], components: Sequence[int]
) -> tuple[tuple[int, ...], int]:
    """Positive exact cofactors for one step-three square progression."""

    anchor = owners[0]
    moduli = tuple(component**2 for component in components)
    residues = tuple(
        (-3 * (owner - anchor)) % modulus
        for owner, modulus in zip(owners, moduli, strict=True)
    )
    base, square_product = crt(residues, moduli)
    # One full modulus makes every residual positive, including the anchor.
    anchor_residual = base + square_product
    cofactors = tuple(
        (anchor_residual + 3 * (owner - anchor)) // component**2
        for owner, component in zip(owners, components, strict=True)
    )
    assert all(cofactor > 0 for cofactor in cofactors)
    return cofactors, anchor_residual


def verify_generalized_elimination(
    *, k: int, owners: Sequence[int], components: Sequence[int], loss: int
) -> dict[str, int | bool]:
    """Reproduce both compositions at every owner in one exact fixture."""

    if len(owners) < 3 or len(set(owners)) != len(owners):
        raise ValueError("expected at least three distinct owners")
    if len(owners) != len(components):
        raise ValueError("owners and components have different lengths")
    cofactors, anchor_residual = square_progression_fixture(owners, components)
    cofactor_product = prod(cofactors)
    gap = loss * prod(components)
    second_ok = True
    third_ok = True
    checks = 0
    for position, (owner, component, owner_cofactor) in enumerate(
        zip(owners, components, cofactors, strict=True)
    ):
        residual = owner_cofactor * component**2
        assert residual == anchor_residual + 3 * (owner - owners[0])
        opposite_components = components[:position] + components[position + 1 :]
        opposite_product = loss * prod(opposite_components)
        constant, linear, quadratic = local_taylor_coefficients(k, owner)[:3]
        second_local = (
            3 * constant * owner_cofactor - 4 * linear * opposite_product**2
        )
        third_local = (
            -3 * second_local
            + 20 * quadratic * component * opposite_product**3
        )
        opposite_cofactor_product = (
            cofactor_product // owner_cofactor
        )
        second_composed = multi_owner_second_obstruction(
            k=k,
            owners=owners,
            owner=owner,
            cofactor_product=cofactor_product,
            loss=loss,
        )
        third_composed = multi_owner_third_obstruction(
            k=k,
            owners=owners,
            owner=owner,
            cofactor_product=cofactor_product,
            loss=loss,
            gap=gap,
        )
        second_ok &= (
            opposite_cofactor_product * second_local - second_composed
        ) % abs(component) == 0
        third_ok &= (
            opposite_cofactor_product * third_local - third_composed
        ) % component**2 == 0
        checks += 1
    return {
        "owner_congruences_checked": checks,
        "all_second_compositions_hold": second_ok,
        "all_third_compositions_hold": third_ok,
    }


@lru_cache(maxsize=1)
def generalized_fixture_report() -> dict[str, int | bool]:
    families = 0
    congruences = 0
    second_ok = True
    third_ok = True
    # Positive and negative losses exercise every sign in the third formula;
    # factors 2 and 3 ensure no unit cancellation is hidden in the audit.
    losses = (-6, -3, -2, -1, 1, 2, 3, 6)
    for k in ROWS:
        for size in range(3, k + 1):
            owners = tuple(range(1, size + 1))
            components = COMPONENT_BASES[:size]
            for loss in losses:
                result = verify_generalized_elimination(
                    k=k, owners=owners, components=components, loss=loss
                )
                congruences += int(result["owner_congruences_checked"])
                second_ok &= bool(result["all_second_compositions_hold"])
                third_ok &= bool(result["all_third_compositions_hold"])
            families += 1
    return {
        "owner_families_checked": families,
        "signed_loss_fixtures": families * len(losses),
        "owner_congruences_checked": congruences,
        "all_second_compositions_hold": second_ok,
        "all_third_compositions_hold": third_ok,
    }


def block_product(k: int, n: int) -> int:
    return prod(n + index for index in range(1, k + 1))


def multi_owner_congruence_crt_witness(
    *, k: int, owners: tuple[int, ...], components: tuple[int, ...]
) -> dict[str, Any]:
    """Target-size non-solution satisfying every selected local lift.

    The free square-progression parameter is solved independently modulo
    every ``P_i^2`` so that the third local lift vanishes.  The second lift
    follows from the same formula modulo ``P_i``.  This is a route falsifier,
    not a counterexample to the block equation: its residuals fail the short
    window by an enormous exact margin.
    """

    if len(owners) < 4 or len(set(owners)) != len(owners):
        raise ValueError("expected at least four distinct owners")
    if len(owners) != len(components):
        raise ValueError("owners and components have different lengths")
    if not all(1 <= owner <= k for owner in owners):
        raise ValueError("owner outside row")
    if any(component <= 1 or gcd(component, 3) != 1 for component in components):
        raise ValueError("components must exceed one and be coprime to three")
    if any(
        gcd(components[left], components[right]) != 1
        for left in range(len(components))
        for right in range(left + 1, len(components))
    ):
        raise ValueError("components must be pairwise coprime")

    anchor = owners[0]
    square_moduli = tuple(component**2 for component in components)
    base_residues = tuple(
        (-3 * (owner - anchor)) % modulus
        for owner, modulus in zip(owners, square_moduli, strict=True)
    )
    base_x, square_product = crt(base_residues, square_moduli)
    gap = prod(components)
    assert square_product == gap**2

    parameter_residues: list[int] = []
    for owner, component in zip(owners, components, strict=True):
        shifted = base_x + 3 * (owner - anchor)
        assert shifted % component**2 == 0
        base_cofactor = shifted // component**2
        parameter_coefficient = gap**2 // component**2
        constant, linear, quadratic = local_taylor_coefficients(k, owner)[:3]
        opposite = gap // component
        second_constant = (
            3 * constant * base_cofactor - 4 * linear * opposite**2
        )
        third_constant = (
            -3 * second_constant + 20 * quadratic * component * opposite**3
        )
        third_linear = -9 * constant * parameter_coefficient
        modulus = component**2
        if gcd(third_linear, modulus) != 1:
            raise ValueError("component meets a local coefficient")
        parameter_residues.append(
            (-third_constant * pow(third_linear, -1, modulus)) % modulus
        )
    parameter, parameter_modulus = crt(parameter_residues, square_moduli)
    assert parameter_modulus == gap**2

    chosen_parameter: int | None = None
    for lift in range(3):
        candidate = parameter + gap**2 * lift
        candidate_x = base_x + gap**2 * candidate
        if (candidate_x + gap) % 3 == 0:
            chosen_parameter = candidate
            break
    if chosen_parameter is None:
        raise AssertionError("failed to reconstruct an integral n")
    anchor_residual = base_x + gap**2 * chosen_parameter
    n = (anchor_residual + gap) // 3 - anchor
    if n < 0:
        raise AssertionError("witness should be positive")

    cofactors: list[int] = []
    local_checks: list[dict[str, int | bool]] = []
    for owner, component in zip(owners, components, strict=True):
        residual = 3 * (n + owner) - gap
        assert residual > 0 and residual % component**2 == 0
        cofactor = residual // component**2
        cofactors.append(cofactor)
        opposite = gap // component
        constant, linear, quadratic = local_taylor_coefficients(k, owner)[:3]
        second = 3 * constant * cofactor - 4 * linear * opposite**2
        third = -3 * second + 20 * quadratic * component * opposite**3
        local_checks.append(
            {
                "owner": owner,
                "second_mod_component": second % component,
                "third_mod_component_square": third % component**2,
                "component_divides_lower_factor": (n + owner) % component == 0,
            }
        )

    cofactor_product = prod(cofactors)
    composed_checks: list[dict[str, int]] = []
    for owner, component in zip(owners, components, strict=True):
        second = multi_owner_second_obstruction(
            k=k,
            owners=owners,
            owner=owner,
            cofactor_product=cofactor_product,
            loss=1,
        )
        third = multi_owner_third_obstruction(
            k=k,
            owners=owners,
            owner=owner,
            cofactor_product=cofactor_product,
            loss=1,
            gap=gap,
        )
        composed_checks.append(
            {
                "owner": owner,
                "second_mod_component": second % component,
                "third_mod_component_square": third % component**2,
            }
        )
    residuals = [3 * (n + owner) - gap for owner in owners]
    return {
        "k": k,
        "owners": list(owners),
        "components": list(components),
        "gap": gap,
        "gap_digits": len(str(gap)),
        "gap_above_target": gap >= TARGET,
        "n": n,
        "n_digits": len(str(n)),
        "local_checks": local_checks,
        "composed_checks": composed_checks,
        "all_local_congruences_hold": all(
            check["second_mod_component"] == 0
            and check["third_mod_component_square"] == 0
            and bool(check["component_divides_lower_factor"])
            for check in local_checks
        ),
        "all_composed_obstructions_hold": all(
            check["second_mod_component"] == 0
            and check["third_mod_component_square"] == 0
            for check in composed_checks
        ),
        "block_equation_holds": (
            block_product(k, n + gap) == 4 * block_product(k, n)
        ),
        "short_window_holds": max(residuals) < ROWS[k] * gap,
        "maximum_residual_to_gap_floor": max(residuals) // gap,
    }


def positive_zero_slope(k: int, owners: Sequence[int], owner: int) -> Fraction:
    """The exact value of ``product(a_s)/g^2`` if ``O_owner=0``."""

    constant, linear = local_taylor_coefficients(k, owner)[:2]
    return Fraction(
        -4 * linear * (-3) ** (len(owners) - 2) * owner_delta(owner, owners),
        constant,
    )


def fraction_json(value: Fraction) -> dict[str, int]:
    return {"numerator": value.numerator, "denominator": value.denominator}


@lru_cache(maxsize=1)
def target_subset_report() -> dict[str, Any]:
    subset_count = 0
    slope_count = 0
    positive_count = 0
    maximum_simultaneous = 0
    collision_subset_count = 0
    maximum_positive: Fraction | None = None
    minimum_margin: Fraction | None = None
    by_size: dict[int, dict[str, int | dict[str, int]]] = {}
    collision_examples: list[dict[str, Any]] = []
    for k in ROWS:
        for size in range(4, k + 1):
            local_subsets = 0
            local_positive = 0
            local_maximum: Fraction | None = None
            for owners in combinations(range(1, k + 1), size):
                subset_count += 1
                local_subsets += 1
                slopes = [positive_zero_slope(k, owners, owner) for owner in owners]
                slope_count += size
                positives = [slope for slope in slopes if slope > 0]
                positive_count += len(positives)
                local_positive += len(positives)
                if positives:
                    counts = {slope: positives.count(slope) for slope in set(positives)}
                    simultaneous = max(counts.values())
                    maximum_simultaneous = max(maximum_simultaneous, simultaneous)
                    if simultaneous > 1:
                        collision_subset_count += 1
                    if simultaneous > 1 and len(collision_examples) < 10:
                        collision_examples.append(
                            {
                                "k": k,
                                "owners": list(owners),
                                "slopes": [fraction_json(slope) for slope in positives],
                            }
                        )
                    for slope in positives:
                        maximum_positive = (
                            slope
                            if maximum_positive is None
                            else max(maximum_positive, slope)
                        )
                        local_maximum = (
                            slope if local_maximum is None else max(local_maximum, slope)
                        )
                        # From X_s>5d and d=g*product(P_s):
                        # product(a_s)/g^2 > 5^size*d^(size-2).
                        target_lower = Fraction(5**size * TARGET ** (size - 2), 1)
                        margin = target_lower / slope
                        minimum_margin = (
                            margin if minimum_margin is None else min(minimum_margin, margin)
                        )
            entry = by_size.setdefault(
                size,
                {
                    "subset_count": 0,
                    "positive_slope_count": 0,
                    "maximum_positive_zero_slope": {"numerator": 0, "denominator": 1},
                },
            )
            entry["subset_count"] = int(entry["subset_count"]) + local_subsets
            entry["positive_slope_count"] = (
                int(entry["positive_slope_count"]) + local_positive
            )
            prior = Fraction(
                int(entry["maximum_positive_zero_slope"]["numerator"]),  # type: ignore[index]
                int(entry["maximum_positive_zero_slope"]["denominator"]),  # type: ignore[index]
            )
            if local_maximum is not None and local_maximum > prior:
                entry["maximum_positive_zero_slope"] = fraction_json(local_maximum)
    assert maximum_positive is not None and minimum_margin is not None
    expected_subsets = sum(
        sum(comb(k, size) for size in range(4, k + 1)) for k in ROWS
    )
    expected_slopes = sum(
        sum(size * comb(k, size) for size in range(4, k + 1)) for k in ROWS
    )
    assert subset_count == expected_subsets
    assert slope_count == expected_slopes
    return {
        "subset_count": subset_count,
        "owner_slope_count": slope_count,
        "positive_slope_count": positive_count,
        "maximum_simultaneous_positive_zeros": maximum_simultaneous,
        "subsets_with_positive_zero_slope_collision": collision_subset_count,
        "collision_examples": collision_examples,
        "maximum_positive_zero_slope": fraction_json(maximum_positive),
        "minimum_target_lower_bound_over_positive_slope": fraction_json(
            minimum_margin
        ),
        "all_positive_zero_slopes_excluded_at_target": minimum_margin > 1,
        "by_owner_count": {str(size): value for size, value in sorted(by_size.items())},
    }


def exponent_selection_report() -> dict[str, Any]:
    """Sharp product-only consequences and an exact selection counterfamily."""

    # At most fifteen nonzero owner buckets.  Sorting their logarithmic sizes
    # gives product(top three) >= (d/g)^(3/t) >= (d/g)^(1/5).
    # This still permits the complement to have exponent 4/5.
    exponent_family = [Fraction(1, 4)] * 4
    # Exact integer realization for the unbounded-complement claim:
    # P=(2^N,3^N,5^N,7^N), d=210^N.  These are pairwise coprime and
    # P_s^2 <= d, while the complement to any three is at least 2^N.
    exact_family = {
        "components": ["2^N", "3^N", "5^N", "7^N"],
        "gap": "210^N",
        "pairwise_coprime": True,
        "every_component_square_at_most_gap": True,
        "minimum_three_selection_complement": "2^N",
    }
    return {
        "largest_three_product_lower_exponent": Fraction(1, 5),
        "complement_upper_exponent": Fraction(4, 5),
        "explicit_four_owner_counterfamily": exponent_family,
        "exact_integer_selection_counterfamily": exact_family,
        "bounded_complement_follows": False,
        "nonzero_obstruction_owner_bound_exponent": {
            str(size): size - 2 for size in range(4, 16)
        },
        "product_of_obstructions_exponent_deficit": {
            str(size): size * (size - 2) - 1 for size in range(4, 16)
        },
    }


def _json_ready(value: Any) -> Any:
    if isinstance(value, Fraction):
        return fraction_json(value)
    if isinstance(value, dict):
        return {key: _json_ready(item) for key, item in value.items()}
    if isinstance(value, (list, tuple)):
        return [_json_ready(item) for item in value]
    return value


def report() -> dict[str, Any]:
    return {
        "rows": ROWS,
        "loss_budgets": LOSS_BUDGETS,
        "generalized_composition": generalized_fixture_report(),
        "target_subset_scan": target_subset_report(),
        "selection_and_scaling": exponent_selection_report(),
        "four_owner_congruence_only_witness": multi_owner_congruence_crt_witness(
            k=5,
            owners=(1, 2, 4, 5),
            components=(101**16, 103**16, 107**16, 109**16),
        ),
        "route_verdict": (
            "in a full bounded-loss t-owner decomposition every second "
            "obstruction is nonzero at target size, but its exact "
            "archimedean size grows as d^(t-2); neither the divisibilities "
            "nor top-three selection closes any t>=4 branch"
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args()
    print(
        json.dumps(
            _json_ready(report()),
            indent=2 if args.pretty else None,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
