#!/usr/bin/env python3
"""Exact quotient/lattice diagnostics for the Erdős 686 three-owner core.

This file deliberately imports no earlier campaign verifier.  It reconstructs
the signed local Taylor coefficients, the cyclic second/third/fourth
obstructions, and the new third-quotient restrictions from integer arithmetic.

The computations do not claim to close the three-owner branch.  They first
look for a target-size short-window pseudo-witness.  Failing that, they record
the proper consequences of the fourth lift which any such witness must obey.
"""

from __future__ import annotations

import argparse
import json
from array import array
from functools import cache, reduce
from itertools import combinations, permutations, product
from math import gcd, isqrt, prod
from typing import Any, Iterable, Sequence


ROWS: dict[int, tuple[int, int]] = {
    5: (14, 108),
    7: (17, 1_620),
    9: (23, 136_080),
    11: (26, 1_224_720),
    13: (29, 242_494_560),
    15: (35, 18_914_575_680),
}
TARGET = 10**120


def block_product(k: int, n: int) -> int:
    return prod(n + index for index in range(1, k + 1))


@cache
def local_coefficients(k: int, owner: int) -> tuple[int, ...]:
    """Coefficients of ``prod_{j != owner}(z+j-owner)``, low first."""

    if not 1 <= owner <= k:
        raise ValueError("owner outside row")
    coefficients = [1]
    for column in range(1, k + 1):
        if column == owner:
            continue
        offset = column - owner
        result = [0] * (len(coefficients) + 1)
        for degree, coefficient in enumerate(coefficients):
            result[degree] += offset * coefficient
            result[degree + 1] += coefficient
        coefficients = result
    return tuple(coefficients)


def owner_geometry(owner: int, left: int, right: int) -> tuple[int, int]:
    return (owner - left) * (owner - right), 2 * owner - left - right


def second_obstruction(
    k: int, owner: int, left: int, right: int, t: int, g: int
) -> int:
    constant, linear = local_coefficients(k, owner)[:2]
    delta, _ = owner_geometry(owner, left, right)
    return 3 * (constant * t - 12 * linear * g**2 * delta)


def third_obstruction(
    k: int, owner: int, left: int, right: int, t: int, g: int, d: int
) -> int:
    quadratic = local_coefficients(k, owner)[2]
    delta, _ = owner_geometry(owner, left, right)
    return (
        -3 * second_obstruction(k, owner, left, right, t, g)
        + 180 * quadratic * g**2 * delta * d
    )


def fourth_correction(
    k: int, owner: int, left: int, right: int, t: int, g: int
) -> int:
    _, linear, quadratic, cubic = local_coefficients(k, owner)[:4]
    delta, sigma = owner_geometry(owner, left, right)
    return (
        -9 * linear * t**2
        - 108 * linear * t * g**2 * sigma
        + 324 * quadratic * t * g**2 * delta
        + 6804 * cubic * g**4 * delta**2
    )


def reduced_fourth_coefficient(
    k: int, owner: int, left: int, right: int
) -> int:
    """Fixed coefficient remaining after eliminating ``t`` with ``O_s``."""

    constant, linear, quadratic, cubic = local_coefficients(k, owner)[:4]
    delta, sigma = owner_geometry(owner, left, right)
    middle = -108 * linear * sigma + 324 * quadratic * delta
    return 108 * delta * (
        -108 * linear**3 * delta
        + constant * linear * middle
        + 567 * constant**2 * cubic * delta
    )


def reduced_fourth_multiplier(
    k: int, owner: int, left: int, right: int, t: int, g: int
) -> int:
    constant, linear, quadratic = local_coefficients(k, owner)[:3]
    delta, sigma = owner_geometry(owner, left, right)
    middle = -108 * linear * sigma + 324 * quadratic * delta
    return (
        -9 * linear * (3 * constant * t + 36 * linear * g**2 * delta)
        + 3 * constant * g**2 * middle
    )


def verify_reduced_fourth_identity(
    k: int,
    owner: int,
    left: int,
    right: int,
    t: int,
    g: int,
) -> bool:
    """Check ``9 C^2 J = multiplier*O + K*g^4`` exactly."""

    constant = local_coefficients(k, owner)[0]
    lhs = 9 * constant**2 * fourth_correction(
        k, owner, left, right, t, g
    )
    rhs = reduced_fourth_multiplier(k, owner, left, right, t, g) * (
        second_obstruction(k, owner, left, right, t, g)
    ) + reduced_fourth_coefficient(k, owner, left, right) * g**4
    return lhs == rhs


def lattice_weights(
    k: int, indices: tuple[int, int, int]
) -> tuple[tuple[int, int, int], int]:
    """Primitive cross product annihilating the ``t`` and ``g^2*d`` terms."""

    rows: list[tuple[int, int, int]] = []
    for owner in indices:
        left, right = (index for index in indices if index != owner)
        constant, linear, quadratic = local_coefficients(k, owner)[:3]
        delta, _ = owner_geometry(owner, left, right)
        rows.append((-9 * constant, 180 * quadratic * delta, 108 * linear * delta))
    (a1, b1, _), (a2, b2, _), (a3, b3, _) = rows
    raw = (
        a2 * b3 - a3 * b2,
        a3 * b1 - a1 * b3,
        a1 * b2 - a2 * b1,
    )
    common = reduce(gcd, (abs(value) for value in raw))
    if common == 0:
        raise AssertionError("coefficient rows unexpectedly have rank below two")
    weights = tuple(value // common for value in raw)
    gamma = sum(weight * row[2] for weight, row in zip(weights, rows, strict=True))
    return weights, gamma


def third_quotient_bound_coefficient(
    k: int, owner: int, left: int, right: int, window: int
) -> int:
    """Coefficient ``B`` in the proper bound ``5|z_s| < B*g^2*a_s``."""

    constant, linear, quadratic = local_coefficients(k, owner)[:3]
    delta, _ = owner_geometry(owner, left, right)
    return (
        9 * abs(constant) * window**3
        + 108 * abs(linear) * abs(delta)
        + 180 * abs(quadratic) * abs(delta)
    )


def local_second_third_fourth(
    *, k: int, owner: int, component: int, cofactor: int, opposite: int
) -> tuple[int, int, int]:
    constant, linear, quadratic, cubic = local_coefficients(k, owner)[:4]
    second = 3 * constant * cofactor - 4 * linear * opposite**2
    third = -3 * second + 20 * quadratic * component * opposite**3
    fourth = 3 * third + component**2 * (
        -9 * linear * cofactor**2
        + 36 * quadratic * cofactor * opposite**2
        + 84 * cubic * opposite**4
    )
    return second, third, fourth


def validate_short_tuple(
    *,
    k: int,
    indices: tuple[int, int, int],
    components: tuple[int, int, int],
    g: int,
    anchor_residual: int,
) -> dict[str, Any]:
    """Validate one exact square/local/composed fourth-lift tuple."""

    if len(set(indices)) != 3 or any(not 1 <= index <= k for index in indices):
        raise ValueError("bad owner triple")
    if any(component <= 1 for component in components):
        raise ValueError("components must be nontrivial")
    if any(
        gcd(components[i], components[j]) != 1
        for i, j in combinations(range(3), 2)
    ):
        raise ValueError("components must be pairwise coprime")
    if g <= 0:
        raise ValueError("loss must be positive")

    anchor = indices[0]
    residuals = tuple(
        anchor_residual + 3 * (index - anchor) for index in indices
    )
    cofactors: list[int] = []
    for residual, component in zip(residuals, components, strict=True):
        if residual <= 0 or residual % component**2:
            raise ValueError("square residual mismatch")
        cofactors.append(residual // component**2)
    a, b, c = cofactors
    t = a * b * c
    d = g * prod(components)
    window, loss_bound = ROWS[k]
    n_integral = (anchor_residual + d) % 3 == 0
    n = (anchor_residual + d) // 3 - anchor if n_integral else -1
    quotient_set = {residual // d for residual in residuals}
    common_quotient = residuals[0] // d
    remainder_quotients = tuple(
        (residual - common_quotient * d) // component
        for residual, component in zip(residuals, components, strict=True)
    )
    quotient_normalization = (
        len(quotient_set) == 1
        and all(
            residual - common_quotient * d == component * remainder_quotient
            and cofactor * component
            == common_quotient * (d // component) + remainder_quotient
            for residual, component, cofactor, remainder_quotient in zip(
                residuals,
                components,
                cofactors,
                remainder_quotients,
                strict=True,
            )
        )
        and all(
            components[left] * remainder_quotients[left]
            - components[right] * remainder_quotients[right]
            == 3 * (indices[left] - indices[right])
            for left, right in combinations(range(3), 2)
        )
    )

    local_rows: list[dict[str, Any]] = []
    composed_rows: list[dict[str, Any]] = []
    quotients: list[int] = []
    for position, (owner, component, cofactor) in enumerate(
        zip(indices, components, cofactors, strict=True)
    ):
        other_positions = tuple(pos for pos in range(3) if pos != position)
        left_position, right_position = other_positions
        left = indices[left_position]
        right = indices[right_position]
        opposite = d // component
        second, third, fourth = local_second_third_fourth(
            k=k,
            owner=owner,
            component=component,
            cofactor=cofactor,
            opposite=opposite,
        )
        composed_second = second_obstruction(k, owner, left, right, t, g)
        composed_third = third_obstruction(k, owner, left, right, t, g, d)
        correction = fourth_correction(k, owner, left, right, t, g)
        left_cofactor = cofactors[left_position]
        right_cofactor = cofactors[right_position]
        composed_fourth = (
            3 * left_cofactor * right_cofactor * composed_third
            + component**2 * correction
        )
        quotient = (
            composed_third // component**2
            if composed_third % component**2 == 0
            else 0
        )
        quotients.append(quotient)
        constant = local_coefficients(k, owner)[0]
        reduced = (
            27 * constant**2 * left_cofactor * right_cofactor * quotient
            + reduced_fourth_coefficient(k, owner, left, right) * g**4
        )
        overlap_left = gcd(component, left_cofactor)
        overlap_right = gcd(component, right_cofactor)
        delta_left = 3 * (owner - left)
        delta_right = 3 * (owner - right)
        bound_coefficient = third_quotient_bound_coefficient(
            k, owner, left, right, window
        )
        local_rows.append(
            {
                "owner": owner,
                "component": component,
                "second_remainder": second % component,
                "third_remainder": third % component**2,
                "fourth_remainder": fourth % component**3,
                "lower_factor_remainder": (
                    (n + owner) % component if n_integral else None
                ),
            }
        )
        composed_rows.append(
            {
                "owner": owner,
                "second_remainder": composed_second % component,
                "third_remainder": composed_third % component**2,
                "fourth_remainder": composed_fourth % component**3,
                "third_quotient": quotient,
                "reduced_fourth_remainder": reduced % component,
                "component_quotient_gcd": gcd(component, abs(quotient)),
                "component_quotient_gcd_divides_fixed": (
                    reduced_fourth_coefficient(k, owner, left, right) * g**4
                )
                % gcd(component, abs(quotient))
                == 0,
                "left_overlap": overlap_left,
                "left_overlap_divides_offset": abs(delta_left) % overlap_left == 0,
                "right_overlap": overlap_right,
                "right_overlap_divides_offset": abs(delta_right) % overlap_right == 0,
                "product_overlap_divides_offset_product": (
                    9 * abs((owner - left) * (owner - right))
                )
                % gcd(component, left_cofactor * right_cofactor)
                == 0,
                "quotient_bound": (
                    5 * abs(quotient)
                    < bound_coefficient * g**2 * cofactor
                ),
            }
        )

    weights, gamma = lattice_weights(k, indices)
    lattice_lhs = sum(
        weight * component**2 * quotient
        for weight, component, quotient in zip(
            weights, components, quotients, strict=True
        )
    )
    block_equation = (
        n_integral
        and n >= 0
        and block_product(k, n + d) == 4 * block_product(k, n)
    )
    return {
        "k": k,
        "indices": list(indices),
        "components": list(components),
        "g": g,
        "d": d,
        "gap_digits": len(str(d)),
        "residuals": list(residuals),
        "cofactors": cofactors,
        "common_floor_quotient": common_quotient,
        "common_floor_quotient_holds": len(quotient_set) == 1,
        "quotient_remainders": [residual % d for residual in residuals],
        "component_remainder_quotients": list(remainder_quotients),
        "quotient_normalization": quotient_normalization,
        "n": n if n_integral else None,
        "n_integral": n_integral,
        "loss_within_row_budget": g <= loss_bound,
        "lower_window": all(5 * d < residual for residual in residuals),
        "upper_window": all(residual < window * d for residual in residuals),
        "local_rows": local_rows,
        "composed_rows": composed_rows,
        "all_local_lifts": all(
            row["second_remainder"] == 0
            and row["third_remainder"] == 0
            and row["fourth_remainder"] == 0
            and row["lower_factor_remainder"] == 0
            for row in local_rows
        ),
        "all_composed_lifts": all(
            row["second_remainder"] == 0
            and row["third_remainder"] == 0
            and row["fourth_remainder"] == 0
            and row["reduced_fourth_remainder"] == 0
            and row["component_quotient_gcd_divides_fixed"]
            and row["left_overlap_divides_offset"]
            and row["right_overlap_divides_offset"]
            and row["product_overlap_divides_offset_product"]
            for row in composed_rows
        ),
        "all_short_quotient_bounds": all(
            row["quotient_bound"] for row in composed_rows
        ),
        "lattice_weights": list(weights),
        "lattice_gamma": gamma,
        "lattice_identity": lattice_lhs == g**2 * gamma,
        "block_equation": block_equation,
    }


def coefficient_audit() -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    total_ordered = 0
    total_center = 0
    total_reflected = 0
    total_zero_reduced = 0
    total_lattice_triples = 0
    total_zero_weight_components = 0
    minimum_lattice_gamma: int | None = None
    maximum_lattice_gamma = 0
    maximum_reduced = 0
    maximum_reduced_case: tuple[int, int, int, int] | None = None
    minimum_nonzero_reduced: int | None = None
    for k, (window, _) in ROWS.items():
        ordered = 0
        centers = 0
        reflected = 0
        zero_reduced = 0
        row_max_bound = 0
        center = (k + 1) // 2
        for owner, left, right in permutations(range(1, k + 1), 3):
            ordered += 1
            if owner == center:
                centers += 1
            if owner + left == k + 1 or owner + right == k + 1 or left + right == k + 1:
                reflected += 1
            reduced = reduced_fourth_coefficient(k, owner, left, right)
            if reduced == 0:
                zero_reduced += 1
                if owner != center:
                    raise AssertionError("noncentral reduced coefficient vanished")
            else:
                absolute = abs(reduced)
                if minimum_nonzero_reduced is None:
                    minimum_nonzero_reduced = absolute
                else:
                    minimum_nonzero_reduced = min(minimum_nonzero_reduced, absolute)
                if absolute > maximum_reduced:
                    maximum_reduced = absolute
                    maximum_reduced_case = (k, owner, left, right)
            bound = third_quotient_bound_coefficient(k, owner, left, right, window)
            row_max_bound = max(row_max_bound, bound)
            weights, _ = lattice_weights(k, tuple(sorted((owner, left, right))))
            if weights == (0, 0, 0):
                raise AssertionError("zero lattice vector")
        expected_center = (k - 1) * (k - 2)
        if zero_reduced != expected_center:
            raise AssertionError((k, zero_reduced, expected_center))
        row_lattice_triples = 0
        row_zero_weight_components = 0
        for indices in combinations(range(1, k + 1), 3):
            weights, gamma = lattice_weights(k, indices)
            row_lattice_triples += 1
            row_zero_weight_components += sum(weight == 0 for weight in weights)
            if gamma == 0:
                raise AssertionError((k, indices, weights, gamma))
            gamma_absolute = abs(gamma)
            if minimum_lattice_gamma is None:
                minimum_lattice_gamma = gamma_absolute
            else:
                minimum_lattice_gamma = min(
                    minimum_lattice_gamma, gamma_absolute
                )
            maximum_lattice_gamma = max(maximum_lattice_gamma, gamma_absolute)
        rows.append(
            {
                "k": k,
                "ordered_distinct_owner_triples": ordered,
                "center_owner_occurrences": centers,
                "reflected_triple_occurrences": reflected,
                "zero_reduced_coefficients": zero_reduced,
                "rank_two_lattice_triples": row_lattice_triples,
                "zero_lattice_weight_components": row_zero_weight_components,
                "maximum_quotient_bound_coefficient": row_max_bound,
            }
        )
        total_ordered += ordered
        total_center += centers
        total_reflected += reflected
        total_zero_reduced += zero_reduced
        total_lattice_triples += row_lattice_triples
        total_zero_weight_components += row_zero_weight_components
    return {
        "rows": rows,
        "ordered_distinct_owner_triples": total_ordered,
        "center_owner_occurrences": total_center,
        "reflected_triple_occurrences": total_reflected,
        "zero_reduced_coefficients": total_zero_reduced,
        "all_zeros_are_centers": True,
        "rank_two_lattice_triples": total_lattice_triples,
        "all_lattice_gammas_nonzero": True,
        "zero_lattice_weight_components": total_zero_weight_components,
        "minimum_lattice_gamma": minimum_lattice_gamma,
        "maximum_lattice_gamma": maximum_lattice_gamma,
        "minimum_nonzero_reduced_coefficient": minimum_nonzero_reduced,
        "maximum_reduced_coefficient": maximum_reduced,
        "maximum_reduced_case": maximum_reduced_case,
    }


def signed_identity_grid() -> dict[str, Any]:
    checks = 0
    for k in (5, 7, 9):
        for owner, left, right in ((1, 2, k), ((k + 1) // 2, 1, k), (k, 1, 2)):
            for t, g in product(range(-8, 9), range(-4, 5)):
                if not verify_reduced_fourth_identity(k, owner, left, right, t, g):
                    raise AssertionError((k, owner, left, right, t, g))
                checks += 1
    return {"signed_reduced_fourth_identities": checks, "all_hold": True}


def two_zero_quotient_scan() -> dict[str, Any]:
    """Finite numeric gate when two noncentral third quotients vanish.

    If the zero quotients occur at components ``P,Q``, their reduced fourth
    congruences put both into ``L*g^4`` for the exact coefficient LCM ``L``.
    The three-term lattice identity gives

    ``R^2*abs(w_R) <= abs(gamma)*g^2``.

    The Lean packing theorem then bounds

    ``d^2*abs(w_R) <= L^2*abs(gamma)*g^12``.
    """

    rows: list[dict[str, Any]] = []
    total_cases = 0
    total_closed = 0
    for k, (_, loss_bound) in ROWS.items():
        center = (k + 1) // 2
        row_cases = 0
        row_closed = 0
        zero_weight_contradictions = 0
        numeric_closures = 0
        minimum_margin: int | None = None
        first_open: dict[str, Any] | None = None
        for indices in combinations(range(1, k + 1), 3):
            weights, gamma = lattice_weights(k, indices)
            coefficients = []
            for owner in indices:
                left, right = (index for index in indices if index != owner)
                coefficients.append(
                    abs(reduced_fourth_coefficient(k, owner, left, right))
                )
            for zeros in combinations(range(3), 2):
                if any(indices[position] == center for position in zeros):
                    continue
                row_cases += 1
                remaining = ({0, 1, 2} - set(zeros)).pop()
                weight = abs(weights[remaining])
                if weight == 0:
                    # With both other quotients zero, the lattice left side
                    # is zero, contrary to gamma != 0 and g > 0.
                    row_closed += 1
                    zero_weight_contradictions += 1
                    continue
                first = coefficients[zeros[0]]
                second = coefficients[zeros[1]]
                if first == 0 or second == 0:
                    raise AssertionError("noncentral reduced coefficient vanished")
                coefficient_lcm = first // gcd(first, second) * second
                majorant = (
                    coefficient_lcm**2
                    * abs(gamma)
                    * loss_bound**12
                )
                cutoff_side = weight * TARGET**2
                if majorant < cutoff_side:
                    row_closed += 1
                    numeric_closures += 1
                    margin = cutoff_side // majorant
                    if minimum_margin is None:
                        minimum_margin = margin
                    else:
                        minimum_margin = min(minimum_margin, margin)
                elif first_open is None:
                    first_open = {
                        "indices": list(indices),
                        "zero_positions": list(zeros),
                        "remaining_weight": weight,
                        "coefficient_lcm": coefficient_lcm,
                        "gamma": abs(gamma),
                        "majorant_digits": len(str(majorant)),
                        "cutoff_side_digits": len(str(cutoff_side)),
                    }
        rows.append(
            {
                "k": k,
                "noncentral_two_zero_cases": row_cases,
                "closed_cases": row_closed,
                "zero_weight_contradictions": zero_weight_contradictions,
                "numeric_closures": numeric_closures,
                "minimum_numeric_margin_floor": minimum_margin,
                "first_open_case": first_open,
            }
        )
        total_cases += row_cases
        total_closed += row_closed
    return {
        "rows": rows,
        "noncentral_two_zero_cases": total_cases,
        "closed_cases": total_closed,
        "all_noncentral_two_zero_cases_closed_for_k_le_13": all(
            row["closed_cases"] == row["noncentral_two_zero_cases"]
            for row in rows
            if row["k"] <= 13
        ),
        "k15_closed_cases": next(
            row["closed_cases"] for row in rows if row["k"] == 15
        ),
        "k15_total_cases": next(
            row["noncentral_two_zero_cases"]
            for row in rows
            if row["k"] == 15
        ),
    }


def _square_divisor_roots(limit: int) -> tuple[array, Any]:
    spf = array("I", range(limit + 7))
    for prime in range(2, isqrt(limit + 6) + 1):
        if spf[prime] == prime:
            for multiple in range(prime * prime, limit + 7, prime):
                if spf[multiple] == multiple:
                    spf[multiple] = prime

    def roots(value: int) -> list[int]:
        divisors = [1]
        while value > 1:
            prime = spf[value]
            exponent = 0
            while value % prime == 0:
                value //= prime
                exponent += 1
            half = exponent // 2
            if half:
                base = list(divisors)
                prime_power = 1
                for _ in range(half):
                    prime_power *= prime
                    divisors.extend(divisor * prime_power for divisor in base)
        return divisors[1:]

    return spf, roots


def exact_small_short_search(limit: int = 200_000) -> dict[str, Any]:
    """Exhaust `k=5`, owners `(1,2,3)` through an exact residual limit."""

    _, roots = _square_divisor_roots(limit)
    k = 5
    indices = (1, 2, 3)
    window, loss_bound = ROWS[k]
    offsets = (0, 3, 6)
    hits: list[dict[str, Any]] = []
    tested_losses = 0
    for anchor_residual in range(1, limit + 1):
        root_lists = [roots(anchor_residual + offset) for offset in offsets]
        if any(not values for values in root_lists):
            continue
        for p in root_lists[0]:
            for q in root_lists[1]:
                if gcd(p, q) != 1:
                    continue
                for r in root_lists[2]:
                    if gcd(p, r) != 1 or gcd(q, r) != 1:
                        continue
                    component_product = p * q * r
                    lower_g = max(
                        1,
                        (anchor_residual + offsets[-1])
                        // (window * component_product)
                        + 1,
                    )
                    upper_g = min(
                        loss_bound,
                        (anchor_residual - 1) // (5 * component_product),
                    )
                    for g in range(lower_g, upper_g + 1):
                        tested_losses += 1
                        d = g * component_product
                        if (anchor_residual + d) % 3:
                            continue
                        result = validate_short_tuple(
                            k=k,
                            indices=indices,
                            components=(p, q, r),
                            g=g,
                            anchor_residual=anchor_residual,
                        )
                        if result["all_local_lifts"] and result["all_composed_lifts"]:
                            hits.append(result)
    if not hits:
        raise AssertionError("short fourth-lift fixture search was empty")
    largest = max(hits, key=lambda result: result["d"])
    return {
        "limit": limit,
        "tested_loss_values": tested_losses,
        "surviving_short_fourth_lift_tuples": len(hits),
        "first_survivor": {
            key: hits[0][key]
            for key in ("components", "g", "d", "residuals", "cofactors", "n")
        },
        "largest_gap_survivor": {
            key: largest[key]
            for key in ("components", "g", "d", "residuals", "cofactors", "n")
        },
        "all_below_target": all(result["d"] < TARGET for result in hits),
        "all_fail_block_equation": all(not result["block_equation"] for result in hits),
    }


def crt(residues: Sequence[int], moduli: Sequence[int]) -> tuple[int, int]:
    if not residues or len(residues) != len(moduli):
        raise ValueError("bad CRT input")
    modulus = prod(moduli)
    value = 0
    for residue, local_modulus in zip(residues, moduli, strict=True):
        complement = modulus // local_modulus
        if gcd(complement, local_modulus) != 1:
            raise ValueError("CRT moduli not coprime")
        value += residue * complement * pow(complement, -1, local_modulus)
    return value % modulus, modulus


def target_size_congruence_family(exponent: int = 20) -> dict[str, Any]:
    """Independently lift the known unbounded local family through order four."""

    k = 5
    indices = (1, 2, 4)
    components = (101**exponent, 103**exponent, 107**exponent)
    anchor = indices[0]
    d = prod(components)
    square_moduli = tuple(component**2 for component in components)
    base_x, square_product = crt(
        tuple(
            (-3 * (index - anchor)) % modulus
            for index, modulus in zip(indices, square_moduli, strict=True)
        ),
        square_moduli,
    )
    if square_product != d**2:
        raise AssertionError

    third_residues: list[int] = []
    for index, component in zip(indices, components, strict=True):
        shifted = base_x + 3 * (index - anchor)
        cofactor = shifted // component**2
        parameter_coefficient = d**2 // component**2
        opposite = d // component
        second, third, _ = local_second_third_fourth(
            k=k,
            owner=index,
            component=component,
            cofactor=cofactor,
            opposite=opposite,
        )
        _ = second
        derivative = -9 * local_coefficients(k, index)[0] * parameter_coefficient
        modulus = component**2
        third_residues.append((-third * pow(derivative, -1, modulus)) % modulus)
    third_parameter, modulus = crt(third_residues, square_moduli)
    if modulus != d**2:
        raise AssertionError

    fourth_residues: list[int] = []
    for index, component in zip(indices, components, strict=True):
        residual = base_x + d**2 * third_parameter + 3 * (index - anchor)
        cofactor = residual // component**2
        opposite = d // component
        _, _, fourth = local_second_third_fourth(
            k=k,
            owner=index,
            component=component,
            cofactor=cofactor,
            opposite=opposite,
        )
        if fourth % component**2:
            raise AssertionError
        quotient_residue = (fourth // component**2) % component
        derivative = -27 * local_coefficients(k, index)[0] * opposite**4
        fourth_residues.append(
            (-quotient_residue * pow(derivative, -1, component)) % component
        )
    fourth_parameter_local, modulus = crt(fourth_residues, components)
    if modulus != d:
        raise AssertionError
    fourth_parameter = third_parameter + d**2 * fourth_parameter_local
    chosen_parameter: int | None = None
    for lift in range(3):
        candidate = fourth_parameter + d**3 * lift
        if (base_x + d**2 * candidate + d) % 3 == 0:
            chosen_parameter = candidate
            break
    if chosen_parameter is None:
        raise AssertionError
    anchor_residual = base_x + d**2 * chosen_parameter
    result = validate_short_tuple(
        k=k,
        indices=indices,
        components=components,
        g=1,
        anchor_residual=anchor_residual,
    )
    return {
        "exponent": exponent,
        "gap_digits": result["gap_digits"],
        "gap_at_least_target": result["d"] >= TARGET,
        "all_local_lifts": result["all_local_lifts"],
        "all_composed_lifts": result["all_composed_lifts"],
        "lower_window": result["lower_window"],
        "upper_window": result["upper_window"],
        "residual_to_gap_floor_digits": len(
            str(result["common_floor_quotient"])
        ),
        "block_equation": result["block_equation"],
        "lattice_identity": result["lattice_identity"],
    }


def boundary_audit() -> dict[str, Any]:
    telescopes = []
    for k, n in ((9, 2), (15, 4)):
        if block_product(k, n + 1) != 4 * block_product(k, n):
            raise AssertionError("telescope reproduction failed")
        telescopes.append({"k": k, "n": n, "d": 1})
    small = validate_short_tuple(
        k=5,
        indices=(1, 2, 3),
        components=(3, 5, 2),
        g=24,
        anchor_residual=4_122,
    )
    if not small["all_local_lifts"] or not small["all_composed_lifts"]:
        raise AssertionError("small-prime fourth fixture failed")
    return {
        "d_eq_one_telescopes": telescopes,
        "small_prime_fixture": {
            key: small[key]
            for key in (
                "components",
                "g",
                "d",
                "residuals",
                "cofactors",
                "lower_window",
                "upper_window",
                "all_local_lifts",
                "all_composed_lifts",
                "block_equation",
            )
        },
        "includes_owner_component_two": 2 in small["components"],
        "includes_owner_component_three": 3 in small["components"],
    }


def report(search_limit: int = 200_000) -> dict[str, Any]:
    target_family = target_size_congruence_family()
    return {
        "boundaries": boundary_audit(),
        "coefficient_audit": coefficient_audit(),
        "signed_identity_grid": signed_identity_grid(),
        "two_zero_quotient_scan": two_zero_quotient_scan(),
        "small_short_search": exact_small_short_search(search_limit),
        "target_size_congruence_family": target_family,
        "target_size_short_window_pseudo_witness_found": False,
        "route_verdict": (
            "No target-size short-window pseudo-witness was found.  The exact "
            "target-size Hensel family still fails the short window.  The new "
            "quotient congruence, quotient gcd bound, and three-term lattice "
            "identity are proper restrictions, not a closure of the branch."
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--pretty", action="store_true")
    parser.add_argument("--search-limit", type=int, default=200_000)
    args = parser.parse_args()
    print(
        json.dumps(
            report(args.search_limit),
            indent=2 if args.pretty else None,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
