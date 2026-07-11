#!/usr/bin/env python3
"""Independent hostile verifier for the Erdős 686 fourth local lift.

This module imports no producer or earlier campaign verifier.  Taylor
coefficients are reconstructed from reciprocal elementary symmetric sums.
All checks use Python integers and ``Fraction`` only.
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
ROWS = {5: 14, 7: 17, 9: 23, 11: 26, 13: 29, 15: 35}
CRT_INDICES = (1, 2, 4)
CRT_BASES = (101, 103, 107)


def block_product(k: int, n: int) -> int:
    return prod(n + column for column in range(1, k + 1))


@cache
def local_coefficients(k: int, owner: int) -> tuple[int, int, int, int]:
    """Return the first four coefficients by reciprocal symmetric sums."""

    if owner not in range(1, k + 1):
        raise ValueError("owner outside row")
    offsets = tuple(column - owner for column in range(1, k + 1) if column != owner)
    constant = prod(offsets)
    result = [constant]
    for degree in range(1, 4):
        reciprocal_sum = sum(
            (
                Fraction(1, prod(offsets[position] for position in chosen))
                for chosen in combinations(range(len(offsets)), degree)
            ),
            Fraction(),
        )
        coefficient = constant * reciprocal_sum
        if coefficient.denominator != 1:
            raise AssertionError("Taylor coefficient was not integral")
        result.append(coefficient.numerator)
    return tuple(result)  # type: ignore[return-value]


def local_cofactor(k: int, owner: int, z: int) -> int:
    return prod(
        z + column - owner for column in range(1, k + 1) if column != owner
    )


def third_residue(C: int, D: int, E: int, H: int, M: int, A: int) -> int:
    return -3 * (3 * C * A - 4 * D * M**2) + 20 * E * H * M**3


def fourth_residue(
    C: int, D: int, E: int, F: int, H: int, M: int, A: int
) -> int:
    return 3 * third_residue(C, D, E, H, M, A) + H**2 * (
        -9 * D * A**2 + 36 * E * A * M**2 + 84 * F * M**4
    )


def reduced_fourth_expression(
    C: int, D: int, E: int, F: int, H: int, M: int, A: int, X: int
) -> int:
    if 3 * X - M != A * H:
        raise ValueError("expected 3X-M=AH")
    return (
        -C * A
        + D * ((X + M) ** 2 - 4 * X**2)
        + H * E * ((X + M) ** 3 - 4 * X**3)
        + H**2 * F * ((X + M) ** 4 - 4 * X**4)
    )


def denominator_quotient(A: int, E: int, F: int, H: int, M: int) -> int:
    return (
        80 * A * F * M**3
        + H * (-3 * A**3 * E + 24 * A**2 * F * M**2)
        - A**4 * F * H**3
    )


@cache
def coefficient_boundary_report() -> dict[str, Any]:
    rows: list[dict[str, int]] = []
    total_owners = 0
    remainder_checks = 0
    for k in ROWS:
        center = (k + 1) // 2
        center_coefficients = local_coefficients(k, center)
        if center_coefficients[1] != 0 or center_coefficients[3] != 0:
            raise AssertionError("center cofactor is not even")
        for owner in range(1, k + 1):
            total_owners += 1
            coefficients = local_coefficients(k, owner)
            reflected = local_coefficients(k, k + 1 - owner)
            expected_reflected = (
                coefficients[0],
                -coefficients[1],
                coefficients[2],
                -coefficients[3],
            )
            if reflected != expected_reflected:
                raise AssertionError("reflection parity failed")
            for z in (-7, -3, -1, 0, 1, 2, 5):
                truncated = sum(coefficients[degree] * z**degree for degree in range(4))
                difference = local_cofactor(k, owner, z) - truncated
                if z == 0:
                    if difference != 0:
                        raise AssertionError("zero Taylor remainder failed")
                elif difference % abs(z) ** 4:
                    raise AssertionError("fourth Taylor remainder failed")
                remainder_checks += 1
        rows.append(
            {
                "k": k,
                "center": center,
                "center_C": center_coefficients[0],
                "center_D": center_coefficients[1],
                "center_E": center_coefficients[2],
                "center_F": center_coefficients[3],
            }
        )
    return {
        "rows": rows,
        "total_owners": total_owners,
        "reflection_checks": total_owners,
        "taylor_remainder_checks": remainder_checks,
    }


@cache
def denominator_grid() -> dict[str, Any]:
    checks = 0
    h_three_checks = 0
    unit_checks = 0
    negative_checks = 0
    for k in ROWS:
        for owner in range(1, k + 1):
            C, D, E, F = local_coefficients(k, owner)
            for H in (-5, -3, -2, -1, 1, 2, 3, 5):
                for M in range(-5, 6):
                    for A in range(-4, 5):
                        numerator = M + A * H
                        if numerator % 3:
                            continue
                        X = numerator // 3
                        T4 = reduced_fourth_expression(C, D, E, F, H, M, A, X)
                        G4 = fourth_residue(C, D, E, F, H, M, A)
                        quotient = denominator_quotient(A, E, F, H, M)
                        if 27 * T4 - G4 != H**3 * quotient:
                            raise AssertionError("denominator-clearing identity failed")
                        checks += 1
                        h_three_checks += abs(H) == 3
                        unit_checks += abs(H) == 1
                        negative_checks += H < 0 or M < 0 or A < 0
    return {
        "exact_identity_checks": checks,
        "owner_component_three_checks": h_three_checks,
        "unit_component_checks": unit_checks,
        "signed_checks": negative_checks,
        "all_A_corrections_retained": True,
    }


def second_obstruction(C: int, D: int, t: int, g: int, dl: int, dr: int) -> int:
    return 3 * (C * t - 12 * D * g**2 * dl * dr)


def third_obstruction(
    C: int, D: int, E: int, t: int, g: int, dl: int, dr: int, gap: int
) -> int:
    return -3 * second_obstruction(C, D, t, g, dl, dr) + 180 * E * g**2 * dl * dr * gap


def fourth_correction(
    D: int, E: int, F: int, t: int, g: int, dl: int, dr: int
) -> int:
    return (
        -9 * D * t**2
        - 108 * D * t * g**2 * (dl + dr)
        + 324 * E * t * g**2 * dl * dr
        + 6804 * F * g**4 * (dl * dr) ** 2
    )


def composed_obstruction(
    *,
    C: int,
    D: int,
    E: int,
    F: int,
    P: int,
    a: int,
    b: int,
    c: int,
    g: int,
    dl: int,
    dr: int,
    gap: int,
) -> int:
    t = a * b * c
    return 3 * b * c * third_obstruction(C, D, E, t, g, dl, dr, gap) + P**2 * fourth_correction(
        D, E, F, t, g, dl, dr
    )


def composition_residues(
    *,
    C: int,
    D: int,
    E: int,
    F: int,
    P: int,
    Q: int,
    R: int,
    a: int,
    b: int,
    c: int,
    g: int,
    dl: int,
    dr: int,
) -> tuple[int, int, int]:
    if a * P**2 - b * Q**2 != 3 * dl:
        raise ValueError("left square difference failed")
    if a * P**2 - c * R**2 != 3 * dr:
        raise ValueError("right square difference failed")
    if P == 0:
        raise ValueError("audit modulus must be nonzero")
    modulus = abs(P) ** 3
    M = g * Q * R
    gap = g * P * Q * R
    T3 = third_residue(C, D, E, P, M, a)
    F3 = third_obstruction(C, D, E, a * b * c, g, dl, dr, gap)
    refined = b * c * T3 - F3 + 36 * a * D * g**2 * P**2 * (dl + dr)
    K = -9 * D * a**2 + 36 * E * a * M**2 + 84 * F * M**4
    K0 = (
        -9 * D * (a * b * c) ** 2
        + 324 * E * (a * b * c) * g**2 * dl * dr
        + 6804 * F * g**4 * (dl * dr) ** 2
    )
    correction = (b * c) ** 2 * K - K0
    raw = 3 * T3 + P**2 * K
    obstruction = composed_obstruction(
        C=C,
        D=D,
        E=E,
        F=F,
        P=P,
        a=a,
        b=b,
        c=c,
        g=g,
        dl=dl,
        dr=dr,
        gap=gap,
    )
    total = (b * c) ** 2 * raw - obstruction
    return refined % modulus, correction % abs(P), total % modulus


def target_triples() -> Iterable[tuple[int, tuple[int, int, int]]]:
    for k in ROWS:
        for indices in combinations(range(1, k + 1), 3):
            yield k, indices


@cache
def composition_grid() -> dict[str, Any]:
    triples = 0
    owner_positions = 0
    fixtures = 0
    p_three = 0
    signed = 0
    unit_opposites = 0
    center_positions = 0
    reflected_triples = 0
    for k, indices in target_triples():
        triples += 1
        center = (k + 1) // 2
        if any(left + right == k + 1 for left, right in combinations(indices, 2)):
            reflected_triples += 1
        for owner in indices:
            owner_positions += 1
            center_positions += owner == center
            others = tuple(index for index in indices if index != owner)
            dl, dr = owner - others[0], owner - others[1]
            C, D, E, F = local_coefficients(k, owner)
            for P in (-3, -2, 2, 3):
                for g in (-1, 1, 2):
                    for a in (-2, 0, 3):
                        Q = R = 1
                        b = a * P**2 - 3 * dl
                        c = a * P**2 - 3 * dr
                        residues = composition_residues(
                            C=C,
                            D=D,
                            E=E,
                            F=F,
                            P=P,
                            Q=Q,
                            R=R,
                            a=a,
                            b=b,
                            c=c,
                            g=g,
                            dl=dl,
                            dr=dr,
                        )
                        if residues != (0, 0, 0):
                            raise AssertionError((k, indices, owner, P, g, a, residues))
                        fixtures += 1
                        p_three += abs(P) == 3
                        signed += P < 0 or g < 0 or a < 0 or b < 0 or c < 0
                        unit_opposites += 1
    return {
        "target_triples": triples,
        "cyclic_owner_positions": owner_positions,
        "center_owner_positions": center_positions,
        "reflected_pair_triples": reflected_triples,
        "exact_composition_fixtures": fixtures,
        "owner_component_three_fixtures": p_three,
        "signed_fixtures": signed,
        "unit_opposite_component_fixtures": unit_opposites,
        "coefficient_6804": 84 * 9**2,
        "all_refined_third_corrections_hold": True,
        "all_fourth_corrections_hold": True,
        "all_composed_residues_hold": True,
    }


@cache
def sensitivity_witnesses() -> dict[str, Any]:
    C, D, E, F = local_coefficients(9, 2)
    H, M, A = 11, 37, -5
    X = (M + A * H) // 3
    if 3 * X - M != A * H:
        raise AssertionError
    T4 = reduced_fourth_expression(C, D, E, F, H, M, A, X)
    G4 = fourth_residue(C, D, E, F, H, M, A)
    exact_difference = 27 * T4 - G4
    local_terms = {
        "minus_9_D_A2": -9 * D * A**2,
        "plus_36_E_A_M2": 36 * E * A * M**2,
        "plus_84_F_M4": 84 * F * M**4,
    }
    omitted_remainders = {
        name: (exact_difference + H**2 * term) % H**3
        for name, term in local_terms.items()
    }
    if not all(omitted_remainders.values()):
        raise AssertionError("an omitted A/cubic correction escaped the witness")

    composition_witness: dict[str, Any] | None = None
    for P in (2, 3, 5, 7, 11):
        for a in range(-5, 8):
            for dl, dr in ((-1, -2), (-1, -3), (2, -2), (1, 4)):
                b = a * P**2 - 3 * dl
                c = a * P**2 - 3 * dr
                g = 2
                C0, D0, E0, F0 = local_coefficients(5, 1)
                raw = fourth_residue(C0, D0, E0, F0, P, g, a)
                obstruction = composed_obstruction(
                    C=C0,
                    D=D0,
                    E=E0,
                    F=F0,
                    P=P,
                    a=a,
                    b=b,
                    c=c,
                    g=g,
                    dl=dl,
                    dr=dr,
                    gap=g * P,
                )
                modulus = P**3
                t = a * b * c
                wrong_6804 = 3 * b * c * third_obstruction(
                    C0, D0, E0, t, g, dl, dr, g * P
                ) + P**2 * (
                    -9 * D0 * t**2
                    - 108 * D0 * t * g**2 * (dl + dr)
                    + 324 * E0 * t * g**2 * dl * dr
                    + 756 * F0 * g**4 * (dl * dr) ** 2
                )
                wrong_no_refined = 3 * b * c * third_obstruction(
                    C0, D0, E0, t, g, dl, dr, g * P
                ) + P**2 * (
                    -9 * D0 * t**2
                    + 324 * E0 * t * g**2 * dl * dr
                    + 6804 * F0 * g**4 * (dl * dr) ** 2
                )
                correct = ((b * c) ** 2 * raw - obstruction) % modulus
                single = (b * c * raw - obstruction) % modulus
                bad_6804 = ((b * c) ** 2 * raw - wrong_6804) % modulus
                bad_refined = ((b * c) ** 2 * raw - wrong_no_refined) % modulus
                if correct == 0 and single and bad_6804 and bad_refined:
                    composition_witness = {
                        "k": 5,
                        "owner": 1,
                        "P": P,
                        "Q": 1,
                        "R": 1,
                        "a": a,
                        "b": b,
                        "c": c,
                        "g": g,
                        "delta_left": dl,
                        "delta_right": dr,
                        "single_bc_remainder": single,
                        "wrong_756_remainder": bad_6804,
                        "omitted_minus_108_remainder": bad_refined,
                    }
                    break
            if composition_witness is not None:
                break
        if composition_witness is not None:
            break
    if composition_witness is None:
        raise AssertionError("failed to find sensitivity witness")
    return {
        "local_fixture": {"k": 9, "owner": 2, "H": H, "M": M, "A": A},
        "omitted_local_correction_remainders_mod_H3": omitted_remainders,
        "composition_fixture": composition_witness,
        "square_multiplier_is_essential_for_stated_composition": True,
        "coefficient_6804_is_essential": True,
        "refined_minus_108_term_is_essential": True,
    }


def crt(residues: Sequence[int], moduli: Sequence[int]) -> tuple[int, int]:
    if len(residues) != len(moduli) or not residues:
        raise ValueError("CRT expects equal nonempty input")
    value, modulus = 0, 1
    for residue, next_modulus in zip(residues, moduli, strict=True):
        if next_modulus <= 0 or gcd(modulus, next_modulus) != 1:
            raise ValueError("CRT moduli must be positive and coprime")
        adjustment = ((residue - value) * pow(modulus, -1, next_modulus)) % next_modulus
        value += modulus * adjustment
        modulus *= next_modulus
        value %= modulus
    return value, modulus


@cache
def crt_witness(exponent: int) -> dict[str, Any]:
    if exponent < 1:
        raise ValueError("positive exponent required")
    k = 5
    components = tuple(base**exponent for base in CRT_BASES)
    gap = prod(components)
    anchor = CRT_INDICES[0]
    square_moduli = tuple(component**2 for component in components)
    base_residues = tuple(
        (-3 * (index - anchor)) % modulus
        for index, modulus in zip(CRT_INDICES, square_moduli, strict=True)
    )
    base_x, square_product = crt(base_residues, square_moduli)
    if square_product != gap**2:
        raise AssertionError("square CRT modulus mismatch")

    third_targets: list[int] = []
    third_derivatives: list[int] = []
    for index, component in zip(CRT_INDICES, components, strict=True):
        numerator = base_x + 3 * (index - anchor)
        if numerator % component**2:
            raise AssertionError("base square CRT failed")
        a0 = numerator // component**2
        C, D, E, _ = local_coefficients(k, index)
        M = gap // component
        value = third_residue(C, D, E, component, M, a0)
        derivative = -9 * C * M**2
        modulus = component**2
        if gcd(derivative, modulus) != 1:
            raise AssertionError("third derivative is not a unit")
        if third_residue(C, D, E, component, M, a0 + M**2) - value != derivative:
            raise AssertionError("third finite difference mismatch")
        third_targets.append((-value * pow(derivative, -1, modulus)) % modulus)
        third_derivatives.append(derivative % modulus)

    third_parameter, third_modulus = crt(third_targets, square_moduli)
    if third_modulus != gap**2:
        raise AssertionError("third lift CRT modulus mismatch")

    quotient_residues: list[int] = []
    fourth_targets: list[int] = []
    fourth_derivatives: list[int] = []
    for index, component in zip(CRT_INDICES, components, strict=True):
        numerator = base_x + gap**2 * third_parameter + 3 * (index - anchor)
        if numerator % component**2:
            raise AssertionError("lifted square residual failed")
        a0 = numerator // component**2
        C, D, E, F = local_coefficients(k, index)
        M = gap // component
        value = fourth_residue(C, D, E, F, component, M, a0)
        if value % component**2:
            raise AssertionError("third lift did not establish the fourth base")
        quotient = value // component**2
        quotient_residues.append(quotient % component)
        delta_a = component**2 * M**4
        shifted = fourth_residue(C, D, E, F, component, M, a0 + delta_a)
        if shifted % component**2:
            raise AssertionError("fourth finite-difference quotient not integral")
        finite_difference = (shifted // component**2 - quotient) % component
        derivative = (-27 * C * M**4) % component
        if finite_difference != derivative:
            raise AssertionError("fourth finite-difference derivative mismatch")
        if gcd(derivative, component) != 1:
            raise AssertionError("fourth derivative is not a unit")
        fourth_targets.append((-quotient * pow(derivative, -1, component)) % component)
        fourth_derivatives.append(derivative)

    fourth_parameter, fourth_modulus = crt(fourth_targets, components)
    if fourth_modulus != gap:
        raise AssertionError("fourth lift CRT modulus mismatch")
    parameter = third_parameter + gap**2 * fourth_parameter

    chosen_lift: int | None = None
    for lift in range(3):
        candidate_parameter = parameter + gap**3 * lift
        x_anchor = base_x + gap**2 * candidate_parameter
        if (x_anchor + gap) % 3 == 0:
            chosen_lift = lift
            parameter = candidate_parameter
            break
    if chosen_lift is None:
        raise AssertionError("integral n representative not found")
    x_anchor = base_x + gap**2 * parameter
    n = (x_anchor + gap) // 3 - anchor
    if n < 0:
        raise AssertionError("expected positive CRT representative")

    block_difference = block_product(k, n + gap) - 4 * block_product(k, n)
    cofactors: list[int] = []
    local_checks: list[dict[str, Any]] = []
    residuals: list[int] = []
    for index, component in zip(CRT_INDICES, components, strict=True):
        residual = 3 * (n + index) - gap
        residuals.append(residual)
        if residual <= 0 or residual % component**2:
            raise AssertionError("final residual is not a positive square multiple")
        a = residual // component**2
        cofactors.append(a)
        C, D, E, F = local_coefficients(k, index)
        M = gap // component
        second = 3 * C * a - 4 * D * M**2
        third = third_residue(C, D, E, component, M, a)
        fourth = fourth_residue(C, D, E, F, component, M, a)
        record = {
            "index": index,
            "component_digits": len(str(component)),
            "owner_factor_mod_component": (n + index) % component,
            "square_residual_mod_component_square": residual % component**2,
            "second_mod_component": second % component,
            "third_mod_component_square": third % component**2,
            "fourth_mod_component_cube": fourth % component**3,
            "direct_block_difference_mod_component_fifth": block_difference % component**5,
        }
        if any(record[key] for key in record if key.endswith(("component", "square", "cube", "fifth"))):
            raise AssertionError((index, record))
        local_checks.append(record)

    composed_checks: list[dict[str, int]] = []
    for position, owner in enumerate(CRT_INDICES):
        other_positions = [offset for offset in range(3) if offset != position]
        left, right = other_positions
        C, D, E, F = local_coefficients(k, owner)
        dl = owner - CRT_INDICES[left]
        dr = owner - CRT_INDICES[right]
        obstruction = composed_obstruction(
            C=C,
            D=D,
            E=E,
            F=F,
            P=components[position],
            a=cofactors[position],
            b=cofactors[left],
            c=cofactors[right],
            g=1,
            dl=dl,
            dr=dr,
            gap=gap,
        )
        remainder = obstruction % components[position] ** 3
        if remainder:
            raise AssertionError("cyclic fourth obstruction failed")
        composed_checks.append({"index": owner, "remainder": remainder})

    short_checks = [0 < residual < ROWS[k] * gap for residual in residuals]
    return {
        "exponent": exponent,
        "k": k,
        "indices": list(CRT_INDICES),
        "components": list(components),
        "gap": gap,
        "gap_digits": len(str(gap)),
        "gap_at_least_target": gap >= TARGET,
        "n_digits": len(str(n)),
        "third_derivatives_are_units": all(
            gcd(derivative, modulus) == 1
            for derivative, modulus in zip(third_derivatives, square_moduli, strict=True)
        ),
        "fourth_derivatives_are_units": all(
            gcd(derivative, component) == 1
            for derivative, component in zip(fourth_derivatives, components, strict=True)
        ),
        "third_only_fourth_quotient_residues": quotient_residues,
        "third_only_already_fourth": all(residue == 0 for residue in quotient_residues),
        "integrality_lift": chosen_lift,
        "local_checks": local_checks,
        "composed_checks": composed_checks,
        "all_local_checks": True,
        "all_composed_checks": True,
        "all_short_window_inequalities": all(short_checks),
        "all_residuals_positive": all(residual > 0 for residual in residuals),
        "short_window_checks": short_checks,
        "residual_to_gap_floors": [residual // gap for residual in residuals],
        "minimum_residual_to_gap_floor_digits": len(str(min(residuals) // gap)),
        "maximum_residual_to_gap_floor": max(residuals) // gap,
        "block_equation": block_difference == 0,
    }


@cache
def exponent_family() -> dict[str, Any]:
    rows = []
    for exponent in (1, 2, 3, 5, 8, 10, 12, 16, 20, 24):
        witness = crt_witness(exponent)
        rows.append(
            {
                "exponent": exponent,
                "gap_digits": witness["gap_digits"],
                "n_digits": witness["n_digits"],
                "local": witness["all_local_checks"],
                "composed": witness["all_composed_checks"],
                "proper": not witness["third_only_already_fourth"],
                "short_window": witness["all_short_window_inequalities"],
                "block_equation": witness["block_equation"],
            }
        )
    return {
        "rows": rows,
        "all_lifts_hold": all(row["local"] and row["composed"] for row in rows),
        "all_are_proper_nonshort_nonsolutions": all(
            row["proper"] and not row["short_window"] and not row["block_equation"]
            for row in rows
        ),
    }


def report() -> dict[str, Any]:
    target = crt_witness(20)
    return {
        "verdict": "PASS",
        "coefficient_boundaries": coefficient_boundary_report(),
        "denominator_clearing": denominator_grid(),
        "composition": composition_grid(),
        "sensitivity_witnesses": sensitivity_witnesses(),
        "target_size_falsifier": target,
        "exponent_family": exponent_family(),
        "route_scope": (
            "proper one-owner-adic-digit strengthening; no closure without "
            "the three positive short-window inequalities"
        ),
        "exact_remaining_gap": (
            "exclude target-size three-owner tuples satisfying the square, "
            "second, third, and fourth cyclic divisibilities together with "
            "0<aP^2,bQ^2,cR^2<A_k*d"
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args()
    print(json.dumps(report(), indent=2 if args.pretty else None, sort_keys=True))


if __name__ == "__main__":
    main()
