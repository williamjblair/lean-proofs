#!/usr/bin/env python3
"""Exact independent verifier for the Erdős 686 fifth local lift.

The script reconstructs all Taylor coefficients from the signed cofactor
polynomial.  It checks the denominator-clearing identity, the cyclic
three-bucket composition, the squared third-quotient congruence, and the
gap-quadratic fixed-coefficient reduction.  It also replays the frozen
121-digit fourth-order CRT family and lifts it by one further owner-adic
digit.
"""

from __future__ import annotations

import argparse
import json
from functools import cache
from itertools import combinations
from math import gcd, prod
from typing import Any, Sequence


TARGET = 10**120
ROWS = {5: 14, 7: 17, 9: 23, 11: 26, 13: 29, 15: 35}
CRT_INDICES = (1, 2, 4)
CRT_BASES = (101, 103, 107)


def block_product(k: int, n: int) -> int:
    return prod(n + i for i in range(1, k + 1))


@cache
def local_coefficients(k: int, owner: int) -> tuple[int, int, int, int, int]:
    """Coefficients C,D,E,F,G of prod(z+j-owner), reconstructed directly."""

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


def third_local(C: int, D: int, E: int, H: int, M: int, A: int) -> int:
    return -3 * (3 * C * A - 4 * D * M**2) + 20 * E * H * M**3


def fourth_local(
    C: int, D: int, E: int, F: int, H: int, M: int, A: int
) -> int:
    return 3 * third_local(C, D, E, H, M, A) + H**2 * (
        -9 * D * A**2 + 36 * E * A * M**2 + 84 * F * M**4
    )


def fifth_local(
    C: int, D: int, E: int, F: int, G: int, H: int, M: int, A: int
) -> int:
    return 3 * fourth_local(C, D, E, F, H, M, A) + 20 * H**3 * M**3 * (
        12 * A * F + 17 * G * M**2
    )


def reduced_fifth_expression(
    C: int,
    D: int,
    E: int,
    F: int,
    G: int,
    H: int,
    M: int,
    A: int,
    X: int,
) -> int:
    if 3 * X - M != A * H:
        raise ValueError("expected 3X-M=AH")
    return (
        -C * A
        + D * ((X + M) ** 2 - 4 * X**2)
        + H * E * ((X + M) ** 3 - 4 * X**3)
        + H**2 * F * ((X + M) ** 4 - 4 * X**4)
        + H**3 * G * ((X + M) ** 5 - 4 * X**5)
    )


def denominator_quotient(A: int, E: int, F: int, G: int, H: int, M: int) -> int:
    return (
        -9 * A**3 * E
        + 72 * A**2 * F * M**2
        + 420 * A * G * M**4
        + H * (200 * A**2 * G * M**3)
        + H**2 * (-3 * A**4 * F + 40 * A**3 * G * M**2)
        - H**4 * A**5 * G
    )


def second_composed(C: int, D: int, t: int, g: int, dl: int, dr: int) -> int:
    return 3 * (C * t - 12 * D * g**2 * dl * dr)


def third_composed(
    C: int, D: int, E: int, t: int, g: int, dl: int, dr: int, gap: int
) -> int:
    return -3 * second_composed(C, D, t, g, dl, dr) + 180 * E * g**2 * dl * dr * gap


def fourth_correction(
    D: int, E: int, F: int, t: int, g: int, dl: int, dr: int
) -> int:
    return (
        -9 * D * t**2
        - 108 * D * t * g**2 * (dl + dr)
        + 324 * E * t * g**2 * dl * dr
        + 6804 * F * g**4 * (dl * dr) ** 2
    )


def fourth_composed(
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
    return 3 * b * c * third_composed(C, D, E, t, g, dl, dr, gap) + P**2 * fourth_correction(
        D, E, F, t, g, dl, dr
    )


def fifth_correction(
    E: int, F: int, G: int, t: int, g: int, dl: int, dr: int
) -> int:
    return (
        -540 * t * E * (dl + dr)
        + 2160 * t * F * dl * dr
        + 27540 * G * g**2 * (dl * dr) ** 2
    )


def fifth_composed(
    C: int,
    D: int,
    E: int,
    F: int,
    G: int,
    P: int,
    Q: int,
    R: int,
    a: int,
    b: int,
    c: int,
    g: int,
    dl: int,
    dr: int,
    gap: int,
) -> int:
    t = a * b * c
    return 3 * fourth_composed(C, D, E, F, P, a, b, c, g, dl, dr, gap) + P**3 * g**3 * Q * R * fifth_correction(
        E, F, G, t, g, dl, dr
    )


def reduced_fifth_coefficient(
    C: int, D: int, E: int, F: int, G: int, gap: int, dl: int, dr: int
) -> int:
    p, s = dl * dr, dl + dr
    return 8748 * p * (
        189 * C**2 * F * p
        + 255 * C**2 * G * gap * p
        - 36 * C * D**2 * s
        - 120 * C * D * E * gap * s
        + 108 * C * D * E * p
        + 240 * C * D * F * gap * p
        - 100 * C * E**2 * gap**2 * s
        + 180 * C * E**2 * gap * p
        + 400 * C * E * F * gap**2 * p
        - 36 * D**3 * p
        - 120 * D**2 * E * gap * p
        - 100 * D * E**2 * gap**2 * p
    )


def reduced_fifth_multiplier(
    C: int, D: int, E: int, F: int, t: int, g: int, gap: int, dl: int, dr: int
) -> int:
    p, s = dl * dr, dl + dr
    return -243 * (
        -12 * C * D * g**2 * s
        - C * D * t
        - 20 * C * E * gap * g**2 * s
        + 36 * C * E * g**2 * p
        + 80 * C * F * gap * g**2 * p
        - 12 * D**2 * g**2 * p
        - 20 * D * E * gap * g**2 * p
    )


@cache
def denominator_grid() -> dict[str, Any]:
    checks = signed = base_three = 0
    omitted_g_detected = 0
    for k in ROWS:
        for owner in range(1, k + 1):
            C, D, E, F, G = local_coefficients(k, owner)
            for H in (-5, -3, -2, -1, 1, 2, 3, 5):
                for M in range(-4, 5):
                    for A in range(-3, 4):
                        numerator = M + A * H
                        if numerator % 3:
                            continue
                        X = numerator // 3
                        T = reduced_fifth_expression(C, D, E, F, G, H, M, A, X)
                        target = fifth_local(C, D, E, F, G, H, M, A)
                        quotient = denominator_quotient(A, E, F, G, H, M)
                        if 81 * T - target != H**4 * quotient:
                            raise AssertionError((k, owner, H, M, A))
                        omitted = target - 340 * H**3 * G * M**5
                        omitted_g_detected += omitted % abs(H) ** 4 != 0
                        checks += 1
                        signed += H < 0 or M < 0 or A < 0
                        base_three += abs(H) == 3
    if not omitted_g_detected:
        raise AssertionError("quartic cofactor term was never load-bearing")
    return {
        "exact_denominator_identities": checks,
        "signed_fixtures": signed,
        "component_three_fixtures": base_three,
        "omitted_quartic_term_detected": omitted_g_detected,
    }


@cache
def composition_grid() -> dict[str, Any]:
    triples = owner_positions = fixtures = signed = unit_opposites = component_three = 0
    quadratic_nonzero = quadratic_zero = 0
    for k in ROWS:
        for indices in combinations(range(1, k + 1), 3):
            triples += 1
            for position, owner in enumerate(indices):
                owner_positions += 1
                other = [p for p in range(3) if p != position]
                dl, dr = owner - indices[other[0]], owner - indices[other[1]]
                C, D, E, F, G = local_coefficients(k, owner)
                degree_two = 8748 * dl * dr * 100 * E * (
                    -C * E * (dl + dr)
                    + 4 * C * F * dl * dr
                    - D * E * dl * dr
                )
                quadratic_nonzero += degree_two != 0
                quadratic_zero += degree_two == 0
                for P in (-3, -2, 2, 3):
                    for g in (-1, 1, 2):
                        for a in (-2, 0, 3):
                            Q = R = 1
                            b = a * P**2 - 3 * dl
                            c = a * P**2 - 3 * dr
                            gap = g * P * Q * R
                            if a * P**2 - b * Q**2 != 3 * dl:
                                raise AssertionError
                            if a * P**2 - c * R**2 != 3 * dr:
                                raise AssertionError
                            raw = fifth_local(C, D, E, F, G, P, g * Q * R, a)
                            composed = fifth_composed(
                                C, D, E, F, G, P, Q, R, a, b, c, g, dl, dr, gap
                            )
                            if ((b * c) ** 2 * raw - composed) % abs(P) ** 4:
                                raise AssertionError((k, indices, owner, P, g, a))
                            t = a * b * c
                            J = fourth_correction(D, E, F, t, g, dl, dr)
                            K5 = fifth_correction(E, F, G, t, g, dl, dr)
                            third = third_composed(C, D, E, t, g, dl, dr, gap)
                            left = 81 * C**2 * (3 * J + g**2 * gap * K5)
                            right = reduced_fifth_multiplier(
                                C, D, E, F, t, g, gap, dl, dr
                            ) * third + reduced_fifth_coefficient(
                                C, D, E, F, G, gap, dl, dr
                            ) * g**4
                            if left != right:
                                raise AssertionError("reduced fifth identity failed")
                            fixtures += 1
                            signed += P < 0 or g < 0 or min(a, b, c) < 0
                            unit_opposites += 1
                            component_three += abs(P) == 3
    if triples != 1035 or owner_positions != 3105:
        raise AssertionError((triples, owner_positions))
    # Each ordered distinct triple occurs twice in the combinations/cyclic view.
    if quadratic_nonzero != 3078 or quadratic_zero != 27:
        raise AssertionError((quadratic_nonzero, quadratic_zero))
    return {
        "target_unordered_triples": triples,
        "cyclic_owner_positions": owner_positions,
        "signed_composition_fixtures": fixtures,
        "signed_fixtures": signed,
        "component_three_fixtures": component_three,
        "unit_opposite_component_fixtures": unit_opposites,
        "gap_quadratic_nonzero_cyclic_positions": quadratic_nonzero,
        "gap_quadratic_zero_cyclic_positions": quadratic_zero,
        "ordered_gap_quadratic_nonzero": 2 * quadratic_nonzero,
        "ordered_gap_quadratic_zero": 2 * quadratic_zero,
    }


def crt(residues: Sequence[int], moduli: Sequence[int]) -> tuple[int, int]:
    if len(residues) != len(moduli) or not residues:
        raise ValueError("CRT expects equal nonempty lists")
    value, modulus = 0, 1
    for residue, next_modulus in zip(residues, moduli, strict=True):
        if next_modulus <= 0 or gcd(modulus, next_modulus) != 1:
            raise ValueError("CRT moduli must be positive and pairwise coprime")
        step = ((residue - value) * pow(modulus, -1, next_modulus)) % next_modulus
        value = (value + modulus * step) % (modulus * next_modulus)
        modulus *= next_modulus
    return value, modulus


def cofactor_at(
    base_x: int,
    gap: int,
    parameter: int,
    anchor: int,
    index: int,
    component: int,
) -> int:
    numerator = base_x + gap**2 * parameter + 3 * (index - anchor)
    if numerator % component**2:
        raise AssertionError("square residual lost")
    return numerator // component**2


def integral_parameter(
    base_x: int, gap: int, anchor: int, parameter: int, period: int
) -> tuple[int, int, int]:
    for lift in range(3):
        candidate = parameter + period * lift
        x_anchor = base_x + gap**2 * candidate
        if (x_anchor + gap) % 3 == 0:
            n = (x_anchor + gap) // 3 - anchor
            if n < 0:
                raise AssertionError("negative CRT representative")
            return candidate, lift, n
    raise AssertionError("integral representative not found")


def evaluate_crt_state(
    *,
    k: int,
    components: tuple[int, int, int],
    gap: int,
    n: int,
) -> dict[str, Any]:
    cofactors: list[int] = []
    local_fifth_remainders: list[int] = []
    composed_fifth_remainders: list[int] = []
    squared_quotient_remainders: list[int] = []
    reduced_remainders: list[int] = []
    third_nonzero: list[bool] = []
    residuals: list[int] = []
    for index, P in zip(CRT_INDICES, components, strict=True):
        residual = 3 * (n + index) - gap
        if residual <= 0 or residual % P**2:
            raise AssertionError("invalid CRT residual")
        residuals.append(residual)
        cofactors.append(residual // P**2)
    for position, owner in enumerate(CRT_INDICES):
        other = [p for p in range(3) if p != position]
        left, right = other
        P, Q, R = components[position], components[left], components[right]
        a, b, c = cofactors[position], cofactors[left], cofactors[right]
        dl, dr = owner - CRT_INDICES[left], owner - CRT_INDICES[right]
        C, D, E, F, G = local_coefficients(k, owner)
        raw5 = fifth_local(C, D, E, F, G, P, gap // P, a)
        W4 = fourth_composed(C, D, E, F, P, a, b, c, 1, dl, dr, gap)
        W5 = fifth_composed(C, D, E, F, G, P, Q, R, a, b, c, 1, dl, dr, gap)
        T = third_composed(C, D, E, a * b * c, 1, dl, dr, gap)
        if T % P**2 or W4 % P**3:
            raise AssertionError("earlier CRT order was lost")
        z = T // P**2
        J = fourth_correction(D, E, F, a * b * c, 1, dl, dr)
        K5 = fifth_correction(E, F, G, a * b * c, 1, dl, dr)
        squared = 9 * b * c * z + 3 * J + P * Q * R * K5
        reduced = (
            729 * C**2 * b * c * z
            + reduced_fifth_coefficient(C, D, E, F, G, gap, dl, dr)
        )
        local_fifth_remainders.append(raw5 % P**4)
        composed_fifth_remainders.append(W5 % P**4)
        squared_quotient_remainders.append(squared % P**2)
        reduced_remainders.append(reduced % P**2)
        third_nonzero.append(T != 0)
    block_difference = block_product(k, n + gap) - 4 * block_product(k, n)
    residual_floors = [residual // gap for residual in residuals]
    return {
        "n_digits": len(str(n)),
        "local_fifth_remainders": local_fifth_remainders,
        "composed_fifth_remainders": composed_fifth_remainders,
        "squared_quotient_remainders": squared_quotient_remainders,
        "reduced_remainders": reduced_remainders,
        "all_third_obstructions_nonzero": all(third_nonzero),
        "upper_window_holds": all(0 < residual < ROWS[k] * gap for residual in residuals),
        "minimum_residual_floor_digits": len(str(min(residual_floors))),
        "maximum_residual_floor_digits": len(str(max(residual_floors))),
        "block_equation": block_difference == 0,
        "block_difference_mod_component_sixth": [
            block_difference % P**6 for P in components
        ],
    }


@cache
def crt_fifth_replay(exponent: int = 20) -> dict[str, Any]:
    k, anchor = 5, CRT_INDICES[0]
    components = tuple(base**exponent for base in CRT_BASES)
    gap = prod(components)
    square_moduli = tuple(P**2 for P in components)
    base_residues = tuple(
        (-3 * (index - anchor)) % modulus
        for index, modulus in zip(CRT_INDICES, square_moduli, strict=True)
    )
    base_x, modulus = crt(base_residues, square_moduli)
    if modulus != gap**2:
        raise AssertionError("square CRT modulus mismatch")

    third_targets: list[int] = []
    for index, P in zip(CRT_INDICES, components, strict=True):
        A = cofactor_at(base_x, gap, 0, anchor, index, P)
        C, D, E, _, _ = local_coefficients(k, index)
        M = gap // P
        value = third_local(C, D, E, P, M, A)
        derivative = -9 * C * M**2
        if gcd(derivative, P**2) != 1:
            raise AssertionError("third derivative not a unit")
        third_targets.append((-value * pow(derivative, -1, P**2)) % P**2)
    third_parameter, modulus = crt(third_targets, square_moduli)
    if modulus != gap**2:
        raise AssertionError

    fourth_targets: list[int] = []
    for index, P in zip(CRT_INDICES, components, strict=True):
        A = cofactor_at(base_x, gap, third_parameter, anchor, index, P)
        C, D, E, F, _ = local_coefficients(k, index)
        M = gap // P
        value = fourth_local(C, D, E, F, P, M, A)
        if value % P**2:
            raise AssertionError("third lift did not establish fourth base")
        derivative = (-27 * C * M**4) % P
        if gcd(derivative, P) != 1:
            raise AssertionError("fourth derivative not a unit")
        fourth_targets.append((-(value // P**2) * pow(derivative, -1, P)) % P)
    fourth_lift, modulus = crt(fourth_targets, components)
    if modulus != gap:
        raise AssertionError
    fourth_parameter = third_parameter + gap**2 * fourth_lift
    fourth_integral_parameter, fourth_integrality_lift, fourth_n = integral_parameter(
        base_x, gap, anchor, fourth_parameter, gap**3
    )
    fourth_state = evaluate_crt_state(k=k, components=components, gap=gap, n=fourth_n)

    fifth_targets: list[int] = []
    fifth_derivatives: list[int] = []
    for index, P in zip(CRT_INDICES, components, strict=True):
        A = cofactor_at(base_x, gap, fourth_parameter, anchor, index, P)
        C, D, E, F, G = local_coefficients(k, index)
        M = gap // P
        value = fifth_local(C, D, E, F, G, P, M, A)
        if value % P**3:
            raise AssertionError("fourth lift did not establish fifth base")
        shifted_A = A + P**3 * M**5
        shifted = fifth_local(C, D, E, F, G, P, M, shifted_A)
        derivative = ((shifted - value) // P**3) % P
        expected = (-81 * C * M**5) % P
        if derivative != expected or gcd(derivative, P) != 1:
            raise AssertionError("fifth finite-difference derivative mismatch")
        fifth_derivatives.append(derivative)
        fifth_targets.append((-(value // P**3) * pow(derivative, -1, P)) % P)
    fifth_lift, modulus = crt(fifth_targets, components)
    if modulus != gap:
        raise AssertionError
    fifth_parameter = fourth_parameter + gap**3 * fifth_lift
    fifth_integral_parameter, fifth_integrality_lift, fifth_n = integral_parameter(
        base_x, gap, anchor, fifth_parameter, gap**4
    )
    fifth_state = evaluate_crt_state(k=k, components=components, gap=gap, n=fifth_n)

    if not any(fourth_state["local_fifth_remainders"]):
        raise AssertionError("frozen fourth fixture unexpectedly passed fifth order")
    if any(
        any(fifth_state[key])
        for key in (
            "local_fifth_remainders",
            "composed_fifth_remainders",
            "squared_quotient_remainders",
            "reduced_remainders",
        )
    ):
        raise AssertionError("fifth CRT lift failed")
    if fifth_state["block_equation"] or fifth_state["upper_window_holds"]:
        raise AssertionError("CRT route falsifier entered theorem scope")
    return {
        "exponent": exponent,
        "gap": gap,
        "gap_digits": len(str(gap)),
        "components": list(components),
        "fourth_fixture": {
            "integrality_lift": fourth_integrality_lift,
            **fourth_state,
        },
        "fifth_extension": {
            "fifth_derivatives_are_units": all(
                gcd(value, P) == 1
                for value, P in zip(fifth_derivatives, components, strict=True)
            ),
            "fifth_lift_nonzero": fifth_lift != 0,
            "fifth_lift_digits": len(str(fifth_lift)),
            "integrality_lift": fifth_integrality_lift,
            **fifth_state,
        },
    }


def telescope_boundary() -> list[dict[str, Any]]:
    return [
        {
            "k": k,
            "n": n,
            "d": 1,
            "equation": block_product(k, n + 1) == 4 * block_product(k, n),
            "target_domain": k <= 1,
        }
        for k, n in ((9, 2), (15, 4))
    ]


@cache
def report() -> dict[str, Any]:
    return {
        "denominator_grid": denominator_grid(),
        "composition_grid": composition_grid(),
        "crt_replay": crt_fifth_replay(),
        "telescope_boundary": telescope_boundary(),
        "scope": (
            "fifth order supplies a squared congruence for every named third "
            "quotient; its generic fixed term is quadratic in d, and a "
            "121-digit congruence-only family lifts through the new order"
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--compact", action="store_true")
    args = parser.parse_args()
    print(json.dumps(report(), indent=None if args.compact else 2, sort_keys=True))


if __name__ == "__main__":
    main()
