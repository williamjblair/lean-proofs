#!/usr/bin/env python3
"""Exact sixth/seventh-order audit for the odd three-owner core of Erdos 686.

This is deliberately a negative-route verifier.  It reconstructs the local
Taylor coefficients from the signed cofactor polynomial, checks the exact
sixth and seventh local formulae, checks their cyclic compositions modulo the
claimed powers, and then combines them with the *actual* residual window.

The output quantifies why the extra two owner-adic digits do not yield the
missing packing bound.  No floating point arithmetic is used in any verdict.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from functools import cache
from itertools import combinations, permutations, product
from math import comb, gcd
from typing import Any, Sequence


TARGET = 10**120

# (exact residual floor, banked coarse upper residual multiple, loss ceiling)
ROWS: dict[int, tuple[int, int, int]] = {
    5: (8, 14, 108),
    7: (12, 17, 1_620),
    9: (15, 23, 136_080),
    11: (20, 26, 1_224_720),
    13: (23, 29, 242_494_560),
    15: (29, 35, 18_914_575_680),
}


@cache
def local_coefficients(k: int, owner: int) -> tuple[int, ...]:
    """Coefficients of prod_{j != owner} (z+j-owner), low degree first."""

    if not 1 <= owner <= k:
        raise ValueError("owner outside row")
    coefficients = [1]
    for offset in (j - owner for j in range(1, k + 1) if j != owner):
        updated = [0] * (len(coefficients) + 1)
        for degree, value in enumerate(coefficients):
            updated[degree] += offset * value
            updated[degree + 1] += value
        coefficients = updated
    # Coefficients beyond the cofactor degree are literally zero.  Padding
    # makes k=5 and k=7 boundary behavior explicit in the same formula.
    return tuple(coefficients + [0] * (8 - len(coefficients)))


def exact_reduced_local(
    coefficients: Sequence[int], component: int, opposite: int, cofactor: int
) -> Fraction:
    """The exact local block equation after its two visible P factors.

    If x=(opposite+cofactor*component)/3 is integral, this is

      -C*a + sum_{r>=1} c_r P^(r-1) ((x+M)^(r+1)-4x^(r+1)).

    Fractions are retained so the denominator-clearing identities also test
    the base-three boundary without silently assuming invertibility of 3.
    """

    P, M, a = component, opposite, cofactor
    x = Fraction(M + a * P, 3)
    value = Fraction(-coefficients[0] * a)
    for degree, coefficient in enumerate(coefficients[1:], start=1):
        value += (
            coefficient
            * P ** (degree - 1)
            * ((x + M) ** (degree + 1) - 4 * x ** (degree + 1))
        )
    return value


def reduced_local_coefficient(
    coefficients: Sequence[int], power: int, opposite: int, cofactor: int
) -> Fraction:
    """Coefficient of P^power after x=(M+aP)/3, by the binomial theorem."""

    M, a = opposite, cofactor
    value = Fraction(-coefficients[0] * a) if power == 0 else Fraction(0)
    for degree, coefficient in enumerate(coefficients[1:], start=1):
        chosen = power - degree + 1
        if not 0 <= chosen <= degree + 1:
            continue
        value += Fraction(
            coefficient
            * comb(degree + 1, chosen)
            * a**chosen
            * M ** (degree + 1 - chosen)
            * (4 ** (degree + 1 - chosen) - 4),
            3 ** (degree + 1),
        )
    return value


def local_fifth(C: int, D: int, E: int, F: int, G: int, P: int, M: int, a: int) -> int:
    third = -3 * (3 * C * a - 4 * D * M**2) + 20 * E * P * M**3
    fourth = 3 * third + P**2 * (-9 * D * a**2 + 36 * E * a * M**2 + 84 * F * M**4)
    return 3 * fourth + 20 * P**3 * M**3 * (12 * a * F + 17 * G * M**2)


def local_sixth(
    C: int,
    D: int,
    E: int,
    F: int,
    G: int,
    H: int,
    P: int,
    M: int,
    a: int,
) -> int:
    """3^5 times the local Taylor truncation through P^4."""

    return 3 * local_fifth(C, D, E, F, G, P, M, a) + P**4 * (
        -27 * E * a**3
        + 216 * F * M**2 * a**2
        + 1_260 * G * M**4 * a
        + 1_364 * H * M**6
    )


def local_seventh(
    C: int,
    D: int,
    E: int,
    F: int,
    G: int,
    H: int,
    I: int,
    P: int,
    M: int,
    a: int,
) -> int:
    """3^6 times the local Taylor truncation through P^5."""

    return 3 * local_sixth(C, D, E, F, G, H, P, M, a) + 60 * P**5 * M**3 * (
        30 * G * a**2 + 102 * H * M**2 * a + 91 * I * M**4
    )


def third_composed(C: int, D: int, E: int, t: int, g: int, p: int, d: int) -> int:
    return -9 * C * t + 108 * D * g**2 * p + 180 * E * g**2 * p * d


def fourth_correction(D: int, E: int, F: int, t: int, g: int, s: int, p: int) -> int:
    return (
        -9 * D * t**2
        - 108 * D * t * g**2 * s
        + 324 * E * t * g**2 * p
        + 6_804 * F * g**4 * p**2
    )


def fifth_correction(E: int, F: int, G: int, t: int, g: int, s: int, p: int) -> int:
    return -540 * t * E * s + 2_160 * t * F * p + 27_540 * G * g**2 * p**2


def sixth_correction(
    D: int, E: int, F: int, G: int, H: int, t: int, g: int, s: int, p: int
) -> int:
    """K6 in W6 = 3*(bc)*W5 + 27*P^4*K6."""

    return (
        -E * t**3
        + g**2 * t**2 * (12 * D - 36 * E * s + 72 * F * p)
        + g**4 * t * (-1_512 * F * p * s + 3_780 * G * p**2)
        + 36_828 * H * g**6 * p**3
    )


def seventh_correction(
    E: int, F: int, G: int, H: int, I: int, t: int, g: int, s: int, p: int
) -> int:
    """K7 in W7 = 3*W6 + 1620*P^5*M*g^2*K7."""

    return (
        t**2 * (E - 4 * F * s + 10 * G * p)
        + t * g**2 * (-102 * G * p * s + 306 * H * p**2)
        + 2_457 * I * g**4 * p**3
    )


def cyclic_obstructions(
    *,
    coefficients: Sequence[int],
    P: int,
    Q: int,
    R: int,
    a: int,
    b: int,
    c: int,
    g: int,
    x: int,
    y: int,
) -> tuple[int, int, int]:
    C, D, E, F, G, H, I = coefficients[:7]
    A, t, s, p = b * c, a * b * c, x + y, x * y
    d, M = g * P * Q * R, g * Q * R
    T = third_composed(C, D, E, t, g, p, d)
    J = fourth_correction(D, E, F, t, g, s, p)
    W4 = 3 * A * T + P**2 * J
    W5 = 3 * W4 + P**3 * g**2 * M * fifth_correction(E, F, G, t, g, s, p)
    W6 = 3 * A * W5 + 27 * P**4 * sixth_correction(D, E, F, G, H, t, g, s, p)
    W7 = 3 * W6 + 1_620 * P**5 * M * g**2 * seventh_correction(
        E, F, G, H, I, t, g, s, p
    )
    return W5, W6, W7


def local_identity_grid() -> dict[str, int]:
    checks = signed = base_three = top_zero = 0
    for k in ROWS:
        for owner in range(1, k + 1):
            coefficients = local_coefficients(k, owner)
            C, D, E, F, G, H, I = coefficients[:7]
            top_zero += (k == 5 and (H != 0 or I != 0)) or (k == 7 and I != 1)
            for P, M, a in product((-5, -3, -1, 1, 3, 5), (-4, -1, 0, 2, 5), (-3, -1, 0, 2, 4)):
                sixth = local_sixth(C, D, E, F, G, H, P, M, a)
                seventh = local_seventh(C, D, E, F, G, H, I, P, M, a)
                trunc6 = sum(
                    reduced_local_coefficient(coefficients, power, M, a) * P**power
                    for power in range(5)
                )
                trunc7 = sum(
                    reduced_local_coefficient(coefficients, power, M, a) * P**power
                    for power in range(6)
                )
                if Fraction(sixth) != 3**5 * trunc6:
                    raise AssertionError(("sixth local identity", k, owner, P, M, a))
                if Fraction(seventh) != 3**6 * trunc7:
                    raise AssertionError(("seventh local identity", k, owner, P, M, a))
                checks += 1
                signed += P < 0 or M < 0 or a < 0
                base_three += abs(P) == 3
    if top_zero:
        raise AssertionError("top-coefficient boundary reconstruction failed")
    return {
        "exact_local_sixth_seventh_checks": checks,
        "signed_checks": signed,
        "component_three_checks": base_three,
    }


def _crt(residues: Sequence[int], moduli: Sequence[int]) -> tuple[int, int]:
    value, modulus = 0, 1
    for residue, next_modulus in zip(residues, moduli, strict=True):
        if gcd(modulus, next_modulus) != 1:
            raise ValueError("non-coprime CRT moduli")
        step = ((residue - value) * pow(modulus, -1, next_modulus)) % next_modulus
        value += modulus * step
        modulus *= next_modulus
        value %= modulus
    return value, modulus


def _residual_fixture(P: int, Q: int, R: int, x: int, y: int) -> tuple[int, int, int] | None:
    """Find positive a,b,c with aP^2-bQ^2=3x and aP^2-cR^2=3y."""

    residues: list[int] = []
    moduli: list[int] = []
    for component, delta in ((Q, x), (R, y)):
        modulus = component**2
        coefficient = P**2 % modulus
        common = gcd(coefficient, modulus)
        if (3 * delta) % common:
            return None
        coefficient //= common
        rhs = (3 * delta) // common
        reduced_modulus = modulus // common
        residue = 0 if reduced_modulus == 1 else rhs * pow(coefficient, -1, reduced_modulus) % reduced_modulus
        residues.append(residue)
        moduli.append(reduced_modulus)
    if gcd(moduli[0], moduli[1]) != 1:
        # The main audit uses pairwise-coprime P,Q,R, but Q^2 and R^2 are
        # therefore coprime too.  Keep this guard explicit.
        return None
    a0, period = _crt(residues, moduli)
    a = a0 + period * (1 + max(0, (20 - a0 + period - 1) // period))
    bnum, cnum = a * P**2 - 3 * x, a * P**2 - 3 * y
    if bnum % Q**2 or cnum % R**2:
        raise AssertionError("CRT residual fixture failed")
    b, c = bnum // Q**2, cnum // R**2
    if min(a, b, c) <= 0:
        raise AssertionError("fixture positivity failed")
    return a, b, c


def composition_grid() -> dict[str, int]:
    checks = component_three = signed_g = 0
    components = ((2, 3, 5), (3, 5, 7), (5, 7, 11))
    for k in ROWS:
        for owner, left, right in permutations(range(1, k + 1), 3):
            coefficients = local_coefficients(k, owner)
            x, y = owner - left, owner - right
            for P, Q, R in components:
                fixture = _residual_fixture(P, Q, R, x, y)
                if fixture is None:
                    continue
                a, b, c = fixture
                for g in (-3, -1, 1, 2):
                    M = g * Q * R
                    raw6 = local_sixth(*coefficients[:6], P, M, a)
                    raw7 = local_seventh(*coefficients[:7], P, M, a)
                    _, W6, W7 = cyclic_obstructions(
                        coefficients=coefficients,
                        P=P,
                        Q=Q,
                        R=R,
                        a=a,
                        b=b,
                        c=c,
                        g=g,
                        x=x,
                        y=y,
                    )
                    A = b * c
                    if (A**3 * raw6 - W6) % P**5:
                        raise AssertionError(("sixth composition", k, owner, left, right, P, Q, R, g))
                    if (A**3 * raw7 - W7) % P**6:
                        raise AssertionError(("seventh composition", k, owner, left, right, P, Q, R, g))
                    checks += 1
                    component_three += 3 in (P, Q, R)
                    signed_g += g < 0
    if not checks:
        raise AssertionError("composition grid unexpectedly empty")
    return {
        "exact_composition_checks": checks,
        "component_three_checks": component_three,
        "negative_loss_checks": signed_g,
    }


@cache
def symbolic_formula_certificate() -> dict[str, bool]:
    """Exact SymPy derivation of both local and composed formulae.

    This is not a numerical interpolation.  The cyclic calculation expands
    B=(aP^2-3x)(aP^2-3y), replaces A*M^2 by g^2*B term by term, and retains
    the exact remainder below P^5 or P^6.
    """

    import sympy as sp

    P, M, a, A, g, s, p = sp.symbols("P M a A g s p")
    C, D, E, F, G, H, I = sp.symbols("C D E F G H I")
    coefficients = (C, D, E, F, G, H, I)
    x = (M + a * P) / 3
    reduced = -C * a
    for degree, coefficient in enumerate(coefficients[1:], start=1):
        reduced += coefficient * P ** (degree - 1) * (
            (x + M) ** (degree + 1) - 4 * x ** (degree + 1)
        )
    reduced = sp.expand(reduced)
    raw6 = sp.expand(3**5 * sum(reduced.coeff(P, power) * P**power for power in range(5)))
    raw7 = sp.expand(3**6 * sum(reduced.coeff(P, power) * P**power for power in range(6)))

    raw5_formula = local_fifth(C, D, E, F, G, P, M, a)
    raw6_formula = local_sixth(C, D, E, F, G, H, P, M, a)
    raw7_formula = local_seventh(C, D, E, F, G, H, I, P, M, a)
    local6_ok = sp.expand(raw6 - raw6_formula) == 0
    local7_ok = sp.expand(raw7 - raw7_formula) == 0

    t = a * A
    T = third_composed(C, D, E, t, g, p, P * M)
    J = fourth_correction(D, E, F, t, g, s, p)
    W4 = 3 * A * T + P**2 * J
    W5 = 3 * W4 + P**3 * g**2 * M * fifth_correction(E, F, G, t, g, s, p)
    W6 = 3 * A * W5 + 27 * P**4 * sixth_correction(D, E, F, G, H, t, g, s, p)
    W7 = 3 * W6 + 1_620 * P**5 * M * g**2 * seventh_correction(E, F, G, H, I, t, g, s, p)
    B = 9 * p - 3 * a * s * P**2 + a**2 * P**4

    def eliminate_opposite_squares(expression: Any, a_power: int) -> Any:
        result = 0
        for term in sp.Add.make_args(sp.expand(A**a_power * expression)):
            powers = term.as_powers_dict()
            m_power = int(powers.get(M, 0))
            A_power = int(powers.get(A, 0))
            pairs = m_power // 2
            if A_power < pairs:
                raise AssertionError((term, A_power, pairs))
            coefficient = term / (M**m_power * A**A_power)
            result += (
                coefficient
                * A ** (A_power - pairs)
                * g ** (2 * pairs)
                * B**pairs
                * (M if m_power % 2 else 1)
            )
        return sp.expand(result)

    composed6 = eliminate_opposite_squares(raw6_formula, 3)
    composed7 = eliminate_opposite_squares(raw7_formula, 3)
    remainder6 = sum(sp.Poly(composed6, P).coeff_monomial(P**power) * P**power for power in range(5))
    remainder7 = sum(sp.Poly(composed7, P).coeff_monomial(P**power) * P**power for power in range(6))
    composition6_ok = sp.expand(remainder6 - W6) == 0
    composition7_ok = sp.expand(remainder7 - W7) == 0
    if not all((local6_ok, local7_ok, composition6_ok, composition7_ok)):
        raise AssertionError("symbolic high-order formula certificate failed")
    # Keep raw5_formula live in the symbolic dependency tree: W5 is built
    # from the same fifth formula and the next recurrences use it literally.
    if sp.expand(raw5_formula - 3**4 * sum(reduced.coeff(P, power) * P**power for power in range(4))) != 0:
        raise AssertionError("fifth recurrence base mismatch")
    return {
        "sixth_local_identity": local6_ok,
        "seventh_local_identity": local7_ok,
        "sixth_cyclic_remainder": composition6_ok,
        "seventh_cyclic_remainder": composition7_ok,
    }


def _owner_constants(k: int, owner: int, left: int, right: int) -> dict[str, int]:
    C, D, E, F, G, H, I = local_coefficients(k, owner)[:7]
    x, y = owner - left, owner - right
    s, p = x + y, x * y
    A2 = 12 * D - 36 * E * s + 72 * F * p
    A1 = -1_512 * F * p * s + 3_780 * G * p**2
    A0 = 36_828 * H * p**3
    B2 = E - 4 * F * s + 10 * G * p
    B1 = -102 * G * p * s + 306 * H * p**2
    B0 = 2_457 * I * p**3
    return {
        "C": C,
        "D": D,
        "E": E,
        "F": F,
        "G": G,
        "H": H,
        "I": I,
        "s": s,
        "p": p,
        "A2": A2,
        "A1": A1,
        "A0": A0,
        "B2": B2,
        "B1": B1,
        "B0": B0,
    }


def _arch_constants(k: int, owner: int, left: int, right: int) -> dict[str, int]:
    L, U, _ = ROWS[k]
    q = _owner_constants(k, owner, left, right)
    C, D, E, F, G = (q[name] for name in ("C", "D", "E", "F", "G"))
    s, p = q["s"], q["p"]
    BT = 9 * abs(C) * U**3 + 108 * abs(D * p) + 180 * abs(E * p)
    BJ = (
        9 * abs(D) * U**6
        + 108 * abs(D * s) * U**3
        + 324 * abs(E * p) * U**3
        + 6_804 * abs(F) * p**2
    )
    BK5 = 540 * abs(E * s) * U**3 + 2_160 * abs(F * p) * U**3 + 27_540 * abs(G) * p**2
    BW5 = 9 * U**2 * BT + 3 * BJ + BK5
    BK6 = abs(E) * U**9 + abs(q["A2"]) * U**6 + abs(q["A1"]) * U**3 + abs(q["A0"])
    C6 = 3 * U**2 * BW5 + 27 * BK6
    BK7 = abs(q["B2"]) * U**6 + abs(q["B1"]) * U**3 + abs(q["B0"])
    C7 = 3 * C6 + 1_620 * BK7
    return {"L": L, "U": U, "BT": BT, "BJ": BJ, "BK5": BK5, "BW5": BW5, "BK6": BK6, "BK7": BK7, "C6": C6, "C7": C7}


def _is_center_reflected(k: int, owner: int, left: int, right: int) -> bool:
    return 2 * owner == k + 1 and left + right == k + 1


def ordered_view_scan() -> dict[str, Any]:
    by_row: dict[str, Any] = {}
    total_views = generic = center_reflected = 0
    total_inside = outside = 0
    worst_w6: tuple[int, int, tuple[int, int, int, int]] | None = None
    for k, (L, U, loss) in ROWS.items():
        row_views = row_generic = row_center = row_inside = 0
        max_c6 = (0, (0, 0, 0))
        max_c7 = (0, (0, 0, 0))
        for owner, left, right in permutations(range(1, k + 1), 3):
            row_views += 1
            q = _owner_constants(k, owner, left, right)
            bounds = _arch_constants(k, owner, left, right)
            if _is_center_reflected(k, owner, left, right):
                row_center += 1
            else:
                row_generic += 1
            if q["E"] == 0 or q["B2"] == 0:
                raise AssertionError(("unexpected leading zero", k, owner, left, right, q))

            # Under t >= L^3 g^2 d and t < U^3 g^2 d, this is the exact
            # triangle-inequality certificate that K6 and then W6/P^4 have
            # sign -E.  The A*W5/P^4 term is included, not waved away.
            lead = 27 * abs(q["E"]) * L**9 * TARGET**3
            tail = (
                (27 * abs(q["A2"]) * U**6 + 3 * U**2 * bounds["BW5"]) * TARGET**2
                + 27 * abs(q["A1"]) * U**3 * TARGET
                + 27 * abs(q["A0"])
            )
            if not tail < lead:
                raise AssertionError(("sixth dominance", k, owner, left, right))
            if worst_w6 is None or tail * worst_w6[1] > worst_w6[0] * lead:
                worst_w6 = (tail, lead, (k, owner, left, right))

            # W7/P^4 has leading normalized coefficient
            # lambda^2*(-81 E lambda + 1620 B2), lambda=t/(g^2 d).
            inside = q["B2"] * q["E"] > 0 and (
                L**3 * abs(q["E"]) <= 20 * abs(q["B2"]) <= U**3 * abs(q["E"])
            )
            if inside:
                row_inside += 1
            else:
                # Away from the rational root, the exact leading gap beats
                # every O(d^2) term already at d=10^120.
                endpoint_gap = min(
                    abs(-81 * q["E"] * L**3 + 1_620 * q["B2"]),
                    abs(-81 * q["E"] * U**3 + 1_620 * q["B2"]),
                )
                leading_gap = L**6 * endpoint_gap * TARGET
                lower_order = (
                    9 * U**2 * bounds["BW5"]
                    + 81 * (
                        abs(q["A2"]) * U**6
                        + abs(q["A1"]) * U**3
                        + abs(q["A0"])
                    )
                    + 1_620 * (abs(q["B1"]) * U**3 + abs(q["B0"]))
                )
                if not lower_order < leading_gap:
                    raise AssertionError(("seventh outside-root dominance", k, owner, left, right))

            if bounds["C6"] > max_c6[0]:
                max_c6 = (bounds["C6"], (owner, left, right))
            if bounds["C7"] > max_c7[0]:
                max_c7 = (bounds["C7"], (owner, left, right))

        if row_views != k * (k - 1) * (k - 2):
            raise AssertionError("ordered-view count mismatch")
        by_row[str(k)] = {
            "ordered_views": row_views,
            "generic_views": row_generic,
            "center_reflected_views": row_center,
            "seventh_leading_root_inside_window": row_inside,
            "seventh_leading_root_outside_window": row_views - row_inside,
            "max_C6": max_c6[0],
            "max_C6_view": list(max_c6[1]),
            "max_C7": max_c7[0],
            "max_C7_view": list(max_c7[1]),
            "max_C6_times_loss_six_digits": len(str(max_c6[0] * loss**6)),
            "max_C7_times_loss_six_digits": len(str(max_c7[0] * loss**6)),
        }
        total_views += row_views
        generic += row_generic
        center_reflected += row_center
        total_inside += row_inside
        outside += row_views - row_inside
    if (total_views, generic, center_reflected) != (6_210, 6_156, 54):
        raise AssertionError((total_views, generic, center_reflected))
    assert worst_w6 is not None
    return {
        "totals": {
            "ordered_views": total_views,
            "generic_views": generic,
            "center_reflected_views": center_reflected,
            "sixth_W6_sign_certificates": total_views,
            "seventh_root_inside_views": total_inside,
            "seventh_root_outside_sign_certificates": outside,
            "worst_W6_tail_over_lead": f"{worst_w6[0]}/{worst_w6[1]}",
            "worst_W6_view": list(worst_w6[2]),
        },
        "by_row": by_row,
    }


def _primitive_cross(rows: Sequence[tuple[int, int]]) -> tuple[int, int, int]:
    if len(rows) != 3:
        raise ValueError
    weights = (
        rows[1][0] * rows[2][1] - rows[1][1] * rows[2][0],
        rows[2][0] * rows[0][1] - rows[2][1] * rows[0][0],
        rows[0][0] * rows[1][1] - rows[0][1] * rows[1][0],
    )
    common = 0
    for weight in weights:
        common = gcd(common, abs(weight))
    if common:
        weights = tuple(weight // common for weight in weights)
    return weights


def _sign(value: Fraction | int) -> int:
    return (value > 0) - (value < 0)


def determinant_scan() -> dict[str, Any]:
    """Audit the only fixed-coefficient cancellation available at order 7.

    The P^2-quotient V_s=W7_s/P_s^4 has two d^3 structures with rows
    (E_s,B2_s).  Their primitive cross product cancels both.  This scan checks
    every exact lambda cell in [L^3,U^3].  A one-sided weighted cell would
    permit an archimedean packing step; none exists.
    """

    by_row: dict[str, Any] = {}
    total_triples = total_cells = total_mixed = total_zero_weights = 0
    total_boundaries = total_mixed_boundaries = total_zero_boundaries = 0
    equal_roots = equal_roots_inside = 0
    minimum_separation: Fraction | None = None
    for k, (L, U, _) in ROWS.items():
        row_triples = row_cells = row_mixed = row_zero_weights = 0
        row_boundaries = row_mixed_boundaries = row_zero_boundaries = 0
        for triple in combinations(range(1, k + 1), 3):
            rows: list[tuple[int, int]] = []
            roots: list[Fraction] = []
            for position, owner in enumerate(triple):
                others = [triple[j] for j in range(3) if j != position]
                q = _owner_constants(k, owner, others[0], others[1])
                rows.append((q["E"], q["B2"]))
                roots.append(Fraction(20 * q["B2"], q["E"]))
            weights = _primitive_cross(rows)
            if weights == (0, 0, 0):
                raise AssertionError(("rank deficient", k, triple, rows))
            if sum(weight * E for weight, (E, _) in zip(weights, rows, strict=True)) != 0:
                raise AssertionError("E cancellation failed")
            if sum(weight * B for weight, (_, B) in zip(weights, rows, strict=True)) != 0:
                raise AssertionError("B2 cancellation failed")
            row_zero_weights += sum(weight == 0 for weight in weights)

            cuts = {Fraction(L**3), Fraction(U**3)}
            for root in roots:
                if Fraction(L**3) < root < Fraction(U**3):
                    cuts.add(root)
            ordered_cuts = sorted(cuts)
            for left, right in zip(ordered_cuts, ordered_cuts[1:]):
                sample = (left + right) / 2
                signs = [
                    _sign(weight * (-E * sample + 20 * B))
                    for weight, (E, B) in zip(weights, rows, strict=True)
                ]
                nonzero = [sign for sign in signs if sign]
                if len(set(nonzero)) == 1:
                    raise AssertionError(("one-sided leading cell", k, triple, left, right, weights, rows))
                row_cells += 1
                row_mixed += 1

            # Audit the rational roots and both window endpoints themselves.
            # At a root one or two weighted terms may vanish; a surviving
            # one-sided boundary would still be useful and must not be hidden
            # by an open-cell-only report.
            for boundary in ordered_cuts:
                signs = [
                    _sign(weight * (-E * boundary + 20 * B))
                    for weight, (E, B) in zip(weights, rows, strict=True)
                ]
                nonzero = [sign for sign in signs if sign]
                if not nonzero:
                    row_zero_boundaries += 1
                elif len(set(nonzero)) == 1:
                    raise AssertionError(("one-sided leading boundary", k, triple, boundary, weights, rows))
                else:
                    row_mixed_boundaries += 1
                row_boundaries += 1

            for i, j in combinations(range(3), 2):
                separation = abs(roots[i] - roots[j])
                if separation == 0:
                    equal_roots += 1
                    if L**3 <= roots[i] <= U**3:
                        equal_roots_inside += 1
                elif minimum_separation is None or separation < minimum_separation:
                    minimum_separation = separation
            row_triples += 1
        by_row[str(k)] = {
            "unordered_triples": row_triples,
            "exact_lambda_cells": row_cells,
            "mixed_weight_cells": row_mixed,
            "zero_primitive_weights": row_zero_weights,
            "one_sided_weight_cells": 0,
            "rational_boundaries": row_boundaries,
            "mixed_boundaries": row_mixed_boundaries,
            "all_zero_boundaries": row_zero_boundaries,
            "one_sided_boundaries": 0,
        }
        total_triples += row_triples
        total_cells += row_cells
        total_mixed += row_mixed
        total_zero_weights += row_zero_weights
        total_boundaries += row_boundaries
        total_mixed_boundaries += row_mixed_boundaries
        total_zero_boundaries += row_zero_boundaries
    if total_triples != 1_035 or minimum_separation is None:
        raise AssertionError((total_triples, minimum_separation))
    return {
        "totals": {
            "unordered_triples": total_triples,
            "exact_lambda_cells": total_cells,
            "mixed_weight_cells": total_mixed,
            "one_sided_weight_cells": 0,
            "rational_boundaries": total_boundaries,
            "mixed_boundaries": total_mixed_boundaries,
            "all_zero_boundaries": total_zero_boundaries,
            "one_sided_boundaries": 0,
            "zero_primitive_weights": total_zero_weights,
            "equal_root_pairs": equal_roots,
            "equal_root_pairs_inside_window": equal_roots_inside,
            "minimum_unequal_root_separation": f"{minimum_separation.numerator}/{minimum_separation.denominator}",
        },
        "by_row": by_row,
    }


def scaling_verdict(scan: dict[str, Any]) -> dict[str, Any]:
    row_bounds: dict[str, Any] = {}
    for k, (_, U, loss) in ROWS.items():
        row = scan["by_row"][str(k)]
        C6, C7 = row["max_C6"], row["max_C7"]
        # Existing short-window positivity gives P^2 < U*d.  Sixth order,
        # even after proving W6 != 0, gives only P <= C6*g^6*d^3.  Seventh
        # outside its leading-root cells gives only P^2 <= C7*g^6*d^3.
        # The following exact comparisons show both new consequences are
        # already weaker at the target boundary, uniformly in g<=loss.
        existing = U * TARGET
        sixth_rhs = C6 * loss**6 * TARGET**3
        seventh_rhs = C7 * loss**6 * TARGET**3
        if not existing < sixth_rhs or not existing < seventh_rhs:
            raise AssertionError(("unexpected packing improvement", k))
        row_bounds[str(k)] = {
            "existing_square_bound_at_target": existing,
            "sixth_bound_rhs_at_target": sixth_rhs,
            "seventh_square_bound_rhs_at_target": seventh_rhs,
            "sixth_is_weaker_than_existing_square_bound": True,
            "seventh_is_weaker_than_existing_square_bound": True,
        }
    return {
        "formal_implications": [
            "W6 nonzero and P^5|W6 imply P <= C6*g^6*d^3",
            "W7 nonzero and P^6|W7 imply P^2 <= C7*g^6*d^3",
        ],
        "existing_bound": "P^2 < U_k*d",
        "row_comparison": row_bounds,
        "verdict": (
            "Orders six and seven add owner-adic digits, but their exact "
            "archimedean corrections grow cubically in d.  The resulting "
            "component bounds are strictly weaker than P^2<U_k*d.  The "
            "only fixed two-column leading determinant is mixed in every "
            "lambda cell, so it supplies no one-sided packing cutoff."
        ),
    }


@cache
def report() -> dict[str, Any]:
    ordered = ordered_view_scan()
    return {
        "symbolic_formula_certificate": symbolic_formula_certificate(),
        "local_identities": local_identity_grid(),
        "cyclic_compositions": composition_grid(),
        "ordered_window_scan": ordered,
        "seventh_leading_determinant": determinant_scan(),
        "scaling": scaling_verdict(ordered),
        "scope": (
            "exact sixth/seventh local and cyclic lifts plus the verified "
            "short residual window; this is a quantified negative result, "
            "not a proof of Target 1"
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args()
    print(json.dumps(report(), indent=2 if args.pretty else None, sort_keys=True))


if __name__ == "__main__":
    main()
