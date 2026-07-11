#!/usr/bin/env python3
"""Exact fourth-local-lift diagnostics for the three-owner Erdős 686 core.

This verifier uses Python integers only.  It independently reconstructs the
local Taylor coefficients, checks the denominator-cleared fourth-order
identity including every residual-cofactor correction, composes that identity
with the two square-residual differences, and lifts the established
three-owner CRT non-solution by one further owner-adic digit.

The CRT output is a route falsifier, not an Erdős 686 counterexample: it
deliberately fails both the short window and the exact block equation.
"""

from __future__ import annotations

import argparse
import json
from functools import cache
from math import gcd, prod
from typing import Any, Sequence


ROWS = {5: 14, 7: 17, 9: 23, 11: 26, 13: 29, 15: 35}
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
        updated = [0] * (len(coefficients) + 1)
        for degree, coefficient in enumerate(coefficients):
            updated[degree] += offset * coefficient
            updated[degree + 1] += coefficient
        coefficients = updated
    return tuple(coefficients)


def third_local_value(
    constant: int,
    linear: int,
    quadratic: int,
    component: int,
    opposite: int,
    cofactor: int,
) -> int:
    """The banked third local residue, before reducing modulo ``component^2``."""

    second = 3 * constant * cofactor - 4 * linear * opposite**2
    return -3 * second + 20 * quadratic * component * opposite**3


def fourth_local_value(
    constant: int,
    linear: int,
    quadratic: int,
    cubic: int,
    component: int,
    opposite: int,
    cofactor: int,
) -> int:
    """The exact denominator-cleared fourth local residue.

    If ``3*L-component*opposite = cofactor*component^2`` and the block
    equation holds, this value is divisible by ``component^3``.
    """

    third = third_local_value(
        constant, linear, quadratic, component, opposite, cofactor
    )
    correction = (
        -9 * linear * cofactor**2
        + 36 * quadratic * cofactor * opposite**2
        + 84 * cubic * opposite**4
    )
    return 3 * third + component**2 * correction


def local_denominator_clearing_difference(
    *,
    constant: int,
    linear: int,
    quadratic: int,
    cubic: int,
    component: int,
    opposite: int,
    cofactor: int,
    quotient: int,
) -> int:
    """Return ``27*T4 - fourth_local_value`` for ``3X-M=A*H``.

    The result is identically divisible by ``H^3``.  Keeping this computation
    separate catches the common but false formula obtained by setting A=0.
    """

    if 3 * quotient - opposite != cofactor * component:
        raise ValueError("expected 3*X-M=A*H")
    upper_quotient = quotient + opposite
    reduced = (
        -constant * cofactor
        + linear * (upper_quotient**2 - 4 * quotient**2)
        + component
        * quadratic
        * (upper_quotient**3 - 4 * quotient**3)
        + component**2
        * cubic
        * (upper_quotient**4 - 4 * quotient**4)
    )
    return 27 * reduced - fourth_local_value(
        constant,
        linear,
        quadratic,
        cubic,
        component,
        opposite,
        cofactor,
    )


def owner_delta(owner: int, other_left: int, other_right: int) -> tuple[int, int]:
    return owner - other_left, owner - other_right


def three_bucket_second_obstruction(
    *,
    constant: int,
    linear: int,
    cofactor_product: int,
    loss: int,
    delta_left: int,
    delta_right: int,
) -> int:
    return 3 * (
        constant * cofactor_product
        - 12 * linear * loss**2 * delta_left * delta_right
    )


def three_bucket_third_obstruction(
    *,
    constant: int,
    linear: int,
    quadratic: int,
    cofactor_product: int,
    loss: int,
    delta_left: int,
    delta_right: int,
    gap: int,
) -> int:
    second = three_bucket_second_obstruction(
        constant=constant,
        linear=linear,
        cofactor_product=cofactor_product,
        loss=loss,
        delta_left=delta_left,
        delta_right=delta_right,
    )
    return (
        -3 * second
        + 180
        * quadratic
        * loss**2
        * delta_left
        * delta_right
        * gap
    )


def three_bucket_fourth_correction(
    *,
    linear: int,
    quadratic: int,
    cubic: int,
    cofactor_product: int,
    loss: int,
    delta_left: int,
    delta_right: int,
) -> int:
    """Correction after eliminating both opposite squares modulo ``P^3``."""

    delta_product = delta_left * delta_right
    delta_sum = delta_left + delta_right
    t = cofactor_product
    return (
        -9 * linear * t**2
        - 108 * linear * t * loss**2 * delta_sum
        + 324 * quadratic * t * loss**2 * delta_product
        + 6804 * cubic * loss**4 * delta_product**2
    )


def three_bucket_fourth_obstruction(
    *,
    k: int,
    owner: int,
    other_left: int,
    other_right: int,
    owner_component: int,
    owner_cofactor: int,
    left_cofactor: int,
    right_cofactor: int,
    loss: int,
    gap: int,
) -> int:
    """The cyclic fourth obstruction at one cleaned owner.

    With ``P=owner_component`` and ``t=abc``, this is

    ``3*b*c*F_i + P^2*J_i``.

    The two square-residual differences turn the raw fourth lift into
    ``P^3`` divisibility of this integral polynomial.
    """

    constant, linear, quadratic, cubic = local_coefficients(k, owner)[:4]
    delta_left, delta_right = owner_delta(owner, other_left, other_right)
    t = owner_cofactor * left_cofactor * right_cofactor
    third = three_bucket_third_obstruction(
        constant=constant,
        linear=linear,
        quadratic=quadratic,
        cofactor_product=t,
        loss=loss,
        delta_left=delta_left,
        delta_right=delta_right,
        gap=gap,
    )
    correction = three_bucket_fourth_correction(
        linear=linear,
        quadratic=quadratic,
        cubic=cubic,
        cofactor_product=t,
        loss=loss,
        delta_left=delta_left,
        delta_right=delta_right,
    )
    return (
        3 * left_cofactor * right_cofactor * third
        + owner_component**2 * correction
    )


def verify_composed_identity(
    *,
    k: int,
    owner: int,
    other_left: int,
    other_right: int,
    owner_component: int,
    left_component: int,
    right_component: int,
    owner_cofactor: int,
    left_cofactor: int,
    right_cofactor: int,
    loss: int,
) -> bool:
    """Check the exact fourth square-residual elimination at one owner."""

    p = owner_component
    x_owner = owner_cofactor * p**2
    x_left = left_cofactor * left_component**2
    x_right = right_cofactor * right_component**2
    delta_left, delta_right = owner_delta(owner, other_left, other_right)
    if x_owner - x_left != 3 * delta_left:
        raise ValueError("left residual difference mismatch")
    if x_owner - x_right != 3 * delta_right:
        raise ValueError("right residual difference mismatch")

    opposite = loss * left_component * right_component
    constant, linear, quadratic, cubic = local_coefficients(k, owner)[:4]
    raw = fourth_local_value(
        constant,
        linear,
        quadratic,
        cubic,
        p,
        opposite,
        owner_cofactor,
    )
    gap = loss * p * left_component * right_component
    composed = three_bucket_fourth_obstruction(
        k=k,
        owner=owner,
        other_left=other_left,
        other_right=other_right,
        owner_component=p,
        owner_cofactor=owner_cofactor,
        left_cofactor=left_cofactor,
        right_cofactor=right_cofactor,
        loss=loss,
        gap=gap,
    )
    modulus = abs(p) ** 3
    if modulus == 0:
        raise ValueError("zero owner component")
    return ((left_cofactor * right_cofactor) ** 2 * raw - composed) % modulus == 0


def signed_composition_grid() -> dict[str, int | bool]:
    """Exercise local and composed formulas over signed exact fixtures."""

    local_checks = 0
    composition_checks = 0
    for k in (5, 7, 9):
        for owner, left, right in ((1, 2, 4), (3, 1, 5), (4, 1, 5)):
            if max(owner, left, right) > k:
                continue
            constant, linear, quadratic, cubic = local_coefficients(k, owner)[:4]
            for component in (-5, -3, -2, -1, 1, 2, 3, 5):
                for opposite in range(-9, 10):
                    for cofactor in range(-7, 8):
                        numerator = opposite + cofactor * component
                        if numerator % 3:
                            continue
                        quotient = numerator // 3
                        difference = local_denominator_clearing_difference(
                            constant=constant,
                            linear=linear,
                            quadratic=quadratic,
                            cubic=cubic,
                            component=component,
                            opposite=opposite,
                            cofactor=cofactor,
                            quotient=quotient,
                        )
                        assert difference % abs(component) ** 3 == 0
                        local_checks += 1

            for p in (-3, -2, -1, 1, 2, 3):
                for q in (-3, -2, -1, 1, 2, 3):
                    for r in (-3, -2, -1, 1, 2, 3):
                        for a in range(-12, 13):
                            x = a * p**2
                            x_left = x - 3 * (owner - left)
                            x_right = x - 3 * (owner - right)
                            if x_left % q**2 or x_right % r**2:
                                continue
                            b = x_left // q**2
                            c = x_right // r**2
                            for loss in (-2, 1, 3):
                                assert verify_composed_identity(
                                    k=k,
                                    owner=owner,
                                    other_left=left,
                                    other_right=right,
                                    owner_component=p,
                                    left_component=q,
                                    right_component=r,
                                    owner_cofactor=a,
                                    left_cofactor=b,
                                    right_cofactor=c,
                                    loss=loss,
                                )
                                composition_checks += 1
    return {
        "signed_local_denominator_fixtures": local_checks,
        "signed_exact_composition_fixtures": composition_checks,
        "all_fourth_compositions_hold": True,
    }


def crt(residues: Sequence[int], moduli: Sequence[int]) -> tuple[int, int]:
    if len(residues) != len(moduli) or not residues:
        raise ValueError("CRT expects equal nonempty lists")
    modulus = prod(moduli)
    value = 0
    for residue, local_modulus in zip(residues, moduli, strict=True):
        complement = modulus // local_modulus
        if gcd(complement, local_modulus) != 1:
            raise ValueError("CRT moduli must be pairwise coprime")
        value += residue * complement * pow(complement, -1, local_modulus)
    return value % modulus, modulus


def _cofactor_at_parameter(
    *,
    base_x: int,
    gap: int,
    parameter: int,
    anchor: int,
    index: int,
    component: int,
) -> int:
    shifted = base_x + gap**2 * parameter + 3 * (index - anchor)
    if shifted % component**2:
        raise AssertionError("square residual lost during CRT lift")
    return shifted // component**2


def local_congruence_crt_witness_fourth(
    *, k: int, indices: tuple[int, int, int], components: tuple[int, int, int]
) -> dict[str, Any]:
    """Lift the known three-owner non-solution through fourth order.

    First solve the third congruence for the free square-residual parameter
    modulo each ``P^2``.  Then write ``parameter=t0+gap^2*u`` and solve the
    fourth congruence modulo each ``P``.  The derivative after division by
    ``P^2`` is ``-27*C_i*(gap/P)^4``, a unit for this fixture.
    """

    if len(set(indices)) != 3 or not all(1 <= index <= k for index in indices):
        raise ValueError("expected three distinct row indices")
    if any(component <= 1 or component % 3 == 0 for component in components):
        raise ValueError("components must exceed one and be coprime to three")
    if any(
        gcd(components[left], components[right]) != 1
        for left in range(3)
        for right in range(left + 1, 3)
    ):
        raise ValueError("components must be pairwise coprime")

    anchor = indices[0]
    gap = prod(components)
    square_moduli = tuple(component**2 for component in components)
    base_residues = tuple(
        (-3 * (index - anchor)) % modulus
        for index, modulus in zip(indices, square_moduli, strict=True)
    )
    base_x, square_product = crt(base_residues, square_moduli)
    if square_product != gap**2:
        raise AssertionError("square CRT modulus mismatch")

    third_parameter_residues: list[int] = []
    for index, component in zip(indices, components, strict=True):
        base_cofactor = _cofactor_at_parameter(
            base_x=base_x,
            gap=gap,
            parameter=0,
            anchor=anchor,
            index=index,
            component=component,
        )
        parameter_coefficient = gap**2 // component**2
        constant, linear, quadratic = local_coefficients(k, index)[:3]
        opposite = gap // component
        constant_value = third_local_value(
            constant,
            linear,
            quadratic,
            component,
            opposite,
            base_cofactor,
        )
        derivative = -9 * constant * parameter_coefficient
        modulus = component**2
        if gcd(derivative, modulus) != 1:
            raise ValueError("third-lift derivative is not a unit")
        third_parameter_residues.append(
            (-constant_value * pow(derivative, -1, modulus)) % modulus
        )

    third_parameter, third_parameter_modulus = crt(
        third_parameter_residues, square_moduli
    )
    if third_parameter_modulus != gap**2:
        raise AssertionError("third parameter modulus mismatch")

    third_only_fourth_residues: list[int] = []
    fourth_lift_residues: list[int] = []
    for index, component in zip(indices, components, strict=True):
        cofactor = _cofactor_at_parameter(
            base_x=base_x,
            gap=gap,
            parameter=third_parameter,
            anchor=anchor,
            index=index,
            component=component,
        )
        constant, linear, quadratic, cubic = local_coefficients(k, index)[:4]
        opposite = gap // component
        value = fourth_local_value(
            constant,
            linear,
            quadratic,
            cubic,
            component,
            opposite,
            cofactor,
        )
        if value % component**2:
            raise AssertionError("third parameter did not reach fourth base")
        quotient_residue = (value // component**2) % component
        third_only_fourth_residues.append(quotient_residue)
        derivative = -27 * constant * (gap // component) ** 4
        if gcd(derivative, component) != 1:
            raise ValueError("fourth-lift derivative is not a unit")
        fourth_lift_residues.append(
            (-quotient_residue * pow(derivative, -1, component)) % component
        )

    lift_parameter, lift_modulus = crt(fourth_lift_residues, components)
    if lift_modulus != gap:
        raise AssertionError("fourth lift modulus mismatch")
    fourth_parameter = third_parameter + gap**2 * lift_parameter

    # Adding gap^3 preserves every fourth congruence.  Select one of three
    # representatives that reconstructs an integral n.
    chosen_parameter = fourth_parameter
    for lift in range(3):
        candidate = fourth_parameter + gap**3 * lift
        candidate_x = base_x + gap**2 * candidate
        if (candidate_x + gap) % 3 == 0:
            chosen_parameter = candidate
            break
    x_anchor = base_x + gap**2 * chosen_parameter
    if (x_anchor + gap) % 3:
        raise AssertionError("failed to reconstruct integral n")
    n = (x_anchor + gap) // 3 - anchor
    if n < 0:
        raise AssertionError("expected a positive CRT non-solution")

    cofactors: list[int] = []
    local_checks: list[dict[str, Any]] = []
    for position, (index, component) in enumerate(
        zip(indices, components, strict=True)
    ):
        residual = 3 * (n + index) - gap
        if residual <= 0 or residual % component**2:
            raise AssertionError("final square residual failed")
        cofactor = residual // component**2
        cofactors.append(cofactor)
        constant, linear, quadratic, cubic = local_coefficients(k, index)[:4]
        opposite = gap // component
        second = 3 * constant * cofactor - 4 * linear * opposite**2
        third = third_local_value(
            constant, linear, quadratic, component, opposite, cofactor
        )
        fourth = fourth_local_value(
            constant,
            linear,
            quadratic,
            cubic,
            component,
            opposite,
            cofactor,
        )
        block_difference = block_product(k, n + gap) - 4 * block_product(k, n)
        local_checks.append(
            {
                "index": index,
                "component_digits": len(str(component)),
                "square_residual_mod_component_square": residual % component**2,
                "second_mod_component": second % component,
                "third_mod_component_square": third % component**2,
                "fourth_mod_component_cube": fourth % component**3,
                "block_difference_mod_component_fifth": (
                    block_difference % component**5
                ),
                "divides_lower_factor": (n + index) % component == 0,
                "position": position,
            }
        )

    composed_checks: list[dict[str, int]] = []
    for position, (owner, component) in enumerate(
        zip(indices, components, strict=True)
    ):
        other_positions = [offset for offset in range(3) if offset != position]
        left_position, right_position = other_positions
        composed = three_bucket_fourth_obstruction(
            k=k,
            owner=owner,
            other_left=indices[left_position],
            other_right=indices[right_position],
            owner_component=component,
            owner_cofactor=cofactors[position],
            left_cofactor=cofactors[left_position],
            right_cofactor=cofactors[right_position],
            loss=1,
            gap=gap,
        )
        composed_checks.append(
            {
                "index": owner,
                "fourth_composed_mod_component_cube": composed % component**3,
            }
        )

    block_equation = block_product(k, n + gap) == 4 * block_product(k, n)
    largest_residual = max(3 * (n + index) - gap for index in indices)
    all_local = all(
        check["square_residual_mod_component_square"] == 0
        and check["second_mod_component"] == 0
        and check["third_mod_component_square"] == 0
        and check["fourth_mod_component_cube"] == 0
        and check["block_difference_mod_component_fifth"] == 0
        and check["divides_lower_factor"]
        for check in local_checks
    )
    all_composed = all(
        check["fourth_composed_mod_component_cube"] == 0
        for check in composed_checks
    )
    return {
        "k": k,
        "indices": list(indices),
        "gap": gap,
        "gap_digits": len(str(gap)),
        "gap_above_target": gap >= TARGET,
        "n_digits": len(str(n)),
        "third_only_fourth_quotient_residues": third_only_fourth_residues,
        "third_only_already_satisfied_fourth": all(
            residue == 0 for residue in third_only_fourth_residues
        ),
        "local_checks": local_checks,
        "composed_checks": composed_checks,
        "all_square_second_third_fourth_congruences_hold": all_local,
        "all_composed_fourth_congruences_hold": all_composed,
        "block_equation_holds": block_equation,
        "short_window_holds": largest_residual < ROWS[k] * gap,
        "residual_to_gap_floor": largest_residual // gap,
    }


def checked_exponent_family() -> dict[str, Any]:
    """Reproduce a geometric range of the unbounded CRT lift family."""

    exponents = (1, 2, 3, 5, 8, 10, 12, 16, 20, 24)
    rows: list[dict[str, Any]] = []
    for exponent in exponents:
        witness = local_congruence_crt_witness_fourth(
            k=5,
            indices=(1, 2, 4),
            components=(101**exponent, 103**exponent, 107**exponent),
        )
        rows.append(
            {
                "exponent": exponent,
                "gap_digits": witness["gap_digits"],
                "n_digits": witness["n_digits"],
                "all_local_congruences": witness[
                    "all_square_second_third_fourth_congruences_hold"
                ],
                "all_composed_congruences": witness[
                    "all_composed_fourth_congruences_hold"
                ],
                "third_only_already_fourth": witness[
                    "third_only_already_satisfied_fourth"
                ],
                "short_window": witness["short_window_holds"],
                "block_equation": witness["block_equation_holds"],
            }
        )
    return {
        "rows": rows,
        "all_checked_lifts_hold": all(
            row["all_local_congruences"] and row["all_composed_congruences"]
            for row in rows
        ),
        "all_checked_members_are_proper_nonshort_nonsolutions": all(
            not row["third_only_already_fourth"]
            and not row["short_window"]
            and not row["block_equation"]
            for row in rows
        ),
    }


def report() -> dict[str, Any]:
    witness = local_congruence_crt_witness_fourth(
        k=5,
        indices=(1, 2, 4),
        components=(101**20, 103**20, 107**20),
    )
    grid = signed_composition_grid()
    return {
        "rows": ROWS,
        "exact_formula": (
            "H^3 divides 3*T3 + H^2*(-9*D*A^2 + 36*E*A*M^2 + "
            "84*F*M^4)"
        ),
        "signed_grid": grid,
        "checked_exponent_family": checked_exponent_family(),
        "target_size_fourth_order_crt_falsifier": witness,
        "proper_strengthening": not witness[
            "third_only_already_satisfied_fourth"
        ],
        "bounded_resultant_verdict": (
            "NO: the fourth lift is a proper one-digit strengthening, but an "
            "exact target-size CRT lift satisfies it cyclically while failing "
            "the short window and the block equation"
        ),
        "remaining_gap": (
            "exploit the verified short window together with the cyclic "
            "fourth congruences; congruence-only lifting remains unbounded"
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args()
    print(json.dumps(report(), indent=2 if args.pretty else None, sort_keys=True))


if __name__ == "__main__":
    main()
