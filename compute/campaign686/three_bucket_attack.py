#!/usr/bin/env python3
"""Exact diagnostics for the three cleaned-bucket Erdős 686 kernel.

The arithmetic in this file is integral.  It records the exact second- and
third-order eliminations for three pairwise-coprime cleaned components and
tests the finite coefficient degeneracies in the six odd target rows.

It also constructs CRT witnesses satisfying *all* square-residual, global
moment, second-local, and third-local congruences while deliberately failing
the block equation.  Those witnesses are a route audit: the congruences alone
have no bounded resultant; the remaining information is archimedean (the
verified short window ``0 < X_i < A*d``) plus the exact block equation.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from math import gcd, prod
from typing import Any, Iterable, Sequence


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


def block_product(k: int, n: int) -> int:
    return prod(n + index for index in range(1, k + 1))


def local_taylor_coefficients(k: int, index: int) -> tuple[int, ...]:
    """Coefficients of ``prod_{j != index} (z+j-index)``, low first."""

    if not 1 <= index <= k:
        raise ValueError("expected 1 <= index <= k")
    coefficients = [1]
    for column in range(1, k + 1):
        if column == index:
            continue
        offset = column - index
        updated = [0] * (len(coefficients) + 1)
        for degree, coefficient in enumerate(coefficients):
            updated[degree] += offset * coefficient
            updated[degree + 1] += coefficient
        coefficients = updated
    return tuple(coefficients)


def second_local_value(
    k: int, owner: int, owner_cofactor: int, opposite_product: int
) -> int:
    constant, linear = local_taylor_coefficients(k, owner)[:2]
    return 3 * constant * owner_cofactor - 4 * linear * opposite_product**2


def third_local_value(
    k: int,
    owner: int,
    component: int,
    owner_cofactor: int,
    opposite_product: int,
) -> int:
    quadratic = local_taylor_coefficients(k, owner)[2]
    second = second_local_value(k, owner, owner_cofactor, opposite_product)
    return -3 * second + 20 * quadratic * component * opposite_product**3


def owner_delta(owner: int, other_left: int, other_right: int) -> int:
    return (owner - other_left) * (owner - other_right)


def three_bucket_second_obstruction(
    k: int,
    owner: int,
    other_left: int,
    other_right: int,
    cofactor_product: int,
    loss: int,
) -> int:
    """The exact fixed second-order residue after eliminating two Pell rows."""

    constant, linear = local_taylor_coefficients(k, owner)[:2]
    delta = owner_delta(owner, other_left, other_right)
    return 3 * (
        constant * cofactor_product - 12 * linear * loss**2 * delta
    )


def three_bucket_third_obstruction(
    k: int,
    owner: int,
    other_left: int,
    other_right: int,
    cofactor_product: int,
    loss: int,
    gap: int,
) -> int:
    """The exact third-order residue after the same two Pell eliminations."""

    quadratic = local_taylor_coefficients(k, owner)[2]
    delta = owner_delta(owner, other_left, other_right)
    second = three_bucket_second_obstruction(
        k, owner, other_left, other_right, cofactor_product, loss
    )
    return -3 * second + 180 * quadratic * loss**2 * delta * gap


def verify_owner_elimination(
    *,
    k: int,
    owner: int,
    other_left: int,
    other_right: int,
    component: int,
    left_component: int,
    right_component: int,
    owner_cofactor: int,
    left_cofactor: int,
    right_cofactor: int,
    loss: int,
) -> dict[str, bool]:
    """Check both exact algebraic eliminations for one owner.

    The pair identities are checked rather than assumed.  No primality is
    required for these identities.
    """

    x_owner = owner_cofactor * component**2
    x_left = left_cofactor * left_component**2
    x_right = right_cofactor * right_component**2
    pair_left = x_owner - x_left
    pair_right = x_owner - x_right
    expected_left = 3 * (owner - other_left)
    expected_right = 3 * (owner - other_right)
    if pair_left != expected_left or pair_right != expected_right:
        raise ValueError("the supplied square residuals do not have step three")

    opposite = loss * left_component * right_component
    second_local = second_local_value(k, owner, owner_cofactor, opposite)
    third_local = third_local_value(
        k, owner, component, owner_cofactor, opposite
    )
    cofactor_product = owner_cofactor * left_cofactor * right_cofactor
    gap = loss * component * left_component * right_component
    second_composed = three_bucket_second_obstruction(
        k,
        owner,
        other_left,
        other_right,
        cofactor_product,
        loss,
    )
    third_composed = three_bucket_third_obstruction(
        k,
        owner,
        other_left,
        other_right,
        cofactor_product,
        loss,
        gap,
    )
    return {
        "second_elimination_identity": (
            left_cofactor * right_cofactor * second_local - second_composed
        )
        % component
        == 0,
        "third_elimination_identity": (
            left_cofactor * right_cofactor * third_local - third_composed
        )
        % component**2
        == 0,
    }


def ordered_distinct_triples(k: int) -> Iterable[tuple[int, int, int]]:
    for left in range(1, k + 1):
        for middle in range(1, k + 1):
            if middle == left:
                continue
            for right in range(1, k + 1):
                if right == left or right == middle:
                    continue
                yield left, middle, right


def zero_slope(k: int, owner: int, other_left: int, other_right: int) -> Fraction:
    """Value of ``abc/g^2`` at which the owner's second obstruction vanishes."""

    constant, linear = local_taylor_coefficients(k, owner)[:2]
    return Fraction(
        12 * linear * owner_delta(owner, other_left, other_right), constant
    )


def row_slope_report(k: int) -> dict[str, Any]:
    unordered_count = 0
    positive_slope_count = 0
    maximum_simultaneous_zeros = 0
    minimum_pairwise_separation: Fraction | None = None
    for i in range(1, k + 1):
        for j in range(i + 1, k + 1):
            for ell in range(j + 1, k + 1):
                unordered_count += 1
                indices = (i, j, ell)
                slopes = tuple(
                    zero_slope(
                        k, owner, *tuple(other for other in indices if other != owner)
                    )
                    for owner in indices
                )
                assert len(set(slopes)) == 3
                positive_slope_count += sum(slope > 0 for slope in slopes)
                simultaneous = max(
                    (slopes.count(slope) for slope in slopes if slope > 0),
                    default=0,
                )
                maximum_simultaneous_zeros = max(
                    maximum_simultaneous_zeros, simultaneous
                )
                separations = (
                    abs(slopes[left] - slopes[right])
                    for left in range(3)
                    for right in range(left + 1, 3)
                )
                for separation in separations:
                    if minimum_pairwise_separation is None:
                        minimum_pairwise_separation = separation
                    else:
                        minimum_pairwise_separation = min(
                            minimum_pairwise_separation, separation
                        )
    assert minimum_pairwise_separation is not None
    return {
        "k": k,
        "unordered_index_triples": unordered_count,
        "all_three_slopes_pairwise_distinct": True,
        "maximum_simultaneous_positive_zeros": maximum_simultaneous_zeros,
        "positive_slope_entries": positive_slope_count,
        "minimum_pairwise_slope_separation": {
            "numerator": minimum_pairwise_separation.numerator,
            "denominator": minimum_pairwise_separation.denominator,
        },
    }


def crt(residues: Sequence[int], moduli: Sequence[int]) -> tuple[int, int]:
    if len(residues) != len(moduli) or not residues:
        raise ValueError("CRT expects equal nonempty residue and modulus lists")
    modulus = prod(moduli)
    value = 0
    for residue, local_modulus in zip(residues, moduli, strict=True):
        complement = modulus // local_modulus
        if gcd(complement, local_modulus) != 1:
            raise ValueError("CRT moduli must be pairwise coprime")
        value += (
            residue
            * complement
            * pow(complement, -1, local_modulus)
        )
    return value % modulus, modulus


def elementary_coefficient_one(values: Sequence[int]) -> int:
    return sum(prod(values[:index] + values[index + 1 :]) for index in range(len(values)))


def local_congruence_crt_witness(
    *, k: int, indices: tuple[int, int, int], components: tuple[int, int, int]
) -> dict[str, Any]:
    """Build a non-solution satisfying every currently available congruence.

    The construction first imposes ``P_i^2 | X_i`` by CRT.  Its free
    parameter is then lifted independently modulo each ``P_i^2`` to satisfy
    the third local congruence.  The latter implies the second local
    congruence because all components are coprime to three.
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
    square_moduli = tuple(component**2 for component in components)
    base_residues = tuple(
        (-3 * (index - anchor)) % modulus
        for index, modulus in zip(indices, square_moduli, strict=True)
    )
    base_x, square_product = crt(base_residues, square_moduli)
    gap = prod(components)
    assert square_product == gap**2

    parameter_residues: list[int] = []
    for index, component in zip(indices, components, strict=True):
        shifted = base_x + 3 * (index - anchor)
        assert shifted % component**2 == 0
        base_cofactor = shifted // component**2
        parameter_coefficient = gap**2 // component**2
        constant, linear, quadratic = local_taylor_coefficients(k, index)[:3]
        opposite = gap // component
        third_constant = (
            -3 * (3 * constant * base_cofactor - 4 * linear * opposite**2)
            + 20 * quadratic * component * opposite**3
        )
        third_linear = -9 * constant * parameter_coefficient
        modulus = component**2
        if gcd(third_linear, modulus) != 1:
            raise ValueError("component meets a local coefficient; choose another")
        parameter_residues.append(
            (-third_constant * pow(third_linear, -1, modulus)) % modulus
        )

    parameter, parameter_modulus = crt(parameter_residues, square_moduli)
    assert parameter_modulus == gap**2

    # Adding ``gap^2`` to the parameter preserves every local congruence;
    # adding it three times lets us choose the residue needed for integral n.
    chosen_parameter = parameter
    for lift in range(3):
        candidate = parameter + gap**2 * lift
        candidate_x = base_x + gap**2 * candidate
        if (candidate_x + gap) % 3 == 0:
            chosen_parameter = candidate
            break
    x_anchor = base_x + gap**2 * chosen_parameter
    if (x_anchor + gap) % 3:
        raise AssertionError("failed to make the reconstructed n integral")
    n = (x_anchor + gap) // 3 - anchor
    if n < 0:
        raise AssertionError("the constructed witness should be positive")

    cofactors: list[int] = []
    local_checks: list[dict[str, Any]] = []
    for index, component in zip(indices, components, strict=True):
        residual = 3 * (n + index) - gap
        assert residual > 0 and residual % component**2 == 0
        cofactor = residual // component**2
        cofactors.append(cofactor)
        opposite = gap // component
        second = second_local_value(k, index, cofactor, opposite)
        third = third_local_value(k, index, component, cofactor, opposite)
        local_checks.append(
            {
                "index": index,
                "component_digits": len(str(component)),
                "second_mod_component": second % component,
                "third_mod_component_square": third % component**2,
                "divides_lower_factor": (n + index) % component == 0,
            }
        )

    lower = [n + index - gap for index in range(1, k + 1)]
    upper = [3 * (n + index) + gap for index in range(1, k + 1)]
    lower_moment = (
        3 * prod(lower) + 2 * gap * elementary_coefficient_one(lower)
    )
    upper_moment = (
        3 * prod(upper) - 6 * gap * elementary_coefficient_one(upper)
    )
    equation = block_product(k, n + gap) == 4 * block_product(k, n)
    residual_max = max(3 * (n + index) - gap for index in indices)
    return {
        "k": k,
        "indices": list(indices),
        "gap_digits": len(str(gap)),
        "gap_above_target": gap >= TARGET,
        "n_digits": len(str(n)),
        "local_checks": local_checks,
        "lower_global_moment_mod_gap_cube": lower_moment % gap**3,
        "upper_global_moment_mod_gap_cube": upper_moment % gap**3,
        "all_current_congruences_hold": all(
            check["second_mod_component"] == 0
            and check["third_mod_component_square"] == 0
            and check["divides_lower_factor"]
            for check in local_checks
        )
        and lower_moment % gap**3 == 0
        and upper_moment % gap**3 == 0,
        "block_equation_holds": equation,
        "short_window_holds": residual_max < ROWS[k] * gap,
        "residual_to_gap_floor": residual_max // gap,
    }


def signed_algebra_grid() -> dict[str, int]:
    """Exercise both elimination identities over signed exact fixtures."""

    checks = 0
    for k in (5, 7):
        for owner, left, right in ((1, 2, 4), (4, 1, 5), (3, 1, 5)):
            for component in (-2, -1, 1, 2):
                for left_component in (-2, -1, 1, 2):
                    for right_component in (-2, -1, 1, 2):
                        # Choose the two nearby residuals from the owner one.
                        # Only retain exact integral quotients.
                        for owner_cofactor in range(-20, 21):
                            x_owner = owner_cofactor * component**2
                            x_left = x_owner - 3 * (owner - left)
                            x_right = x_owner - 3 * (owner - right)
                            if (
                                x_left % left_component**2
                                or x_right % right_component**2
                            ):
                                continue
                            left_cofactor = x_left // left_component**2
                            right_cofactor = x_right // right_component**2
                            result = verify_owner_elimination(
                                k=k,
                                owner=owner,
                                other_left=left,
                                other_right=right,
                                component=component,
                                left_component=left_component,
                                right_component=right_component,
                                owner_cofactor=owner_cofactor,
                                left_cofactor=left_cofactor,
                                right_cofactor=right_cofactor,
                                loss=3,
                            )
                            assert all(result.values())
                            checks += 1
    return {"signed_exact_elimination_fixtures": checks}


def report() -> dict[str, Any]:
    row_reports = [row_slope_report(k) for k in ROWS]
    witness = local_congruence_crt_witness(
        k=5,
        indices=(1, 2, 4),
        components=(101**20, 103**20, 107**20),
    )
    return {
        "rows": row_reports,
        "all_rows_have_at_most_one_zero_second_obstruction": all(
            row["maximum_simultaneous_positive_zeros"] <= 1
            for row in row_reports
        ),
        "all_row_slopes_pairwise_distinct": all(
            row["all_three_slopes_pairwise_distinct"] for row in row_reports
        ),
        "loss_budgets": LOSS_BUDGETS,
        "signed_grid": signed_algebra_grid(),
        "target_size_congruence_only_witness": witness,
        "route_verdict": (
            "second/third local lifts and both global cubic moments have no "
            "standalone bounded resultant for three buckets; the target-size "
            "CRT witness fails exactly the short window and block equation"
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args()
    print(json.dumps(report(), indent=2 if args.pretty else None, sort_keys=True))


if __name__ == "__main__":
    main()
