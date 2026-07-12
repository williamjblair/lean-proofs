#!/usr/bin/env python3
"""Exact audit of the ratio-window third-obstruction nonvanishing bridge.

This file is deliberately independent of the Lean coefficient tables.  It
reconstructs the local cofactor polynomial with Python integers, checks the
six rational root brackets, proves the finite residual-floor inequalities,
and enumerates every ordered distinct three-owner placement.

The 121- and 130-digit CRT fixtures are replayed from their frozen exact
reconstructors only as boundary witnesses.  They remain congruence
falsifiers: both fail the block equation (and the coarse upper residual
window), so neither contradicts the equation-facing theorem.
"""

from __future__ import annotations

import json
import sys
from itertools import combinations, permutations
from math import gcd
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))


TARGET = 10**120
DENOMINATOR = 100_000
ROWS = (5, 7, 9, 11, 13, 15)
ROOT_UPPER_NUMERATOR = {
    5: 131_951,
    7: 121_902,
    9: 116_653,
    11: 113_432,
    13: 111_254,
    15: 109_683,
}
RESIDUAL_FLOOR = {5: 8, 7: 12, 9: 15, 11: 20, 13: 23, 15: 29}


def block_product(k: int, n: int) -> int:
    result = 1
    for index in range(1, k + 1):
        result *= n + index
    return result


def local_coefficients(k: int, owner: int) -> tuple[int, int, int]:
    """Low three coefficients of product_(j != owner)(z+j-owner)."""

    coefficients = [1]
    for index in range(1, k + 1):
        if index == owner:
            continue
        offset = index - owner
        updated = [0] * (len(coefficients) + 1)
        for degree, coefficient in enumerate(coefficients):
            updated[degree] += offset * coefficient
            updated[degree + 1] += coefficient
        coefficients = updated
    return coefficients[0], coefficients[1], coefficients[2]


def ratio_bridge_audit() -> dict[str, Any]:
    """Check every exact integer inequality used by the Lean window bridge."""

    rows: list[dict[str, Any]] = []
    for k in ROWS:
        numerator = ROOT_UPPER_NUMERATOR[k]
        denominator = numerator - DENOMINATOR
        residual_numerator = 4 * DENOMINATOR - numerator - 1
        floor = RESIDUAL_FLOOR[k]
        if not 4 * DENOMINATOR**k < numerator**k:
            raise AssertionError(("not an upper bracket", k))
        if not (numerator - 1) ** k <= 4 * DENOMINATOR**k:
            raise AssertionError(("bracket was not minimal at this denominator", k))
        if not denominator * floor <= residual_numerator:
            raise AssertionError(("floor exceeds rational residual bound", k))
        maximum_offset = 3 * denominator * (k - 1)
        if not maximum_offset < TARGET:
            raise AssertionError(("target does not absorb owner offset", k))
        rows.append(
            {
                "k": k,
                "root_upper": f"{numerator}/{DENOMINATOR}",
                "upper_bracket_power_margin":
                    numerator**k - 4 * DENOMINATOR**k,
                "residual_lower": f"{residual_numerator}/{denominator}",
                "residual_floor": floor,
                "floor_margin": residual_numerator - denominator * floor,
                "maximum_absorbed_owner_offset": maximum_offset,
            }
        )
    return {
        "verdict": "PASS",
        "derivation": (
            "B*d < (A-B)*(n+k), then "
            "(4B-A-1)*d < (A-B)*(3*(n+i)-d)"
        ),
        "rows": rows,
    }


def coefficient_dominance_audit() -> dict[str, Any]:
    """Enumerate all 6,210 ordered distinct target triples exactly."""

    total = 0
    per_row: list[dict[str, Any]] = []
    global_main: tuple[int, tuple[int, int, int, int]] | None = None
    global_cutoff: tuple[int, tuple[int, int, int, int]] | None = None
    for k in ROWS:
        floor = RESIDUAL_FLOOR[k]
        row_main: tuple[int, tuple[int, int, int]] | None = None
        row_cutoff: tuple[int, tuple[int, int, int]] | None = None
        count = 0
        for owner, left, right in permutations(range(1, k + 1), 3):
            constant, linear, quadratic = local_coefficients(k, owner)
            delta = (owner - left) * (owner - right)
            main = 9 * abs(constant) * floor**3
            linear_correction = 180 * abs(quadratic * delta)
            constant_correction = 108 * abs(linear * delta)
            main_margin = main - linear_correction
            cutoff_margin = TARGET * main_margin - constant_correction
            if main_margin <= 0 or cutoff_margin <= 0:
                raise AssertionError(
                    (k, owner, left, right, main_margin, cutoff_margin)
                )
            case = (owner, left, right)
            if row_main is None or main_margin < row_main[0]:
                row_main = (main_margin, case)
            if row_cutoff is None or cutoff_margin < row_cutoff[0]:
                row_cutoff = (cutoff_margin, case)
            full_case = (k, owner, left, right)
            if global_main is None or main_margin < global_main[0]:
                global_main = (main_margin, full_case)
            if global_cutoff is None or cutoff_margin < global_cutoff[0]:
                global_cutoff = (cutoff_margin, full_case)
            count += 1
        if row_main is None or row_cutoff is None:
            raise AssertionError(("empty row", k))
        per_row.append(
            {
                "k": k,
                "ordered_distinct_triples": count,
                "minimum_main_margin": row_main[0],
                "minimum_main_case": row_main[1],
                "minimum_cutoff_margin": row_cutoff[0],
                "minimum_cutoff_case": row_cutoff[1],
            }
        )
        total += count
    if total != 6_210 or global_main is None or global_cutoff is None:
        raise AssertionError((total, global_main, global_cutoff))
    return {
        "verdict": "PASS",
        "ordered_distinct_triples": total,
        "minimum_main_margin": global_main[0],
        "minimum_main_case": global_main[1],
        "minimum_cutoff_margin": global_cutoff[0],
        "minimum_cutoff_case": global_cutoff[1],
        "rows": per_row,
    }


def fixed_sign_lattice_audit() -> dict[str, Any]:
    """Audit the lattice after domination fixes sign(z_s)=-sign(C_s)."""

    pattern_counts: dict[str, int] = {}
    row_counts: list[dict[str, Any]] = []
    total = 0
    for k in ROWS:
        mixed = 0
        one_positive = 0
        two_positive = 0
        for indices in combinations(range(1, k + 1), 3):
            rows = []
            for owner in indices:
                others = tuple(index for index in indices if index != owner)
                constant, linear, quadratic = local_coefficients(k, owner)
                delta = (owner - others[0]) * (owner - others[1])
                rows.append(
                    (-9 * constant, 180 * quadratic * delta, 108 * linear * delta)
                )
            raw_weights = (
                rows[1][0] * rows[2][1] - rows[1][1] * rows[2][0],
                rows[2][0] * rows[0][1] - rows[2][1] * rows[0][0],
                rows[0][0] * rows[1][1] - rows[0][1] * rows[1][0],
            )
            divisor = 0
            for weight in raw_weights:
                divisor = gcd(divisor, abs(weight))
            if divisor == 0:
                raise AssertionError(("rank-one coefficient matrix", k, indices))
            weights = tuple(weight // divisor for weight in raw_weights)
            gamma = sum(weight * row[2] for weight, row in zip(weights, rows))
            if gamma == 0:
                raise AssertionError(("zero lattice correction", k, indices))
            if gamma < 0:
                weights = tuple(-weight for weight in weights)
                gamma = -gamma
            term_signs = tuple(
                0
                if weight == 0
                else (1 if weight > 0 else -1)
                * (-1 if constant > 0 else 1)
                for weight, (constant, _linear, _quadratic) in zip(
                    weights,
                    (local_coefficients(k, owner) for owner in indices),
                    strict=True,
                )
            )
            nonzero_signs = set(term_signs) - {0}
            if nonzero_signs != {-1, 1}:
                raise AssertionError(("unexpected one-sided exact cell", k, indices))
            positives = sum(value > 0 for value in term_signs)
            if positives == 1:
                one_positive += 1
            elif positives == 2:
                two_positive += 1
            else:
                raise AssertionError((k, indices, term_signs))
            key = str(term_signs)
            pattern_counts[key] = pattern_counts.get(key, 0) + 1
            mixed += 1
            total += 1
        row_counts.append(
            {
                "k": k,
                "triples": mixed,
                "mixed": mixed,
                "one_positive_term": one_positive,
                "two_positive_terms": two_positive,
            }
        )
    if total != 1_035:
        raise AssertionError(total)
    return {
        "verdict": "PASS",
        "unordered_triples": total,
        "mixed_cells": total,
        "one_sided_cells": 0,
        "patterns": dict(sorted(pattern_counts.items())),
        "rows": row_counts,
        "consequence": (
            "the exact ratio window removes zero quotients but does not make "
            "the primitive weighted lattice one-sided"
        ),
    }


def telescope_boundary_audit() -> list[dict[str, Any]]:
    result = []
    for k, n, d in ((9, 2, 1), (15, 4, 1)):
        result.append(
            {
                "k": k,
                "n": n,
                "d": d,
                "equation":
                    block_product(k, n + d) == 4 * block_product(k, n),
                "target_cutoff": TARGET <= d,
            }
        )
    return result


def crt_boundary_audit() -> dict[str, Any]:
    # Imports are local so the coefficient/window audit above remains fully
    # independent of the producer modules.
    from compute.campaign686.fourth_local_lift_hostile_verify import crt_witness
    from compute.campaign686.multi_owner_extension_hostile_verify import (
        reconstruct_crt_falsifier,
    )

    three = crt_witness(20)
    four = reconstruct_crt_falsifier()
    if not (
        three["gap_digits"] == 121
        and three["all_local_checks"]
        and three["all_composed_checks"]
        and not three["all_short_window_inequalities"]
        and not three["block_equation"]
    ):
        raise AssertionError("121-digit falsifier replay failed")
    if not (
        four["gap_digits"] == 130
        and four["all_local_congruences_hold"]
        and four["all_composed_congruences_hold"]
        and not four["upper_window_holds"]
        and not four["block_equation_holds"]
    ):
        raise AssertionError("130-digit falsifier replay failed")
    return {
        "three_owner_121_digit": {
            "gap_digits": three["gap_digits"],
            "local_and_composed_congruences": True,
            "coarse_upper_residual_window":
                three["all_short_window_inequalities"],
            "block_equation": three["block_equation"],
            "verdict": "outside equation-facing theorem",
        },
        "four_owner_130_digit": {
            "gap_digits": four["gap_digits"],
            "local_and_composed_congruences": True,
            "coarse_upper_residual_window": four["upper_window_holds"],
            "block_equation": four["block_equation_holds"],
            "verdict": "outside exactly-three and equation-facing theorem",
        },
    }


def report() -> dict[str, Any]:
    return {
        "ratio_bridge": ratio_bridge_audit(),
        "coefficient_dominance": coefficient_dominance_audit(),
        "fixed_sign_lattice": fixed_sign_lattice_audit(),
        "telescope_boundary": telescope_boundary_audit(),
        "crt_boundary": crt_boundary_audit(),
        "scope": (
            "proves nonvanishing of all three composed third obstructions; "
            "does not close their joint all-nonzero lattice cancellation"
        ),
    }


if __name__ == "__main__":
    print(json.dumps(report(), indent=2, sort_keys=True))
