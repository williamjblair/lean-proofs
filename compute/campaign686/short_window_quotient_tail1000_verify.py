#!/usr/bin/env python3
"""Independent exact audit of the historical quotient-zero ledger.

This verifier deliberately does not import ``short_window_quotient_attack``.
It reconstructs the local coefficient polynomials, fourth/fifth reductions,
primitive third-quotient lattice, and all 2,603 noncentral two-zero
placements directly with Python integers.  Its final tail-size Hensel replay
calls the separately frozen and hostile-audited fifth-lift constructor at a
new exponent; that dependency is reported explicitly rather than described
as an independent reconstruction.

The resulting cutoff census is historical: equation-facing exact-ratio
theorems now exclude every zero third quotient already at ``10^120``.  No
record below is evidence for the live all-nonzero branch.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import itertools
import json
from math import comb, gcd, isqrt
from pathlib import Path
import sys
from typing import Any, Iterable, Sequence


TARGET_ROWS = (5, 7, 9, 11, 13, 15)
TARGET_120 = 10**120
TARGET_130 = 10**130
TARGET_131 = 10**131
TARGET_1000 = 10**1000

RESIDUAL_CEILING = {5: 14, 7: 17, 9: 23, 11: 26, 13: 29, 15: 35}
LOSS_BOUND = {
    5: 108,
    7: 1_620,
    9: 136_080,
    11: 1_224_720,
    13: 242_494_560,
    15: 18_914_575_680,
}

EXPECTED_COEFFICIENT_TABLE_SHA256 = (
    "f1661fe354bbf168be5b81996556c59fe73336bd9e5ad7e3ae5ec2d047068751"
)
EXPECTED_R5_TARGET_TABLE_SHA256 = (
    "2375c14e9b6ccc37598bfa396dedf1e0ff277e81de75cb37fe399e15da5aeb9a"
)


def product(values: Iterable[int]) -> int:
    result = 1
    for value in values:
        result *= value
    return result


def polynomial_mul(left: Sequence[int], right: Sequence[int]) -> list[int]:
    result = [0] * (len(left) + len(right) - 1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            result[i + j] += a * b
    return result


def local_coefficient_polynomial(k: int, owner: int) -> tuple[int, ...]:
    """Coefficients of ``prod_{j != owner} (z+j-owner)`` in low order."""

    coefficients = [1]
    for index in range(1, k + 1):
        if index != owner:
            coefficients = polynomial_mul(coefficients, (index - owner, 1))
    return tuple(coefficients)


def local_coefficients(k: int, owner: int) -> tuple[int, int, int, int, int]:
    coefficients = local_coefficient_polynomial(k, owner)
    return tuple(coefficients[:5])  # type: ignore[return-value]


def reduced_fourth_coefficient(
    C: int, D: int, E: int, F: int, delta_left: int, delta_right: int
) -> int:
    p = delta_left * delta_right
    s = delta_left + delta_right
    return 108 * p * (
        -108 * D**3 * p
        + C * D * (-108 * D * s + 324 * E * p)
        + 567 * C**2 * F * p
    )


def reduced_fifth_coefficient(
    C: int,
    D: int,
    E: int,
    F: int,
    G: int,
    gap: int,
    delta_left: int,
    delta_right: int,
) -> int:
    p = delta_left * delta_right
    s = delta_left + delta_right
    return 8_748 * p * (
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


def reduced_fifth_linear_coefficient(
    C: int,
    D: int,
    E: int,
    F: int,
    G: int,
    delta_left: int,
    delta_right: int,
) -> int:
    p = delta_left * delta_right
    s = delta_left + delta_right
    return 131_220 * p * (
        17 * C**2 * G * p
        - 8 * C * D * E * s
        + 16 * C * D * F * p
        + 12 * C * E**2 * p
        - 8 * D**2 * E * p
    )


def reduced_fifth_quadratic_coefficient(
    C: int,
    D: int,
    E: int,
    F: int,
    delta_left: int,
    delta_right: int,
) -> int:
    p = delta_left * delta_right
    s = delta_left + delta_right
    return 874_800 * E * p * (
        -C * E * s + 4 * C * F * p - D * E * p
    )


def reduced_fifth_decomposition_holds(
    C: int,
    D: int,
    E: int,
    F: int,
    G: int,
    gap: int,
    delta_left: int,
    delta_right: int,
) -> bool:
    fourth = reduced_fourth_coefficient(C, D, E, F, delta_left, delta_right)
    linear = reduced_fifth_linear_coefficient(
        C, D, E, F, G, delta_left, delta_right
    )
    quadratic = reduced_fifth_quadratic_coefficient(
        C, D, E, F, delta_left, delta_right
    )
    return reduced_fifth_coefficient(
        C, D, E, F, G, gap, delta_left, delta_right
    ) == 27 * fourth + gap * linear + gap**2 * quadratic


def primitive_lattice(k: int, owners: tuple[int, int, int]) -> tuple[tuple[int, int, int], int]:
    rows: list[tuple[int, int, int]] = []
    for owner in owners:
        other = tuple(index for index in owners if index != owner)
        C, D, E, _F, _G = local_coefficients(k, owner)
        delta = (owner - other[0]) * (owner - other[1])
        rows.append((-9 * C, 180 * E * delta, 108 * D * delta))

    weights = (
        rows[1][0] * rows[2][1] - rows[2][0] * rows[1][1],
        rows[2][0] * rows[0][1] - rows[0][0] * rows[2][1],
        rows[0][0] * rows[1][1] - rows[1][0] * rows[0][1],
    )
    divisor = 0
    for weight in weights:
        divisor = gcd(divisor, abs(weight))
    if divisor == 0:
        raise AssertionError(("rank-one lattice", k, owners))
    primitive = tuple(weight // divisor for weight in weights)
    gamma = sum(weight * row[2] for weight, row in zip(primitive, rows, strict=True))
    if gamma == 0:
        raise AssertionError(("zero lattice correction", k, owners))
    return primitive, gamma


def coefficient_table_report() -> dict[str, Any]:
    rows = [
        {
            "k": k,
            "owner": owner,
            "coefficients": list(local_coefficients(k, owner)),
        }
        for k in TARGET_ROWS
        for owner in range(1, k + 1)
    ]
    encoded = json.dumps(rows, sort_keys=True, separators=(",", ":")).encode()
    digest = hashlib.sha256(encoded).hexdigest()
    reflection_checks = 0
    for k in TARGET_ROWS:
        for owner in range(1, k + 1):
            reflected = k + 1 - owner
            C, D, E, F, G = local_coefficients(k, owner)
            Cr, Dr, Er, Fr, Gr = local_coefficients(k, reflected)
            if (Cr, Dr, Er, Fr, Gr) != (C, -D, E, -F, G):
                raise AssertionError((k, owner, reflected))
            reflection_checks += 1
    return {
        "owner_rows": len(rows),
        "sha256": digest,
        "reflection_checks": reflection_checks,
        "rows": rows,
    }


def fifth_decomposition_report() -> dict[str, Any]:
    signed_checks = 0
    for C, D, E, F, G, gap, delta_left, delta_right in itertools.product(
        (-11, -1, 0, 7),
        (-5, 0, 3),
        (-4, 0, 6),
        (-3, 1),
        (-2, 0, 5),
        (-9, -1, 0, 1, 13),
        (-4, -1, 1, 3),
        (-3, 2),
    ):
        if not reduced_fifth_decomposition_holds(
            C, D, E, F, G, gap, delta_left, delta_right
        ):
            raise AssertionError(
                (C, D, E, F, G, gap, delta_left, delta_right)
            )
        signed_checks += 1

    target_rows: list[dict[str, int]] = []
    target_decomposition_checks = 0
    quadratic_zero_cases: list[dict[str, int]] = []
    for k in TARGET_ROWS:
        for owner in range(1, k + 1):
            C, D, E, F, G = local_coefficients(k, owner)
            for left in range(1, k + 1):
                if left == owner:
                    continue
                for right in range(1, k + 1):
                    if right == owner or right == left:
                        continue
                    delta_left = owner - left
                    delta_right = owner - right
                    linear = reduced_fifth_linear_coefficient(
                        C, D, E, F, G, delta_left, delta_right
                    )
                    quadratic = reduced_fifth_quadratic_coefficient(
                        C, D, E, F, delta_left, delta_right
                    )
                    if linear == 0:
                        raise AssertionError(("zero R1", k, owner, left, right))
                    row = {
                        "k": k,
                        "owner": owner,
                        "left": left,
                        "right": right,
                        "R1": linear,
                        "R2": quadratic,
                    }
                    target_rows.append(row)
                    if quadratic == 0:
                        if not (
                            owner == (k + 1) // 2 and left + right == k + 1
                        ):
                            raise AssertionError(("unexpected zero R2", row))
                        quadratic_zero_cases.append(row)
                    for gap in (-17, 0, 23):
                        if not reduced_fifth_decomposition_holds(
                            C, D, E, F, G, gap, delta_left, delta_right
                        ):
                            raise AssertionError(("target decomposition", row, gap))
                        target_decomposition_checks += 1

    encoded = json.dumps(target_rows, sort_keys=True, separators=(",", ":")).encode()
    return {
        "signed_fixture_checks": signed_checks,
        "ordered_target_views": len(target_rows),
        "target_decomposition_checks": target_decomposition_checks,
        "linear_nonzero_views": sum(row["R1"] != 0 for row in target_rows),
        "minimum_abs_linear": min(abs(row["R1"]) for row in target_rows),
        "maximum_abs_linear": max(abs(row["R1"]) for row in target_rows),
        "quadratic_nonzero_views": sum(row["R2"] != 0 for row in target_rows),
        "quadratic_zero_views": len(quadratic_zero_cases),
        "all_quadratic_zeros_are_oriented_center_reflections": True,
        "target_table_sha256": hashlib.sha256(encoded).hexdigest(),
        "quadratic_zero_cases": quadratic_zero_cases,
    }


def cutoff_records() -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    for k in TARGET_ROWS:
        center = (k + 1) // 2
        loss = LOSS_BOUND[k]
        for owners in itertools.combinations(range(1, k + 1), 3):
            weights, gamma = primitive_lattice(k, owners)
            fourth_coefficients: list[int] = []
            for owner in owners:
                other = tuple(index for index in owners if index != owner)
                C, D, E, F, _G = local_coefficients(k, owner)
                fourth_coefficients.append(
                    abs(
                        reduced_fourth_coefficient(
                            C, D, E, F, owner - other[0], owner - other[1]
                        )
                    )
                )

            for zero_positions in itertools.combinations(range(3), 2):
                if any(owners[position] == center for position in zero_positions):
                    continue
                remaining_position = next(
                    iter({0, 1, 2} - set(zero_positions))
                )
                weight = abs(weights[remaining_position])
                record: dict[str, Any] = {
                    "k": k,
                    "owners": list(owners),
                    "zero_positions": list(zero_positions),
                    "zero_owners": [owners[position] for position in zero_positions],
                    "remaining_owner": owners[remaining_position],
                    "remaining_weight": weight,
                    "gamma": abs(gamma),
                }
                if weight == 0:
                    record.update(
                        {
                            "kind": "zero_weight_contradiction",
                            "closed_at_10_120": True,
                            "closed_at_10_130": True,
                            "closed_at_10_131": True,
                            "closed_at_10_1000": True,
                        }
                    )
                    records.append(record)
                    continue

                first = fourth_coefficients[zero_positions[0]]
                second = fourth_coefficients[zero_positions[1]]
                if first == 0 or second == 0:
                    raise AssertionError(("noncentral fourth zero", record))
                coefficient_lcm = first // gcd(first, second) * second
                majorant = coefficient_lcm**2 * abs(gamma) * loss**12
                dmin = isqrt(majorant // weight) + 1
                if not (
                    weight * (dmin - 1) ** 2
                    <= majorant
                    < weight * dmin**2
                ):
                    raise AssertionError(("sharp root", record, majorant, dmin))
                record.update(
                    {
                        "kind": "numeric_cutoff",
                        "coefficient_lcm": coefficient_lcm,
                        "majorant": majorant,
                        "Dmin": dmin,
                        "Dmin_digits": len(str(dmin)),
                        "sharp_lower_check": weight * (dmin - 1) ** 2,
                        "sharp_upper_check": weight * dmin**2,
                        "closed_at_10_120": dmin <= TARGET_120,
                        "closed_at_10_130": dmin <= TARGET_130,
                        "closed_at_10_131": dmin <= TARGET_131,
                        "closed_at_10_1000": dmin <= TARGET_1000,
                    }
                )
                records.append(record)
    return records


def cutoff_report() -> dict[str, Any]:
    records = cutoff_records()
    rows: list[dict[str, Any]] = []
    numeric = [record for record in records if record["kind"] == "numeric_cutoff"]
    for k in TARGET_ROWS:
        row = [record for record in records if record["k"] == k]
        row_numeric = [record for record in row if record["kind"] == "numeric_cutoff"]
        row_zero = [
            record for record in row if record["kind"] == "zero_weight_contradiction"
        ]
        rows.append(
            {
                "k": k,
                "placements": len(row),
                "zero_weight_contradictions": len(row_zero),
                "numeric_records": len(row_numeric),
                "numeric_closed_at_10_120": sum(
                    record["closed_at_10_120"] for record in row_numeric
                ),
                "numeric_closed_at_10_1000": sum(
                    record["closed_at_10_1000"] for record in row_numeric
                ),
                "new_numeric_closures_beyond_10_120": sum(
                    record["closed_at_10_1000"]
                    and not record["closed_at_10_120"]
                    for record in row_numeric
                ),
                "maximum_Dmin_digits": max(
                    record["Dmin_digits"] for record in row_numeric
                ),
            }
        )

    maximum = max(record["Dmin"] for record in numeric)
    maximum_records = [record for record in numeric if record["Dmin"] == maximum]
    return {
        "placements": len(records),
        "zero_weight_contradictions": len(records) - len(numeric),
        "numeric_records": len(numeric),
        "numeric_closed_at_10_120": sum(
            record["closed_at_10_120"] for record in numeric
        ),
        "numeric_closed_at_10_1000": sum(
            record["closed_at_10_1000"] for record in numeric
        ),
        "all_closed_at_10_1000": all(
            record["closed_at_10_1000"] for record in records
        ),
        "new_numeric_closures_beyond_10_120": sum(
            record["closed_at_10_1000"] and not record["closed_at_10_120"]
            for record in numeric
        ),
        "open_at_10_130": sum(
            not record["closed_at_10_130"] for record in numeric
        ),
        "open_at_10_131": sum(
            not record["closed_at_10_131"] for record in numeric
        ),
        "maximum_Dmin": maximum,
        "maximum_Dmin_digits": len(str(maximum)),
        "maximum_records": maximum_records,
        "rows": rows,
        "records": records,
    }


def support_subset_ledger() -> dict[str, Any]:
    rows = []
    for k in TARGET_ROWS:
        total = sum(comb(k, size) for size in range(3, k + 1))
        reflected = (k - 1) // 2
        rows.append(
            {
                "k": k,
                "support_subsets_size_at_least_three": total,
                "closed_center_reflected": reflected,
                "open_non_center_reflected": total - reflected,
            }
        )
    return {
        "rows": rows,
        "support_subsets_size_at_least_three": sum(
            row["support_subsets_size_at_least_three"] for row in rows
        ),
        "closed_center_reflected": sum(
            row["closed_center_reflected"] for row in rows
        ),
        "open_non_center_reflected": sum(
            row["open_non_center_reflected"] for row in rows
        ),
    }


def tail_hensel_replay_report() -> dict[str, Any]:
    """Replay the frozen exact fifth-lift constructor above the live cutoff."""

    sys.set_int_max_str_digits(max(sys.get_int_max_str_digits(), 20_000))
    source = (
        Path(__file__).resolve().parent
        / "agent_t1_all_owner"
        / "fifth_local_lift_verify.py"
    )
    spec = importlib.util.spec_from_file_location(
        "erdos686_frozen_fifth_local_lift_verify", source
    )
    if spec is None or spec.loader is None:
        raise AssertionError(("cannot load frozen fifth verifier", source))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    replay = module.crt_fifth_replay(166)
    fifth = replay["fifth_extension"]
    return {
        "source": (
            "frozen hostile-audited fifth_local_lift_verify.crt_fifth_replay"
        ),
        "exponent": replay["exponent"],
        "gap_digits": replay["gap_digits"],
        "n_digits": fifth["n_digits"],
        "all_third_obstructions_nonzero": fifth[
            "all_third_obstructions_nonzero"
        ],
        "all_local_and_reduced_remainders_zero": all(
            not any(fifth[key])
            for key in (
                "local_fifth_remainders",
                "composed_fifth_remainders",
                "squared_quotient_remainders",
                "reduced_remainders",
            )
        ),
        "block_equation": fifth["block_equation"],
        "upper_window_holds": fifth["upper_window_holds"],
    }


def report() -> dict[str, Any]:
    return {
        "scope": (
            "historical quotient-zero arithmetic only; all quotient-zero "
            "branches are equation-facing obsolete and no all-nonzero "
            "closure is claimed"
        ),
        "arithmetic": "exact Python integers only",
        "coefficient_table": coefficient_table_report(),
        "fifth_decomposition": fifth_decomposition_report(),
        "cutoff": cutoff_report(),
        "support_subset_ledger": support_subset_ledger(),
        "tail_hensel_replay": tail_hensel_replay_report(),
    }


def assert_report(result: dict[str, Any]) -> None:
    table = result["coefficient_table"]
    assert table["owner_rows"] == table["reflection_checks"] == 60
    assert table["sha256"] == EXPECTED_COEFFICIENT_TABLE_SHA256

    fifth = result["fifth_decomposition"]
    assert fifth["signed_fixture_checks"] == 8_640
    assert fifth["ordered_target_views"] == 6_210
    assert fifth["target_decomposition_checks"] == 18_630
    assert fifth["linear_nonzero_views"] == 6_210
    assert fifth["minimum_abs_linear"] == 27_818_640
    assert fifth["maximum_abs_linear"] == (
        277_726_044_983_936_190_440_323_571_987_184_359_571_456_000
    )
    assert fifth["quadratic_nonzero_views"] == 6_156
    assert fifth["quadratic_zero_views"] == 54
    assert fifth["all_quadratic_zeros_are_oriented_center_reflections"] is True
    assert fifth["target_table_sha256"] == EXPECTED_R5_TARGET_TABLE_SHA256

    cutoff = result["cutoff"]
    assert cutoff["placements"] == 2_603
    assert cutoff["zero_weight_contradictions"] == 27
    assert cutoff["numeric_records"] == 2_576
    assert cutoff["numeric_closed_at_10_120"] == 2_294
    assert cutoff["numeric_closed_at_10_1000"] == 2_576
    assert cutoff["all_closed_at_10_1000"] is True
    assert cutoff["new_numeric_closures_beyond_10_120"] == 282
    assert cutoff["open_at_10_130"] == 2
    assert cutoff["open_at_10_131"] == 0
    assert cutoff["maximum_Dmin_digits"] == 131
    assert len(cutoff["maximum_records"]) == 2

    expected_rows = {
        5: (18, 2, 16, 0, 28),
        7: (75, 3, 72, 0, 45),
        9: (196, 4, 192, 0, 67),
        11: (405, 5, 400, 0, 82),
        13: (726, 6, 720, 0, 107),
        15: (1_183, 7, 1_176, 282, 131),
    }
    for row in cutoff["rows"]:
        total, zero, numeric, additions, digits = expected_rows[row["k"]]
        assert row["placements"] == total
        assert row["zero_weight_contradictions"] == zero
        assert row["numeric_closed_at_10_1000"] == numeric
        assert row["new_numeric_closures_beyond_10_120"] == additions
        assert row["maximum_Dmin_digits"] == digits

    support = result["support_subset_ledger"]
    assert [
        row["support_subsets_size_at_least_three"] for row in support["rows"]
    ] == [16, 99, 466, 1_981, 8_100, 32_647]
    assert [row["closed_center_reflected"] for row in support["rows"]] == [
        2,
        3,
        4,
        5,
        6,
        7,
    ]
    assert [row["open_non_center_reflected"] for row in support["rows"]] == [
        14,
        96,
        462,
        1_976,
        8_094,
        32_640,
    ]
    assert support["support_subsets_size_at_least_three"] == 43_309
    assert support["closed_center_reflected"] == 27
    assert support["open_non_center_reflected"] == 43_282

    hensel = result["tail_hensel_replay"]
    assert hensel["exponent"] == 166
    assert hensel["gap_digits"] == 1_004
    assert hensel["n_digits"] == 6_023
    assert hensel["all_third_obstructions_nonzero"] is True
    assert hensel["all_local_and_reduced_remainders_zero"] is True
    assert hensel["block_equation"] is False
    assert hensel["upper_window_holds"] is False


def compact_report(result: dict[str, Any]) -> dict[str, Any]:
    compact = dict(result)
    compact["coefficient_table"] = {
        key: value
        for key, value in result["coefficient_table"].items()
        if key != "rows"
    }
    compact["fifth_decomposition"] = {
        key: value
        for key, value in result["fifth_decomposition"].items()
        if key != "quadratic_zero_cases"
    }
    compact["cutoff"] = {
        key: value for key, value in result["cutoff"].items() if key != "records"
    }
    return compact


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--compact", action="store_true")
    args = parser.parse_args()
    result = report()
    assert_report(result)
    if args.compact:
        result = compact_report(result)
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
