#!/usr/bin/env python3
"""Exact audit fixtures for the large-owner aggregation probe.

There are two deliberately different fixtures.

* ``DEEP_17`` is the mandatory falsification-record point. It satisfies the
  exact quotient-four ratio window and rows 1--16, but row 17 and the equation
  fail. It is outside the live quadratic complement.
* ``LIVE_OWNER_CRT`` satisfies the live ratio/strip inequalities, has no prime
  above ``d+k-1`` in either length-``k`` block, and satisfies the complete
  reflection-congruence, reflection-lcm, reflected-owner, and square-lift
  package. Nevertheless it is not an equation and no row divisibility holds.

The second point proves that those aggregated reflection consequences alone
cannot force either a large block prime or a contradiction. A successful
argument must use the individual row divisibilities in a way not captured by
the existing matching/reflection compression.

Every calculation is integer-only. No floating point is used.
"""

from __future__ import annotations

from dataclasses import asdict
from json import dumps
from math import factorial, gcd

from compute.campaign686.large_k_rows import (
    block_equation_holds,
    factor,
    greatest_prime_factor_of_block,
    ratio_window_holds,
    row_passes,
)
from compute.campaign686.reflection_lcm_correlation_verify import (
    owner_correlations,
    reflection_center,
    reflection_congruence,
    reflection_lcm_compression,
    reflection_product_compression,
)


DEEP_17 = (984, 3_177_026, 4_480)
LIVE_OWNER_CRT = (22, 13_237_302_206, 860_968_557)
LIVE_OWNER_COMPONENTS = ((47, 10), (73, 5))


def exact_live_owner_certificate() -> dict[str, object]:
    k, n, d = LIVE_OWNER_CRT
    center = reflection_center(k, n, d)
    bound = d + k - 1
    correlations = owner_correlations(k, n, d)
    residual = [row for row in correlations if row.residual_exponent]

    component_rows: list[dict[str, int | bool]] = []
    for prime, owner in LIVE_OWNER_COMPONENTS:
        row = next(item for item in residual if item.prime == prime)
        square_form = center + 3 * (n + owner)
        center_cofactor = center // prime
        center_gap_gcd = gcd(center_cofactor, d)
        component_rows.append(
            {
                "prime": prime,
                "owner": owner,
                "upper_owner": row.upper_owner,
                "reflection_difference": row.reflection_difference,
                "square_form": square_form,
                "square_quotient": square_form // prime**2,
                "center_cofactor": center_cofactor,
                "center_gap_gcd": center_gap_gcd,
                "gap_coprime_quotient": center_cofactor // center_gap_gcd,
                "reflected": row.reflected,
                "component_ceiling": 2 * prime**2 < 5 * center,
            }
        )

    q_row, r_row = component_rows
    signed_defect = (
        r_row["prime"] ** 2 * r_row["square_quotient"]
        - q_row["prime"] ** 2 * q_row["square_quotient"]
    )

    return {
        "point": LIVE_OWNER_CRT,
        "center": center,
        "center_factorization": factor(center),
        "small_center_cofactor": center // (47 * 73),
        "small_center_cofactor_divides_3_factorial":
            (3 * factorial(k - 1)) % (center // (47 * 73)) == 0,
        "large_prime_bound": bound,
        "lower_block_gpf": greatest_prime_factor_of_block(k, n),
        "upper_block_gpf": greatest_prime_factor_of_block(k, n + d),
        "ratio_window": ratio_window_holds(k, n, d),
        "sharp_ratio": 1_218_443 * k * d < 1_853_952 * n,
        "live_quadratic_strip": k**2 < 18 * d,
        "equation": block_equation_holds(k, n, d),
        "passing_rows": [i for i in range(1, k + 1) if row_passes(k, n, d, i)],
        "reflection_congruence": reflection_congruence(k, n, d),
        "reflection_product_compression": reflection_product_compression(k, n, d),
        "reflection_lcm_compression": reflection_lcm_compression(k, n, d),
        "residual_correlations": [asdict(row) for row in residual],
        "components": component_rows,
        "signed_defect": signed_defect,
        "signed_defect_expected": 3 * (r_row["owner"] - q_row["owner"]),
        "absolute_defect_bound": abs(signed_defect) < 3 * k,
    }


def exact_mandatory_fixture_certificate() -> dict[str, object]:
    k, n, d = DEEP_17
    return {
        "point": DEEP_17,
        "ratio_window": ratio_window_holds(k, n, d),
        "rows_1_through_16": all(row_passes(k, n, d, i) for i in range(1, 17)),
        "row_17": row_passes(k, n, d, 17),
        "row_17_modulus_factorization": factor(n + 17),
        "row_17_interval": (d + 1 - 17, d + k - 17),
        "equation": block_equation_holds(k, n, d),
        "reflection_congruence": reflection_congruence(k, n, d),
        "outside_live_quadratic_complement": 18 * d <= k**2,
    }


def verify() -> None:
    mandatory = exact_mandatory_fixture_certificate()
    assert mandatory == {
        "point": DEEP_17,
        "ratio_window": True,
        "rows_1_through_16": True,
        "row_17": False,
        "row_17_modulus_factorization": [(439, 1), (7_237, 1)],
        "row_17_interval": (4_464, 5_447),
        "equation": False,
        "reflection_congruence": False,
        "outside_live_quadratic_complement": True,
    }

    live = exact_live_owner_certificate()
    assert live["center"] == 27_335_572_992
    assert live["center_factorization"] == [
        (2, 9),
        (3, 2),
        (7, 1),
        (13, 1),
        (19, 1),
        (47, 1),
        (73, 1),
    ]
    assert live["small_center_cofactor"] == 7_967_232
    assert live["small_center_cofactor_divides_3_factorial"] is True
    assert (3 * factorial(21)) // live["small_center_cofactor"] == 19_237_901_760_000
    assert live["large_prime_bound"] == 860_968_578
    assert live["lower_block_gpf"] == 696_700_117
    assert live["upper_block_gpf"] == 671_346_227
    assert live["lower_block_gpf"] <= live["large_prime_bound"]
    assert live["upper_block_gpf"] <= live["large_prime_bound"]
    assert live["ratio_window"] is True
    assert live["sharp_ratio"] is True
    assert live["live_quadratic_strip"] is True
    assert live["equation"] is False
    assert live["passing_rows"] == []
    assert live["reflection_congruence"] is True
    assert live["reflection_product_compression"] is True
    assert live["reflection_lcm_compression"] is True
    assert [row["prime"] for row in live["residual_correlations"]] == [47, 73]

    components = live["components"]
    assert components == [
        {
            "prime": 47,
            "owner": 10,
            "upper_owner": 13,
            "reflection_difference": 860_968_560,
            "square_form": 67_047_479_640,
            "square_quotient": 30_351_960,
            "center_cofactor": 581_607_936,
            "center_gap_gcd": 9,
            "gap_coprime_quotient": 64_623_104,
            "reflected": True,
            "component_ceiling": True,
        },
        {
            "prime": 73,
            "owner": 5,
            "upper_owner": 18,
            "reflection_difference": 860_968_570,
            "square_form": 67_047_479_625,
            "square_quotient": 12_581_625,
            "center_cofactor": 374_459_904,
            "center_gap_gcd": 9,
            "gap_coprime_quotient": 41_606_656,
            "reflected": True,
            "component_ceiling": True,
        },
    ]
    assert live["signed_defect"] == -15
    assert live["signed_defect_expected"] == -15
    assert live["absolute_defect_bound"] is True


if __name__ == "__main__":
    verify()
    print(
        dumps(
            {
                "mandatory_fixture": exact_mandatory_fixture_certificate(),
                "live_owner_fixture": exact_live_owner_certificate(),
            },
            indent=2,
            sort_keys=True,
        )
    )
