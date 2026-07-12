#!/usr/bin/env python3
"""Exact arithmetic for the sharp centered Erdős-686 ratio lane."""

from __future__ import annotations

from fractions import Fraction
from math import comb


ROOT_NUMERATOR = 3_621
ROOT_DENOMINATOR = 2_500


def root_bracket_audit(k_max: int = 1_024) -> dict[str, object]:
    """Reproduce the seven-term exact binomial root bracket."""
    c = Fraction(ROOT_NUMERATOR, ROOT_DENOMINATOR)
    partial = sum(
        (Fraction(comb(16, j)) * (c / 16) ** j for j in range(7)),
        Fraction(),
    )
    expected = Fraction(
        2_048_194_856_715_132_747_962_308_721,
        512_000_000_000_000_000_000_000_000,
    )
    assert partial == expected
    excess = partial - 4
    assert excess == Fraction(
        194_856_715_132_747_962_308_721,
        512_000_000_000_000_000_000_000_000,
    ) > 0

    samples: list[dict[str, int]] = []
    for k in range(16, k_max + 1):
        margin = (
            (ROOT_DENOMINATOR * k + ROOT_NUMERATOR) ** k
            - 4 * (ROOT_DENOMINATOR * k) ** k
        )
        if margin <= 0:
            raise AssertionError(("sharp root bracket", k, margin))
        if k in (16, 17, 19, 64, 256, k_max):
            samples.append({"k": k, "integer_margin": margin})
    return {
        "k_min": 16,
        "k_max": k_max,
        "root_numerator": ROOT_NUMERATOR,
        "root_denominator": ROOT_DENOMINATOR,
        "partial_sum_numerator": partial.numerator,
        "partial_sum_denominator": partial.denominator,
        "excess_numerator": excess.numerator,
        "excess_denominator": excess.denominator,
        "samples": samples,
    }


def sharp_linear_boundary_audit(k_max: int = 10_000) -> dict[str, object]:
    """Audit the exact integer slack behind `23*k*d < 35*n`.

    After multiplying by 35, the contrary assumption contributes
    `253470*n <= 166566*k*d`.  The remaining boundary inequality is
    `126735*(k+1) < 8434*k*d`; its worst case is `d=k`, `k=16`.
    """
    samples: list[dict[str, int]] = []
    for k in range(16, k_max + 1):
        slack = 8_434 * k * k - 126_735 * (k + 1)
        if slack <= 0:
            raise AssertionError(("sharp linear boundary", k, slack))
        if k in (16, 17, 19, 64, 256, k_max):
            samples.append({"k": k, "worst_case_slack": slack})
    assert samples[0] == {"k": 16, "worst_case_slack": 4_609}
    return {"k_min": 16, "k_max": k_max, "samples": samples}


def maximal_fixed_bracket_ratio_audit() -> dict[str, object]:
    """Exact maximal coefficient supported by the fixed `3621/2500` bracket."""
    ratio = Fraction(1_218_443, 1_853_952)
    assert ratio == Fraction(2_500, 3_621) - Fraction(17, 512)
    assert Fraction(23, 35) < ratio < Fraction(7, 10)
    # At k=d=16 the scaled linear boundary is exact equality.
    assert 256 * 17 == 17 * 16 * 16
    return {
        "numerator": ratio.numerator,
        "denominator": ratio.denominator,
        "maximal_cofactor_left": 2 * ratio.denominator,
        "maximal_cofactor_right": ratio.numerator,
        "clean_corollary": "23/35",
    }


def seven_tenths_counterboundary() -> dict[str, object]:
    """Exact ratio-window counterboundary at `(k,n,d)=(16,175,16)`.

    This is not a block-product equation.  It shows that the lower endpoint,
    upper endpoint, and centered power windows are jointly compatible with
    `10*n <= 7*k*d`, so those windows cannot by themselves prove `7/10`.
    """
    k, n, d = 16, 175, 16
    T = 2 * n + k + 1
    W = T + 2 * d
    centered_margin = 4 * T**k - W**k
    lower_margin = (n + d + 1) ** k - 4 * (n + 1) ** k
    upper_margin = 4 * (n + k) ** k - (n + d + k) ** k
    assert (T, W) == (367, 399)
    assert 10 * n <= 7 * k * d
    assert centered_margin > 0
    assert lower_margin >= 0
    assert upper_margin >= 0
    return {
        "k": k,
        "n": n,
        "d": d,
        "ten_n": 10 * n,
        "seven_kd": 7 * k * d,
        "center": T,
        "shifted_center": W,
        "centered_margin": centered_margin,
        "lower_endpoint_margin": lower_margin,
        "upper_endpoint_margin": upper_margin,
        "is_equation": False,
    }


def seven_tenths_bracket_incompatibility() -> dict[str, object]:
    """Exact `k=16` obstruction to the proposed rational-bracket algebra."""
    # A root increment c must exceed 7/5 already at k=16, because
    # `(1 + (7/5)/16)^16 = (87/80)^16 < 4`.
    assert 87**16 < 4 * 80**16
    # But the 7/10 linear comparison at k=d=16 requires
    # `c < 2560/1877`, which is strictly below 7/5.
    linear_ceiling = Fraction(2_560, 1_877)
    assert linear_ceiling < Fraction(7, 5)
    return {
        "root_lower_bound": "7/5",
        "linear_ceiling_numerator": linear_ceiling.numerator,
        "linear_ceiling_denominator": linear_ceiling.denominator,
        "strictly_incompatible": True,
    }


def report() -> dict[str, object]:
    return {
        "root_bracket": root_bracket_audit(),
        "sharp_linear_boundary": sharp_linear_boundary_audit(),
        "maximal_fixed_bracket_ratio": maximal_fixed_bracket_ratio_audit(),
        "seven_tenths_counterboundary": seven_tenths_counterboundary(),
        "seven_tenths_bracket_incompatibility": seven_tenths_bracket_incompatibility(),
        "certified_ratio": "1218443/1853952",
        "certified_cofactor_band": "3707904*a <= 1218443*k",
        "clean_ratio_corollary": "23/35",
        "clean_cofactor_corollary": "70*a <= 23*k",
    }


if __name__ == "__main__":
    import json

    print(json.dumps(report(), indent=2, sort_keys=True))
