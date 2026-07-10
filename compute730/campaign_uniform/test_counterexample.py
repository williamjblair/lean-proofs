"""Pytest certificates for the #730 incomplete-block counterexample.

All assertions in this file are exact integer assertions.  In particular,
the theorem-level comparison clears the denominator p^(2r); it does not use
the floating-point logarithm printed by the diagnostic CLI.
"""

import pytest

from compute730.campaign_uniform.test_uniformity import (
    A,
    BRANCHES,
    expanded_value,
    q_branch_scan,
    root_data,
    validate_maps,
)


def test_exact_expanded_coefficients_and_permutations() -> None:
    assert A == 84_591_927_504
    assert {name: branch["b"] for name, branch in BRANCHES.items()} == {
        "P": -1_301_094,
        "Q": 1_301_094,
        "R": 1_364_562,
        "S": -1_364_562,
    }
    validate_maps()


@pytest.mark.parametrize(
    ("p", "r", "expected_start", "expected_hits"),
    [
        (5, 2, 137, 6),
        (7, 3, 16_138, 16),
        (11, 2, 1_461, 14),
    ],
)
def test_exact_interval_counts_and_integer_main_term(
    p: int, r: int, expected_start: int, expected_hits: int
) -> None:
    row = q_branch_scan(p, r)
    assert row["a"] == 2 * r
    assert row["max_exact_start"] == expected_start
    assert row["max_exact"] == expected_hits
    assert len(row["hits"]) == expected_hits

    # Exact comparison with |I| * ((p+1)/(2p))^(2r).
    h = (p + 1) // 2
    denominator = p ** (2 * r)
    numerator = h ** (2 * r) * row["N"]
    assert expected_hits * denominator > numerator


def test_p7_only_q_and_s_have_admissible_roots() -> None:
    assert BRANCHES["P"]["lam"] % 7 == 0
    assert BRANCHES["P"]["mu"] % 7 != 0
    assert BRANCHES["R"]["lam"] % 7 == 0
    assert BRANCHES["R"]["mu"] % 7 != 0
    assert BRANCHES["Q"]["lam"] % 7 != 0
    assert BRANCHES["S"]["lam"] % 7 != 0


@pytest.mark.parametrize(
    ("p", "r", "a"),
    [
        (5, 4, 5),   # s=3
        (7, 4, 7),   # s=1
        (11, 4, 6),  # s=2
        (5, 4, 9),   # a>2r, so s=0
    ],
)
def test_exact_near_affine_progression_identity(p: int, r: int, a: int) -> None:
    branch = BRANCHES["Q"]
    _, c0 = root_data(branch, p, a)
    modulus = p ** (2 * r)
    s = max(2 * r - a, 0)
    step = p ** max(s, 1)  # also preserves the exact valuation class
    for k in (0, 1, 17, modulus - 1):
        for multiplier in (-3, -1, 0, 1, 4):
            t = step * multiplier
            difference = (
                expanded_value(branch, p, a, c0, k + t)
                - expanded_value(branch, p, a, c0, k)
                - branch["b"] * t
            )
            assert difference % modulus == 0
