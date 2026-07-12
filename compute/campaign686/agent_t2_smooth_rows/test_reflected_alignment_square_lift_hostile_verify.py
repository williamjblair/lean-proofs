from __future__ import annotations

from math import gcd

from compute.campaign686.agent_t2_smooth_rows.reflected_alignment_square_lift_hostile_verify import (
    independent_first_failure,
    independent_row,
)


def test_independent_grid() -> None:
    checked = 0
    for k in range(1, 15):
        for n in range(0, 27):
            for d in range(0, 24):
                for i in range(1, k + 1):
                    A = n + i
                    B = n + d + (k + 1 - i)
                    common = gcd(A, B)
                    candidates = {1, common}
                    for q in range(2, min(common, 40) + 1):
                        if common % q == 0:
                            candidates.add(q)
                    for q in candidates:
                        row = independent_row(k, n, d, i, q)
                        assert row["landings"]
                        assert row["quadratic_congruence"]
                        if row["equation_error"] == 0:
                            assert row["weighted_lift"]
                        checked += 1
    assert checked == 109_133


def test_independent_named_boundaries() -> None:
    assert independent_first_failure(984, 3_177_026, 4_480) == 17
    assert independent_first_failure(244, 48_502, 277) == 16


def test_independent_first_order_synthetic_points_fail_new_lift() -> None:
    cases = (
        (984, 3_177_027, 4_480, 1_489, 499),
        (984, 3_177_027, 4_480, 4_271, 597),
        (16, 582_087, 52_684, 59, 7),
        (17, 996_082, 84_632, 19, 12),
        (17, 996_082, 84_632, 31, 10),
        (17, 996_082, 84_632, 41, 13),
        (17, 996_082, 84_632, 43, 13),
    )
    for k, n, d, q, i in cases:
        row = independent_row(k, n, d, i, q)
        assert row["landings"]
        assert row["quadratic_congruence"]
        assert row["cancellable"]
        assert row["equation_error"] != 0
        assert not row["bare_lift"]
