from __future__ import annotations

from .large_k_rows import (
    allowed_positions,
    block_equation_holds,
    factor,
    first_failed_row,
    ratio_window_holds,
    row_anatomy,
    row_passes,
    valuation_in_interval,
)


DEEP_17 = (984, 3_177_026, 4_480)
DEEP_16 = (244, 48_502, 277)


def test_factorizations_named_in_falsification_record() -> None:
    assert factor(3_177_026 + 17) == [(439, 1), (7_237, 1)]
    assert factor(48_502 + 16) == [(2, 1), (17, 1), (1_427, 1)]


def test_deep_17_is_exact_window_prefix_survivor_not_equation_solution() -> None:
    k, n, d = DEEP_17
    assert ratio_window_holds(k, n, d)
    assert all(row_passes(k, n, d, row) for row in range(1, 17))
    assert first_failed_row(k, n, d, 17) == 17
    assert not block_equation_holds(k, n, d)

    anatomy = row_anatomy(k, n, d, 17)
    assert anatomy["interval"] == (4_464, 5_447)
    assert anatomy["passes"] is False
    p7237 = next(item for item in anatomy["prime_data"] if item["prime"] == 7_237)
    assert p7237["block_valuation"] == 0
    assert p7237["allowed_positions_for_full_power"] == []


def test_deep_16_is_exact_window_prefix_survivor_not_equation_solution() -> None:
    k, n, d = DEEP_16
    assert ratio_window_holds(k, n, d)
    assert all(row_passes(k, n, d, row) for row in range(1, 16))
    assert first_failed_row(k, n, d, 16) == 16
    assert not block_equation_holds(k, n, d)

    anatomy = row_anatomy(k, n, d, 16)
    assert anatomy["interval"] == (262, 505)
    assert anatomy["passes"] is False
    p1427 = next(item for item in anatomy["prime_data"] if item["prime"] == 1_427)
    assert p1427["block_valuation"] == 0
    assert p1427["allowed_positions_for_full_power"] == []


def test_large_prime_power_has_at_most_one_allowed_position() -> None:
    for k, n, d in (DEEP_16, DEEP_17):
        for row in range(1, min(k, 30) + 1):
            for prime, exponent in factor(n + row):
                prime_power = prime**exponent
                if prime_power > k:
                    assert len(allowed_positions(k, d, row, prime_power)) <= 1


def test_interval_valuation_matches_direct_small_products() -> None:
    for prime in (2, 3, 5, 7, 11):
        for lo, hi in ((1, 20), (17, 53), (262, 505)):
            direct = 0
            for value in range(lo, hi + 1):
                while value % prime == 0:
                    direct += 1
                    value //= prime
            assert valuation_in_interval(prime, lo, hi) == direct
