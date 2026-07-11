from __future__ import annotations

from math import gcd

from compute.campaign686.global_residual_concentration_verify import (
    DEEP_FIXTURES,
    block_product,
)
from compute.campaign686.two_owner_aggregate_verify import (
    AGGREGATE_LOSS_BUDGETS,
    SECOND_OBSTRUCTION_BOUND,
    TARGET,
    cancellation_implication_holds,
    exact_cubic_pair_bound,
    exact_obstruction_majorant,
    generic_cutoff_bound,
    pell_gcd_consequences_hold,
    report,
    uniform_cubic_cutoff_bound,
)


def test_exact_aggregate_loss_budgets() -> None:
    assert AGGREGATE_LOSS_BUDGETS == {
        5: 108,
        7: 1_620,
        9: 136_080,
        11: 1_224_720,
        13: 242_494_560,
        15: 18_914_575_680,
    }


def test_exact_second_obstruction_majorants_fit_10_pow_16() -> None:
    assert SECOND_OBSTRUCTION_BOUND == 10**16
    assert {k: exact_obstruction_majorant(k) for k in AGGREGATE_LOSS_BUDGETS} == {
        5: 16_512,
        7: 751_248,
        9: 74_507_904,
        11: 8_634_643_200,
        13: 1_422_568_811_520,
        15: 368_002_448_916_480,
    }
    assert all(
        exact_obstruction_majorant(k) < SECOND_OBSTRUCTION_BOUND
        for k in AGGREGATE_LOSS_BUDGETS
    )


def test_all_row_specific_generic_cutoffs() -> None:
    assert all(
        generic_cutoff_bound(k) < TARGET for k in AGGREGATE_LOSS_BUDGETS
    )


def test_all_row_specific_uniform_cubic_cutoffs() -> None:
    assert all(
        uniform_cubic_cutoff_bound(k) < TARGET
        for k in AGGREGATE_LOSS_BUDGETS
    )


def test_all_exact_pairwise_cubic_bounds() -> None:
    values = [
        exact_cubic_pair_bound(k, i, j)
        for k in AGGREGATE_LOSS_BUDGETS
        for i in range(1, k + 1)
        for j in range(1, k + 1)
        if i != j
    ]
    assert len(values) == 610
    assert max(values) == (
        93_984_078_683_194_682_557_325_451_381_987_070_845_762_855_139_556_197_071_318_510_982_175_649_195_251_213_580_361_531_392_000_000_000
    )
    assert max(values) < TARGET


def test_generic_gcd_cancellation_exhaustively() -> None:
    checked = 0
    for modulus in range(1, 41):
        for factor in range(1, 31):
            for coefficient in range(0, 31):
                for delta_multiple in range(1, 31):
                    if (coefficient * factor) % modulus:
                        continue
                    if delta_multiple % gcd(modulus, factor):
                        continue
                    checked += 1
                    assert cancellation_implication_holds(
                        modulus, factor, coefficient, delta_multiple
                    )
    assert checked > 10_000


def test_pell_gcd_consequences_exhaustively() -> None:
    checked = 0
    for a in range(1, 13):
        for b in range(1, 13):
            for p in range(1, 13):
                for q in range(1, 13):
                    difference = a * p * p - b * q * q
                    if difference % 3:
                        continue
                    delta = difference // 3
                    checked += 1
                    assert pell_gcd_consequences_hold(a, b, p, q, delta)
    assert checked > 1_000


def test_named_falsification_boundaries() -> None:
    assert [(k, k // 3 - 1, 1) for k in (3, 6, 9, 12, 15)] == [
        (3, 0, 1),
        (6, 1, 1),
        (9, 2, 1),
        (12, 3, 1),
        (15, 4, 1),
    ]
    for k, n, d in DEEP_FIXTURES:
        assert block_product(k, n + d) != 4 * block_product(k, n)


def test_report_is_fully_green() -> None:
    result = report()
    assert result["all_second_obstructions_below_10_pow_16"] is True
    assert result["all_generic_cutoffs_below_target"] is True
    assert result["all_uniform_cubic_cutoffs_below_target"] is True
    assert result["all_exact_cubic_pair_bounds_below_target"] is True
