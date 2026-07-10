from __future__ import annotations

from compute.campaign686.two_prime_gap_verify import (
    PER_PRIME_LOSS,
    TARGETS,
    TWO_PRIME_LOSS,
    absolute_gap_constants,
    coefficient_family_summary,
    small_prime_loss_table,
    telescope_checks,
)


def test_exact_small_prime_losses() -> None:
    assert small_prime_loss_table() == {
        2: 4096,
        3: 729,
        5: 125,
        7: 343,
        11: 121,
        13: 169,
    }
    assert PER_PRIME_LOSS == 4096
    assert TWO_PRIME_LOSS == 16_777_216


def test_absolute_constants_are_exact_and_below_target() -> None:
    constants = absolute_gap_constants()
    assert constants["same_bucket"] == 858_847_761_981_817_541_885_952_000
    assert constants["center_plus_other"] == int(
        "500733675106336395918545298815399096057504984362231236206385578627747149218985279488000000000000000"
    )
    assert constants["same_bucket"] < 10**120
    assert constants["center_plus_other"] < 10**120


def test_finite_coefficient_family_counts() -> None:
    expected = {
        5: (1061, 246, 280),
        7: (1686, 390, 668),
        9: (3402, 881, 1762),
        11: (4509, 1161, 2902),
        13: (5804, 1491, 4474),
        15: (8906, 2277, 7970),
    }
    for k, bound_a in TARGETS.items():
        summary = coefficient_family_summary(k, bound_a)
        assert (
            summary["raw_coefficient_pairs"],
            summary["filtered_coefficient_pairs"],
            summary["filtered_pell_triples"],
        ) == expected[k]
        assert summary["delta_count"] == 2 * (k - 1)
        assert summary["delta_min"] == -(k - 1)
        assert summary["delta_max"] == k - 1
def test_named_telescopes_are_preserved_outside_the_hypotheses() -> None:
    checks = telescope_checks()
    assert [(row["k"], row["X"], row["Y"], row["d"]) for row in checks] == [
        (9, 8, 7, 1),
        (15, 13, 12, 1),
    ]
    assert all(row["equation_holds"] is True for row in checks)
    assert all(row["outside_d_ge_k"] is True for row in checks)
    assert all(row["has_two_positive_prime_power_components"] is False for row in checks)
