from fractions import Fraction

import pytest

from compute730.campaign_uniform.repair.far.far_fourier import (
    A,
    absolute_triangle_exponent_obstruction,
    branch_forbidden_digit,
    brute_cumulative_fourier_energy,
    certified_block_length,
    cumulative_fourier_energy,
    completion_conductor,
    gauss_sum_prediction,
    gauss_sum_prediction_holds_exactly,
    is_separated_far,
    long_interval_trivial_threshold,
    restricted_exact_size,
    restricted_exact_values,
    scan_hostile_grid,
    valuation,
)


def test_exact_valuation_output_alphabet() -> None:
    for p in (5, 7, 11):
        H = (p + 1) // 2
        assert branch_forbidden_digit("P", p) == 0
        assert branch_forbidden_digit("Q", p) == 0
        assert branch_forbidden_digit("R", p) == H - 1
        assert branch_forbidden_digit("S", p) == H - 1
        for m in (1, 2, 3, 4):
            for branch in ("P", "Q", "R", "S"):
                values = restricted_exact_values(p, m, branch)
                assert len(values) == restricted_exact_size(p, m)
                assert len(values) == (H - 1) * H ** (m - 1)
                forbidden = branch_forbidden_digit(branch, p)
                for value in values:
                    work = value
                    digits = []
                    for _ in range(m):
                        digits.append(work % p)
                        work //= p
                    assert all(0 <= digit < H for digit in digits)
                    assert digits[0] != forbidden


def test_exact_cumulative_fourier_energy_identity() -> None:
    # This checks the subgroup-Parseval identity through integer collision
    # counts; no complex or floating-point Fourier arithmetic is involved.
    for p, m in ((5, 4), (7, 3), (11, 2)):
        for branch in ("Q", "S"):
            for v in range(m):
                assert brute_cumulative_fourier_energy(p, m, branch, v) == (
                    cumulative_fourier_energy(p, m, v)
                )


@pytest.mark.parametrize(
    ("p", "r", "expected"),
    [
        (5, 1, 13),
        (5, 2, 260),
        (5, 3, 2915),
        (5, 4, 25903),
        (7, 1, 27),
        (7, 2, 743),
        (7, 3, 11690),
        (11, 1, 64),
        (11, 2, 2783),
        (11, 3, 68879),
    ],
)
def test_certified_critical_block_lengths(p: int, r: int, expected: int) -> None:
    certificate = certified_block_length(p, r)
    assert certificate["length"] == expected
    assert certificate["lower_strict"]
    assert certificate["upper_weak"]


def test_exact_separated_range_and_seven_adic_conductor() -> None:
    assert valuation(A, 5) == 0
    assert valuation(A, 7) == 1
    assert valuation(A, 11) == 0

    # Exact comparisons use rational powers, not floating approximations to
    # kappa_p.
    assert is_separated_far(5, r=4, a=6)  # s=2
    assert not is_separated_far(5, r=4, a=7)  # s=1
    assert is_separated_far(7, r=3, a=4)  # s=2
    assert not is_separated_far(7, r=3, a=5)  # s=1
    assert is_separated_far(11, r=3, a=4)  # s=2
    assert not is_separated_far(11, r=3, a=5)  # s=1

    assert completion_conductor(5, r=3, a=4, frequency_valuation=0) == {
        "n": 6,
        "tau": 4,
        "d": 2,
    }
    assert completion_conductor(7, r=3, a=4, frequency_valuation=0) == {
        "n": 6,
        "tau": 5,
        "d": 1,
    }
    assert completion_conductor(7, r=3, a=4, frequency_valuation=1) == {
        "n": 5,
        "tau": 5,
        "d": 0,
    }

    assert all(absolute_triangle_exponent_obstruction(p) for p in (5, 7, 11))
    assert not absolute_triangle_exponent_obstruction(13)
    assert long_interval_trivial_threshold(5, 4) == 2 * 5**4


@pytest.mark.parametrize(
    ("p", "n", "tau", "quad_unit", "linear_unit"),
    [
        (5, 3, 0, 2, 1),
        (5, 3, 1, 2, 3),
        (7, 3, 2, 3, 2),
        (11, 2, 2, 1, 5),
    ],
)
def test_gauss_support_and_magnitude_exactly(
    p: int, n: int, tau: int, quad_unit: int, linear_unit: int
) -> None:
    modulus = p**n
    quadratic = (p**tau * quad_unit) % modulus
    for completion_frequency in range(modulus):
        prediction = gauss_sum_prediction(
            p=p,
            n=n,
            quadratic=quadratic,
            linear=(linear_unit + completion_frequency) % modulus,
        )
        assert gauss_sum_prediction_holds_exactly(
            p=p,
            n=n,
            quadratic=quadratic,
            linear=(linear_unit + completion_frequency) % modulus,
            prediction=prediction,
        )


def test_hostile_grid_has_no_small_counterexample_but_is_finite_only() -> None:
    rows = scan_hostile_grid()
    assert len(rows) == 104
    assert {row["p"] for row in rows} == {5, 7, 11}
    assert {row["branch"] for row in rows} == {"P", "Q", "R", "S"}
    assert all(row["separated"] for row in rows)
    assert all(row["max_hits"] * row["main_denominator"] <= row["main_numerator"] for row in rows)

    # The least exact margin in the grid is banked so changes in the maps,
    # interval convention, or exact-valuation filter cannot silently weaken
    # the hostile check.
    worst = max(
        rows,
        key=lambda row: Fraction(
            row["max_hits"] * row["main_denominator"],
            row["main_numerator"],
        ),
    )
    assert (worst["p"], worst["r"], worst["branch"], worst["a"]) == (
        11,
        1,
        "R",
        1,
    )
    assert Fraction(
        worst["max_hits"] * worst["main_denominator"],
        worst["main_numerator"],
    ) == Fraction(2299, 2304)
