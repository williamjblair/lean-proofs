from fractions import Fraction

import pytest

from compute730.campaign_uniform.repair.far.unit_range_block import (
    block_identity_fixture_grid,
    corrected_case_scan,
    higher_power_first_moment_certificate,
    higher_power_series_at_prime,
    low_word_block_bound,
)


@pytest.mark.parametrize(
    "branch,p,r,a,expected",
    [
        (
            "Q",
            5,
            5,
            4,
            {
                "critical_length": 202_367,
                "maximum_start": 1_099_150,
                "maximum_hits": 1_008,
                "ratio": Fraction(1_093_750_000, 1_327_729_887),
            },
        ),
        (
            "Q",
            7,
            4,
            1,
            {
                "critical_length": 145_465,
                "maximum_start": 281_184,
                "maximum_hits": 1_341,
                "ratio": Fraction(7_730_598_141, 9_533_194_240),
            },
        ),
        (
            "S",
            11,
            3,
            1,
            {
                "critical_length": 68_879,
                "maximum_start": 53_482,
                "maximum_hits": 1_660,
                "ratio": Fraction(735_197_815, 803_404_656),
            },
        ),
    ],
)
def test_new_corrected_range_scans(
    branch: str, p: int, r: int, a: int, expected: dict[str, object]
) -> None:
    result = corrected_case_scan(branch, p, r, a)
    for key, value in expected.items():
        assert result[key] == value
    assert result["a_le_r"] is True
    assert result["maximum_hits_below_uninflated_main"] is True
    assert result["full_period_count_exact"] is True
    assert result["maximum_aligned_block_hits"] <= result["aligned_block_bound"]
    assert result["maximum_hits"] <= result["critical_block_cover_bound"]


def test_quadratic_block_identity_signed_grid() -> None:
    result = block_identity_fixture_grid()
    assert result["fixtures"] == 1_764
    assert result["all_exact"] is True


def test_low_word_bound_has_exact_deleted_digit_density() -> None:
    assert low_word_block_bound(5, 5) == 2 * 3**4
    assert low_word_block_bound(7, 4) == 3 * 4**3
    assert low_word_block_bound(11, 3) == 5 * 6**2


def test_higher_prime_power_first_moment_is_below_half() -> None:
    result = higher_power_first_moment_certificate()
    assert result["log5_lower_gt_one"] is True
    assert result["primes_through_1000"] == 166
    assert result["largest_checked_prime"] == 997
    assert result["partial_prime_sum"] < Fraction(57, 1000)
    assert result["tail_bound"] == Fraction(1, 1000)
    assert result["single_branch_series_bound"] < Fraction(29, 500)
    assert result["four_branch_normalized_bound"] < Fraction(58, 125)
    assert result["four_branch_normalized_bound"] < Fraction(1, 2)


def test_closed_geometric_series_formula_exactly() -> None:
    for p in (5, 7, 11, 101):
        H = (p + 1) // 2
        ratio = Fraction(H, p * p)
        reconstructed = (
            Fraction(2 * p, p + 1) * ratio**2 / (1 - ratio)
        )
        assert higher_power_series_at_prime(p) == reconstructed
