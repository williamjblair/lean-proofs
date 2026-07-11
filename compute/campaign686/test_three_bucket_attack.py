from fractions import Fraction

from compute.campaign686.three_bucket_attack import (
    ROWS,
    TARGET,
    local_congruence_crt_witness,
    report,
    row_slope_report,
    signed_algebra_grid,
    three_bucket_second_obstruction,
    three_bucket_third_obstruction,
    zero_slope,
)


def test_all_target_row_zero_slopes_are_pairwise_distinct() -> None:
    for k in ROWS:
        row = row_slope_report(k)
        assert row["all_three_slopes_pairwise_distinct"] is True
        assert row["maximum_simultaneous_positive_zeros"] <= 1


def test_zero_slope_is_exact() -> None:
    k, i, j, ell, g = 15, 4, 9, 14, 37
    slope = zero_slope(k, i, j, ell)
    t = slope * g**2
    if t.denominator == 1 and t > 0:
        assert three_bucket_second_obstruction(
            k, i, j, ell, t.numerator, g
        ) == 0
    else:
        assert isinstance(slope, Fraction)


def test_third_composed_residue_reduces_to_second_mod_component() -> None:
    # The exact formula is F_i = -3 O_i + K_i*d.  Thus every component of
    # d sees no new first-order polynomial in abc.
    k, i, j, ell = 13, 3, 8, 12
    p, q, r, g, t = 101, 103, 107, 19, 1234567
    d = g * p * q * r
    second = three_bucket_second_obstruction(k, i, j, ell, t, g)
    third = three_bucket_third_obstruction(k, i, j, ell, t, g, d)
    assert (third + 3 * second) % p == 0


def test_signed_algebra_grid() -> None:
    assert signed_algebra_grid()["signed_exact_elimination_fixtures"] > 0


def test_target_size_crt_witness_locates_the_missing_input() -> None:
    witness = local_congruence_crt_witness(
        k=5,
        indices=(1, 2, 4),
        components=(101**20, 103**20, 107**20),
    )
    assert witness["gap_above_target"] is True
    assert witness["all_current_congruences_hold"] is True
    assert witness["lower_global_moment_mod_gap_cube"] == 0
    assert witness["upper_global_moment_mod_gap_cube"] == 0
    assert witness["block_equation_holds"] is False
    assert witness["short_window_holds"] is False
    assert witness["gap_digits"] >= len(str(TARGET))


def test_full_report() -> None:
    result = report()
    assert result["all_rows_have_at_most_one_zero_second_obstruction"] is True
    assert result["all_row_slopes_pairwise_distinct"] is True
