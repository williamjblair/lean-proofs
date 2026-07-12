from fractions import Fraction

from even_uniform_sqrt_verify import (
    continuous_boundary_certificate,
    eval_poly,
    make_data,
    mul_poly,
    _poly_add_scaled,
    k18_trap_certificate,
)
from k20_k24_cover_verify import cover_certificate, trap_certificate
from k18_archimedean_closure_verify import (
    KERNEL_COVER,
    finite_strip_certificate,
    kernel_cover_certificate,
    large_gap_cover_certificate,
    large_gap_certificate,
)


def test_k16_exact_polynomials_and_fixed_divisor() -> None:
    row = make_data(16)
    assert row.scale == 1
    assert row.t_poly == {
        8: 1,
        6: -340,
        4: 31926,
        2: -862580,
        0: -2167279,
    }
    assert row.d_poly == {
        6: 2139095040,
        4: -280506662912,
        2: 8679734640640,
        0: 588267913216,
    }
    assert row.fixed_divisor_odd == 16384
    assert row.first_admissible_odd_center == 355


def test_square_identity_exact_at_independent_points() -> None:
    for k in (16, 18, 20, 32):
        row = make_data(k)
        rhs = _poly_add_scaled(row.s_poly, row.d_poly, row.scale**2)
        lhs = mul_poly(row.t_poly, row.t_poly)
        assert lhs == rhs
        for x in (k + 1, 3 * k + 7, 17 * k + 1):
            assert eval_poly(lhs, x) == eval_poly(rhs, x)


def test_continuous_boundary_separates_k16_from_k18() -> None:
    k16 = continuous_boundary_certificate(make_data(16), bits=192)
    k18 = continuous_boundary_certificate(make_data(18), bits=192)
    assert k16["abs_h_below_fixed"] == 1
    assert k18["abs_h_exceeds_fixed"] == 1
    assert Fraction(k16["root_lo_num"], k16["root_lo_den"]) < Fraction(
        k16["root_hi_num"], k16["root_hi_den"]
    )


def test_k18_exact_trap_coefficients() -> None:
    cert = k18_trap_certificate()
    assert cert["trap"] == 731_939_653
    assert cert["candidate_count"] == 9_036_292
    assert cert["lower_terms"] == 55
    assert cert["lower_min_coefficient"] == 93_688_275_584


def test_k20_and_k24_traps_and_covers() -> None:
    k20 = trap_certificate(20)
    k24 = trap_certificate(24)
    assert (k20["trap"], k20["fixed"], k20["candidate_count"]) == (
        5_853_806,
        3_200,
        1_829,
    )
    assert (k24["trap"], k24["fixed"], k24["candidate_count"]) == (
        5_993_518_490,
        10_616_832,
        564,
    )
    assert cover_certificate(20)[-1] == 0
    assert cover_certificate(24)[-1] == 0


def test_k18_archimedean_second_stage() -> None:
    large = large_gap_certificate()
    cover = large_gap_cover_certificate()
    kernel_cover = kernel_cover_certificate()
    finite = finite_strip_certificate()
    assert (large["gap"], large["trap"], large["terms"]) == (
        56,
        242_269_137,
        55,
    )
    assert large["min_coefficient"] == 31_010_449_536
    assert cover["candidate_count"] == 2_990_976
    assert cover["survivor_counts"][-1] == 0
    assert kernel_cover["candidate_count"] == 2_990_976
    assert len(KERNEL_COVER) == 62
    assert len(set(KERNEL_COVER)) == 62
    assert kernel_cover["survivor_counts"][-1] == 0
    assert finite["checked"] == 1_311
