from __future__ import annotations

from math import factorial

from .large_k_rows import row_passes
from .reflection_lcm_correlation_verify import (
    exact_equation,
    exact_large_gap_threshold,
    nonreflected_residual_bound,
    owner_correlations,
    positive_reflection_values,
    reflection_center,
    reflection_coefficient,
    reflection_congruence,
    reflection_lcm,
    reflection_lcm_compression,
    reflection_product,
    reflection_product_compression,
    small_index_lcm,
    uniform_large_gap_threshold,
)


DEEP_17 = (984, 3_177_026, 4_480)
DEEP_16 = (244, 48_502, 277)
SMOOTH_REFLECTION_984 = (984, 3_177_027, 4_480)
EVEN_SYNTHETIC = (16, 582_087, 52_684)
ODD_SYNTHETIC = (17, 996_082, 84_632)


def test_positive_reflection_interval_and_lcm_are_exact() -> None:
    assert positive_reflection_values(5, 7) == [11, 9, 7, 5, 3]
    assert reflection_lcm(5, 7) == 3_465
    assert reflection_product(5, 7) == 10_395
    assert reflection_product(5, 7) % reflection_lcm(5, 7) == 0


def test_lcm_and_product_compressions_are_structurally_incomparable() -> None:
    comparisons = []
    for k, _n, d in (DEEP_16, SMOOTH_REFLECTION_984, EVEN_SYNTHETIC, ODD_SYNTHETIC):
        lcm_rhs = reflection_coefficient(k) * factorial(k - 1) * reflection_lcm(k, d)
        product_rhs = reflection_coefficient(k) * reflection_product(k, d)
        comparisons.append(lcm_rhs < product_rhs)
    # The lcm statement carries one consecutive-block factorial loss.  It is
    # arithmetically sharper prime by prime, but not a uniformly smaller raw
    # integer than the old product RHS.  Both size directions occur exactly.
    assert any(comparisons)
    assert not all(comparisons)


def test_named_prefix_boundaries_and_premises_are_not_blurred() -> None:
    k, n, d = DEEP_17
    assert all(row_passes(k, n, d, row) for row in range(1, 17))
    assert not row_passes(k, n, d, 17)
    assert not exact_equation(k, n, d)
    assert not reflection_congruence(k, n, d)
    assert not reflection_product_compression(k, n, d)
    assert not reflection_lcm_compression(k, n, d)

    k, n, d = DEEP_16
    assert all(row_passes(k, n, d, row) for row in range(1, 16))
    assert not row_passes(k, n, d, 16)
    assert not exact_equation(k, n, d)
    assert reflection_congruence(k, n, d)
    assert reflection_product_compression(k, n, d)
    assert reflection_lcm_compression(k, n, d)


def test_two_stronger_synthetic_reflection_points_pass_lcm_compression() -> None:
    for k, n, d in (EVEN_SYNTHETIC, ODD_SYNTHETIC, SMOOTH_REFLECTION_984):
        assert not exact_equation(k, n, d)
        assert reflection_congruence(k, n, d)
        assert reflection_product_compression(k, n, d)
        assert reflection_lcm_compression(k, n, d)


def test_residual_owner_chunks_correlate_on_synthetic_reflection_points() -> None:
    # These points are not equations, so the theorem does not apply.  They
    # were engineered so that the nontrivial residual primes nevertheless
    # land in reflected owner pairs.  This reproduces the exact obstruction
    # to replacing the correlation analysis by a gross lcm-size estimate.
    expected = {
        SMOOTH_REFLECTION_984: [(1_489, 499, 486), (4_271, 597, 388)],
        EVEN_SYNTHETIC: [(5, 13, 4), (59, 7, 10)],
        ODD_SYNTHETIC: [(19, 12, 6), (31, 10, 8), (41, 13, 5), (43, 13, 5)],
    }
    for point, triples in expected.items():
        rows = [row for row in owner_correlations(*point) if row.residual_exponent]
        assert [(row.prime, row.lower_owner, row.upper_owner) for row in rows] == triples
        assert all(row.reflected for row in rows)
        assert all(row.reflection_landing for row in rows)
        assert all(row.centered_landing for row in rows)
        assert all(row.offset_landing for row in rows)
        assert not nonreflected_residual_bound(*point)


def test_d_one_telescopes_are_outside_positive_reflection_range_and_vacuous() -> None:
    for k, n, d in ((9, 2, 1), (15, 4, 1)):
        assert exact_equation(k, n, d)
        assert reflection_congruence(k, n, d)
        assert d < k
        rows = owner_correlations(k, n, d)
        assert all(row.residual_exponent == 0 for row in rows)
        assert nonreflected_residual_bound(k, n, d)
        try:
            reflection_lcm(k, d)
        except ValueError as exc:
            assert "1 <= k <= d" in str(exc)
        else:
            raise AssertionError("separated reflection lcm accepted d<k")


def test_nonreflected_offset_is_always_small_and_absorbed_by_small_lcm() -> None:
    small_points = []
    # This is a purely exact owner-ledger test; points need not solve the
    # equation.  Whenever a residual ledger row happens to land in both
    # differences and is not reflected, the offset identity supplies the
    # advertised small-index absorption.
    for k in range(2, 12):
        for n in range(0, 50):
            for d in range(k, k + 20):
                for row in owner_correlations(k, n, d):
                    if (
                        row.residual_exponent
                        and not row.reflected
                        and row.reflection_landing
                        and row.centered_landing
                    ):
                        small_points.append((k, n, d, row.prime))
                        assert 1 <= row.owner_offset <= k - 1
                        assert small_index_lcm(k) % row.residual_power == 0
    assert small_points


def test_large_gap_thresholds_are_exact_and_unbounded() -> None:
    assert small_index_lcm(16) == 360_360
    exact16 = 3 * factorial(15) * 360_360
    uniform16 = 5 * factorial(15) * 360_360
    assert exact_large_gap_threshold(16) == (exact16 + 18) // 19
    assert uniform_large_gap_threshold(16) == (uniform16 + 18) // 19
    assert 19 * (exact_large_gap_threshold(16) - 1) < exact16
    assert exact16 <= 19 * exact_large_gap_threshold(16)
    assert exact_large_gap_threshold(16) < uniform_large_gap_threshold(16)
    assert all(
        uniform_large_gap_threshold(k + 1) > uniform_large_gap_threshold(k)
        for k in range(16, 30)
    )


def test_center_values_on_named_points() -> None:
    assert reflection_center(*DEEP_17) == 6_359_517
    assert reflection_center(*DEEP_16) == 97_526
    assert reflection_center(*SMOOTH_REFLECTION_984) == 6_359_519
