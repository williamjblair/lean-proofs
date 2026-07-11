from __future__ import annotations

from compute.campaign686.global_residual_concentration_verify import (
    DEEP_FIXTURES,
    ROWS,
    TARGET,
    TWO_PRIME_LOSS_BOUND,
    aggregate_loss_budget,
    block_product,
    exhaustive_positive_square_checks,
    local_taylor_coefficients,
    report,
    third_order_remainder,
    two_bucket_row_report,
    verify_third_algebra_identity,
)


def test_exact_loss_budgets() -> None:
    assert {k: aggregate_loss_budget(k) for k in ROWS} == {
        5: 108,
        7: 1_620,
        9: 136_080,
        11: 1_224_720,
        13: 242_494_560,
        15: 18_914_575_680,
    }


def test_exhaustive_global_square_components_clean() -> None:
    premise_rows, component_rows = exhaustive_positive_square_checks()
    assert (premise_rows, component_rows) == (13_056, 24_447)


def test_third_taylor_remainder_is_exact() -> None:
    for k in ROWS:
        for index in range(1, k + 1):
            for value in range(-8, 9):
                remainder = third_order_remainder(k, index, value)
                if value == 0:
                    assert remainder == 0
                else:
                    assert remainder % value**3 == 0


def test_third_algebra_identity_mod_square() -> None:
    # Choose x,m,h first and retain only integral a=(3x-m)/h.
    for h in range(1, 12):
        for x in range(-10, 11):
            for m in range(-10, 11):
                if (3 * x - m) % h:
                    continue
                a = (3 * x - m) // h
                for constant, linear, quadratic in ((24, 50, 35), (-6, -5, 5)):
                    assert verify_third_algebra_identity(
                        x, m, a, h, constant, linear, quadratic
                    )


def test_reflected_pairs_are_the_only_second_order_degeneracies() -> None:
    expected_counts = {5: 2, 7: 3, 9: 4, 11: 5, 13: 6, 15: 7}
    for k, bound in ROWS.items():
        row = two_bucket_row_report(k, bound)
        assert row["reflected_exception_count"] == expected_counts[k]
        assert row["generic_ordered_pair_count"] == k * (k - 1) - 2 * expected_counts[k]
        assert all(
            item["j"] == k + 1 - item["i"]
            and item["quadratics_nonzero"]
            for item in row["reflected_exceptions"]
        )


def test_every_two_bucket_majorant_is_below_target() -> None:
    result = report()
    assert result["all_generic_bounds_below_target"] is True
    assert result["all_reflected_third_gcd_bounds_below_target"] is True
    assert max(
        row["generic_gap_bound"] for row in result["two_bucket_rows"]
    ) < TARGET


def test_lean_two_prime_uniform_constants() -> None:
    result = report()
    assert TWO_PRIME_LOSS_BOUND == 3_486_784_401
    assert result["lean_two_prime_bounds_below_target"] is True
    assert result["lean_two_prime_generic_bound"] < TARGET
    assert result["lean_two_prime_third_bound"] < TARGET
    assert max(
        row["maximum_third_gcd_bound"] for row in result["two_bucket_rows"]
    ) < TARGET


def test_named_falsification_boundaries() -> None:
    # The genuine telescopes have d=1<k and no nontrivial gap component.
    assert [(k, k // 3 - 1, 1) for k in (3, 6, 9, 12, 15)] == [
        (3, 0, 1),
        (6, 1, 1),
        (9, 2, 1),
        (12, 3, 1),
        (15, 4, 1),
    ]
    for k, n, d in DEEP_FIXTURES:
        assert block_product(k, n + d) != 4 * block_product(k, n)


def test_selected_signed_coefficients() -> None:
    assert local_taylor_coefficients(5, 1) == (24, 50, 35)
    assert local_taylor_coefficients(5, 3) == (4, 0, -5)
    assert local_taylor_coefficients(15, 1) == (
        87_178_291_200,
        283_465_647_360,
        392_156_797_824,
    )
    assert local_taylor_coefficients(15, 8) == (-25_401_600, 0, 38_402_064)
