from compute.campaign686.agent_t2_smooth_rows.reflected_alignment_square_lift import (
    reflected_owner_terms,
)
from compute.campaign686.agent_t2_smooth_rows.reflected_second_lift import (
    common_divisors,
    reflected_second_lift_row,
)


def test_exact_cubic_congruence_grid() -> None:
    checked = 0
    for k in range(2, 13):
        for n in range(0, 31):
            for d in range(0, 24):
                for owner in range(1, k + 1):
                    lower, upper = reflected_owner_terms(k, n, d, owner)
                    for h in common_divisors(lower, upper):
                        try:
                            row = reflected_second_lift_row(k, n, d, owner, h)
                        except ValueError as error:
                            assert str(error) == "quadratic reflected residual is absent"
                            continue
                        assert row.cubic_congruence
                        if row.exact_equation:
                            assert row.next_lift
                        checked += 1
    assert checked == 66_910


def test_signs_on_both_parities() -> None:
    even = reflected_second_lift_row(2, 0, 3, 1, 1)
    odd = reflected_second_lift_row(3, 0, 1, 2, 1)
    assert even.obstruction == even.constant * even.a - 12 * even.linear * even.x**2
    assert odd.obstruction == odd.constant * odd.a + 20 * odd.linear * odd.x**2


def test_synthetic_large_prime_rows_keep_quadratic_premise_visible() -> None:
    cases = (
        (984, 3_177_027, 4_480, 499, 1_489),
        (984, 3_177_027, 4_480, 597, 4_271),
    )
    for k, n, d, owner, prime in cases:
        try:
            reflected_second_lift_row(k, n, d, owner, prime)
        except ValueError as error:
            assert str(error) == "quadratic reflected residual is absent"
        else:
            raise AssertionError("a failed square lift was promoted to next order")
