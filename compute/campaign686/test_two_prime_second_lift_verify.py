from __future__ import annotations

from compute.campaign686.two_prime_second_lift_verify import (
    LEAN_ABS_BOUND,
    ROWS,
    local_coefficients,
    obstruction_pair,
    report,
    row_report,
    second_order_remainder,
)


def test_signed_coefficient_tables() -> None:
    assert [local_coefficients(5, i) for i in range(1, 6)] == [
        (24, 50),
        (-6, -5),
        (4, 0),
        (-6, 5),
        (24, -50),
    ]
    assert local_coefficients(15, 1) == (87_178_291_200, 283_465_647_360)
    assert local_coefficients(15, 8) == (-25_401_600, 0)
    assert local_coefficients(15, 15) == (87_178_291_200, -283_465_647_360)


def test_second_order_remainder_is_divisible_by_value_squared() -> None:
    for k in ROWS:
        for i in range(1, k + 1):
            for value in range(-9, 10):
                remainder = second_order_remainder(k, i, value)
                if value == 0:
                    assert remainder == 0
                else:
                    assert remainder % (value * value) == 0


def test_pell_substitution_signs_are_exact() -> None:
    # If a*P^2-b*Q^2=3*delta, multiplying the P-local congruence by b
    # changes -4*D_i*b*Q^2 into +12*D_i*delta modulo P.  The Q-local
    # congruence analogously gets the minus sign.
    k, i, j, a, b, p_component, q_component = 5, 2, 1, 3, 1, 2, 3
    delta = i - j
    assert a * p_component**2 - b * q_component**2 == 3 * delta
    left, right = obstruction_pair(k, i, j, a * b)
    constant_i, linear_i = local_coefficients(k, i)
    constant_j, linear_j = local_coefficients(k, j)
    assert left == constant_i * a * b + 4 * linear_i * delta
    assert right == constant_j * a * b - 4 * linear_j * delta
    local_p = 3 * constant_i * a - 4 * linear_i * q_component**2
    local_q = 3 * constant_j * b - 4 * linear_j * p_component**2
    assert b * local_p - 3 * left == -4 * linear_i * a * p_component**2
    assert a * local_q - 3 * right == -4 * linear_j * b * q_component**2


def test_no_simultaneous_zero_and_exact_maxima() -> None:
    expected = {
        5: (13_440, 8),
        7: (600_912, 8),
        9: (62_551_872, 8),
        11: (7_220_776_320, 0),
        13: (1_189_246_717_440, 0),
        15: (316_717_097_518_080, 0),
    }
    for k, bound_a in ROWS.items():
        row = row_report(k, bound_a)
        assert row["simultaneous_zeros"] == []
        assert (
            row["maximum_three_times_abs_obstruction"],
            row["single_zero_count"],
        ) == expected[k]
        assert row["below_lean_abs_bound"] is True


def test_global_bound_closes_target_cutoff() -> None:
    result = report()
    assert result["all_nonzero"] is True
    assert result["all_below_lean_abs_bound"] is True
    assert result["global_maximum_three_times_abs_obstruction"] == 316_717_097_518_080
    assert LEAN_ABS_BOUND == 10**20
    assert result["final_product_bound"] == 35 * 10**40
    assert result["final_product_bound_below_cutoff"] is True
