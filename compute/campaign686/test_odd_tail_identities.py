from __future__ import annotations

from math import gcd

from .odd_tail_identities import (
    PRIME_POWER_BOUND_A,
    TARGET_K,
    WINDOW_C,
    block_product,
    centered_coordinates,
    centered_product,
    equation_residue_mod_gap,
    evaluate,
    polynomial_coefficients,
    root_derivative,
    shifted_equation_coefficients,
    unique_factor_offset_mod_prime,
    window_power_check,
)


def test_centered_block_identity() -> None:
    for k in TARGET_K:
        for n in (0, 1, 17):
            for d in (1, k, 31):
                x, y = centered_coordinates(k, n, d)
                assert centered_product(k, x) == block_product(k, n + d)
                assert centered_product(k, y) == block_product(k, n)


def test_polynomial_coefficients_are_exact_and_odd() -> None:
    assert polynomial_coefficients(5) == [0, 4, 0, -5, 0, 1]
    for k in TARGET_K:
        coefficients = polynomial_coefficients(k)
        assert len(coefficients) == k + 1
        assert coefficients[k] == 1
        assert all(coefficients[degree] == 0 for degree in range(0, k + 1, 2))
        for value in range(-20, 21):
            assert evaluate(coefficients, value) == centered_product(k, value)


def test_named_d_one_telescopes() -> None:
    assert centered_product(9, 8) == 4 * centered_product(9, 7)
    assert centered_product(15, 13) == 4 * centered_product(15, 12)
    assert 1 < 9
    assert 1 < 15


def test_explicit_window_and_prime_power_constants() -> None:
    assert WINDOW_C == {5: 4, 7: 5, 9: 7, 11: 8, 13: 9, 15: 11}
    assert PRIME_POWER_BOUND_A == {5: 14, 7: 17, 9: 23, 11: 26, 13: 29, 15: 35}
    assert all(window_power_check(k) for k in TARGET_K)


def test_gap_reduction_is_three_times_lower_product() -> None:
    for k in TARGET_K:
        for y in range(1, 30):
            for d in (1, 2, k, 2 * k + 1):
                assert equation_residue_mod_gap(k, y, d) == (
                    -3 * centered_product(k, y)
                ) % d


def test_shifted_taylor_linear_part_and_center_cubic_gain() -> None:
    for k in TARGET_K:
        radius = (k - 1) // 2
        for offset in range(-radius, radius + 1):
            coefficients = shifted_equation_coefficients(k, offset)
            derivative = root_derivative(k, offset)
            assert coefficients.get((0, 0), 0) == 0
            assert coefficients.get((0, 1), 0) == derivative
            assert coefficients.get((1, 0), 0) == -3 * derivative
            assert all(
                z_degree + d_degree >= 2
                for (z_degree, d_degree) in coefficients
                if (z_degree, d_degree) not in {(0, 1), (1, 0)}
            )
            if offset == 0:
                assert all(
                    z_degree + d_degree >= 3
                    for (z_degree, d_degree) in coefficients
                    if (z_degree, d_degree) not in {(0, 1), (1, 0)}
                )


def test_root_derivative_is_a_unit_for_primes_above_k() -> None:
    for k in TARGET_K:
        radius = (k - 1) // 2
        for offset in range(-radius, radius + 1):
            derivative = root_derivative(k, offset)
            for prime in (5, 7, 11, 13, 17, 19, 23, 29, 31):
                if prime >= k:
                    assert gcd(derivative, prime) == 1


def test_modular_square_lift_exhaustively_for_k5_p7() -> None:
    k = 5
    prime = 7
    modulus = prime**2
    for d in range(0, modulus, prime):
        for y in range(modulus):
            equation = centered_product(k, y + d) - 4 * centered_product(k, y)
            if equation % modulus:
                continue
            offset = unique_factor_offset_mod_prime(k, y, prime)
            assert (d - 3 * (y + offset)) % modulus == 0


def test_modular_center_cubic_lift_exhaustively_for_k5_p7() -> None:
    k = 5
    prime = 7
    modulus = prime**3
    for d in range(0, modulus, prime):
        for y in range(0, modulus, prime):
            equation = centered_product(k, y + d) - 4 * centered_product(k, y)
            if equation % modulus == 0:
                assert unique_factor_offset_mod_prime(k, y, prime) == 0
                assert (d - 3 * y) % modulus == 0


def test_equal_prime_boundary_k5_p5() -> None:
    k = 5
    prime = 5
    modulus = prime**2
    for d in range(0, modulus, prime):
        for y in range(modulus):
            equation = centered_product(k, y + d) - 4 * centered_product(k, y)
            if equation % modulus:
                continue
            offset = unique_factor_offset_mod_prime(k, y, prime)
            assert (d - 3 * (y + offset)) % modulus == 0
