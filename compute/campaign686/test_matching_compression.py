from __future__ import annotations

from math import factorial

from .large_k_rows import row_passes
from .matching_compression import (
    all_rows_pass,
    block_product,
    centered_lcm,
    centered_product,
    compression_rhs,
    consecutive_factorial_lcm_absorption,
    equation_compression_rhs,
    factorial_valuation,
    lcm,
    matched_owner_chunks,
    matched_owner_product,
    owner_chunks,
    scaled_ratio_power_check,
    verify_compression_certificate,
)


DEEP_17 = (984, 3_177_026, 4_480)
DEEP_16 = (244, 48_502, 277)


def chunk_for_prime(k: int, n: int, d: int, prime: int):
    return next(chunk for chunk in owner_chunks(k, n, d) if chunk.prime == prime)


def test_legendre_factorial_valuation_exact_values() -> None:
    assert factorial_valuation(15, 2) == 11
    assert factorial_valuation(15, 3) == 6
    assert factorial_valuation(243, 17) == 14
    assert factorial_valuation(983, 7_237) == 0


def test_deep_17_missing_owner_chunk_is_exactly_visible_at_row_17() -> None:
    k, n, d = DEEP_17
    assert all(row_passes(k, n, d, row) for row in range(1, 17))
    assert not row_passes(k, n, d, 17)

    obstruction = chunk_for_prime(k, n, d, 7_237)
    assert obstruction.block_exponent == 1
    assert obstruction.owner_exponent == 1
    assert obstruction.loss_exponent == 0
    assert obstruction.chunk == 7_237
    assert obstruction.owner_row == 17
    assert obstruction.landing_column is None
    assert all((d + column - 17) % 7_237 for column in range(1, k + 1))


def test_deep_16_missing_owner_chunk_is_exactly_visible_at_row_16() -> None:
    k, n, d = DEEP_16
    assert all(row_passes(k, n, d, row) for row in range(1, 16))
    assert not row_passes(k, n, d, 16)

    obstruction = chunk_for_prime(k, n, d, 1_427)
    assert obstruction.block_exponent == 1
    assert obstruction.owner_exponent == 1
    assert obstruction.loss_exponent == 0
    assert obstruction.chunk == 1_427
    assert obstruction.owner_row == 16
    assert obstruction.landing_column is None
    assert all((d + column - 16) % 1_427 for column in range(1, k + 1))


def test_full_row_synthetic_family_member_satisfies_compression() -> None:
    # If d is divisible by every n+j, row j contains the factor d at column
    # j, so the full row skeleton survives.  This exact point is deliberately
    # outside the N=4 ratio window and witnesses that compression is strictly
    # weaker than the target.
    k, n = 16, 1
    d = lcm(list(range(n + 1, n + k + 1)))
    assert d == 12_252_240
    assert all_rows_pass(k, n, d)
    assert verify_compression_certificate(k, n, d)
    assert compression_rhs(k, d) % block_product(k, n) == 0


def test_two_factorial_losses_are_exact_primewise_on_synthetic_point() -> None:
    k, n = 16, 1
    d = lcm(list(range(n + 1, n + k + 1)))
    chunks = owner_chunks(k, n, d)
    owner_product = 1
    for chunk in chunks:
        owner_product *= chunk.chunk
        assert chunk.block_exponent <= (
            chunk.chunk_exponent + 2 * chunk.loss_exponent
        )
        if chunk.chunk_exponent:
            assert chunk.landing_value is not None
            assert chunk.landing_value % chunk.chunk == 0
    assert factorial(k - 1) ** 2 * owner_product % block_product(k, n) == 0
    assert centered_lcm(k, d) % owner_product == 0


def test_one_factorial_owner_matching_on_both_exact_telescopes() -> None:
    # These are genuine equations, but d<k, so they audit the owner matching
    # only.  The separated-block centered-lcm theorem assumes d>=k.
    for k, n, d in ((9, 2, 1), (15, 4, 1)):
        lower = block_product(k, n)
        upper = block_product(k, n + d)
        assert upper == 4 * lower
        chunks = matched_owner_chunks(k, n, d)
        assert all(
            chunk.upper_block_exponent >= chunk.lower_block_exponent
            for chunk in chunks
        )
        assert all(chunk.divides_lower_owner for chunk in chunks)
        assert all(chunk.divides_upper_owner for chunk in chunks)
        assert all(
            chunk.shifted_difference % chunk.chunk == 0 for chunk in chunks
        )
        assert factorial(k - 1) * matched_owner_product(k, n, d) % lower == 0


def test_crude_size_comparison_cannot_close_the_large_d_regime() -> None:
    # Equation matching plus n>9d forces L_center > (9d)^k / (k-1)!.
    # The unconditional product bound is L_center <= (2d)^(2k-1).
    # Already at the smallest large-k boundary and d=k the latter dominates;
    # its d-degree is k-1 larger, so this comparison only gets weaker as d
    # grows.  This is the exact obstruction to a size-only finish.
    k, d = 16, 16
    demand_numerator = 9**k * d**k
    supply_after_clearing_loss = factorial(k - 1) * (2 * d) ** (2 * k - 1)
    assert demand_numerator < supply_after_clearing_loss


def test_equation_compression_is_one_factorial_stronger_than_row_only() -> None:
    k, d = 16, 16
    assert (
        equation_compression_rhs(k, d) * factorial(k - 1)
        == compression_rhs(k, d)
    )


def test_scaled_ratio_inequality_is_exact_and_survives_named_fixtures() -> None:
    assert 4 * 21**16 == 5_722_274_760_967_941_313_284
    assert 26**16 == 43_608_742_899_428_874_059_776
    assert scaled_ratio_power_check(16)
    assert all(scaled_ratio_power_check(k) for k in range(16, 200))
    for k, n, d in (DEEP_17, DEEP_16):
        assert k * d < 5 * n


def test_factorial_lcm_absorption_on_consecutive_blocks() -> None:
    for length in range(1, 40):
        for start in range(1, 80):
            assert consecutive_factorial_lcm_absorption(start, length)


def test_centered_absorption_on_both_named_large_fixtures() -> None:
    for k, _n, d in (DEEP_17, DEEP_16):
        assert consecutive_factorial_lcm_absorption(d - k + 1, 2 * k - 1)
        assert (
            centered_product(k, d)
            % (factorial(k - 1) * centered_lcm(k, d))
            == 0
        )
