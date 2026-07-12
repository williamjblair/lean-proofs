from __future__ import annotations

from compute.campaign686.agent_t2_smooth_rows.two_factor_center import (
    TwoFactorRow,
    candidate_rows,
    even_reflected_linear,
    large_prime_supported,
    odd_reflected_linear,
    owner_aggregated_candidate_rows,
    prime_factors,
    reflection_center,
    reflection_loss_exponent,
    residue_obstruction_tables,
)
from compute.campaign686.large_k_rows import block_equation_holds, first_failed_row


def sampled_owners(k: int) -> tuple[int, ...]:
    return tuple(sorted({1, 2, k // 2, (k + 1) // 2, k - 1, k}))


def test_exact_product_windows_grid() -> None:
    checked = 0
    for k in range(16, 41):
        for d in range(k, k + 9):
            for n in (9 * d + 1, 9 * d + 2, 10 * d, 12 * d + 17):
                center_square = reflection_center(k, n, d) ** 2
                for i in sampled_owners(k):
                    for j in sampled_owners(k):
                        if k % 2 == 0:
                            product = (
                                even_reflected_linear(k, n, d, i)
                                * even_reflected_linear(k, n, d, j)
                            )
                            assert 5 * center_square < product < 8 * center_square
                        else:
                            product = (
                                odd_reflected_linear(k, n, d, i)
                                * odd_reflected_linear(k, n, d, j)
                            )
                            assert center_square < product < 4 * center_square
                        checked += 1
    assert checked == 27_252


def test_no_two_factor_square_lift_package_on_exact_grid() -> None:
    centers = 0
    for k in range(16, 43):
        for d in range(k, k + 8):
            for n in range(9 * d + 1, 9 * d + 122):
                assert candidate_rows(k, n, d) == []
                centers += 1
    assert centers == 26_136


def test_no_two_owner_large_supported_aggregate_on_exact_grid() -> None:
    checked = 0
    for k in range(16, 35):
        for d in range(k, k + 6):
            for n in range(9 * d + 1, 9 * d + 83):
                assert owner_aggregated_candidate_rows(k, n, d) == []
                checked += 1
    assert checked == 9_348


def test_large_support_allows_composite_owner_aggregates() -> None:
    assert prime_factors(17**2 * 19 * 23**3) == (17, 19, 23)
    assert large_prime_supported(16, 17**2 * 19 * 23**3)
    assert not large_prime_supported(16, 13 * 17 * 19)
    assert not large_prime_supported(16, 1)


def test_one_large_component_square_is_beyond_every_linear() -> None:
    centers = 0
    for k in range(16, 41):
        for d in range(k, k + 8):
            for n in range(9 * d + 1, 9 * d + 101):
                center = reflection_center(k, n, d)
                factors = prime_factors(center)
                if len(factors) != 1 or factors[0] <= k:
                    continue
                centers += 1
                for owner in sampled_owners(k):
                    line = (
                        even_reflected_linear(k, n, d, owner)
                        if k % 2 == 0
                        else odd_reflected_linear(k, n, d, owner)
                    )
                    assert 0 < line < center**2
                    assert line % center**2 != 0
    assert centers == 3_020


def test_reflection_loss_decomposition_is_exact() -> None:
    checked = 0
    for k in range(16, 51):
        for d in range(k, k + 5):
            for n in range(9 * d + 1, 9 * d + 31):
                center = reflection_center(k, n, d)
                for prime in prime_factors(center):
                    exponent = 0
                    value = center
                    while value % prime == 0:
                        value //= prime
                        exponent += 1
                    loss = reflection_loss_exponent(k, prime)
                    residual = max(0, exponent - loss)
                    assert prime**exponent <= prime**loss * prime**residual
                    checked += 1
    assert checked == 11_284


def test_window_multiplier_and_residue_tables() -> None:
    tables = residue_obstruction_tables()
    assert tables["even_uv_6"] == ((1, 6), (2, 3), (3, 2), (6, 1))
    assert tables["even_uv_7"] == ((1, 7), (7, 1))
    assert tables["odd_uv_2"] == ((1, 2), (2, 1))
    assert tables["odd_uv_3"] == ((1, 3), (3, 1))

    # For nonzero q,r modulo 3, their squares are 1.  Thus the uv=6
    # alternatives would require u=v mod 3, which none satisfies.
    assert all(u % 3 != v % 3 for u, v in tables["even_uv_6"])

    # Enumerate every nonzero square pair modulo 5.  None realizes a ratio
    # 2 or 3, in either orientation.
    for q in range(1, 5):
        for r in range(1, 5):
            q2, r2 = q * q % 5, r * r % 5
            assert q2 != 2 * r2 % 5
            assert 2 * q2 % 5 != r2
            assert q2 != 3 * r2 % 5
            assert 3 * q2 % 5 != r2


def test_even_seven_branch_opposing_strict_inequalities() -> None:
    # This checks the two exact coefficient-one identities used in Lean.  Any
    # hypothetical uv=7 row would have to satisfy both strict inequalities.
    for k in range(16, 65, 2):
        for d in range(k, k + 4):
            for n in range(9 * d + 1, 9 * d + 80):
                center = reflection_center(k, n, d)
                for q in range(k + 1, int(center**0.5) + 1):
                    if center % q:
                        continue
                    r = center // q
                    if r <= k:
                        continue
                    for i in sampled_owners(k):
                        if q**2 != even_reflected_linear(k, n, d, i):
                            continue
                        assert 2 * q < 5 * r
                        for j in sampled_owners(k):
                            if 7 * r**2 != even_reflected_linear(k, n, d, j):
                                continue
                            assert 5 * r < 2 * q
                            raise AssertionError("opposing strict inequalities coexisted")


def test_mandatory_fixtures_do_not_gain_the_missing_equation() -> None:
    fixtures = ((984, 3_177_026, 4_480, 17), (244, 48_502, 277, 16))
    for k, n, d, failed in fixtures:
        assert first_failed_row(k, n, d) == failed
        assert not block_equation_holds(k, n, d)

    # Their centers are not products of exactly two complete large-prime
    # components, so the equation-level corollary cannot be invoked either.
    assert reflection_center(984, 3_177_026, 4_480) == 3**2 * 706_613
    assert reflection_center(244, 48_502, 277) == 2 * 11**2 * 13 * 31


def test_row_object_keeps_every_premise_explicit() -> None:
    row = TwoFactorRow(k=16, n=145, d=16, q=17, r=19, i=1, j=16)
    assert row.target_range
    assert row.center_factorization
    assert row.large_factors
    assert row.residue_units
    assert not row.square_lifts
    assert not row.pure_theorem_premises
