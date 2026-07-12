from __future__ import annotations

from math import gcd

from compute.campaign686.agent_t2_smooth_rows.reflected_alignment_square_lift import (
    center_large_prime_row,
    reflected_owner_terms,
    square_lift_row,
)
from compute.campaign686.large_k_rows import (
    block_equation_holds,
    first_failed_row,
)
from compute.campaign686.reflection_lcm_correlation_verify import (
    reflection_congruence,
)


def divisors(value: int) -> list[int]:
    return [d for d in range(1, value + 1) if value % d == 0]


def test_universal_quadratic_congruence_grid() -> None:
    checked = 0
    for k in range(1, 13):
        for n in range(0, 35):
            for d in range(0, 29):
                for owner in range(1, k + 1):
                    lower, upper = reflected_owner_terms(k, n, d, owner)
                    for modulus in divisors(gcd(lower, upper)):
                        row = square_lift_row(k, n, d, owner, modulus)
                        assert row.owner_landings
                        assert row.quadratic_congruence
                        if row.exact_equation:
                            assert row.weighted_square_lift
                        checked += 1
    assert checked == 127_288


def test_exact_equation_boundaries() -> None:
    # k=1 is the degenerate equality family; the parity linear vanishes.
    for n in range(0, 101):
        k = 1
        d = 3 * (n + 1)
        lower, upper = reflected_owner_terms(k, n, d, 1)
        for modulus in divisors(gcd(lower, upper)):
            row = square_lift_row(k, n, d, 1, modulus)
            assert row.exact_equation
            assert row.weighted_square_lift
            assert row.parity_linear == 0

    # The two telescope identities remain outside d>=k but obey the raw lift.
    for k, n, d in ((9, 2, 1), (15, 4, 1)):
        assert block_equation_holds(k, n, d)
        for owner in range(1, k + 1):
            lower, upper = reflected_owner_terms(k, n, d, owner)
            for modulus in divisors(gcd(lower, upper)):
                row = square_lift_row(k, n, d, owner, modulus)
                assert row.quadratic_congruence
                assert row.weighted_square_lift


def test_mandatory_prefix_fixtures_keep_missing_premises_visible() -> None:
    deep = (984, 3_177_026, 4_480)
    medium = (244, 48_502, 277)
    assert first_failed_row(*deep) == 17
    assert first_failed_row(*medium) == 16
    assert not block_equation_holds(*deep)
    assert not block_equation_holds(*medium)
    assert not reflection_congruence(*deep)

    # The deep point's large center prime does not land on a reflected owner,
    # so the new theorem cannot be invoked on the row-prefix survivor.
    try:
        center_large_prime_row(*deep, 706_613, 1)
    except ValueError as error:
        assert str(error) == "the reflected owner landing is absent"
    else:
        raise AssertionError("missing equation-level landing was inferred")


def test_reflected_synthetic_points_show_equation_is_load_bearing() -> None:
    cases = (
        (984, 3_177_027, 4_480, 1_489, 499),
        (984, 3_177_027, 4_480, 4_271, 597),
        (16, 582_087, 52_684, 59, 7),
        (17, 996_082, 84_632, 19, 12),
        (17, 996_082, 84_632, 31, 10),
        (17, 996_082, 84_632, 41, 13),
        (17, 996_082, 84_632, 43, 13),
    )
    for k, n, d, prime, owner in cases:
        row = center_large_prime_row(k, n, d, prime, owner)
        assert row.owner_landings
        assert row.quadratic_congruence
        assert not row.exact_equation
        assert not row.cancellable_square_lift
