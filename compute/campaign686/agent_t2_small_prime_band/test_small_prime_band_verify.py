from math import prod

from .small_prime_band_verify import (
    block_valuation,
    block_valuation_direct,
    check_prime_power_endpoint,
    check_internal_prime_power_position,
    check_small_prime_system,
    exact_crossing_band,
    factorial_valuation,
    lower_window_holds,
    lower_prime_power_positions,
    named_fixture_report,
    primes_through,
    scan_band,
    upper_window_holds,
    valuation_discrepancy,
    valuation_discrepancy_by_powers,
)


def test_crossing_band_endpoints_are_exact() -> None:
    for k in range(2, 22):
        for d in range(k, 4 * k + 1):
            band = exact_crossing_band(k, d)
            assert lower_window_holds(k, d, band.lower)
            assert band.lower == 0 or not lower_window_holds(k, d, band.lower - 1)
            assert upper_window_holds(k, d, band.upper)
            assert not upper_window_holds(k, d, band.upper + 1)


def test_crossing_band_has_exact_width_k_minus_one() -> None:
    # For k>=3 equality in the defining kth-power threshold would force
    # k*(v_2(a)-v_2(b))=2 for a reduced rational a/b, which is impossible.
    for k in range(3, 30):
        for d in range(k, 5 * k + 1):
            assert exact_crossing_band(k, d).width == k - 1


def test_floor_valuations_match_direct_products() -> None:
    for k in range(1, 14):
        for n in range(0, 30):
            for p in primes_through(k + n + 2):
                assert block_valuation(k, n, p) == block_valuation_direct(k, n, p)
                for d in (1, k, 2 * k + 1):
                    assert valuation_discrepancy(k, n, d, p) == (
                        valuation_discrepancy_by_powers(k, n, d, p)
                    )


def test_small_prime_system_is_necessary_for_direct_equations() -> None:
    for k in range(1, 10):
        for d in range(1, 14):
            for n in range(0, 100):
                if prod(range(n + d + 1, n + d + k + 1)) == 4 * prod(
                    range(n + 1, n + k + 1)
                ):
                    assert check_small_prime_system(k, n, d).passes


def test_named_fixtures_replay_exactly() -> None:
    rows = named_fixture_report()
    assert [(row["k"], row["n"], row["d"]) for row in rows] == [
        (984, 3_177_026, 4_480),
        (244, 48_502, 277),
    ]
    assert all(row["in_band"] for row in rows)
    assert rows[0] == {
        "k": 984,
        "n": 3_177_026,
        "d": 4_480,
        "band_lower": 3_176_708,
        "band_upper": 3_177_690,
        "in_band": True,
        "valuation_passes": False,
        "first_failure": 2,
        "failure_discrepancy": 0,
    }
    assert rows[1] == {
        "k": 244,
        "n": 48_502,
        "d": 277,
        "band_lower": 48_373,
        "band_upper": 48_615,
        "in_band": True,
        "valuation_passes": False,
        "first_failure": 2,
        "failure_discrepancy": -5,
    }


def test_prime_power_endpoint_bounds_include_both_prime_cases() -> None:
    # p=2 checks the multiplier-prime case v_2(4)=2; odd p checks v_p(4)=0.
    for p in (2, 3, 5, 7):
        for exponent in range(1, 5):
            endpoint = p**exponent
            for k in range(1, min(endpoint, 15)):
                for d in {k, (k + endpoint - 1) // 2, endpoint - 1}:
                    check = check_prime_power_endpoint(p, exponent, k, d)
                    assert check.valuation_discrepancy < 0
                    required = 2 if p == 2 else 0
                    assert check.valuation_discrepancy != required


def test_internal_position_falsifies_the_all_prime_valuation_claim() -> None:
    two = check_internal_prime_power_position(2, 9, 33, 33, 2)
    assert (two.n, two.lower_valuation, two.upper_valuation) == (510, 35, 37)
    assert two.valuation_discrepancy == 2
    assert factorial_valuation(32, 2) == 31
    assert two.split_factorial_baseline == 26
    assert 31 > 2 + 26

    odd = check_internal_prime_power_position(3, 5, 16, 19, 8)
    assert (odd.n, odd.lower_valuation, odd.upper_valuation) == (235, 9, 9)
    assert odd.valuation_discrepancy == 0
    assert factorial_valuation(15, 3) == 6
    assert odd.split_factorial_baseline == 4
    assert 6 > 0 + 4


def test_both_endpoint_positions_for_small_exponents() -> None:
    for p, exponent, k, d in ((13, 2, 16, 16), (2, 8, 16, 16)):
        for i in (1, k):
            check = check_internal_prime_power_position(p, exponent, k, d, i)
            required = 2 if p == 2 else 0
            assert check.valuation_discrepancy != required


def test_prime_larger_than_length_excludes_every_tested_position() -> None:
    # This is the finite arithmetic replay of the new Lean any-position core.
    for p, exponent, k in ((17, 3, 16), (19, 3, 16), (23, 3, 20)):
        endpoint = p**exponent
        for d in (k, 2 * k, 3 * k):
            for i in range(1, k + 1):
                check = check_internal_prime_power_position(p, exponent, k, d, i)
                assert check.valuation_discrepancy < 0


def test_small_cofactor_large_base_strengthening() -> None:
    p, exponent, k, d = 17, 2, 16, 16
    endpoint = p**exponent
    for coefficient in range(1, 5):
        for i in range(1, k + 1):
            n = coefficient * endpoint - i
            assert 9 * d < n
            lower = block_valuation(k, n, p)
            upper = block_valuation(k, n + d, p)
            assert lower == exponent
            assert upper < exponent


def test_named_fixtures_have_exact_large_base_prime_owners() -> None:
    first = lower_prime_power_positions(984, 3_177_026)
    second = lower_prime_power_positions(244, 48_502)
    assert (len(first), len(second)) == (63, 20)
    assert all(base > 984 and exponent == 1 for _, base, exponent in first)
    assert all(base > 244 and exponent == 1 for _, base, exponent in second)


def test_scan_band_survivors_really_pass() -> None:
    for k, d in ((16, 16), (17, 34), (23, 69), (32, 160)):
        scan = scan_band(k, d)
        assert all(check_small_prime_system(k, n, d).passes for n in scan.survivors)
