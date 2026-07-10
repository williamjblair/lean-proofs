from fractions import Fraction
from math import gcd

import pytest

from compute730.campaign_uniform.repair.near_affine_payment import (
    BRANCHES,
    MAX_SLOPE,
    T,
    base_p_digit_length,
    branch_values,
    cofactor_test_value,
    divisibility_count,
    dyadic_one_percent_certificate,
    exact_valuation_count,
    floor_nth_root,
    kappa_one_third_certificate,
    max_branch_value,
    near_envelope,
    prime_power_pair_count_upper,
    prime_power_tail_partial,
    rational_tail_upper,
    threshold_consequence,
)


def brute_divisibility_count(name: str, p: int, a: int, X: int) -> int:
    branch = BRANCHES[name]
    q = p**a
    return sum(
        1
        for x in range(1, X + 1)
        if (branch.slope * x + branch.intercept) % q == 0
    )


def test_exact_branch_geometry_and_residue_counts() -> None:
    assert T == 5289
    assert MAX_SLOPE == 380_808
    assert {name: (b.slope, b.intercept) for name, b in BRANCHES.items()} == {
        "P": (222_138, 11),
        "Q": (380_808, 13),
        "R": (148_092, 5),
        "S": (380_808, 19),
    }
    for X in (1, 2, 17, 100):
        values = branch_values(X)
        assert max(values.values()) == max_branch_value(X) == 380_808 * X + 19
        for name, branch in BRANCHES.items():
            assert values[name] == branch.slope * X + branch.intercept

    for name, branch in BRANCHES.items():
        for p in (5, 7, 11, 13):
            if gcd(branch.slope, p) != 1:
                continue
            for a in (1, 2, 3):
                for X in (1, 9, 100, 777):
                    count = divisibility_count(name, p, a, X)
                    assert count == brute_divisibility_count(name, p, a, X)
                    q = p**a
                    assert count * q <= X + q
                    assert X <= (count + 1) * q


def test_cofactor_values_and_digit_length_bound_are_exact() -> None:
    for x in range(1, 80):
        values = branch_values(x)
        M = max_branch_value(x)
        for name, value in values.items():
            for p in (5, 7, 11, 13, 17, 19):
                q = 1
                while value % (q * p) == 0:
                    q *= p
                if q == 1:
                    continue
                a = 0
                work = q
                while work > 1:
                    work //= p
                    a += 1
                z = cofactor_test_value(name, x, p, a)
                assert z > 0
                assert 2 * q * z <= 3 * M * M
                digits = base_p_digit_length(z, p)
                assert p ** (digits - 1) <= z < p**digits


def test_rational_near_envelope_for_eta_one_twelfth() -> None:
    for p in range(5, 500):
        assert kappa_one_third_certificate(p)

    for r in range(1, 100):
        for a in range(1, 250):
            if near_envelope(a, r):
                assert a >= 2
                assert 12 * a > 19 * r

    # If r were allowed to stay artificially fixed at 1, the pair (a,r)=(2,1)
    # would remain near-affine and valuation rarity would not improve with X.
    # Complete blocks give this exact positive-density obstruction.
    assert near_envelope(2, 1)
    X = 125 * 1_000
    assert exact_valuation_count("Q", 5, 2, X) == 4_000
    assert Fraction(4_000, X) == Fraction(4, 125)


def test_threshold_consequence_is_exact_fraction_arithmetic() -> None:
    # These tuples satisfy the abstract maximal-r premises with rational
    # stand-ins for the next block weight.  The theorem uses the same
    # implication with w_(r+1)=((r+1) log p)^2.
    cases = [
        (10**8, 5, 8, 3, 260, Fraction(17, 3)),
        (10**12, 7, 10, 4, 90, Fraction(29, 5)),
        (10**18, 11, 14, 5, 80, Fraction(41, 7)),
    ]
    for X, p, a, r, N, w_next in cases:
        q = p**a
        # Enlarge N if necessary to make the residue-count lower relation
        # true, while retaining the abstract maximality inequality.
        N = max(N, (X + q - 1) // q - 1)
        if not N < p ** (r + 1) * w_next:
            pytest.skip("fixture does not meet abstract maximality")
        W_bar = w_next + 1
        certificate = threshold_consequence(
            X=X,
            p=p,
            a=a,
            r=r,
            residue_count=N,
            next_weight=w_next,
            global_weight_upper=W_bar,
        )
        assert certificate
        assert Fraction(X**38, 1) < (2 * W_bar) ** 38 * q**81


def test_prime_power_elementary_sums() -> None:
    for Y in (2, 5, 50, 1_000, 10_000):
        partial = prime_power_tail_partial(Y=Y, prime_limit=2_000, exponent_limit=20)
        assert partial <= rational_tail_upper(Y)

    for M in (4, 10, 100, 10_000):
        actual = 0
        for p in range(2, M + 1):
            if any(p % d == 0 for d in range(2, floor_nth_root(p, 2) + 1)):
                continue
            q = p * p
            while q <= M:
                actual += 1
                q *= p
        assert actual <= prime_power_pair_count_upper(M)


def test_exact_uniform_one_percent_certificate() -> None:
    cert = dyadic_one_percent_certificate()
    assert cert["X0"] == 2**57
    assert cert["M_upper"] == 2**77
    assert cert["bit_length_upper"] == 78
    assert cert["Y_integer_lower"] == 1_210_239
    assert cert["sqrt_Y_floor"] == 1100
    assert cert["cuberoot_Y_floor"] == 106
    assert cert["threshold_powered_inequality"]
    payment = cert["payment_upper"]
    assert payment == Fraction(
        232_437_037_423_222_418_449,
        27_831_344_977_224_191_180_800,
    )
    assert payment < Fraction(1, 100)
