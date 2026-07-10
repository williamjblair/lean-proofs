from compute.campaign686.moment_lifts_verify import (
    block,
    evaluate,
    moment_certificate,
    moment_remainders,
    polynomial_coefficients,
)


def test_polynomial_coefficient_convention() -> None:
    # (z+2)(z-3)=z^2-z-6
    assert polynomial_coefficients([2, -3]) == [-6, -1, 1]


def test_generic_identities_monomial_by_monomial() -> None:
    for degree in range(13):
        for coefficient in (-11, -1, 0, 7):
            coefficients = [0] * degree + [coefficient]
            for d in range(-6, 7):
                direct, reflected = moment_remainders(coefficients, d)
                expected_direct = (
                    coefficient * (2**degree - 4) * d**degree
                    if degree >= 3
                    else 0
                )
                expected_reflected = (
                    coefficient
                    * (2**degree - 4 * (-1) ** degree)
                    * d**degree
                    if degree >= 3
                    else 0
                )
                assert direct == expected_direct
                assert reflected == expected_reflected
                if d == 0:
                    assert direct == reflected == 0
                else:
                    assert direct % d**3 == 0
                    assert reflected % d**3 == 0


def test_both_residual_transformations_exactly() -> None:
    for k in range(9):
        for n in range(13):
            for d in range(13):
                lower = polynomial_coefficients(
                    [n + i - d for i in range(1, k + 1)]
                )
                upper = polynomial_coefficients(
                    [3 * (n + i) + d for i in range(1, k + 1)]
                )
                assert evaluate(lower, d) == block(k, n)
                assert evaluate(lower, 2 * d) == block(k, n + d)
                assert evaluate(upper, -d) == 3**k * block(k, n)
                assert evaluate(upper, 2 * d) == 3**k * block(k, n + d)


def test_vacuous_k_zero_and_d_zero_boundaries() -> None:
    for n in range(20):
        for d in range(20):
            assert block(0, n + d) == 1
            assert block(0, n + d) != 4 * block(0, n)
        for k in range(1, 20):
            assert block(k, n) != 4 * block(k, n)


def test_cubic_product_overclaim_is_false() -> None:
    # This is an exact equation solution: B(1,3) = 4 B(1,0).  The corrected
    # combinations vanish, but neither residual product contains d^3 = 27.
    k, n, d = 1, 0, 3
    lower = polynomial_coefficients([n + 1 - d])
    upper = polynomial_coefficients([3 * (n + 1) + d])
    assert block(k, n + d) == 4 * block(k, n)
    assert moment_remainders(lower, d)[0] == 0
    assert moment_remainders(upper, d)[1] == 0
    assert lower[0] == -2 and lower[0] % d**3 != 0
    assert upper[0] == 6 and upper[0] % d**3 != 0


def test_every_small_equation_solution_satisfies_both_cubic_lifts() -> None:
    solutions = []
    for k in range(1, 16):
        for n in range(0, 40):
            for d in range(1, 40):
                if block(k, n + d) == 4 * block(k, n):
                    solutions.append((k, n, d))
                    certificate = moment_certificate(k, n, d)
                    assert certificate["lower_identity"] == 0
                    assert certificate["upper_identity"] == 0
                    assert certificate["lower_cube_divides"]
                    assert certificate["upper_cube_divides"]
    assert solutions == [
        (1, 0, 3),
        (1, 1, 6),
        (1, 2, 9),
        (1, 3, 12),
        (1, 4, 15),
        (1, 5, 18),
        (1, 6, 21),
        (1, 7, 24),
        (1, 8, 27),
        (1, 9, 30),
        (1, 10, 33),
        (1, 11, 36),
        (1, 12, 39),
        (3, 0, 1),
        (6, 1, 1),
        (9, 2, 1),
        (12, 3, 1),
        (15, 4, 1),
    ]


def test_non_solutions_do_not_trigger_a_claim() -> None:
    for fixture in ((5, 100, 5), (984, 3_177_026, 4_480), (244, 48_502, 277)):
        certificate = moment_certificate(*fixture)
        assert not certificate["equation"]
        k, n, d = fixture
        block_difference = block(k, n + d) - 4 * block(k, n)
        assert certificate["lower_identity"] == block_difference
        assert certificate["upper_identity"] == 3**k * block_difference
