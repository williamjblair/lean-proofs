from compute.campaign686.global_square_lift_verify import (
    affine_product_coefficients,
    exact_small_solutions,
    random_polynomial_identity,
    residual_quotient_formula,
    residuals,
    verify_square_lift,
)


def test_affine_product_coefficients() -> None:
    # (z+2)(z-3)(z+5) = z^3+4z^2-11z-30.
    assert affine_product_coefficients([2, -3, 5]) == [-30, -11, 4, 1]


def test_random_exact_polynomial_identity() -> None:
    assert random_polynomial_identity(samples=500)


def test_all_small_equation_solutions_satisfy_square_lift() -> None:
    solutions = exact_small_solutions()
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
        (3, 0, 1),
        (6, 1, 1),
        (9, 2, 1),
        (12, 3, 1),
        (15, 4, 1),
    ]
    assert all(verify_square_lift(*row) for row in solutions)


def test_k5_quotient_formula_is_exact() -> None:
    # This row is an algebra check, not an equation solution.
    k, n, d = 5, 123, 37
    values = residuals(k, n, d)
    coefficients = affine_product_coefficients(values)
    correction = sum(
        (4**degree - 4) * coefficient * d**degree
        for degree, coefficient in enumerate(coefficients)
        if degree >= 2
    )
    assert correction == 3 * d * d * residual_quotient_formula(k, n, d)


def test_named_large_k_fixtures_do_not_meet_equation_premise() -> None:
    from compute.campaign686.global_square_lift_verify import block_product

    for k, n, d in ((984, 3177026, 4480), (244, 48502, 277)):
        assert block_product(k, n + d) != 4 * block_product(k, n)
