from compute.campaign686.fourth_local_lift_verify import (
    ROWS,
    TARGET,
    fourth_local_value,
    local_coefficients,
    local_congruence_crt_witness_fourth,
    local_denominator_clearing_difference,
    report,
    signed_composition_grid,
    three_bucket_fourth_obstruction,
    third_local_value,
)


def test_fourth_formula_retains_every_a_correction() -> None:
    # This deliberately uses A != 0.  Omitting any of -9 D A^2,
    # 36 E A M^2, or the cubic-coefficient term changes the exact residue.
    k, owner = 9, 2
    c, d, e, f = local_coefficients(k, owner)[:4]
    h, m, a = 11, 37, -5
    third = third_local_value(c, d, e, h, m, a)
    expected = 3 * third + h**2 * (
        -9 * d * a**2 + 36 * e * a * m**2 + 84 * f * m**4
    )
    assert fourth_local_value(c, d, e, f, h, m, a) == expected
    quotient = (m + a * h) // 3
    assert 3 * quotient - m == a * h
    exact_difference = local_denominator_clearing_difference(
        constant=c,
        linear=d,
        quadratic=e,
        cubic=f,
        component=h,
        opposite=m,
        cofactor=a,
        quotient=quotient,
    )
    assert exact_difference % h**3 == 0
    correction_terms = (
        -9 * d * a**2,
        36 * e * a * m**2,
        84 * f * m**4,
    )
    # Removing any one term changes 27*T4-G4 by H^2 times a nonmultiple of H.
    assert all(
        (exact_difference + h**2 * term) % h**3 != 0
        for term in correction_terms
    )


def test_signed_three_bucket_composition_grid() -> None:
    result = signed_composition_grid()
    assert result["signed_exact_composition_fixtures"] > 1_000
    assert result["all_fourth_compositions_hold"] is True


def test_composed_obstruction_is_cyclically_well_formed() -> None:
    k = 7
    indices = (1, 4, 7)
    components = (5, 11, 17)
    cofactors = (19, 4, 1)
    # This fixture is not required to satisfy the step-three equations; the
    # function itself is an integral polynomial at every cyclic owner.
    values = []
    for position, owner in enumerate(indices):
        others = tuple(index for index in indices if index != owner)
        left = (position + 1) % 3
        right = (position + 2) % 3
        values.append(
            three_bucket_fourth_obstruction(
                k=k,
                owner=owner,
                other_left=others[0],
                other_right=others[1],
                owner_component=components[position],
                owner_cofactor=cofactors[position],
                left_cofactor=cofactors[left],
                right_cofactor=cofactors[right],
                loss=3,
                gap=3 * components[0] * components[1] * components[2],
            )
        )
    assert len(values) == 3
    assert all(isinstance(value, int) for value in values)


def test_target_size_fourth_order_crt_falsifier_is_not_a_solution() -> None:
    witness = local_congruence_crt_witness_fourth(
        k=5,
        indices=(1, 2, 4),
        components=(101**20, 103**20, 107**20),
    )
    assert witness["gap"] >= TARGET
    assert witness["all_square_second_third_fourth_congruences_hold"] is True
    assert witness["all_composed_fourth_congruences_hold"] is True
    assert witness["block_equation_holds"] is False
    assert witness["short_window_holds"] is False
    assert witness["gap_digits"] >= 121


def test_report_states_the_exact_route_boundary() -> None:
    result = report()
    assert set(result["rows"]) == set(ROWS)
    assert result["checked_exponent_family"]["all_checked_lifts_hold"] is True
    assert result["checked_exponent_family"][
        "all_checked_members_are_proper_nonshort_nonsolutions"
    ] is True
    assert result["target_size_fourth_order_crt_falsifier"][
        "all_square_second_third_fourth_congruences_hold"
    ] is True
    assert result["bounded_resultant_verdict"] == (
        "NO: the fourth lift is a proper one-digit strengthening, but an "
        "exact target-size CRT lift satisfies it cyclically while failing "
        "the short window and the block equation"
    )
