from compute.campaign686.agent_odd_fifth_gcd_eliminant.odd_fifth_gcd_eliminant_verify import (
    report,
)


def test_all_1008_geometries_and_leading_determinants() -> None:
    scan = report()["scan"]
    assert scan["totals"]["nonreflected_triples"] == 1008
    assert [row["nonreflected_triples"] for row in scan["rows"]] == [
        8,
        32,
        80,
        160,
        280,
        448,
    ]
    assert scan["leading_determinant_positive"] == 504
    assert scan["leading_determinant_negative"] == 504
    assert scan["rank_failures"] == 0
    assert scan["totals"]["full_rank_packing_geometries"] == 1008
    for family in ("raw", "opposite_packed", "pair_packed", "triple_product"):
        assert (
            scan["totals"][f"{family}_equation_quotient_kernel_zero"] == 1008
        )


def test_three_cross_lattice_sign_census() -> None:
    totals = report()["scan"]["totals"]
    assert totals["ab_mixed"] == 1008
    assert totals["ac_mixed"] == 1008
    assert totals["bc_mixed"] == 566
    assert totals["bc_one_sided_positive"] == 221
    assert totals["bc_one_sided_negative"] == 221
    assert totals["bc_one_sided_total"] == 442
    assert [row["bc_one_sided_total"] for row in report()["scan"]["rows"]] == [
        2,
        10,
        34,
        68,
        124,
        204,
    ]


def test_natural_packing_families_are_full_rank_at_closing_degree() -> None:
    certificate = report()["scan"]["rank_certificate"]
    assert certificate == {
        "raw": {
            "known_divisor_exponent": 4,
            "polynomial_degree": 5,
            "closing_degree_cutoff": 3,
            "rank_on_terms_degree_at_least_4": 3,
        },
        "opposite_packed_Xt_Xu_Js": {
            "known_divisor_exponent": 6,
            "polynomial_degree": 7,
            "closing_degree_cutoff": 5,
            "rank_on_terms_degree_at_least_6": 3,
        },
        "pair_packed_Xs_Jt_Ju": {
            "known_divisor_exponent": 10,
            "polynomial_degree": 11,
            "closing_degree_cutoff": 9,
            "rank_on_terms_degree_at_least_10": 3,
        },
        "triple_product": {
            "known_divisor_exponent": 14,
            "polynomial_degree": 15,
            "uncancelled_degree_deficit": 1,
        },
        "exact_block_equation_quotient": {
            "method": (
                "allow every multiplier monomial through degree "
                "polynomial_degree-k and project away the exact cleared "
                "block-difference polynomial"
            ),
            "raw_kernel_zero_geometries": 1008,
            "opposite_packed_kernel_zero_geometries": 1008,
            "pair_packed_kernel_zero_geometries": 1008,
            "triple_product_kernel_zero_geometries": 1008,
        },
    }


def test_one_sided_bound_constants_are_frozen_exactly() -> None:
    rows = report()["scan"]["rows"]
    assert [row["one_sided_uniform_H"] for row in rows] == [
        281977658168593580928,
        64756146619640142341307629568,
        19998831987650954057717903628603755593728,
        1697446799463578737674770682177308518186824499200,
        79620649493943859271436554905870151542650622317881720832000,
        131443214186113056779275329051984784346429689046767891479303458232729600000,
    ]
    assert [row["one_sided_uniform_H_digits"] for row in rows] == [
        21,
        29,
        41,
        49,
        59,
        75,
    ]
    assert [row["one_sided_minimum_abs_weight"] for row in rows] == [
        203,
        10543,
        12339295,
        164430032,
        103538921875,
        47767948526030,
    ]


def test_small_coarse_short_fixture_reaches_fifth_but_not_target_ratio() -> None:
    fixture = report()["small_short_fifth_fixture"]
    assert fixture["components"] == [2, 5, 3]
    assert fixture["g"] == 30
    assert fixture["d"] == 900
    assert fixture["n"] == 3423
    assert fixture["residuals"] == [9372, 9375, 9378]
    assert fixture["cofactors"] == [2343, 375, 1042]
    assert fixture["anchor_residual_ratio"] == [781, 75]
    assert fixture["pairwise_coprime"] is True
    assert fixture["coarse_window"] is True
    assert fixture["target_ratio_window"] is False
    assert fixture["all_lifts_through_fifth"] is True
    assert fixture["block_equation"] is False


def test_121_and_1004_digit_historical_fixtures_replay() -> None:
    fixtures = report()["historical_fixtures"]
    fourth = fixtures["fourth_order_121_digit"]
    fifth_121 = fixtures["fifth_order_121_digit"]
    fifth_1004 = fixtures["fifth_order_1004_digit"]
    assert fourth["gap_digits"] == 121
    assert fourth["all_local_lifts"] is True
    assert fourth["all_composed_lifts"] is True
    assert fourth["upper_window"] is False
    assert fourth["block_equation"] is False
    for digits, fixture in ((121, fifth_121), (1004, fifth_1004)):
        assert fixture["gap_digits"] == digits
        assert fixture["local_fifth_remainders"] == [0, 0, 0]
        assert fixture["reduced_remainders"] == [0, 0, 0]
        assert fixture["normalized_remainders"] == [0, 0, 0]
        assert fixture["all_z_nonzero"] is True
        assert fixture["all_w_nonzero"] is True
        assert fixture["all_normalized_nonzero"] is True
        assert fixture["upper_window"] is False
        assert fixture["block_equation"] is False
