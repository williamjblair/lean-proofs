from compute.campaign686.three_bucket_short_crt_lcm_hostile_verify import (
    TARGET,
    boundary_report,
    coarse_bound_audit,
    report,
)


EXPECTED = {
    5: (12, 5_443_200, 46_296_296_296_296_296_296_296_296_296_294_624_457),
    7: (45, 59_999_849_280, 716_294_573_088_391_804_384_271_040_815_308_651),
    9: (112, 736_171_343_178_485_760, 3_214_574_169_492_218_063_895_298_388_397_719),
    11: (225, 34_885_840_090_609_728_000, 18_497_091_393_047_867_380_101_052_189_640),
    13: (396, 820_995_472_546_561_208_033_280, 25_548_663_987_620_205_641_977_050_294),
    15: (637, 138_245_988_147_349_868_236_401_258_147_840, 33_652_495_592_619_590_630_929_591),
}

EXPECTED_BOUNDARIES = {
    5: (18, 6, 6, 0, 1, [1, 4, 5]),
    7: (60, 15, 15, 18, 5, [1, 2, 7]),
    9: (140, 28, 28, 54, 35, [1, 8, 9]),
    11: (270, 45, 45, 84, 7, [1, 10, 11]),
    13: (462, 66, 66, 150, 77, [1, 12, 13]),
    15: (728, 91, 91, 294, 143, [1, 14, 15]),
}


def test_all_row_certificates_are_independent_and_exact() -> None:
    result = report()
    assert result["total_positive_zero_cases"] == 1_427
    assert result["total_nonpositive_zero_cases"] == 1_678
    for row in result["rows"]:
        count, maximum_lcm, threshold = EXPECTED[row["k"]]
        (
            nonpositive,
            centers,
            reflections,
            nonintegral,
            maximum_denominator,
            maximum_case,
        ) = EXPECTED_BOUNDARIES[row["k"]]
        assert row["positive_zero_cases"] == count
        assert row["nonpositive_zero_cases"] == nonpositive
        assert row["positive_zero_cases"] + row["nonpositive_zero_cases"] == 3 * row["triples"]
        assert row["center_triples"] == centers
        assert row["reflected_pair_triples"] == reflections
        assert row["nonintegral_denominator_cases"] == nonintegral
        assert row["maximum_denominator"] == maximum_denominator
        assert row["maximum_lcm"] == maximum_lcm
        assert row["maximum_lcm_case"]["indices"] == maximum_case
        assert row["maximum_lcm_case"]["zero_owner"] == 1
        assert row["abc_threshold"] == threshold
        assert row["zero_bound"] < TARGET
        assert row["abc_before"] < TARGET <= row["abc_at"]
        assert row["abc_threshold_indices"] == [1, 2, row["k"]]


def test_global_maximum_and_coarse_bounds() -> None:
    result = report()
    row15 = next(row for row in result["rows"] if row["k"] == 15)
    assert row15["maximum_lcm_case"]["indices"] == [1, 14, 15]
    assert row15["maximum_lcm_case"]["zero_owner"] == 1
    coarse = coarse_bound_audit()
    assert coarse["second_numerator_bound"] == 348_736_460_194_535_895_465_984_000
    assert coarse["third_coefficient_bound"] == 13_835_291_827_230_720
    assert coarse["coarse_product_bound"] < TARGET


def test_boundaries_and_old_falsifiers() -> None:
    boundaries = boundary_report()
    sharp = boundaries["packing"]["g_fourth_power_sharp_fixture"]
    assert sharp["d"] == 810
    assert sharp["d_divides_Lg4"] is True
    assert sharp["d_divides_Lg3"] is False
    assert boundaries["d_eq_one_telescopes"] == [[9, 2, 1], [15, 4, 1]]
    below = boundaries["below_threshold_fixture"]
    assert below["below_target"] is True
    assert below["below_new_abc_threshold"] is True
    assert below["short_window"] is True
    assert below["local_divisibilities"] is True
    assert below["equation"] is False
    pseudo = boundaries["crt_pseudo_witness"]
    assert pseudo["gap_digits"] == 121
    assert pseudo["gap_at_least_target"] is True
    assert pseudo["local_divisibilities"] is True
    assert pseudo["composed_divisibilities"] is True
    assert pseudo["all_second_obstructions_nonzero"] is True
    assert pseudo["short_window"] is False
    assert pseudo["equation"] is False


def test_equation_context_makes_new_abc_thresholds_redundant() -> None:
    result = report()
    for row in result["rows"]:
        assert row["equation_context_minimum_abc"] == 125 * TARGET + 1
        assert row["equation_context_minimum_abc"] > row["abc_threshold"]
        assert row["equation_context_to_new_threshold_floor"] > 10**70
