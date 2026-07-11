from compute.campaign686.three_bucket_short_crt_lcm_verify import report


EXPECTED = {
    5: {
        "positive_zero_cases": 12,
        "maximum_lcm": 5_443_200,
        "zero_branch_bound": 740_541_350_707_200,
        "minimum_abc": 46_296_296_296_296_296_296_296_296_296_294_624_457,
    },
    7: {
        "positive_zero_cases": 45,
        "maximum_lcm": 59_999_849_280,
        "zero_branch_bound": 413_247_483_519_713_740_800_000,
        "minimum_abc": 716_294_573_088_391_804_384_271_040_815_308_651,
    },
    9: {
        "positive_zero_cases": 112,
        "maximum_lcm": 736_171_343_178_485_760,
        "zero_branch_bound":
            252_438_801_810_021_029_402_684_623_002_009_600_000,
        "minimum_abc": 3_214_574_169_492_218_063_895_298_388_397_719,
    },
    11: {
        "positive_zero_cases": 225,
        "maximum_lcm": 34_885_840_090_609_728_000,
        "zero_branch_bound":
            78_486_764_429_761_645_052_953_426_899_755_335_680_000_000,
        "minimum_abc": 18_497_091_393_047_867_380_101_052_189_640,
    },
    13: {
        "positive_zero_cases": 396,
        "maximum_lcm": 820_995_472_546_561_208_033_280,
        "zero_branch_bound":
            2_838_891_296_780_015_046_791_841_911_350_004_426_030_003_822_316_748_800_000,
        "minimum_abc": 25_548_663_987_620_205_641_977_050_294,
    },
    15: {
        "positive_zero_cases": 637,
        "maximum_lcm": 138_245_988_147_349_868_236_401_258_147_840,
        "zero_branch_bound":
            17_694_526_643_294_042_605_461_686_913_458_493_647_472_960_653_351_115_605_266_135_410_278_400_000,
        "minimum_abc": 33_652_495_592_619_590_630_929_591,
    },
}


def test_exact_row_certificates() -> None:
    result = report()
    assert result["target"] == 10**120
    assert result["all_zero_branches_below_target"] is True
    for row in result["rows"]:
        expected = EXPECTED[row["k"]]
        for key, value in expected.items():
            assert row[key] == value
        assert row["zero_branch_bound"] < result["target"]
        assert row["abc_bound_at_predecessor"] < result["target"]
        assert row["abc_bound_at_minimum"] >= result["target"]


def test_maximizers_are_retained() -> None:
    rows = {row["k"]: row for row in report()["rows"]}
    assert rows[5]["maximum_lcm_case"]["indices"] == [1, 4, 5]
    assert rows[15]["maximum_lcm_case"]["indices"] == [1, 14, 15]
    assert rows[15]["maximum_lcm_case"]["zero_owner"] == 1
    assert rows[15]["abc_threshold_case"] == [1, 2, 15]
