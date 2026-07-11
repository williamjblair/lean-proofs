from compute.campaign686.three_bucket_zero_exclusion_verify import report


def test_all_ordered_target_owner_triples_are_certified() -> None:
    certificate = report()
    assert certificate["ordered_distinct_owner_triples"] == 6_210
    assert certificate["all_zero_obstruction_branches_excluded_above_cutoff"]


def test_rounded_bounds_retain_a_strict_cutoff_margin() -> None:
    certificate = report()
    assert certificate["global_maximum_cross_numerator"] < certificate["cross_bound"]
    assert certificate["global_maximum_third_coefficient"] < certificate["third_bound"]
    assert certificate["numeric_majorant"] < certificate["cutoff"]
    assert certificate["cutoff_margin_floor"] == 7
