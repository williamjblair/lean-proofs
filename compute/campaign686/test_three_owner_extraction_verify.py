from compute.campaign686.three_owner_extraction_verify import report


def test_no_two_cover_extracts_three_live_distinct_owners() -> None:
    certificate = report()
    assert certificate["finite_models"] > 200_000
    assert certificate["no_two_cover_models"] > 0
    assert certificate["successful_three_owner_extractions"] == certificate["no_two_cover_models"]


def test_zero_clean_and_small_owner_boundaries_are_retained() -> None:
    certificate = report()
    counts = certificate["boundary_counts"]
    assert counts["zero"] > 0
    assert counts["one"] > 0
    assert counts["two"] > 0
    assert counts["three_or_more"] > 0
    assert certificate["zero_clean_outside_cover_occurrences"] > 0
