from compute.campaign686.agent_t1_all_owner.reflected_three_bucket_verify import (
    LEGACY_TARGET,
    TAIL1000_INTERMEDIATE_CUTOFF,
    TAIL1000_TARGET,
    report,
)


def test_reflected_three_bucket_exact_report() -> None:
    data = report()
    assert data["view_count"] == {
        "unoriented_pairs": 27,
        "oriented_views": 54,
        "legacy_10_120_closed_pairs": 12,
        "legacy_10_120_closed_oriented_views": 24,
        "legacy_10_120_surviving_pairs": 15,
        "legacy_10_120_surviving_oriented_views": 30,
    }
    fifth = data["fifth_specialization"]
    assert fifth["all_constants_zero"]
    assert fifth["all_quadratics_zero"]
    assert fifth["all_linear_slopes_nonzero"]
    assert data["all_27_cubic_sign_certificates"]
    assert data["determinant_grid"]["exact_identities"] > 100_000
    assert {
        (row["k"], row["r"])
        for row in data["legacy_10_120_surviving"]
    } == {
        (11, 4),
        (11, 5),
        *((13, r) for r in range(1, 7)),
        *((15, r) for r in range(1, 8)),
    }
    assert data["quantified_remaining_gap"] == (
        "all 27 center/reflected pairs close below 10^1000; arbitrary "
        "owner configurations and exactly-three configurations not "
        "consisting of the center plus a reflected pair remain outside "
        "this packing slice"
    )


def test_tail1000_upgrade_closes_all_27_pairs_by_exact_integers() -> None:
    upgrade = report()["tail1000_upgrade"]
    assert upgrade["legacy_target"] == LEGACY_TARGET == 10**120
    assert (
        upgrade["intermediate_cutoff"]
        == TAIL1000_INTERMEDIATE_CUTOFF
        == 10**200
    )
    assert upgrade["tail1000_target"] == TAIL1000_TARGET == 10**1000
    assert upgrade["intermediate_cutoff"] < upgrade["tail1000_target"]
    assert upgrade["total_pairs"] == 27
    assert upgrade["legacy_closed_pairs"] == 12
    assert upgrade["newly_closed_pairs"] == 15
    assert upgrade["all_pairs_below_10_200"] is True
    assert upgrade["all_pairs_below_tail1000"] is True

    maxima = upgrade["per_row_maxima"]
    assert [(row["k"], row["pair_count"]) for row in maxima] == [
        (5, 2),
        (7, 3),
        (9, 4),
        (11, 5),
        (13, 6),
        (15, 7),
    ]
    assert [row["maximum_cutoff_digits"] for row in maxima] == [
        49,
        71,
        104,
        125,
        163,
        197,
    ]
    assert [row["maximum_r"] for row in maxima] == [2, 3, 4, 5, 6, 7]
    assert maxima[-1]["maximum_cutoff"] == int(
        "1161064963187601011337086887452471131614906161135846190889451108310"
        "485772374885488152059625867041244822070082580575375389674741721690772"
        "9085457360108954666243725838628597792768000000000000000000000"
    )
    assert all(row["maximum_below_10_200"] is True for row in maxima)
    assert all(row["maximum_below_tail1000"] is True for row in maxima)
    assert all(isinstance(row["maximum_cutoff"], int) for row in maxima)

    new_pairs = {(row["k"], row["r"]) for row in upgrade["newly_closed"]}
    assert new_pairs == {
        (11, 4),
        (11, 5),
        *((13, r) for r in range(1, 7)),
        *((15, r) for r in range(1, 8)),
    }
    assert all(
        LEGACY_TARGET <= row["cutoff"] < TAIL1000_INTERMEDIATE_CUTOFF
        for row in upgrade["newly_closed"]
    )
