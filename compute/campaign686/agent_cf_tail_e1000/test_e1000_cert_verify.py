from compute.campaign686.agent_cf_tail_e1000.e1000_cert_verify import (
    EXPECTED_ARTIFACT_SET_SHA256,
    EXPECTED_ARTIFACTS,
    EXPECTED_GENERATOR_SHA256,
    EXPECTED_STATS,
    TARGET_K,
    full_report,
)


REPORT = full_report()


def rows_by_k() -> dict[int, dict]:
    return {row["k"]: row for row in REPORT["per_k"]}


def test_all_six_artifacts_regenerate_byte_for_byte_without_lean_output() -> None:
    assert REPORT["arithmetic"] == "exact Python integers; no Lean output consumed"
    assert REPORT["generator"]["sha256"] == EXPECTED_GENERATOR_SHA256
    assert REPORT["artifact_set_sha256"] == EXPECTED_ARTIFACT_SET_SHA256
    assert [row["k"] for row in REPORT["per_k"]] == list(TARGET_K)
    for k, row in rows_by_k().items():
        assert row["bytes"] == EXPECTED_ARTIFACTS[k]["bytes"]
        assert row["sha256"] == EXPECTED_ARTIFACTS[k]["sha256"]
        assert row["render_matches_artifact"]
        assert row["semantic_verify"]
        assert row["chunk_reference_multiplicity"] == 2


def test_frozen_tree_statistics_and_full_binary_identities() -> None:
    assert EXPECTED_STATS
    for k, row in rows_by_k().items():
        assert row["tree"] == EXPECTED_STATS[k]
        tree = row["tree"]
        assert tree["nodes"] == 2 * tree["splits"] + 1
        assert tree["kills"] + tree["highs"] == tree["splits"] + 1
        assert tree["nodes"] == tree["splits"] + tree["kills"] + tree["highs"]
        assert row["full_binary_identities"]


def test_strict_d_boundary_and_exact_equality_residual() -> None:
    expected = {
        5: (3, [1], [1]),
        7: (3, [1, 2], [2, 1]),
        9: (4, [1, 2, 3], [3, 2, 1]),
        11: (4, [1, 2, 3, 4], [4, 3, 2, 1]),
        13: (4, [1, 2, 3, 4, 5], [5, 4, 3, 2, 1]),
        15: (5, [1, 2, 3, 4, 5, 6], [6, 5, 4, 3, 2, 1]),
    }
    for k, row in rows_by_k().items():
        boundary = row["boundary"]
        slack, residual_r, excess = expected[k]
        assert boundary["target"] == "d < 10^1000"
        assert boundary["strict_y_slack_below_ymax"] == slack
        assert boundary["equality_uncovered_r"] == residual_r
        assert boundary["equality_uncovered_y_excess"] == excess
        assert boundary["equality_uncovered_count"] == (k + 1) // 2 - 2
        assert boundary["equality_first_covered_r"] == (k + 1) // 2 - 1


def test_named_d1_telescopes_remain_exact_counterfixtures_below_the_tail() -> None:
    assert [
        (row["k"], row["X"], row["Y"], row["n"], row["d"])
        for row in REPORT["telescopes"]
    ] == [(9, 8, 7, 2, 1), (15, 13, 12, 4, 1)]
    for row in REPORT["telescopes"]:
        assert row["gcd_XY"] == 1
        assert row["centered_residual"] == 0
        assert row["block_residual"] == 0
        assert row["below_Ylo_by"] > 0
        assert row["outside_tail_d_ge_221"]
