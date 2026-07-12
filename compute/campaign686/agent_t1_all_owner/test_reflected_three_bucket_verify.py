from compute.campaign686.agent_t1_all_owner.reflected_three_bucket_verify import report


def test_reflected_three_bucket_exact_report() -> None:
    data = report()
    assert data["view_count"] == {
        "unoriented_pairs": 27,
        "oriented_views": 54,
        "closed_pairs": 12,
        "closed_oriented_views": 24,
        "surviving_pairs": 15,
        "surviving_oriented_views": 30,
    }
    fifth = data["fifth_specialization"]
    assert fifth["all_constants_zero"]
    assert fifth["all_quadratics_zero"]
    assert fifth["all_linear_slopes_nonzero"]
    assert data["all_27_cubic_sign_certificates"]
    assert data["determinant_grid"]["exact_identities"] > 100_000
    assert {(row["k"], row["r"]) for row in data["surviving"]} == {
        (11, 4),
        (11, 5),
        *((13, r) for r in range(1, 7)),
        *((15, r) for r in range(1, 8)),
    }
