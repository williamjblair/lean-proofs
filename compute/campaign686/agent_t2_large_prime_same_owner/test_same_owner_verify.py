import same_owner_verify as verify


def test_least_dominant_component_is_exact_at_both_sides():
    for k, d in [(16, 32), (16, 323), (17, 17 * 19), (100, 10**12)]:
        h = verify.least_dominant_component(k, d)
        target = verify.dominance_ceiling(k, d)
        assert 6 * h * h >= target
        assert h == 0 or 6 * (h - 1) * (h - 1) < target


def test_k16_two_prime_exponent_one_boundary():
    row = verify.whole_two_component_certificate(16, 17, 1, 19, 1)
    assert row["d"] == 323
    assert row["dominance_ceiling"] == 65_516
    assert row["six_d_squared"] == 625_974
    assert row["margin"] == 560_458


def test_exponent_one_components_are_included():
    for k in range(16, 80):
        row = verify.whole_two_component_certificate(k, k, 1, k + 1, 1)
        assert row["margin"] > 0


def test_higher_exponents_and_rows_preserve_dominance():
    for k in range(16, 64):
        for e in range(1, 4):
            for f in range(1, 4):
                row = verify.whole_two_component_certificate(k, k + 1, e, k + 3, f)
                assert row["dominance_ceiling"] <= row["six_d_squared"]


def test_full_audit_freezes_subsumption_and_positive_margin():
    report = verify.audit()
    assert report["reused_aggregation"] == (
        "globalResidualGroupedLeft_square_dvd_residual"
    )
    assert report["sweep_cases"] == 41_625
    assert report["sweep_minimum_margin"][0] > 0
