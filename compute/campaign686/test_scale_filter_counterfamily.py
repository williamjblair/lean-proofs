from __future__ import annotations

from compute.campaign686.scale_filter_counterfamily import (
    BASE_G,
    BASE_Z,
    EXPECTED_SCALE_LADDER,
    POSITIVITY_NEGATIVE_COEFFICIENT_SUM,
    T1_FIXTURE,
    counterfamily_point,
    k5_convergent_floor_summary,
    k5_floor_pin,
    scale_ladder_summary,
    telescope_checks,
    verify_counterfamily,
)


def test_t1_fixture_is_byte_stable_and_exact() -> None:
    point = counterfamily_point(1)
    assert point.g == BASE_G
    assert point.z == BASE_Z
    assert {
        "g": point.g,
        "z": point.z,
        "u": point.u,
        "v": point.v,
    } == T1_FIXTURE
    report = verify_counterfamily(point)
    assert report["gcd_u_v"] == 1
    assert report["v_is_odd"] is True
    assert report["v2_u"] == 2
    assert report["constant_congruence_remainder"] == 0
    assert report["next_congruence_remainder"] == 0
    assert report["Q_positive"] is True


def test_counterfamily_checks_hold_at_multiple_unbounded_scales() -> None:
    for t in (1, 2, 17):
        report = verify_counterfamily(counterfamily_point(t))
        assert report["g"] == BASE_G * t
        assert report["z"] == (BASE_G * t) ** 2
        assert report["ratio_lower_margin_100u_minus_131v"] > 0
        assert report["ratio_upper_margin_211v_minus_160u"] > 0
        assert report["alpha_side_margin_4x160pow5_minus_211pow5"] == 1_203_197_949
        assert report["positivity_margin_907z_minus_negative_sum"] > 0
        assert report["Q"] > 0


def test_explicit_positivity_constant_is_exact() -> None:
    assert POSITIVITY_NEGATIVE_COEFFICIENT_SUM == 7_151_859_139_313_955
    assert 907 * BASE_Z == 11_987_586_730_230_192
    assert 907 * BASE_Z - POSITIVITY_NEGATIVE_COEFFICIENT_SUM == 4_835_727_590_916_237


def test_floor_pin_lemma_on_an_exact_degenerate_root() -> None:
    # P_5(2) = 0 supplies a root of the scale polynomial.  Coprimality is
    # not part of the floor lemma, and v = 2 meets its explicit size bound.
    assert k5_floor_pin(u=2, v=2, z=1) == 1


def test_floor_pin_implication_on_all_small_roots() -> None:
    checked = 0
    for v in range(2, 20):
        for u in range(1, (4 * v - 1) // 3 + 1):
            for z in range(1, 30):
                try:
                    result = k5_floor_pin(u, v, z)
                except ValueError:
                    continue
                assert result == z
                checked += 1
    assert checked > 0


def test_k5_341_convergent_floor_counts_and_indices() -> None:
    summary = k5_convergent_floor_summary()
    assert summary["source"] == "compute/artifacts/thue_convergents_k5.json"
    assert summary["generated_by"] == "compute/theory/gen_thue_convergents.py"
    assert summary["index_range"] == [0, 340]
    assert summary["rows"] == 341
    assert summary["below_side_A5_positive"] == 171
    assert summary["positive_floor"] == 125
    assert summary["square_floor"] == 71
    assert summary["square_floor_ge_4"] == 4
    assert summary["square_floor_and_divides_4A1"] == 70
    assert summary["square_floor_ge_4_and_divides_4A1"] == 3
    assert summary["floor_candidate_exact_roots"] == 0
    assert summary["square_floor_ge_4_indices_and_z"] == [
        [38, 4],
        [116, 4],
        [204, 4],
        [334, 64],
    ]
    assert summary["square_floor_ge_4_divisor_indices_and_z"] == [
        [38, 4],
        [116, 4],
        [204, 4],
    ]


def test_all_six_341_row_scale_ladders_reproduce() -> None:
    for k, expected in EXPECTED_SCALE_LADDER.items():
        summary = scale_ladder_summary(k)
        assert summary["rows"] == 341
        assert summary["generated_by"] == "compute/theory/gen_thue_convergents.py"
        assert summary["candidate_scales_g_ge_2"] == expected["candidate_scales_g_ge_2"]
        assert summary["z_adic_passes"] == expected["z_adic_passes"]
        assert summary["exact_roots"] == []


def test_d_one_telescopes_survive_and_are_outside_domain() -> None:
    checks = telescope_checks()
    assert [(item["k"], item["Y"], item["X"]) for item in checks] == [
        (9, 7, 8),
        (15, 12, 13),
    ]
    assert all(item["g"] == 1 and item["z"] == 1 for item in checks)
    assert all(item["equation_holds"] is True for item in checks)
    assert all(item["outside_disjoint_domain"] is True for item in checks)

