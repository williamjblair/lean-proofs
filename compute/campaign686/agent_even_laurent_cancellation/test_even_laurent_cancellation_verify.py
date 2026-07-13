from __future__ import annotations

import even_laurent_cancellation_verify as verify


REPORT = verify.audit()


def test_first_complement_windows_are_exact() -> None:
    assert REPORT["rows"]["11"]["first_complement_window"] == {
        "k": 22,
        "d": 27,
        "least_n": 394,
        "greatest_n": 414,
        "least_center": 811,
        "greatest_center": 851,
        "candidate_count": 21,
    }
    assert REPORT["rows"]["13"]["first_complement_window"] == {
        "k": 26,
        "d": 38,
        "least_n": 668,
        "greatest_n": 692,
        "least_center": 1363,
        "greatest_center": 1411,
        "candidate_count": 25,
    }
    assert REPORT["rows"]["15"]["first_complement_window"] == {
        "k": 30,
        "d": 51,
        "least_n": 1049,
        "greatest_n": 1077,
        "least_center": 2129,
        "greatest_center": 2185,
        "candidate_count": 29,
    }
    assert REPORT["rows"]["17"]["first_complement_window"] == {
        "k": 34,
        "d": 65,
        "least_n": 1528,
        "greatest_n": 1560,
        "least_center": 3091,
        "greatest_center": 3155,
        "candidate_count": 33,
    }


def test_canonical_data_and_k34_fixture_are_reproduced() -> None:
    assert REPORT["rows"]["11"]["canonical"]["scale"] == 256
    assert REPORT["rows"]["11"]["canonical"]["odd_fixed_divisor"] == 33
    assert REPORT["rows"]["13"]["canonical"]["scale"] == 1024
    assert REPORT["rows"]["13"]["canonical"]["odd_fixed_divisor"] == 13
    assert REPORT["rows"]["15"]["canonical"]["scale"] == 2048
    assert REPORT["rows"]["15"]["canonical"]["odd_fixed_divisor"] == 30_375
    assert REPORT["rows"]["17"]["canonical"] == {
        "scale": 32_768,
        "deficit_degree": 16,
        "deficit_leading_coefficient": 188_162_318_421_570_695_167_361_039_564_800,
        "odd_fixed_divisor": 255,
    }


def test_first_negative_and_pade_deficits_do_not_gain_degree() -> None:
    for row in REPORT["rows"].values():
        r = row["r"]
        assert row["first_negative"]["deficit_degree"] == r - 1
        assert row["pade_even_orders"]["1"]["deficit_degree"] == r - 1
        assert row["pade_even_orders"]["2"]["deficit_degree"] == r - 1
        assert row["pade_even_orders"]["3"]["deficit_degree"] == r - 1
        assert row["pade_even_orders"]["4"]["deficit_degree"] == r - 1


def test_strongest_first_negative_lattice_test_fails_every_boundary_pair() -> None:
    expected_counts = {"11": 21, "13": 25, "15": 29, "17": 33}
    for r, row in REPORT["rows"].items():
        lattice = row["first_negative"]["boundary_lattice_audit"]
        assert lattice["tested_pairs"] == expected_counts[r]
        assert lattice["fixed_divisor_successes"] == 0
        assert lattice["variable_congruence_successes"] == 0


def test_one_parameter_even_pade_trap_fails_every_boundary_pair() -> None:
    expected_counts = {"11": 21, "13": 25, "15": 29, "17": 33}
    for r, row in REPORT["rows"].items():
        lattice = row["pade_even_orders"]["1"]["boundary_lattice_audit"]
        assert lattice["tested_pairs"] == expected_counts[r]
        assert lattice["fixed_divisor_successes"] == 0


def test_k22_root_fixtures_remain_exact_but_outside_positive_center_scope() -> None:
    assert REPORT["k22_root_fixtures"] == [
        {"t": 28_643_526_033, "w": -3, "v": -1},
        {"t": 19_687_413_989, "w": -7, "v": -1},
        {"t": 3_809_308_513, "w": 13, "v": 15},
    ]


def test_canonical_payload_hash() -> None:
    assert verify.payload_sha256(REPORT) == (
        "6de2a507b30ea4e71398e6f9a5d8c10ac6b437d68318134cb14991d22637f41b"
    )
