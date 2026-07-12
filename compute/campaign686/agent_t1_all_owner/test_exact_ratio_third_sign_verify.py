from compute.campaign686.agent_t1_all_owner.exact_ratio_third_sign_verify import (
    coefficient_dominance_audit,
    crt_boundary_audit,
    fixed_sign_lattice_audit,
    ratio_bridge_audit,
    telescope_boundary_audit,
)


def test_ratio_bridge_is_exact() -> None:
    report = ratio_bridge_audit()
    assert report["verdict"] == "PASS"
    assert [row["k"] for row in report["rows"]] == [5, 7, 9, 11, 13, 15]
    assert all(row["floor_margin"] >= 0 for row in report["rows"])


def test_all_ordered_distinct_triples_are_dominated() -> None:
    report = coefficient_dominance_audit()
    assert report["verdict"] == "PASS"
    assert report["ordered_distinct_triples"] == 6_210
    assert report["minimum_main_margin"] > 0
    assert report["minimum_cutoff_margin"] > 0


def test_exact_sign_cells_remain_mixed() -> None:
    report = fixed_sign_lattice_audit()
    assert report["verdict"] == "PASS"
    assert report["unordered_triples"] == 1_035
    assert report["mixed_cells"] == 1_035
    assert report["one_sided_cells"] == 0


def test_telescopes_are_exact_but_outside_cutoff() -> None:
    assert telescope_boundary_audit() == [
        {"k": 9, "n": 2, "d": 1, "equation": True, "target_cutoff": False},
        {"k": 15, "n": 4, "d": 1, "equation": True, "target_cutoff": False},
    ]


def test_crt_falsifiers_do_not_meet_the_new_scope() -> None:
    report = crt_boundary_audit()
    assert report["three_owner_121_digit"]["gap_digits"] == 121
    assert not report["three_owner_121_digit"]["block_equation"]
    assert report["four_owner_130_digit"]["gap_digits"] == 130
    assert not report["four_owner_130_digit"]["block_equation"]
