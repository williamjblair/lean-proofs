from compute.campaign686.third_obstruction_nonzero_verify import (
    MULTI_OWNER_THIRD_BOUND,
    RESIDUAL_FLOOR,
    audit_multi_owner_constant,
    audit_target_rows,
    reproduce_telescopes,
)


def test_target_third_obstruction_coefficients_are_dominated() -> None:
    report = audit_target_rows()
    assert report["verdict"] == "PASS"
    assert report["ordered_distinct_triples"] == 6210
    assert report["residual_floor"] == RESIDUAL_FLOOR
    assert report["minimum_main_margin"] > 0
    assert report["minimum_cutoff_margin"] > 0


def test_telescopes_are_reproduced_but_outside_cutoff() -> None:
    report = reproduce_telescopes()
    assert report == [
        {"k": 9, "n": 2, "d": 1, "equation": True, "in_target": False},
        {"k": 15, "n": 4, "d": 1, "equation": True, "in_target": False},
    ]


def test_complete_grid_third_coefficient_bound() -> None:
    report = audit_multi_owner_constant()
    assert report["verdict"] == "PASS"
    assert report["multi_owner_third_bound"] == MULTI_OWNER_THIRD_BOUND
    assert report["target_product_margin"] > 0
    assert all(sample["strict"] for sample in report["samples"].values())
