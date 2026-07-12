from compute.campaign686.agent_t2_smooth_rows.two_factor_center_hostile_verify import (
    run_audit,
)


def test_independent_hostile_audit() -> None:
    result = run_audit()
    assert result == {
        "product_window_rows": 14_616,
        "centers": 15_456,
        "oriented_large_factor_pairs": 801,
        "large_supported_factor_pairs": 108,
        "simultaneous_square_lifts": 0,
        "one_component_centers": 2_680,
        "mod_five_checks": 64,
        "mandatory_fixtures": 2,
    }
