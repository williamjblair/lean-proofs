from compute.campaign686.agent_t2_three_owner.three_owner_floor_lattice_verify import (
    canonical_mixed_scan,
    deep_window_falsifier,
    restricted_k220_window_audit,
    synthetic_fixture_audit,
)


def test_deep_window_falsifier() -> None:
    assert deep_window_falsifier()["window"]


def test_restricted_k220_window() -> None:
    assert restricted_k220_window_audit() == 180


def test_synthetic_fixtures() -> None:
    synthetic_fixture_audit()


def test_canonical_mixed_scan() -> None:
    assert canonical_mixed_scan() == 185
