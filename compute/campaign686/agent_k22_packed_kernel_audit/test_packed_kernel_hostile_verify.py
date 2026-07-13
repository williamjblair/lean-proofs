from __future__ import annotations

from .packed_kernel_hostile_verify import (
    BRANCHES,
    EXPECTED_KILLS,
    quarantine_audit,
)


def test_exact_arithmetic_and_quarantine_state() -> None:
    result = quarantine_audit()
    assert result["active_primes"] == {"count": 132, "first": 83, "last": 953}
    assert result["semantics"]["generated_files"] == []
    assert result["semantics"]["quarantined"] is True


def test_all_24_shifted_intersections_are_exactly_empty() -> None:
    result = quarantine_audit()
    assert result["packed"]["shard_count"] == 24
    assert len(result["packed"]["last_survivor_records"]) == len(EXPECTED_KILLS)
    assert result["packed"]["branch_lengths"] == {
        "17": 82_503_186,
        "21": 82_503_186,
        "25": 82_503_185,
        "29": 82_503_185,
    }
    assert result["semantics"]["odd_mod46_classes"] == list(BRANCHES)


def test_dependency_graph_is_explicitly_reported() -> None:
    result = quarantine_audit()
    assert result["verdict"] == "FAIL_KERNEL_QUARANTINED"
