from __future__ import annotations

from compute.campaign686.two_owner_grouping_verify import (
    EXPECTED_LOSSES,
    EXPECTED_PUBLIC_THEOREMS,
    EXPECTED_SOURCE_SHA256,
    ROWS,
    aggregate_loss,
    assemble,
    exhaustive_grouping_certificate,
    parse_lean_loss_table,
    range_rejection_certificate,
    report,
    source_gate_certificate,
)


def test_exact_loss_table_is_independently_recomputed() -> None:
    assert {k: aggregate_loss(k) for k in ROWS} == EXPECTED_LOSSES
    assert parse_lean_loss_table() == EXPECTED_LOSSES


def test_grouping_exhausts_binary_and_same_owner_boundaries() -> None:
    certificate = exhaustive_grouping_certificate()
    assert certificate["assignment_cases"] == 64_866
    assert certificate["same_owner_cases"] == 12_000
    assert min(
        certificate["both_buckets_unit"],
        certificate["left_bucket_unit"],
        certificate["right_bucket_unit"],
        certificate["nontrivial_left_bucket"],
        certificate["nontrivial_right_bucket"],
    ) > 0


def test_zero_clean_and_large_prime_boundaries_are_exercised() -> None:
    certificate = exhaustive_grouping_certificate(500)
    assert min(
        certificate["zero_clean_components"],
        certificate["outside_owner_zero_clean_components"],
        certificate["primes_at_least_k_components"],
    ) > 0
    ranges = range_rejection_certificate()
    assert ranges == {
        "outside_nontrivial_rejected": 6,
        "outside_zero_clean_accepted": 6,
    }


def test_first_owner_precedence_when_indices_coincide() -> None:
    # At k=5, 2^5 retains 2^3 after loss 2.  With i=j, all retained mass
    # must go left and the right product must be one.
    g, left, right, _ = assemble(5, 2**5, {2: 3}, 3, 3)
    assert (g, left, right) == (2**2, 2**3, 1)


def test_nontrivial_owner_outside_cover_is_rejected() -> None:
    try:
        assemble(5, 7, {7: 99}, 2, 4)
    except ValueError:
        pass
    else:
        raise AssertionError("outside nontrivial owner was accepted")


def test_source_gate_has_one_import_and_exact_theorem_surface() -> None:
    certificate = source_gate_certificate()
    assert certificate["source_sha256"] == EXPECTED_SOURCE_SHA256
    assert certificate["forbidden"] == {}
    assert certificate["imports"] == (
        "ErdosProblems.Erdos686TwoOwnerAggregate",
    )
    assert certificate["public_theorems"] == EXPECTED_PUBLIC_THEOREMS
    assert certificate["public_theorem_count"] == 13


def test_full_report() -> None:
    result = report(500)
    assert result["loss_table"]["lean"] == EXPECTED_LOSSES
    assert result["grouping"]["assignment_cases"] > 10_000
