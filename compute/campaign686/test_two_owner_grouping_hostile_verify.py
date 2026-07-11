from __future__ import annotations

from compute.campaign686.two_owner_grouping_hostile_verify import (
    EXPECTED_AGGREGATE_SHA256,
    EXPECTED_CANDIDATE_SHA256,
    EXPECTED_CONCENTRATION_SHA256,
    EXPECTED_PUBLIC_THEOREMS,
    EXPECTED_ROW_LOSSES,
    ROWS,
    aggregate_loss,
    chooser_composition_certificate,
    exact_row_boundary_certificate,
    exhaustive_small_certificate,
    no_two_cover_equivalence_certificate,
    parse_target_loss_table,
    random_large_certificate,
    report,
    source_surface_certificate,
)


def full_report():
    return report(1_500, 5_000)


def test_frozen_source_and_dependency_hashes() -> None:
    source = source_surface_certificate()
    assert source["candidate_sha256"] == EXPECTED_CANDIDATE_SHA256
    assert source["aggregate_sha256"] == EXPECTED_AGGREGATE_SHA256
    assert source["concentration_sha256"] == EXPECTED_CONCENTRATION_SHA256


def test_public_surface_forbidden_and_private_gates() -> None:
    source = source_surface_certificate()
    assert source["imports"] == ("ErdosProblems.Erdos686TwoOwnerAggregate",)
    assert source["public_theorems"] == EXPECTED_PUBLIC_THEOREMS
    assert source["public_theorem_count"] == 13
    assert source["forbidden"] == {}
    assert source["audit_forbidden"] == {}
    assert source["private_header_leaks"] == {}
    assert source["imports_producer_verifier"] is False


def test_final_quantifiers_bind_one_certified_assignment() -> None:
    source = source_surface_certificate()
    assert all(source["final_quantifier_markers"].values())
    coverage = no_two_cover_equivalence_certificate()
    assert coverage["finite_assignments_checked"] == 6_144
    assert coverage["coverable_assignments"] > 0
    assert coverage["not_two_cover_assignments"] > 0


def test_exact_six_row_loss_table() -> None:
    assert {k: aggregate_loss(k) for k in ROWS} == EXPECTED_ROW_LOSSES
    assert parse_target_loss_table() == EXPECTED_ROW_LOSSES
    boundaries = exact_row_boundary_certificate()
    assert boundaries["exact_loss_rows"] == 6
    assert boundaries["large_prime_zero_loss_rows"] == 6
    assert boundaries["p2_rows"] == boundaries["p3_rows"] == 6


def test_exhaustive_small_grouping_boundaries() -> None:
    result = exhaustive_small_certificate(1_500)
    assert result["gaps"] == 9_000
    assert result["covered_maps"] > 25_000
    assert result["rejected_maps"] > 1_000
    assert result["same_owner_covered"] > 5_000
    assert result["same_owner_rejected"] > 1_000
    assert min(
        result["empty_support"],
        result["one_prime_support"],
        result["zero_clean_components"],
        result["zero_clean_outside_cover"],
        result["p2_components"],
        result["p3_components"],
        result["prime_at_least_k_components"],
        result["both_buckets_unit"],
        result["left_bucket_unit"],
        result["right_bucket_unit"],
    ) > 0


def test_large_random_exact_grouping_boundaries() -> None:
    result = random_large_certificate(5_000)
    assert result["cases"] == 5_000
    assert result["maximum_gap_digits"] > 100
    assert min(
        result["cases_with_p2"],
        result["cases_with_p3"],
        result["cases_with_prime_at_least_k"],
        result["cases_with_zero_clean_component"],
        result["same_owner_cases"],
    ) > 0


def test_total_chooser_composition_boundaries() -> None:
    result = chooser_composition_certificate()
    assert result["support_families"] == 30
    assert result["empty_supports"] == 6
    assert result["selected_support_primes"] > 0
    assert result["zero_clean_selected_components"] > 0


def test_full_hostile_report() -> None:
    result = full_report()
    assert result["row_losses"]["recomputed"] == EXPECTED_ROW_LOSSES
    assert result["source"]["public_theorem_count"] == 13
