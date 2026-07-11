from __future__ import annotations

from compute.campaign686.all_owner_assembly_verify import (
    EXPECTED_IMPORTS,
    EXPECTED_PUBLIC_THEOREMS,
    EXPECTED_SOURCE_SHA256,
    ROWS,
    all_owner_scan,
    assemble_all_owners,
    boundary_report,
    progression_composition_report,
    report,
    source_gate_report,
)


def test_all_owner_product_swap_is_exact_on_deterministic_scan() -> None:
    scan = all_owner_scan(500)
    assert scan["rows_checked"] == len(ROWS)
    assert scan["gap_assignment_cases"] == 15_000
    assert scan["all_decompositions_exact"]
    assert scan["all_empty_buckets_are_one"]
    assert scan["zero_clean_components"] > 0
    assert scan["empty_buckets"] > 0


def test_special_and_endpoint_boundaries_are_exercised() -> None:
    boundaries = boundary_report()
    assert boundaries["base_two_cases"] > 0
    assert boundaries["base_three_cases"] > 0
    assert boundaries["large_prime_cases"] > 0
    assert boundaries["left_endpoint_assignments"] > 0
    assert boundaries["right_endpoint_assignments"] > 0
    assert boundaries["all_primes_one_owner_cases"] > 0
    assert boundaries["d_one_cases"] == len(ROWS)


def test_empty_buckets_and_zero_clean_factors_are_literal_units() -> None:
    assembled = assemble_all_owners(5, 2 * 3, {2: 1, 3: 5})
    assert assembled["loss"] * assembled["bucket_product"] == 2 * 3
    assert assembled["buckets"][2] == 1
    assert assembled["buckets"][4] == 1
    assert all(
        component["clean_factor"] == 1
        for component in assembled["components"]
    )


def test_exact_progression_quotients_and_compositions() -> None:
    composition = progression_composition_report()
    assert composition["families_checked"] == len(ROWS)
    assert composition["owner_congruences_checked"] == sum(ROWS)
    assert composition["all_quotients_exact"]
    assert composition["all_residual_differences_exact"]
    assert composition["all_second_compositions_hold"]
    assert composition["all_third_compositions_hold"]


def test_report_is_explicitly_non_closing() -> None:
    result = report(200)
    assert result["route_verdict"] == (
        "the unchanged bounded loss and every owner bucket assemble exactly; "
        "the local lifts give nonzero finite-family obstructions, but no "
        "archimedean bound closes their nonzero branch"
    )


def test_frozen_lean_source_and_public_surface() -> None:
    gate = source_gate_report()
    assert gate["source_sha256"] == EXPECTED_SOURCE_SHA256
    assert gate["imports"] == EXPECTED_IMPORTS
    assert gate["public_theorems"] == EXPECTED_PUBLIC_THEOREMS
    assert gate["public_theorem_count"] == 30
    assert gate["forbidden"] == {}
