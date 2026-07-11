from __future__ import annotations

import pytest
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from all_owner_assembly_hostile_verify import (
    FINDINGS_SHA256,
    ROWS,
    TARGET,
    assemble_owner_grid,
    boundary_audit,
    coefficient_and_target_audit,
    composition_audit,
    independent_assembly_scan,
    scope_counterexamples,
    source_surface_report,
    verify_frozen_hashes,
)


def test_all_five_producer_artifacts_are_frozen() -> None:
    hashes = verify_frozen_hashes()
    assert len(hashes) == 5
    assert hashes["compute/campaign686/all_owner_assembly_findings.md"] == (
        FINDINGS_SHA256
    )
    assert FINDINGS_SHA256 == (
        "1610f635ecdf37f8c192fbd7f4866d33d6089602f1599fced1f178be3497b3d9"
    )


def test_public_surface_and_certificate_fields_are_independently_inventoried() -> None:
    audit = source_surface_report()
    assert audit["public_theorem_count"] == 30
    assert audit["all_expected_theorems_present"] is True
    assert audit["definitions"] == [
        "allOwnerGrid",
        "allOwnerBucket",
        "allOwnerCofactor",
        "allOwnerIntGrid",
        "allOwnerBucketInt",
        "allOwnerCofactorInt",
        "allOwnerAssemblyCertificate_of_assignment",
    ]
    assert audit["certificate_fields"] == [
        "owner",
        "assignment",
        "exactGap",
        "positiveLoss",
        "boundedLoss",
        "positiveCofactors",
        "exactResiduals",
        "residualDifferences",
        "secondObstructions",
        "thirdObstructions",
        "nonzeroSecondObstructions",
    ]
    assert audit["forbidden"] == {}


def test_independent_full_grid_scan_reproduces_exact_counts() -> None:
    audit = independent_assembly_scan(500)
    assert audit == {
        "rows_checked": 6,
        "gap_assignment_cases": 15_000,
        "prime_placements_checked": 30_240,
        "zero_clean_components": 15_430,
        "empty_buckets": 136_028,
        "all_decompositions_exact": True,
        "all_prime_placements_unique": True,
        "all_empty_buckets_are_one": True,
        "all_losses_positive": True,
    }


def test_named_arithmetic_boundaries_are_exact() -> None:
    audit = boundary_audit()
    assert audit["base_two_cases"] == 7_500
    assert audit["base_three_cases"] == 4_980
    assert audit["large_prime_cases"] == 11_950
    assert audit["left_endpoint_assignments"] == 9_829
    assert audit["right_endpoint_assignments"] == 5_728
    assert audit["all_primes_one_owner_cases"] == 5_988
    assert audit["d_one_cases"] == len(ROWS)
    assert audit["d_one_telescopes"] == [
        {"k": k, "loss": 1, "buckets": [1] * k, "product": 1}
        for k in ROWS
    ]


def test_empty_and_further_owner_buckets_are_not_absorbed() -> None:
    factors = {
        2: 8,
        3: 10,
        5: 4,
        7: 4,
        11: 3,
        13: 2,
    }
    d = 1
    for prime, exponent in factors.items():
        d *= prime**exponent
    owners = {2: 1, 3: 2, 5: 3, 7: 4, 11: 5, 13: 5}
    assembled = assemble_owner_grid(5, d, owners)
    assert assembled["loss"] * assembled["bucket_product"] == d
    assert assembled["live_owners"] == {1, 2, 3, 4, 5}
    assert assembled["buckets"][5] % 11 == 0
    assert assembled["buckets"][5] % 13 == 0
    assert assembled["retained_prime_occurrences"] == {
        2: [1],
        3: [2],
        5: [3],
        7: [4],
        11: [5],
        13: [5],
    }

    sparse = assemble_owner_grid(5, 2 * 3, {2: 1, 3: 5})
    assert sparse["buckets"] == {1: 1, 2: 1, 3: 1, 4: 1, 5: 1}
    assert sparse["loss"] == 6

    fifteen_primes = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47)
    d15 = 1
    for prime in fifteen_primes:
        d15 *= prime**20
    full15 = assemble_owner_grid(
        15, d15, {prime: index for index, prime in enumerate(fifteen_primes, 1)}
    )
    assert full15["live_owners"] == set(range(1, 16))
    assert full15["loss"] * full15["bucket_product"] == d15


def test_full_grid_progressions_and_compositions_include_units_centers_and_small_primes() -> None:
    audit = composition_audit()
    assert audit["target_families_checked"] == len(ROWS)
    assert audit["target_owner_congruences_checked"] == sum(ROWS)
    assert audit["adversarial_families_checked"] == 5
    assert audit["adversarial_owner_congruences_checked"] == 29
    assert audit["all_quotients_exact"] is True
    assert audit["all_residual_differences_exact"] is True
    assert audit["all_second_compositions_hold"] is True
    assert audit["all_third_compositions_hold"] is True
    assert audit["features"] == [
        "unit empty buckets",
        "row centers",
        "k=5",
        "k=15",
        "small components 2 and 3",
        "permuted components",
        "signed loss",
        "zero loss",
    ]


def test_target_coefficient_and_zero_exclusion_bounds_are_reproduced() -> None:
    audit = coefficient_and_target_audit()
    assert audit["owner_rows_checked"] == 60
    assert audit["all_constants_nonzero"] is True
    assert audit["maximum_abs_constant"] == 87_178_291_200
    assert audit["maximum_abs_linear"] == 283_465_647_360
    assert audit["all_linear_nat_abs_lt_10_pow_12"] is True
    assert audit["zero_linear_centers"] == [
        [5, 3],
        [7, 4],
        [9, 5],
        [11, 6],
        [13, 7],
        [15, 8],
    ]
    assert audit["zero_coefficient_bound"] == (
        558_515_440_794_946_289_062_500_000_000_000_001
    )
    assert audit["target_four_owner_lower_slope"] == 625 * TARGET**2
    assert audit["bound_below_target_four_owner_lower_slope"] is True
    assert audit["minimum_grid_cardinality"] == 5
    assert audit["maximum_grid_cardinality"] == 15


def test_scope_counterexamples_prevent_false_closure_or_dropped_owner_claims() -> None:
    audit = scope_counterexamples()
    assert audit["divisibility_nonzero_does_not_bound_component"] is True
    assert audit["arbitrary_component_digits"] >= 121
    assert audit["dropping_owner_changes_exact_product"] is True
    assert audit["certificate_contains_no_below_cutoff_field"] is True
    assert audit["certificate_contains_no_block_contradiction_field"] is True
    assert audit["exact_remaining_lemma"] == (
        "for all target k,n,d, the block equation and an "
        "AllOwnerAssemblyCertificate imply d < 10^120"
    )


def test_invalid_inputs_are_rejected_instead_of_silently_truncated() -> None:
    with pytest.raises(ValueError, match="positive"):
        assemble_owner_grid(5, 0, {})
    with pytest.raises(ValueError, match="exactly"):
        assemble_owner_grid(5, 2 * 3, {2: 1})
    with pytest.raises(ValueError, match="outside"):
        assemble_owner_grid(5, 2, {2: 0})
    with pytest.raises(ValueError, match="target row"):
        assemble_owner_grid(6, 2, {2: 1})
