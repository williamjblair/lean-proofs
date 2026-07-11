import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from multi_owner_extension_hostile_verify import (
    TARGET,
    adversarial_composition_report,
    reconstruct_crt_falsifier,
    selection_scope_audit,
    subset_and_coefficient_audit,
    verify_frozen_hashes,
    zero_bound_arithmetic,
)


def test_frozen_multi_owner_hashes() -> None:
    hashes = verify_frozen_hashes()
    assert len(hashes) == 5
    assert all(len(value) == 64 for value in hashes.values())


def test_adversarial_signed_compositions() -> None:
    audit = adversarial_composition_report()
    assert audit["owner_congruences_checked"] == 19
    assert audit["all_hold"] is True
    assert all(case["all_hold"] for case in audit["cases"])
    assert "negative components" in audit["features"]
    assert "zero loss" in audit["features"]
    assert "p=2" in audit["features"]
    assert "p=3" in audit["features"]


def test_all_target_subsets_and_coefficients_reproduced() -> None:
    audit = subset_and_coefficient_audit()
    assert audit["subset_count"] == 42_274
    assert audit["owner_slope_count"] == 309_329
    assert audit["positive_slope_count"] == 154_654
    assert audit["collision_subset_count"] == 327
    assert audit["maximum_positive_multiplicity"] == 2
    assert audit["maximum_positive_slope"] == "1807743205183749120"
    assert Fraction(audit["minimum_target_margin"]) > 1
    assert audit["maximum_abs_constant"] == 87_178_291_200
    assert audit["maximum_abs_linear"] == 283_465_647_360
    assert audit["maximum_delta"] == 87_178_291_200
    assert audit["zero_linear_centers"] == [
        [5, 3],
        [7, 4],
        [9, 5],
        [11, 6],
        [13, 7],
        [15, 8],
    ]
    assert audit["all_constants_nonzero"] is True
    assert audit["all_linear_coefficients_below_10_pow_12"] is True
    assert audit["all_deltas_below_15_pow_14"] is True


def test_zero_bound_boundary_and_reflection_collision() -> None:
    audit = zero_bound_arithmetic()
    assert audit["zero_coefficient_bound"] == (
        558_515_440_794_946_289_062_500_000_000_000_001
    )
    assert audit["target_four_owner_lower_slope"] == 625 * TARGET**2
    assert audit["bound_below_target_four_owner_lower_slope"] is True
    assert audit["reflected_k5_collision"] == {
        "owners": [1, 2, 4, 5],
        "owner_1_slope": "900",
        "owner_5_slope": "900",
    }


def test_crt_falsifier_reconstructed_without_producer_import() -> None:
    audit = reconstruct_crt_falsifier()
    assert audit["gap"] == (
        2_205_474_220_935_356_988_722_497_885_428_160_025_770_701_632_629_547_097_778_915_063_286_735_417_113_828_847_388_008_212_536_791_307_861_015_482_562_878_387_550_877_008_961
    )
    assert audit["gap_digits"] == 130
    assert audit["n_digits"] == 517
    assert audit["n_sha256"] == (
        "19a60511c39f9e68c01aab641e2db28489379b628ffdbcbe0859c4576e3ae07c"
    )
    assert audit["all_local_congruences_hold"] is True
    assert audit["all_composed_congruences_hold"] is True
    assert audit["all_second_obstructions_nonzero"] is True
    assert audit["lower_window_holds"] is True
    assert audit["upper_window_holds"] is False
    assert audit["block_equation_holds"] is False


def test_selection_counterfamily_scope_is_not_overread() -> None:
    audit = selection_scope_audit()
    assert audit["pairwise_coprime"] is True
    assert all(audit["component_square_base_checks"].values())
    assert audit["unbounded_complement"] is True
    assert audit["full_residual_progression_or_window_fixture_supplied"] is False
    assert audit["sound_scope"] == (
        "falsifies bounded complement from product averaging and "
        "component-square bounds only"
    )
