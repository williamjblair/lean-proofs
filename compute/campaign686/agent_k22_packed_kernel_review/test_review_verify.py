from review_verify import (
    EXPONENT,
    P23_MASK,
    WIDTH,
    exact_intersection_audit,
    independently_enumerated_p23_residues,
    odd_p23_classes_mod46,
)


def test_independent_p23_mask_and_parity_classes() -> None:
    residues = independently_enumerated_p23_residues()
    assert residues == frozenset({2, 6, 17, 21})
    assert sum(1 << residue for residue in residues) == P23_MASK
    assert odd_p23_classes_mod46() == (17, 21, 25, 29)


def test_actual_shard_width_and_pattern_boundaries() -> None:
    result = exact_intersection_audit()
    assert result["item_count"] == 132
    assert result["unique_period_count"] == 132
    assert result["minimum_period"] == 83
    assert result["minimum_extent"] == 83 * 2**EXPONENT == 21_757_952
    assert result["minimum_extent"] > WIDTH
    assert result["patterns_fit_one_period"] is True
    assert result["inventory_matches_independent_reconstruction"] is True


def test_actual_shard_exact_intersection_is_zero() -> None:
    result = exact_intersection_audit()
    assert result["intersection_is_zero"] is True
    assert result["first_zero_prime"] == 857
