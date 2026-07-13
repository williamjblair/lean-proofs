from __future__ import annotations

import importlib.util
import sys
from pathlib import Path


SOURCE = Path(__file__).with_name("k22_crt_tree_probe_verify.py")
SPEC = importlib.util.spec_from_file_location("k22_crt_tree_probe_verify", SOURCE)
assert SPEC is not None and SPEC.loader is not None
PROBE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = PROBE
SPEC.loader.exec_module(PROBE)


def test_base_interval_is_exactly_the_banked_compression() -> None:
    base = PROBE.base_certificate()
    assert base["candidate_bound"] == 3_795_146_531
    assert base["base_residues"] == [17, 21, 25, 29]
    assert base["branch_lengths"] == {
        "17": 82_503_186,
        "21": 82_503_186,
        "25": 82_503_185,
        "29": 82_503_185,
    }
    assert base["candidate_integer_count"] == 330_012_742


def test_active_mask_inventory_is_frozen() -> None:
    masks = PROBE.active_masks()
    assert len(masks) == 132
    assert PROBE.mask_inventory_sha256(masks) == (
        "48c2171142fd02c807946a070c6ddf1d56bf5c3693d48761a8b41688f130ed12"
    )
    smallest = sorted((len(allowed), prime) for prime, allowed in masks)[:3]
    assert smallest == [(81, 83), (95, 97), (99, 101)]


def test_cyclic_window_routine_matches_independent_brute_force() -> None:
    prime = 13
    allowed = frozenset({0, 1, 4, 6, 10})
    for multiplier in (1, 2, 5, 12):
        transformed = {(multiplier * residue) % prime for residue in allowed}
        for length in range(1, prime):
            expected = min(
                sum((start + offset) % prime in transformed for offset in range(length))
                for start in range(prime)
            )
            assert (
                PROBE.minimum_cyclic_window_hits(
                    allowed, prime, multiplier, length
                )
                == expected
            )


def test_all_residue_case_counts_classes_not_integer_multiplicity() -> None:
    allowed101 = dict(PROBE.active_masks())[101]
    children, mode = PROBE.third_level_child_lower_bound(
        pair_modulus=370_346,
        interval_length=10_247,
        prime=101,
        allowed=allowed101,
    )
    assert (children, mode) == (99, "all_residues")


def test_adaptive_scan_exhausts_every_pair_and_has_no_early_kill() -> None:
    scan = PROBE.adaptive_three_level_certificate()
    assert scan["unordered_pair_count"] == 8_646
    assert scan["potential_pair_third_tests"] == 1_123_980
    assert scan["exact_cyclic_window_evaluations"] == 170_728
    assert scan["zero_third_child_pairs"] == 0
    assert scan["global_minimum"] == {
        "four_root_live_children": 3_047_220,
        "one_root_live_children": 761_805,
        "p1": 83,
        "p2": 97,
        "p3": 101,
        "allowed_sizes": [81, 95, 99],
        "pair_modulus": 370_346,
        "minimum_node_interval_length": 10_247,
        "third_child_mode": "all_residues",
    }


def test_fixed_optimal_prefix_crosses_target_at_level_three() -> None:
    payload = PROBE.audit()
    prefix = payload["optimal_fixed_three_prime_prefix"]
    assert prefix["primes"] == [83, 97, 101]
    assert prefix["moduli_by_level"] == [46, 3_818, 370_346, 37_404_946]
    assert prefix["live_nodes_by_level"] == [4, 324, 30_780, 3_047_220]
    assert prefix["live_nodes_by_level"][2] < payload["simple_node_target"]
    assert prefix["live_nodes_by_level"][3] > payload["simple_node_target"]


def test_canonical_payload_hash() -> None:
    assert PROBE.payload_sha256(PROBE.audit()) == (
        "7c6e19d2b5e44ae6f5f0fdf600e0e1c4a663189d17820d1bebdf486571088673"
    )
