from compute.campaign686.agent_fifth_configuration_bridge.fifth_configuration_bridge_verify import (
    report,
)


def test_exact_domain_and_position_signs() -> None:
    result = report()
    assert result["arithmetic"] == "exact Python integers and fractions.Fraction"
    assert [row["nonreflected_triples"] for row in result["rows"]] == [
        8,
        32,
        80,
        160,
        280,
        448,
    ]
    assert [row["cyclic_positions"] for row in result["rows"]] == [
        24,
        96,
        240,
        480,
        840,
        1344,
    ]
    assert result["totals"]["nonreflected_triples"] == 1008
    assert result["totals"]["cyclic_positions"] == 3024
    assert result["totals"]["w_sign_equals_minus_C"] == 3024


def test_normalized_sign_flips_are_frozen() -> None:
    result = report()
    assert [
        row["normalized_sign_flips_from_w"] for row in result["rows"]
    ] == [0, 4, 8, 16, 26, 36]
    assert result["totals"]["normalized_sign_flips_from_w"] == 90


def test_canonical_cyclic_weighted_signs_are_always_mixed() -> None:
    result = report()
    triples = [8, 32, 80, 160, 280, 448]
    assert [row["nonzero_cyclic_weights"] for row in result["rows"]] == [
        3 * count for count in triples
    ]
    assert [row["weighted_w_mixed_triples"] for row in result["rows"]] == triples
    assert [row["weighted_n_mixed_triples"] for row in result["rows"]] == triples
    assert result["totals"]["nonzero_cyclic_weights"] == 3024
    assert result["totals"]["weighted_w_mixed_triples"] == 1008
    assert result["totals"]["weighted_n_mixed_triples"] == 1008
    assert result["totals"]["gamma_positive"] == 502
    assert result["totals"]["gamma_negative"] == 506
