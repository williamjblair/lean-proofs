from even_k28_verify import (
    CANDIDATE_COUNT,
    COVER,
    COVER_COUNTS,
    FIXED,
    SPLIT_GAP,
    TRAP,
    GREEDY_COVER,
    GREEDY_COVER_COUNTS,
    audit,
)


REPORT = audit()


def test_fixed_divisor_and_polynomial_identity() -> None:
    assert REPORT["degrees"] == {"S": 28, "T": 14, "D": 12}
    assert REPORT["fixed_divisor"] == {
        "fixed_divisor": FIXED,
        "factorization": {"2": 10, "7": 2},
        "values_used": 15,
    }


def test_archimedean_trap_and_strict_endpoints() -> None:
    cert = REPORT["archimedean"]
    assert cert["split_gap"] == SPLIT_GAP
    assert cert["trap"] == TRAP
    assert cert["candidate_count"] == CANDIDATE_COUNT
    assert cert["least_trap_degree"] == (0, 0)
    assert cert["trap_terms"] == 120
    assert cert["negative_terms"] == 13
    assert REPORT["boundaries"]["strict_trap_endpoints"] == [-TRAP, 0]


def test_finite_strip_and_boundary_d28() -> None:
    cert = REPORT["finite_strip"]
    assert cert["gap_lo"] == 28
    assert cert["gap_hi"] == 383
    assert cert["checked"] == 64_258
    assert cert["d28_candidates"] == 47
    assert cert["d383_candidates"] == 314
    assert REPORT["boundaries"]["d28_in_finite_strip"]
    assert REPORT["boundaries"]["d384_in_large_gap"]


def test_exact_cover_and_local_survivor_semantics() -> None:
    cert = REPORT["cover"]
    assert cert["primes"] == COVER
    assert cert["survivor_counts"] == COVER_COUNTS
    assert cert["survivor_counts"][-1] == 0
    assert cert["p29_classes"] == [5, 14, 15, 24]
    greedy = REPORT["exploratory_greedy_cover"]
    assert greedy["primes"] == GREEDY_COVER
    assert greedy["survivor_counts"] == GREEDY_COVER_COUNTS


def test_payload_is_stable() -> None:
    assert REPORT["payload_sha256"] == "ad9612473125746a0a665e659f3b3b61c158aee49a1d3f61ac012a3eee4fb5cf"
