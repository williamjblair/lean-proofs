from fractions import Fraction
from pathlib import Path

import pytest

from compute730.campaign_uniform.repair.far.stronger_affine_counterexample import (
    explicit_p5_certificate,
)
from compute730.full_density.verify import (
    EXPECTED_IDENTITIES,
    EXPECTED_LOG_UPPERS,
    SOURCE_BYTES,
    SOURCE_LINES,
    SOURCE_SHA256,
    T,
    crt_class_certificate,
    exceptional_prime_certificate,
    family_certificate,
    rational_certificate,
    restricted_digit_count,
    source_digest,
    top_residue_tables,
    verify_all,
)


SOURCE_PATH = Path(
    "/Users/williamblair/.codex/attachments/"
    "a6bdaeec-cb7e-456b-a0e6-d99af242235d/pasted-text.txt"
)


def test_frozen_source_artifact_when_available() -> None:
    """The attachment is local-session evidence, so absence is CI-safe."""

    if not SOURCE_PATH.exists():
        pytest.skip("original Codex attachment is not available in this checkout")
    assert source_digest(SOURCE_PATH) == (SOURCE_SHA256, SOURCE_LINES, SOURCE_BYTES)


def test_family_arithmetic_and_all_six_identities() -> None:
    result = family_certificate()
    assert T == 5289
    assert result["slopes"] == {
        "P": 222_138,
        "Q": 380_808,
        "R": 148_092,
        "S": 380_808,
    }
    assert result["constants"] == {"P": 11, "Q": 13, "R": 5, "S": 19}
    assert result["two_pq_minus_one"] == result["three_rs"]
    assert result["two_pq_minus_one"] == (
        6048 * T * T,
        2676 * T,
        285,
    )
    assert result["identities"] == EXPECTED_IDENTITIES
    assert result["common_quadratic_coefficient"] == {
        name: Fraction(84_591_927_504) for name in ("P", "Q", "R", "S")
    }
    assert result["C0"] == 380_827


def test_exceptional_prime_factorizations_and_fixed_residues() -> None:
    result = exceptional_prime_certificate()
    assert result["b_values"] == {
        "P": -1_301_094,
        "Q": 1_301_094,
        "R": 1_364_562,
        "S": -1_364_562,
    }
    assert result["b_factorization"] == {
        "P": ((2, 1), (3, 2), (41, 2), (43, 1)),
        "Q": ((2, 1), (3, 2), (41, 2), (43, 1)),
        "R": ((2, 1), (3, 2), (41, 1), (43, 2)),
        "S": ((2, 1), (3, 2), (41, 1), (43, 2)),
    }
    assert result["exceptional_primes"] == (2, 3, 41, 43)
    assert result["fixed_branch_residues"] == {
        2: {"P": 1, "Q": 1, "R": 1, "S": 1},
        3: {"P": 2, "Q": 1, "R": 2, "S": 1},
        41: {"P": 11, "Q": 13, "R": 5, "S": 19},
        43: {"P": 11, "Q": 13, "R": 5, "S": 19},
    }
    assert result["three_quotient_residue"] == 2


def test_top_range_residue_tables_are_exhaustive() -> None:
    assert top_residue_tables() == {
        "P": (
            (1, 1, 5, False),
            (2, 4, 6, False),
            (3, 2, 3, True),
            (4, 2, 3, True),
            (5, 4, 6, False),
            (6, 1, 5, False),
        ),
        "Q": (
            (1, 1, 7, False),
            (5, 1, 7, False),
            (7, 1, 7, False),
            (11, 1, 7, False),
        ),
        "R": (
            (1, 1, 12, False),
            (3, 9, 10, False),
            (5, 11, 6, True),
            (9, 11, 6, True),
            (11, 9, 10, False),
            (13, 1, 12, False),
        ),
        "S": (
            (1, 1, 7, False),
            (5, 1, 7, False),
            (7, 1, 7, False),
            (11, 1, 7, False),
        ),
    }


def test_crt_allowed_class_counts_by_full_enumeration() -> None:
    assert crt_class_certificate() == {
        "P": {"modulus": 222_138, "phi": 60_480, "allowed": 20_160},
        "R": {"modulus": 148_092, "phi": 40_320, "allowed": 13_440},
    }


@pytest.mark.parametrize("p", [3, 5, 7, 11])
@pytest.mark.parametrize("digits", [1, 2, 3, 4])
@pytest.mark.parametrize("endpoint", ["low", "high"])
def test_exact_restricted_digit_count(p: int, digits: int, endpoint: str) -> None:
    h = (p + 1) // 2
    excluded = 0 if endpoint == "low" else h - 1
    assert restricted_digit_count(p, digits, excluded) == (h - 1) * h ** (digits - 1)


def test_six_log_bounds_tail_and_final_margin_are_exact() -> None:
    result = rational_certificate()
    assert result["finite_log_uppers"] == EXPECTED_LOG_UPPERS
    assert result["tail_upper"] == Fraction(1, 98_304)
    assert result["s_upper"] == Fraction(
        11_117_760_449_158_646_497,
        89_848_527_388_139_520_000,
    )
    assert result["log2_upper"] == Fraction(1123, 1620)
    assert result["total_upper"] == Fraction(
        21_498_408_212_212_214_497,
        22_462_131_847_034_880_000,
    )
    assert result["target"] == Fraction(2393, 2500)
    assert result["difference"] == Fraction(
        2_344_391_769_572_639,
        22_462_131_847_034_880_000,
    )
    assert result["difference"] > 0


def test_legacy_p5_affine_witness_is_preserved_but_outside_new_lemma() -> None:
    """Regression for the exact hostile witness named in the intake protocol."""

    legacy = explicit_p5_certificate()
    assert (legacy["p"], legacy["r"], legacy["s"], legacy["a"]) == (
        5,
        432,
        176,
        688,
    )
    assert legacy["counterexample"] is True
    assert legacy["cleared_margin"] > 0

    # The submitted fixed-depth Fourier lemma is explicitly an a=1 lemma.
    # The witness has a>=2 and is therefore assigned to the separately stated
    # higher-power dominated-convergence node, not silently claimed away.
    assert legacy["a"] >= 2
    assert legacy["a"] != 1


def test_complete_exact_verifier() -> None:
    result = verify_all()
    assert result["rational"]["difference"] > 0
