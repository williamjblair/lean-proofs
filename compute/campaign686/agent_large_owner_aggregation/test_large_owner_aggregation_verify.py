from __future__ import annotations

from .large_owner_aggregation_verify import (
    exact_live_owner_certificate,
    exact_mandatory_fixture_certificate,
    verify,
)


def test_complete_exact_certificate() -> None:
    verify()


def test_mandatory_fixture_keeps_every_boundary_premise_visible() -> None:
    cert = exact_mandatory_fixture_certificate()
    assert cert["ratio_window"]
    assert cert["rows_1_through_16"]
    assert not cert["row_17"]
    assert not cert["equation"]
    assert not cert["reflection_congruence"]
    assert cert["outside_live_quadratic_complement"]


def test_live_owner_fixture_refutes_owner_aggregation_only_dichotomy() -> None:
    cert = exact_live_owner_certificate()
    assert cert["ratio_window"] and cert["sharp_ratio"]
    assert cert["live_quadratic_strip"]
    assert cert["reflection_congruence"]
    assert cert["reflection_product_compression"]
    assert cert["reflection_lcm_compression"]
    assert cert["lower_block_gpf"] <= cert["large_prime_bound"]
    assert cert["upper_block_gpf"] <= cert["large_prime_bound"]
    assert cert["signed_defect"] == cert["signed_defect_expected"]
    assert cert["absolute_defect_bound"]
    assert not cert["equation"]
    assert cert["passing_rows"] == []
