from .pure_three_floor_verify import (
    affine_only_fixture_audit,
    campaign_summary,
    third_only_fixture_audit,
    translated_family_audit,
)


def test_campaign_summary() -> None:
    summary = campaign_summary()
    assert summary["exhaustive_prime_triples"] == 33_511
    assert summary["k220_square_rows"] == 71
    assert summary["k223_square_rows"] == 2
    assert summary["square_rows_with_endpoint_window"] == 0
    assert summary["square_rows_with_any_third_component"] == 0


def test_translated_families() -> None:
    summary = translated_family_audit()
    assert summary["total_square_rows"] == 981
    assert all(row["zero_third_components"] == 0 for row in summary["rows"])


def test_affine_only_boundary_fixtures() -> None:
    even, odd = affine_only_fixture_audit()
    assert even["k"] == 220 and even["equation"] is False
    assert odd["k"] == 223 and odd["equation"] is False
    assert all(value != 0 for value in even["square_residues"])
    assert all(value != 0 for value in odd["square_residues"])


def test_third_only_boundary_fixtures() -> None:
    even, odd = third_only_fixture_audit()
    assert even["endpoint_window"] is True and even["equation"] is False
    assert odd["endpoint_window"] is True and odd["equation"] is False
    assert even["third_residues"] == (0, 0, 0)
    assert odd["third_residues"] == (0, 0, 0)
    assert all(value != 0 for value in even["square_residues"])
    assert all(value != 0 for value in odd["square_residues"])
