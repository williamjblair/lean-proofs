from .two_cover_verify import verify_offline


def test_k5_genus_two_cover_certificate() -> None:
    result = verify_offline()
    assert result["verdict"] == "PASS"
    assert result["cover_count"] == 8
    assert result["pair_resolvent_degree"] == 15
    assert result["pair_resolvent_irreducible"] is True
    assert result["factor_degrees"] == [2, 4]
    assert result["known_point_class_counts"] == [2, 4, 4, 4, 4, 4, 6, 6]
    assert result["elliptic_covers_constructed"] == 8
