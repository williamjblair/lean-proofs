from .magma_rank_verify import verify_offline


def test_k5_genus_two_rank_certificate() -> None:
    result = verify_offline()
    assert result["verdict"] == "PASS"
    assert result["point_count"] == 36
    assert result["rank"] == 5
    assert result["two_selmer_dimension"] == 5
    assert result["full_mordell_weil_group_proved"] is True
    assert result["unimodular_basis_determinant"] == -1
    assert result["target_pullbacks"] == []
