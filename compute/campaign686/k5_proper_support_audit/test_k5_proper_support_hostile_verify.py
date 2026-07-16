from .k5_proper_support_hostile_verify import verify


def test_k5_proper_support_hostile_verifier() -> None:
    result = verify()
    assert result["verdict"] == "PASS"
    assert result["counts"]["puncture_endpoints"] == 25
    assert result["counts"]["local_row_modules"] == 1272
    assert result["counts"]["elimination_leaves"] == 477
    assert result["counts"]["elimination_assemblies"] == 53
    assert result["counts"]["bezout_kernels"] == 25
    assert result["forbidden_hits"] == []
    assert result["missing_oleans"] == []
