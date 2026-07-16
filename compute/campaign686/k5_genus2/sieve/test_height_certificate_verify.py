from .height_certificate_verify import verify_offline


def test_k5_genus_two_height_certificate() -> None:
    result = verify_offline()
    assert result["verdict"] == "PASS"
    assert result["certified_true_matrix_lower_eigenvalue"] == "43/200"
    assert result["height_constant_is_one_sided"] is True
    assert result["global_curve_height_upper_bound_complete"] is False
