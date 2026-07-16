from .infinity_vector_verify import verify_offline


def test_k5_genus_two_infinity_vectors() -> None:
    result = verify_offline()
    assert result["verdict"] == "PASS"
    assert result["known_projective_vector_count"] == 36
    assert result["all_infinity_vectors_survive_all_packets"] is True
