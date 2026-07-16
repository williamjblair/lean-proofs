from .verify_packets import verify_packets


def test_k5_genus_two_sieve_packets() -> None:
    result = verify_packets()
    assert result["verdict"] == "PASS"
    assert result["packet_count"] == 14
    assert result["known_affine_point_count"] == 34
    assert result["all_known_points_survive"] is True
    assert result["surjective_primes"] == [
        7, 11, 13, 17, 19, 23, 29, 31, 41, 43, 47, 53, 59
    ]
    assert result["nonsurjective_primes"] == [37]
    assert result["packets"]["37"]["ambient_group_order"] == 1520
    assert result["packets"]["37"]["reduction_image_order"] == 760
    assert result["packets"]["37"]["reachable_curve_image_size"] == 27
    assert result["packets"]["37"]["effective_density"] == "27/760"
    assert result["infinity_vectors_certified"] is True
