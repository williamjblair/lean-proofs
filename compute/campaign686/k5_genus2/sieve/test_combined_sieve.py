from .combined_sieve import run_sieve


def test_k5_genus_two_combined_sieve() -> None:
    result = run_sieve()
    assert result["verdict"] == "PASS"
    assert result["packet_count"] == 14
    assert result["combined_lattice_index"] == (
        42343330413030424784735169272832000000
    )
    assert result["surviving_cosets"] == 516168751624777728
    assert result["surviving_density"] == (
        "5383303927/441613360315210220469081750000"
    )
    assert result["known_affine_combined_class_count"] == 34
    assert result["known_affine_class_merges"] == []
    assert result["known_projective_combined_class_count"] == 36
    assert result["known_projective_class_merges"] == []
