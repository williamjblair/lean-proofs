from .invariant_scout import parse_magma_output


def test_parse_magma_output() -> None:
    output = """
SCOUT_PRIME 61
SCOUT_INVARIANTS [ 4495 ]
SCOUT_BASIS [
    [ 208 ],
    [ 2157 ],
    [ 751 ],
    [ 1715 ],
    [ 781 ]
]
SCOUT_BAD_PRIME 67
"""
    assert parse_magma_output(output) == {
        61: {
            "bad_prime": False,
            "invariants": [4495],
            "basis": [[208], [2157], [751], [1715], [781]],
        },
        67: {"bad_prime": True},
    }
