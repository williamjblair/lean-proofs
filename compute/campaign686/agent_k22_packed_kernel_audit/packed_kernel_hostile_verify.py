#!/usr/bin/env python3
"""Independent exact audit of the generated k=22 packed-kernel cover.

This module does not import the producer generator or its arithmetic verifier.
It reconstructs the row polynomials, local tables, m-to-t transform, four
mod-46 branches, all 24 shifted chunk masks, and the generated-file dependency
chain directly.  All computations use Python integers and ``Fraction``.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache, reduce
from hashlib import sha256
from json import dumps
from math import comb, gcd, lcm
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[3]
ERDOS = ROOT / "ErdosProblems"
PREFIX = "Erdos686EvenK22"
BRANCHES = (17, 21, 25, 29)
BOUND = 3_795_146_531
CHUNK = 16_000_000
EXPONENT = 18


Poly = dict[int, int]


@dataclass(frozen=True)
class RowData:
    s_poly: Poly
    t_poly: Poly
    scale: int


def _add(poly: Poly, degree: int, coefficient: int) -> None:
    poly[degree] = poly.get(degree, 0) + coefficient
    if poly[degree] == 0:
        del poly[degree]


def _elementary(values: list[int]) -> list[int]:
    result = [1]
    for value in values:
        result.append(0)
        for index in range(len(result) - 1, 0, -1):
            result[index] += value * result[index - 1]
    return result


@lru_cache(maxsize=1)
def row_data() -> RowData:
    """Reconstruct S and the polynomial part T of sqrt(S) from scratch."""
    r = 11
    elementary = _elementary([(2 * j - 1) ** 2 for j in range(1, r + 1)])
    square_coefficients = [(-1) ** j * elementary[j] for j in range(r + 1)]
    root_coefficients = [Fraction(1)]
    for index in range(1, r // 2 + 1):
        cross = sum(
            root_coefficients[j] * root_coefficients[index - j]
            for j in range(1, index)
        )
        root_coefficients.append((Fraction(square_coefficients[index]) - cross) / 2)
    scale = reduce(lcm, (coefficient.denominator for coefficient in root_coefficients), 1)
    s_poly = {
        2 * r - 2 * index: coefficient
        for index, coefficient in enumerate(square_coefficients)
    }
    t_poly = {
        r - 2 * index: int(scale * coefficient)
        for index, coefficient in enumerate(root_coefficients)
    }
    assert scale == 256
    assert t_poly == {
        11: 256,
        9: -226_688,
        7: 67_609_696,
        5: -8_111_362_160,
        3: 352_497_378_310,
        1: -6_055_670_906_453,
    }
    return RowData(s_poly=s_poly, t_poly=t_poly, scale=scale)


def eval_poly_mod(poly: Poly, value: int, modulus: int) -> int:
    return sum(coefficient * pow(value, degree, modulus) for degree, coefficient in poly.items()) % modulus


def primes_through(limit: int) -> list[int]:
    primes: list[int] = []
    for candidate in range(2, limit + 1):
        if all(candidate % prime for prime in primes if prime * prime <= candidate):
            primes.append(candidate)
    return primes


@lru_cache(maxsize=None)
def local_allowed_m_residues(prime: int) -> frozenset[int]:
    """Directly enumerate T(w)-2T(v) when S(w)=4S(v) modulo prime."""
    assert gcd(prime, 33) == 1
    row = row_data()
    s_values = [eval_poly_mod(row.s_poly, x, prime) for x in range(prime)]
    t_values = [eval_poly_mod(row.t_poly, x, prime) for x in range(prime)]
    buckets: dict[int, list[int]] = {}
    for w, value in enumerate(s_values):
        buckets.setdefault(value, []).append(w)
    allowed: set[int] = set()
    for v in range(prime):
        for w in buckets.get(4 * s_values[v] % prime, ()):
            allowed.add((t_values[w] - 2 * t_values[v]) % prime)
    return frozenset(allowed)


@lru_cache(maxsize=None)
def local_allowed_t_residues(prime: int) -> frozenset[int]:
    inverse = pow(-33 % prime, -1, prime)
    return frozenset(m * inverse % prime for m in local_allowed_m_residues(prime))


@lru_cache(maxsize=1)
def active_primes() -> tuple[int, ...]:
    result = tuple(
        prime
        for prime in primes_through(953)
        if prime not in (2, 3, 11, 23)
        and len(local_allowed_t_residues(prime)) != prime
    )
    assert len(result) == 132
    assert result[0] == 83 and result[-1] == 953
    return result


def bit_mask(residues: frozenset[int]) -> int:
    return sum(1 << residue for residue in residues)


def q_pattern(prime: int, branch: int, lo: int) -> int:
    inverse = pow(46, -1, prime)
    global_q = {
        ((t_residue - branch) * inverse) % prime
        for t_residue in local_allowed_t_residues(prime)
    }
    local_i = {(residue - lo) % prime for residue in global_q}
    return bit_mask(frozenset(local_i))


def periodic_mask(pattern: int, period: int, length: int) -> int:
    """Repeat a low-bit-first residue mask, truncated to exactly length bits."""
    repetitions = (length + period - 1) // period
    result = 0
    result_length = 0
    block = pattern
    block_length = period
    while repetitions:
        if repetitions & 1:
            result |= block << result_length
            result_length += block_length
        repetitions >>= 1
        if repetitions:
            block |= block << block_length
            block_length *= 2
    return result & ((1 << length) - 1)


def branch_length(branch: int) -> int:
    return (BOUND - branch) // 46 + 1


def chunks(branch: int) -> list[tuple[int, int]]:
    length = branch_length(branch)
    return [
        (lo, min(CHUNK, length - lo))
        for lo in range(0, length, CHUNK)
    ]


def first_import(text: str) -> str | None:
    imported = all_imports(text)
    return None if not imported else imported[0]


def all_imports(text: str) -> list[str]:
    return re.findall(r"^import ErdosProblems\.([A-Za-z0-9_]+)$", text, re.MULTILINE)


def expected_table_files(table_primes: list[int]) -> set[Path]:
    result = {ERDOS / f"{PREFIX}TableDefs.lean", ERDOS / f"{PREFIX}Tables.lean"}
    for prime in table_primes:
        result.add(ERDOS / f"{PREFIX}TableP{prime}.lean")
        for shard in range((prime + 127) // 128):
            result.add(ERDOS / f"{PREFIX}TableP{prime}S{shard}.lean")
    return result


def audit_base_defs() -> dict[str, object]:
    path = ERDOS / f"{PREFIX}Defs.lean"
    text = path.read_text()
    compact = re.sub(r"\s+", "", text)
    assert "defevenTable22S{R:Type}[CommRingR](W:R):R:=" in compact
    for odd in range(1, 22, 2):
        assert f"(W^2-{odd * odd})" in compact
    assert "defevenTable22T{R:Type}[CommRingR](W:R):R:=" in compact
    expected_terms = (
        "256*W^11",
        "-226688*W^9",
        "+67609696*W^7",
        "-8111362160*W^5",
        "+352497378310*W^3",
        "-6055670906453*W",
    )
    for term in expected_terms:
        assert term in compact
    row = row_data()
    return {
        "factor_count": 11,
        "t_coefficient_count": len(row.t_poly),
        "source_sha256": sha256(path.read_bytes()).hexdigest(),
    }


def audit_table_defs(table_primes: list[int]) -> dict[str, object]:
    path = ERDOS / f"{PREFIX}TableDefs.lean"
    text = path.read_text()
    matches = re.findall(
        r"def even22A(\d+) \(x : ZMod \d+\) : Bool :=\n\s+\((\d+)\)\.testBit x\.val",
        text,
    )
    parsed = {int(prime): int(mask) for prime, mask in matches}
    assert list(parsed) == table_primes
    for prime in table_primes:
        direct_m = local_allowed_m_residues(prime)
        transformed_m = frozenset(
            (-33 * t) % prime for t in local_allowed_t_residues(prime)
        )
        assert direct_m == transformed_m
        assert parsed[prime] == bit_mask(direct_m)
    return {
        "definition_count": len(parsed),
        "first_prime": table_primes[0],
        "last_prime": table_primes[-1],
        "mask_digest": sha256(
            dumps(parsed, sort_keys=True, separators=(",", ":")).encode()
        ).hexdigest(),
    }


def audit_prime_tables(table_primes: list[int]) -> dict[str, object]:
    expected = expected_table_files(table_primes)
    actual = set(ERDOS.glob(f"{PREFIX}Table*.lean"))
    assert actual == expected
    shard_count = 0
    for prime in table_primes:
        ranges = [(lo, min(lo + 128, prime)) for lo in range(0, prime, 128)]
        for shard, (lo, hi) in enumerate(ranges):
            path = ERDOS / f"{PREFIX}TableP{prime}S{shard}.lean"
            text = path.read_text()
            assert all_imports(text) == [f"{PREFIX}TableDefs"]
            statement = (
                f"theorem even22_allowed_{prime}_shard_{shard} :\n"
                f"    ∀ w : ZMod {prime}, {lo} ≤ w.val → w.val < {hi} → ∀ v : ZMod {prime},\n"
                "      evenTable22S w = 4 * evenTable22S v →\n"
                f"        even22A{prime} (evenTable22T w - 2 * evenTable22T v) = true := by\n"
                "  decide +kernel"
            )
            assert statement in text
            shard_count += 1
        full = (ERDOS / f"{PREFIX}TableP{prime}.lean").read_text()
        assert all_imports(full) == [
            f"{PREFIX}TableP{prime}S{shard}" for shard in range(len(ranges))
        ]
        thresholds = [
            int(value)
            for value in re.findall(r"by_cases h\d+ : w\.val < (\d+)", full)
        ]
        assert thresholds == [hi for _lo, hi in ranges[:-1]]
        assert f"theorem even22_allowed_{prime}" in full
        assert f"even22A{prime} (evenTable22T w - 2 * evenTable22T v)" in full
    tables = (ERDOS / f"{PREFIX}Tables.lean").read_text()
    assert all_imports(tables) == [f"{PREFIX}TableP{prime}" for prime in table_primes]
    return {
        "prime_count": len(table_primes),
        "shard_count": shard_count,
        "generated_table_file_count": len(actual),
    }


EXPECTED_KILLS = (
    (17, 0, 0, 16_000_000, 857, (88_193,)),
    (17, 1, 16_000_000, 16_000_000, 823, (4_272_914,)),
    (17, 2, 32_000_000, 16_000_000, 857, (111_689,)),
    (17, 3, 48_000_000, 16_000_000, 919, (5_730_695,)),
    (17, 4, 64_000_000, 16_000_000, 839, (843_261, 1_259_563)),
    (17, 5, 80_000_000, 2_503_186, 907, (2_297_010,)),
    (21, 0, 0, 16_000_000, 877, (12_687_134,)),
    (21, 1, 16_000_000, 16_000_000, 881, (564_167,)),
    (21, 2, 32_000_000, 16_000_000, 821, (13_923_406,)),
    (21, 3, 48_000_000, 16_000_000, 881, (8_447_313,)),
    (21, 4, 64_000_000, 16_000_000, 797, (12_765_533,)),
    (21, 5, 80_000_000, 2_503_186, 761, (689_289,)),
    (25, 0, 0, 16_000_000, 827, (12_678_617,)),
    (25, 1, 16_000_000, 16_000_000, 953, (7_775_358,)),
    (25, 2, 32_000_000, 16_000_000, 821, (447_869,)),
    (25, 3, 48_000_000, 16_000_000, 839, (15_029_291,)),
    (25, 4, 64_000_000, 16_000_000, 883, (2_959_393,)),
    (25, 5, 80_000_000, 2_503_185, 751, (1_808_792,)),
    (29, 0, 0, 16_000_000, 821, (11_654_428,)),
    (29, 1, 16_000_000, 16_000_000, 853, (13_243_689,)),
    (29, 2, 32_000_000, 16_000_000, 857, (111_711,)),
    (29, 3, 48_000_000, 16_000_000, 787, (15_495_036,)),
    (29, 4, 64_000_000, 16_000_000, 853, (4_718_938,)),
    (29, 5, 80_000_000, 2_503_185, 839, (1_521_729,)),
)


def set_bit_indices(value: int) -> tuple[int, ...]:
    result: list[int] = []
    while value:
        low = value & -value
        result.append(low.bit_length() - 1)
        value -= low
    return tuple(result)


def exact_intersection_audit(primes: tuple[int, ...]) -> dict[str, object]:
    """Reproduce all 24 empty intersections without generated Lean sources."""
    records: list[tuple[int, int, int, int, int, tuple[int, ...]]] = []
    for branch in BRANCHES:
        for shard, (lo, width) in enumerate(chunks(branch)):
            bits = (1 << width) - 1
            killing_prime = 0
            previous_bits = 0
            for prime in primes:
                previous_bits = bits
                bits &= periodic_mask(q_pattern(prime, branch, lo), prime, width)
                if bits == 0:
                    killing_prime = prime
                    break
            assert bits == 0
            assert width <= primes[0] * 2**EXPONENT
            records.append(
                (branch, shard, lo, width, killing_prime, set_bit_indices(previous_bits))
            )
    assert tuple(records) == EXPECTED_KILLS
    return {
        "shard_count": len(records),
        "branch_lengths": {str(branch): branch_length(branch) for branch in BRANCHES},
        "last_survivor_records": [
            {
                "branch": branch,
                "shard": shard,
                "lo": lo,
                "width": width,
                "kill_prime": prime,
                "local_indices": list(indices),
                "q_values": [lo + index for index in indices],
                "t_values": [46 * (lo + index) + branch for index in indices],
            }
            for branch, shard, lo, width, prime, indices in records
        ],
    }


PackedTree = tuple[str, int, int] | tuple[str, "PackedTree", "PackedTree"]


def _parse_tree_expression(expression: str) -> PackedTree:
    """Parse the deliberately tiny `.leaf`/`.node` generated Lean grammar."""
    cursor = 0

    def skip_space() -> None:
        nonlocal cursor
        while cursor < len(expression) and expression[cursor].isspace():
            cursor += 1

    def expect(literal: str) -> None:
        nonlocal cursor
        skip_space()
        assert expression.startswith(literal, cursor), (cursor, literal)
        cursor += len(literal)

    def natural() -> int:
        nonlocal cursor
        skip_space()
        match = re.match(r"\d+", expression[cursor:])
        assert match is not None, cursor
        cursor += len(match.group(0))
        return int(match.group(0))

    def tree() -> PackedTree:
        nonlocal cursor
        skip_space()
        expect("(")
        skip_space()
        if expression.startswith(".leaf", cursor):
            cursor += len(".leaf")
            prime = natural()
            pattern = natural()
            expect(")")
            return ("leaf", prime, pattern)
        expect(".node")
        left = tree()
        right = tree()
        expect(")")
        return ("node", left, right)

    result = tree()
    skip_space()
    assert cursor == len(expression), (cursor, len(expression))
    return result


def _balanced_tree(items: list[tuple[int, int]]) -> PackedTree:
    assert items
    if len(items) == 1:
        return ("leaf", items[0][0], items[0][1])
    middle = len(items) // 2
    return ("node", _balanced_tree(items[:middle]), _balanced_tree(items[middle:]))


def parse_packed_tree(text: str, branch: int, shard: int) -> PackedTree:
    match = re.search(
        rf"def even22PackedB{branch}S{shard}Tree : Even22PeriodicTree :=\n"
        rf"  (.*?)\n\ndef even22PackedB{branch}S{shard}Intersection",
        text,
        re.DOTALL,
    )
    assert match is not None
    return _parse_tree_expression(match.group(1))


def audit_packed_shards(primes: tuple[int, ...]) -> dict[str, object]:
    records: list[tuple[int, int, int, int, int, tuple[int, ...]]] = []
    generated_names: list[str] = []
    for branch in BRANCHES:
        for shard, (lo, width) in enumerate(chunks(branch)):
            name = f"{PREFIX}PackedB{branch}S{shard}"
            text = (ERDOS / f"{name}.lean").read_text()
            assert all_imports(text) == [f"{PREFIX}PackedDefs"]
            expected_items = [
                (prime, q_pattern(prime, branch, lo)) for prime in primes
            ]
            assert parse_packed_tree(text, branch, shard) == _balanced_tree(expected_items)
            assert (
                f"def even22PackedB{branch}S{shard}Intersection : BitVec {width} :=\n"
                f"  even22PackedB{branch}S{shard}Tree.eval {width} {EXPONENT}"
            ) in text
            assert (
                f"theorem even22PackedB{branch}S{shard}Intersection_zero :\n"
                f"    even22PackedB{branch}S{shard}Intersection = BitVec.zero {width} := by\n"
                "  decide +kernel"
            ) in text
            assert text.count(f"private theorem even22_b{branch}_s{shard}_map_") == 2 * len(primes)
            for prime, pattern in expected_items:
                stem = f"even22_b{branch}_s{shard}_map_{prime}"
                assert f"private theorem {stem}_fin" in text
                assert f"(46 * ({lo} + (r.val : ZMod {prime})) + {branch})" in text
                assert f"({pattern}).testBit r.val = true" in text
                assert f"({pattern}).testBit (i % {prime}) = true" in text
            assert (
                f"theorem even22_packed_b{branch}_s{shard}_no_centers\n"
                "    {w v : ℤ} {q : ℕ}\n"
                f"    (hlo : {lo} ≤ q) (hhi : q < {lo + width})"
            ) in text
            assert (
                f"(hm : -(33 * (46 * (q : ℤ) + {branch})) =\n"
                "      evenTable22T w - 2 * evenTable22T v) : False"
            ) in text

            bits = (1 << width) - 1
            killing_prime = 0
            previous_bits = 0
            for prime, pattern in expected_items:
                previous_bits = bits
                bits &= periodic_mask(pattern, prime, width)
                if bits == 0:
                    killing_prime = prime
                    break
            assert bits == 0
            assert width <= primes[0] * 2**EXPONENT
            records.append(
                (branch, shard, lo, width, killing_prime, set_bit_indices(previous_bits))
            )
            generated_names.append(name)
    assert tuple(records) == EXPECTED_KILLS
    return {
        "shard_count": len(records),
        "branch_lengths": {str(branch): branch_length(branch) for branch in BRANCHES},
        "last_survivor_records": [
            {
                "branch": branch,
                "shard": shard,
                "lo": lo,
                "width": width,
                "kill_prime": prime,
                "local_indices": list(indices),
                "q_values": [lo + index for index in indices],
                "t_values": [46 * (lo + index) + branch for index in indices],
            }
            for branch, shard, lo, width, prime, indices in records
        ],
        "last_module": generated_names[-1],
    }


@lru_cache(maxsize=1)
def quarantine_audit() -> dict[str, object]:
    """Audit the current safe state after contaminated declarations were removed."""
    primes = active_primes()
    assert {branch: branch_length(branch) for branch in BRANCHES} == {
        17: 82_503_186,
        21: 82_503_186,
        25: 82_503_185,
        29: 82_503_185,
    }
    assert sum(branch_length(branch) for branch in BRANCHES) == 330_012_742
    generated = sorted(
        path.name
        for path in ERDOS.glob(f"{PREFIX}*.lean")
        if "Table" in path.name or "Packed" in path.name
    )
    assert generated == []
    odd_classes = tuple(
        residue
        for residue in range(46)
        if residue % 2 == 1 and residue % 23 in local_allowed_t_residues(23)
    )
    assert odd_classes == BRANCHES
    payload = {
        "row_scale": row_data().scale,
        "base_defs": audit_base_defs(),
        "active_primes": {
            "count": len(primes),
            "first": primes[0],
            "last": primes[-1],
        },
        "packed": exact_intersection_audit(primes),
        "semantics": {
            "odd_mod46_classes": list(odd_classes),
            "generated_files": generated,
            "quarantined": True,
        },
        "verdict": "FAIL_KERNEL_QUARANTINED",
    }
    payload["payload_sha256"] = sha256(
        dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()
    return payload


def audit_packed_semantics(last_module: str) -> dict[str, object]:
    defs_path = ERDOS / f"{PREFIX}PackedDefs.lean"
    defs = defs_path.read_text()
    assert first_import(defs) == f"{PREFIX}Tables"
    for theorem in (
        "even22PeriodicPowMask_getLsbD_true",
        "even22IntersectPeriodicItems_getLsbD_true",
        "even22No_index_of_intersection_zero",
        "Even22PeriodicTree.eval_getLsbD_true",
        "even22No_index_of_tree_zero",
        "even22_allowed_int",
    ):
        assert f"theorem {theorem}" in defs
    assert "native_decide" not in defs

    shard_aggregator_path = ERDOS / f"{PREFIX}PackedShards.lean"
    shard_aggregator = shard_aggregator_path.read_text()
    expected_shards = [
        f"{PREFIX}PackedB{branch}S{shard}"
        for branch in BRANCHES
        for shard in range(len(chunks(branch)))
    ]
    assert all_imports(shard_aggregator) == expected_shards

    cover_path = ERDOS / f"{PREFIX}PackedCover.lean"
    cover = cover_path.read_text()
    assert all_imports(cover) == [f"{PREFIX}PackedShards"]
    assert last_module == expected_shards[-1]
    assert "r.val = 17 ∨ r.val = 21 ∨ r.val = 25 ∨ r.val = 29" in cover
    assert f"(htbound : t ≤ {BOUND})" in cover
    assert "(hm : -(33 * (t : ℤ)) = evenTable22T w - 2 * evenTable22T v)" in cover
    assert local_allowed_t_residues(23) == frozenset({2, 6, 17, 21})
    odd_classes = tuple(
        residue
        for residue in range(46)
        if residue % 2 == 1 and residue % 23 in local_allowed_t_residues(23)
    )
    assert odd_classes == BRANCHES
    for branch in BRANCHES:
        assert f"have ht : t = 46 * q + {branch}" in cover
        for shard, (lo, width) in enumerate(chunks(branch)[:-1]):
            assert f"by_cases h{shard} : q < {lo + width}" in cover
        last = len(chunks(branch)) - 1
        assert f"even22_packed_b{branch}_s{last}_no_centers" in cover

    generated = [
        path
        for path in ERDOS.glob(f"{PREFIX}*.lean")
        if "Table" in path.name or "Packed" in path.name
    ]
    forbidden = {
        token: [path.name for path in generated if token in path.read_text()]
        for token in ("native_decide", "sorry", "admit")
    }
    assert forbidden == {"native_decide": [], "sorry": [], "admit": []}
    missing_imports: list[dict[str, str]] = []
    for path in generated:
        for dependency in all_imports(path.read_text()):
            if not (ERDOS / f"{dependency}.lean").exists():
                missing_imports.append({"file": path.name, "missing": f"{dependency}.lean"})
    return {
        "odd_mod46_classes": list(odd_classes),
        "generated_file_count": len(generated),
        "missing_imports": missing_imports,
        "forbidden_tokens": forbidden,
    }


@lru_cache(maxsize=1)
def audit() -> dict[str, object]:
    primes = active_primes()
    table_primes = [23, *primes]
    assert {branch: branch_length(branch) for branch in BRANCHES} == {
        17: 82_503_186,
        21: 82_503_186,
        25: 82_503_185,
        29: 82_503_185,
    }
    assert sum(branch_length(branch) for branch in BRANCHES) == 330_012_742
    table_defs = audit_table_defs(table_primes)
    tables = audit_prime_tables(table_primes)
    packed = audit_packed_shards(primes)
    semantics = audit_packed_semantics(packed["last_module"])
    verdict = "PASS" if not semantics["missing_imports"] else "FAIL_MISSING_IMPORT"
    payload = {
        "row_scale": row_data().scale,
        "base_defs": audit_base_defs(),
        "active_primes": {
            "count": len(primes),
            "first": primes[0],
            "last": primes[-1],
        },
        "table_defs": table_defs,
        "tables": tables,
        "packed": packed,
        "semantics": semantics,
        "verdict": verdict,
    }
    payload["payload_sha256"] = sha256(
        dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()
    return payload


if __name__ == "__main__":
    print(dumps(quarantine_audit(), indent=2, sort_keys=True))
