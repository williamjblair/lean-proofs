#!/usr/bin/env python3
"""Exact lattice and sparse-coset intersection for the k=5 MW sieve."""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import platform
from collections import defaultdict, deque
from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
from pathlib import Path
from typing import Hashable, Iterable

import sympy
from sympy.matrices.normalforms import hermite_normal_form

from .verify_packets import generated_subgroup, normalize, phi


HERE = Path(__file__).resolve().parent
PACKETS = HERE / "packets.json"
Variable = tuple[int, int]
Value = Hashable


@lru_cache(maxsize=None)
def factorization(value: int) -> dict[int, int]:
    return {
        int(prime): int(exponent)
        for prime, exponent in sympy.factorint(value).items()
    }


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def extended_gcd(a: int, b: int) -> tuple[int, int, int]:
    old_r, r = abs(a), abs(b)
    old_s, s = 1, 0
    old_t, t = 0, 1
    while r:
        quotient = old_r // r
        old_r, r = r, old_r - quotient * r
        old_s, s = s, old_s - quotient * s
        old_t, t = t, old_t - quotient * t
    return (
        old_r,
        old_s * (1 if a >= 0 else -1),
        old_t * (1 if b >= 0 else -1),
    )


def one_congruence_kernel_basis(
    coefficients: list[int], modulus: int
) -> sympy.Matrix:
    """Column basis for z with coefficients*z = 0 modulo modulus."""
    dimension = len(coefficients)
    current = list(coefficients)
    transform = [
        [int(row == column) for column in range(dimension)]
        for row in range(dimension)
    ]
    for column in range(1, dimension):
        x, y = current[0], current[column]
        if y == 0:
            continue
        gcd, s, t = extended_gcd(x, y)
        old_zero = [transform[row][0] for row in range(dimension)]
        old_column = [
            transform[row][column] for row in range(dimension)
        ]
        for row in range(dimension):
            transform[row][0] = (
                s * old_zero[row] + t * old_column[row]
            )
            transform[row][column] = (
                (-y // gcd) * old_zero[row]
                + (x // gcd) * old_column[row]
            )
        current[0] = gcd
        current[column] = 0
    step = modulus // math.gcd(modulus, abs(current[0]))
    for row in range(dimension):
        transform[row][0] *= step
    return sympy.Matrix(transform)


def packet_kernel_update(
    lattice: sympy.Matrix, packet: dict[str, object]
) -> sympy.Matrix:
    basis = packet["basis"]
    for coordinate, modulus in enumerate(packet["invariants"]):
        row = sympy.Matrix([[
            basis[index][coordinate] for index in range(5)
        ]])
        coefficients = [int(value) for value in list(row * lattice)]
        lattice = lattice * one_congruence_kernel_basis(
            coefficients, modulus
        )
        lattice = hermite_normal_form(lattice)
    return lattice


def integer_matrix(matrix: sympy.Matrix) -> list[list[int]]:
    return [
        [int(matrix[row, column]) for column in range(matrix.cols)]
        for row in range(matrix.rows)
    ]


def primary_moduli(
    invariants: tuple[int, ...], rational_prime: int
) -> tuple[int, ...]:
    result = []
    for modulus in invariants:
        exponent = factorization(modulus).get(rational_prime, 0)
        if exponent:
            result.append(rational_prime**exponent)
    return tuple(result)


def primary_projection(
    element: tuple[int, ...],
    invariants: tuple[int, ...],
    rational_prime: int,
) -> tuple[int, ...]:
    result = []
    for value, modulus in zip(element, invariants):
        exponent = factorization(modulus).get(rational_prime, 0)
        if exponent:
            result.append(value % (rational_prime**exponent))
    return tuple(result)


def add_primary(
    left: tuple[tuple[int, ...], ...],
    right: tuple[tuple[int, ...], ...],
    moduli: tuple[tuple[int, ...], ...],
) -> tuple[tuple[int, ...], ...]:
    return tuple(
        tuple(
            (a + b) % modulus
            for a, b, modulus in zip(
                left_component, right_component, component_moduli
            )
        )
        for left_component, right_component, component_moduli
        in zip(left, right, moduli)
    )


def primary_image_relation(
    packets: dict[int, dict[str, object]],
    packet_primes: list[int],
    rational_prime: int,
) -> set[tuple[tuple[int, ...], ...]]:
    moduli = tuple(
        primary_moduli(
            tuple(packets[packet_prime]["invariants"]),
            rational_prime,
        )
        for packet_prime in packet_primes
    )
    generators = []
    for basis_index in range(5):
        generators.append(tuple(
            primary_projection(
                tuple(packets[packet_prime]["basis"][basis_index]),
                tuple(packets[packet_prime]["invariants"]),
                rational_prime,
            )
            for packet_prime in packet_primes
        ))
    zero = tuple(tuple(0 for _ in component) for component in moduli)
    relation = {zero}
    queue = deque([zero])
    while queue:
        current = queue.popleft()
        for generator in generators:
            following = add_primary(current, generator, moduli)
            if following not in relation:
                relation.add(following)
                queue.append(following)
    return relation


@dataclass(frozen=True)
class Factor:
    variables: tuple[Variable, ...]
    table: dict[tuple[Value, ...], int]


def join_factors(left: Factor, right: Factor) -> Factor:
    common = [
        variable for variable in left.variables
        if variable in right.variables
    ]
    output_variables = left.variables + tuple(
        variable for variable in right.variables
        if variable not in left.variables
    )
    if not common:
        return Factor(
            output_variables,
            {
                left_key + right_key: left_count * right_count
                for left_key, left_count in left.table.items()
                for right_key, right_count in right.table.items()
            },
        )
    left_indices = [
        left.variables.index(variable) for variable in common
    ]
    right_indices = [
        right.variables.index(variable) for variable in common
    ]
    right_new_indices = [
        index for index, variable in enumerate(right.variables)
        if variable not in left.variables
    ]
    index: dict[tuple[Value, ...],
                list[tuple[tuple[Value, ...], int]]] = defaultdict(list)
    for key, count in right.table.items():
        common_key = tuple(key[index] for index in right_indices)
        index[common_key].append((key, count))
    output: dict[tuple[Value, ...], int] = {}
    for left_key, left_count in left.table.items():
        common_key = tuple(left_key[index] for index in left_indices)
        for right_key, right_count in index.get(common_key, ()):
            key = left_key + tuple(
                right_key[index] for index in right_new_indices
            )
            output[key] = (
                output.get(key, 0) + left_count * right_count
            )
    return Factor(output_variables, output)


def sum_out(factor: Factor, variable: Variable) -> Factor:
    index = factor.variables.index(variable)
    variables = (
        factor.variables[:index] + factor.variables[index + 1:]
    )
    output: dict[tuple[Value, ...], int] = {}
    for key, count in factor.table.items():
        reduced = key[:index] + key[index + 1:]
        output[reduced] = output.get(reduced, 0) + count
    return Factor(variables, output)


def contract_factors(
    factors: list[Factor],
    keep: set[Variable] | None = None,
) -> Factor:
    keep = keep or set()
    active = list(factors)
    while True:
        variables = {
            variable
            for factor in active
            for variable in factor.variables
            if variable not in keep
        }
        if not variables:
            break

        def score(variable: Variable) -> tuple[int, int, int]:
            selected = [
                factor for factor in active
                if variable in factor.variables
            ]
            union = set().union(*(
                set(factor.variables) for factor in selected
            ))
            return (
                len(union),
                math.prod(len(factor.table) for factor in selected),
                len(selected),
            )

        variable = min(variables, key=score)
        selected = [
            factor for factor in active
            if variable in factor.variables
        ]
        active = [
            factor for factor in active
            if variable not in factor.variables
        ]
        combined = selected[0]
        for factor in selected[1:]:
            combined = join_factors(combined, factor)
        active.append(sum_out(combined, variable))

    combined = active[0]
    for factor in active[1:]:
        combined = join_factors(combined, factor)
    return combined


def reachable_packet_image(
    packet: dict[str, object]
) -> set[tuple[int, ...]]:
    invariants = tuple(packet["invariants"])
    basis = [
        normalize(generator, invariants)
        for generator in packet["basis"]
    ]
    subgroup = generated_subgroup(basis, invariants)
    return {
        normalize(element, invariants)
        for element in packet["image"]
    } & subgroup


def build_primary_factors(
    packets: dict[int, dict[str, object]],
    packet_primes: list[int],
    reachable: dict[int, set[tuple[int, ...]]],
) -> list[Factor]:
    rational_prime_packets: dict[int, list[int]] = defaultdict(list)
    for packet_prime in packet_primes:
        for modulus in packets[packet_prime]["invariants"]:
            for rational_prime in factorization(modulus):
                if packet_prime not in rational_prime_packets[rational_prime]:
                    rational_prime_packets[rational_prime].append(
                        packet_prime
                    )
    shared = {
        rational_prime: primes
        for rational_prime, primes
        in rational_prime_packets.items()
        if len(primes) >= 2
    }

    factors: list[Factor] = []
    for packet_prime in packet_primes:
        packet = packets[packet_prime]
        invariants = tuple(packet["invariants"])
        scopes = sorted(
            rational_prime
            for rational_prime, primes in shared.items()
            if packet_prime in primes
        )
        if not scopes:
            factors.append(Factor((), {(): len(reachable[packet_prime])}))
            continue
        table: dict[tuple[Value, ...], int] = {}
        for element in reachable[packet_prime]:
            key = tuple(
                primary_projection(
                    element, invariants, rational_prime
                )
                for rational_prime in scopes
            )
            table[key] = table.get(key, 0) + 1
        factors.append(Factor(
            tuple(
                (packet_prime, rational_prime)
                for rational_prime in scopes
            ),
            table,
        ))

    for rational_prime, primes in sorted(shared.items()):
        relation = primary_image_relation(
            packets, primes, rational_prime
        )
        factors.append(Factor(
            tuple(
                (packet_prime, rational_prime)
                for packet_prime in primes
            ),
            {element: 1 for element in relation},
        ))
    return factors


def count_surviving_cosets(
    packets: dict[int, dict[str, object]],
    packet_primes: list[int],
    reachable: dict[int, set[tuple[int, ...]]],
) -> int:
    factors = build_primary_factors(packets, packet_primes, reachable)
    if packet_primes[-1] == 59:
        boundary = {(59, 2), (59, 5)}
        contracted = contract_factors(factors, keep=boundary)
        assert set(contracted.variables) == boundary
        return sum(contracted.table.values())
    contracted = contract_factors(factors)
    assert contracted.variables == ()
    return contracted.table[()]


def known_combined_classes(
    data: dict[str, object],
    packet_primes: list[int],
    include_infinity: bool = False,
) -> list[list[int]]:
    classes: dict[tuple[tuple[int, ...], ...], list[int]] = defaultdict(list)
    points = list(data["known_affine_points"])
    if include_infinity:
        points.extend(data["known_infinity_points"]["points"])
    for index, point in enumerate(points):
        signature = []
        for packet_prime in packet_primes:
            packet = data["packets"][str(packet_prime)]
            invariants = tuple(packet["invariants"])
            basis = [
                normalize(generator, invariants)
                for generator in packet["basis"]
            ]
            signature.append(phi(point["vector"], basis, invariants))
        classes[tuple(signature)].append(index)
    return sorted(classes.values())


def run_sieve() -> dict[str, object]:
    data = json.loads(PACKETS.read_text())
    packets = {
        int(prime): packet
        for prime, packet in data["packets"].items()
    }
    packet_primes = sorted(packets)
    reachable = {
        prime: reachable_packet_image(packet)
        for prime, packet in packets.items()
    }
    packet_image_orders = {
        prime: len(generated_subgroup(
            [
                normalize(generator, tuple(packet["invariants"]))
                for generator in packet["basis"]
            ],
            tuple(packet["invariants"]),
        ))
        for prime, packet in packets.items()
    }

    lattice = sympy.eye(5)
    previous_index = 1
    incremental: list[dict[str, object]] = []
    for endpoint, packet_prime in enumerate(packet_primes, start=1):
        lattice = packet_kernel_update(lattice, packets[packet_prime])
        index = abs(int(lattice.det()))
        relative_index = index // previous_index
        assert index % previous_index == 0
        assert packet_image_orders[packet_prime] % relative_index == 0
        prefix = packet_primes[:endpoint]
        surviving = count_surviving_cosets(
            packets, prefix, reachable
        )
        assert index % surviving == 0 or surviving < index
        known_classes = known_combined_classes(data, prefix)
        known_projective_classes = known_combined_classes(
            data, prefix, include_infinity=True
        )
        incremental.append({
            "added_packet_prime": packet_prime,
            "packet_reduction_image_order":
                packet_image_orders[packet_prime],
            "relative_kernel_index_gain": relative_index,
            "overlap_factor":
                packet_image_orders[packet_prime] // relative_index,
            "relative_index_factorization": {
                str(prime): exponent
                for prime, exponent
                in factorization(relative_index).items()
            },
            "combined_lattice_index": index,
            "combined_lattice_column_hnf": integer_matrix(lattice),
            "surviving_cosets": surviving,
            "surviving_density": str(Fraction(surviving, index)),
            "known_affine_class_count": len(known_classes),
            "known_affine_class_merges": [
                indices for indices in known_classes if len(indices) > 1
            ],
            "known_projective_class_count":
                len(known_projective_classes),
            "known_projective_class_merges": [
                indices for indices in known_projective_classes
                if len(indices) > 1
            ],
        })
        previous_index = index

    final = incremental[-1]
    assert final["known_affine_class_count"] == 34
    assert final["known_affine_class_merges"] == []
    assert final["known_projective_class_count"] == 36
    assert final["known_projective_class_merges"] == []
    return {
        "verdict": "PASS",
        "algorithm": (
            "exact primary-component factor graph plus HNF kernel lattice"
        ),
        "python_version": platform.python_version(),
        "sympy_version": sympy.__version__,
        "packet_file": str(PACKETS.relative_to(HERE.parents[3])),
        "packet_sha256": sha256(PACKETS),
        "packet_primes": packet_primes,
        "packet_count": len(packet_primes),
        "incremental": incremental,
        "combined_lattice_index": final["combined_lattice_index"],
        "combined_lattice_column_hnf":
            final["combined_lattice_column_hnf"],
        "combined_index_factorization": {
            str(prime): exponent
            for prime, exponent
            in factorization(final["combined_lattice_index"]).items()
        },
        "surviving_cosets": final["surviving_cosets"],
        "surviving_density": final["surviving_density"],
        "known_affine_combined_class_count":
            final["known_affine_class_count"],
        "known_affine_class_merges":
            final["known_affine_class_merges"],
        "known_projective_combined_class_count":
            final["known_projective_class_count"],
        "known_projective_class_merges":
            final["known_projective_class_merges"],
        "infinity_vectors_certified": bool(
            data["known_infinity_points"].get("points")
        ),
        "rational_points_proved_complete": False,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = run_sieve()
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output is not None:
        args.output.write_text(rendered)
    print(rendered, end="")


if __name__ == "__main__":
    main()
