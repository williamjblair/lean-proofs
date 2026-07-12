#!/usr/bin/env python3
"""Exact second-stage closure certificate for the k=18 square-root row."""

from __future__ import annotations

import numpy as np

from even_uniform_sqrt_verify import (
    add_bivariate_term,
    add_term,
    eval_poly,
    eval_shift_coefficients,
    k18_trap_certificate,
    make_data,
    shifted_w_coefficients,
)
from k18_modular_scan import allowed_t_residues, audit as modular_audit


ROW = make_data(18)
LARGE_GAP = 56
LARGE_TRAP = 242_269_137
LARGE_COVER = [
    19, 907, 827, 941, 887, 857, 991, 919, 967, 911, 883, 947,
    839, 997, 821, 751, 769, 547, 859, 659, 977, 797, 491, 811,
    757, 809, 509, 619, 281, 677, 773, 431, 593, 487, 163,
]
LARGE_COVER_COUNTS = [
    2_990_976, 629_678, 433_898, 299_046, 209_294, 147_358,
    104_870, 74_591, 53_653, 38_716, 27_980, 20_257, 14_697,
    10_744, 7_859, 5_763, 4_222, 3_076, 2_244, 1_627, 1_194,
    855, 610, 443, 317, 227, 156, 108, 75, 49, 33, 19, 11, 4, 1, 0,
]
KERNEL_COVER = [
    19, 857, 797, 541, 467, 491, 523, 509, 487, 359, 431, 281, 373,
    439, 463, 409, 347, 433, 389, 521, 307, 443, 421, 227, 311, 419,
    271, 331, 193, 379, 367, 353, 191, 241, 337, 349, 269, 397, 317,
    283, 211, 251, 173, 313, 383, 137, 229, 257, 179, 181, 151, 239,
    149, 223, 97, 131, 139, 197, 233, 263, 277, 293,
]
KERNEL_COVER_COUNTS = [
    2_990_976, 629_678, 448_206, 331_836, 247_320, 185_899,
    140_149, 105_847, 80_456, 61_818, 47_748, 36_866, 28_578,
    22_318, 17_541, 14_041, 11_252, 9_025, 7_256, 5_839, 4_755,
    3_891, 3_193, 2_613, 2_151, 1_773, 1_462, 1_217, 1_016, 854,
    715, 602, 503, 424, 358, 298, 247, 204, 169, 138, 113, 94, 79,
    66, 54, 45, 39, 33, 27, 22, 18, 15, 12, 10, 8, 7, 6, 5, 4, 3,
    2, 1, 0,
]


def large_gap_certificate() -> dict[str, int]:
    """Certify m>-242269137 whenever d>=56."""
    # 4*12^18 < 13^18 gives 12d<n+18.  At d>=56 this gives
    # n>=655, hence v=2n+19>=1329; w-v=2d>=112.
    assert 4 * 12**18 < 13**18
    v0 = 1329
    w0 = v0 + 2 * LARGE_GAP
    wpoly = dict(ROW.d_poly)
    for e, c in ROW.t_poly.items():
        add_term(wpoly, e, LARGE_TRAP * c)
    coeffs = shifted_w_coefficients(wpoly, w0)
    vpoly: dict[int, int] = {}
    for e, c in ROW.t_poly.items():
        add_term(vpoly, e, 2 * LARGE_TRAP * c)
    for e, c in ROW.d_poly.items():
        add_term(vpoly, e, -4 * c)
    for i, c in eval_shift_coefficients(vpoly, v0).items():
        add_bivariate_term(coeffs, (i, 0), c)
    assert len(coeffs) == 55 and min(coeffs.values()) > 0
    assert min(eval_shift_coefficients(ROW.t_poly, v0).values()) > 0
    assert min(eval_shift_coefficients(ROW.t_poly, w0).values()) > 0
    return {
        "gap": LARGE_GAP,
        "trap": LARGE_TRAP,
        "v0": v0,
        "w0": w0,
        "terms": len(coeffs),
        "min_coefficient": min(coeffs.values()),
        "constant": coeffs[(0, 0)],
    }


def finite_strip_certificate() -> dict[str, int]:
    """Check every ratio-window candidate for 18<=d<=55 exactly."""
    # Lower: 4*12^18<13^18 -> 12d<n+18 -> n>=12d-17.
    # Upper: 27^18<4*25^18 -> 2n+2<25d -> n<=(25d-3)//2.
    assert 4 * 12**18 < 13**18
    assert 27**18 < 4 * 25**18
    checked = 0
    minimum_abs_error: int | None = None
    minimum_point: tuple[int, int] | None = None
    for d in range(18, LARGE_GAP):
        lower = 12 * d - 17
        upper = (25 * d - 3) // 2
        for n in range(lower, upper + 1):
            v = 2 * n + 19
            w = v + 2 * d
            error = int(eval_poly(ROW.s_poly, w) - 4 * eval_poly(ROW.s_poly, v))
            assert error != 0
            checked += 1
            if minimum_abs_error is None or abs(error) < minimum_abs_error:
                minimum_abs_error = abs(error)
                minimum_point = (d, n)
    assert checked == 1311
    assert minimum_abs_error is not None and minimum_point is not None
    return {
        "gap_lo": 18,
        "gap_hi": 55,
        "checked": checked,
        "minimum_abs_error": minimum_abs_error,
        "minimum_d": minimum_point[0],
        "minimum_n": minimum_point[1],
    }


def large_gap_cover_certificate() -> dict[str, object]:
    """Cover every remaining large-gap candidate by explicit prime fields."""
    # The strict archimedean bound is m>-LARGE_TRAP and m=-81*t, hence
    # 1 <= t <= (LARGE_TRAP-1)//81 = 2,990,976.
    candidate_count = (LARGE_TRAP - 1) // 81
    assert candidate_count == LARGE_COVER_COUNTS[0]
    survivors = np.arange(1, candidate_count + 1, dtype=np.int64)
    counts = [len(survivors)]
    for p in LARGE_COVER:
        allowed, _ = allowed_t_residues(p)
        survivors = survivors[allowed[survivors % p]]
        counts.append(len(survivors))
    assert counts == LARGE_COVER_COUNTS
    assert not survivors.size
    return {
        "candidate_count": candidate_count,
        "primes": LARGE_COVER,
        "survivor_counts": counts,
    }


def kernel_cover_certificate() -> dict[str, object]:
    """Reproduce the lower-peak-memory cover selected for Lean sharding."""
    candidate_count = (LARGE_TRAP - 1) // 81
    survivors = np.arange(1, candidate_count + 1, dtype=np.int64)
    counts = [len(survivors)]
    for p in KERNEL_COVER:
        allowed, _ = allowed_t_residues(p)
        survivors = survivors[allowed[survivors % p]]
        counts.append(len(survivors))
    assert counts == KERNEL_COVER_COUNTS
    assert not survivors.size
    return {
        "candidate_count": candidate_count,
        "primes": KERNEL_COVER,
        "survivor_counts": counts,
    }


def audit() -> dict[str, object]:
    global_trap = k18_trap_certificate()
    survivors, witness_digest = modular_audit()
    assert survivors == [2_990_977, 3_541_067]
    survivor_m = [-81 * t for t in survivors]
    # The first value equals the excluded lower endpoint; the second is lower.
    assert max(survivor_m) == -LARGE_TRAP
    return {
        "global_trap": global_trap,
        "modular_survivor_t": survivors,
        "modular_survivor_m": survivor_m,
        "witness_digest": witness_digest,
        "large_gap": large_gap_certificate(),
        "large_gap_cover": large_gap_cover_certificate(),
        "kernel_cover": kernel_cover_certificate(),
        "finite_strip": finite_strip_certificate(),
    }


def main() -> None:
    for key, value in audit().items():
        print(key, value)


if __name__ == "__main__":
    main()
