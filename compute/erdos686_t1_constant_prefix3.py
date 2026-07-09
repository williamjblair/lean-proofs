"""T1 - constant-quotient prefix-three survivors (Erdos #686, N = 4 branch).

For each constant (k,q) case, enumerate d in 221..constantPrefixThreeBound(k,q)
and u in 0..d-1; set A = (q+1)*d - u (so n = A-1).  Keep the (d,u) with the
exact ratio window in (A,d,k)-form:
    (A+d+k-1)^k <= 4*(A+k-1)^k   and   4*A^k <= (A+d)^k
and check the residual divisibilities for t = 0,1,2:
    (A+t) | residualRowPoly(k, q, d-u+(q+1)*t)
Survivors pass all three.  Consistency of the constant-quotient hypothesis
(q_j = q for j = 1..4, q_j = (n+j) // (d+1-j)) is recorded per window pair.

All arithmetic is exact (Python ints).  The u-enumeration is implemented as
the exact intersection of the window A-interval (obtained by monotone integer
bisection, endpoints re-verified) with the u-range 0 <= u <= d-1, i.e.
q*d+1 <= A <= (q+1)*d; this is equivalent to scanning u = 0..d-1 directly.

Artifacts:
    compute/artifacts/constant_prefix3_survivors.json
    compute/artifacts/constant_prefix3_survivors.csv
"""

import csv
import json
import os
import time

from erdos686_exact_core import (
    CONSTANT_KQ_TABLE, CONSTANT_PREFIX_THREE_BOUND,
    A_window_interval, window_A, residual_row_poly,
    verify_per_factor_identity,
)

HERE = os.path.dirname(os.path.abspath(__file__))
ART = os.path.join(HERE, "artifacts")

EXPECTED = {
    (5, 3): (0, None), (6, 3): (0, None), (7, 4): (0, None),
    (8, 5): (0, None), (9, 6): (0, None),
    (10, 6): (3, 266), (11, 7): (7, 7029), (12, 8): (5, 2695),
    (13, 8): (7, 4467), (14, 9): (10, 2811), (15, 10): (13, 2915),
}
EXPECTED_TOTAL = 45


def quotient_tuple(A: int, d: int):
    """(q_1,...,q_4) with q_j = (n+j)//(d+1-j) = (A+j-1)//(d+1-j)."""
    return tuple((A + j - 1) // (d + 1 - j) for j in range(1, 5))


def run():
    assert verify_per_factor_identity(), "per-factor identity FAILED"
    t0 = time.time()
    survivors = []
    per_case = {}
    inconsistent_window_pairs = []

    for (k, q) in CONSTANT_KQ_TABLE:
        bound = CONSTANT_PREFIX_THREE_BOUND[(k, q)]
        n_window_pairs = 0
        n_consistent = 0
        case_survivors = []
        for d in range(221, bound + 1):
            iv = A_window_interval(k, d)
            if iv is None:
                continue
            A_lo = max(iv[0], q * d + 1)       # u <= d-1
            A_hi = min(iv[1], (q + 1) * d)     # u >= 0
            for A in range(A_lo, A_hi + 1):
                u = (q + 1) * d - A
                assert 0 <= u < d
                assert window_A(k, A, d)       # re-verify window exactly
                n_window_pairs += 1
                qt = quotient_tuple(A, d)
                consistent = qt == (q, q, q, q)
                if consistent:
                    n_consistent += 1
                else:
                    inconsistent_window_pairs.append(
                        {"k": k, "q": q, "d": d, "u": u, "A": A,
                         "qtuple": list(qt)})
                ok = True
                for t in range(3):
                    poly = residual_row_poly(k, q, d - u + (q + 1) * t)
                    if poly % (A + t) != 0:
                        ok = False
                        break
                if ok:
                    rec = {"k": k, "q": q, "d": d, "u": u, "A": A,
                           "qtuple_consistent": consistent}
                    case_survivors.append(rec)
                    survivors.append(rec)
        max_d = max((s["d"] for s in case_survivors), default=None)
        per_case[(k, q)] = {
            "bound": bound,
            "window_pairs": n_window_pairs,
            "qtuple_consistent_pairs": n_consistent,
            "survivors": len(case_survivors),
            "max_survivor_d": max_d,
        }
        exp_count, exp_maxd = EXPECTED[(k, q)]
        status = "OK" if (len(case_survivors) == exp_count
                          and (exp_count == 0 or max_d == exp_maxd)) else "MISMATCH"
        print(f"(k,q)=({k},{q}) d<=%d window_pairs=%d survivors=%d "
              "max_d=%s expected=(%s,%s) %s"
              % (bound, n_window_pairs, len(case_survivors), max_d,
                 exp_count, exp_maxd, status))

    elapsed = time.time() - t0
    total = len(survivors)
    print(f"TOTAL survivors={total} expected={EXPECTED_TOTAL} "
          f"{'OK' if total == EXPECTED_TOTAL else 'MISMATCH'}")
    print(f"window pairs failing q-tuple consistency: "
          f"{len(inconsistent_window_pairs)}")
    print(f"elapsed={elapsed:.2f}s")

    os.makedirs(ART, exist_ok=True)
    payload = {
        "description": "Constant-quotient prefix-three survivors for "
                       "Erdos 686 N=4 branch: window-passing (k,q,d,u,A) "
                       "with A=(q+1)d-u, d>=221, 0<=u<d, passing residual "
                       "divisibilities (A+t) | residualRowPoly(k,q,d-u+(q+1)t) "
                       "for t=0,1,2.",
        "window": "(A+d+k-1)^k <= 4*(A+k-1)^k and 4*A^k <= (A+d)^k",
        "d_range": "221..constantPrefixThreeBound(k,q)",
        "constantPrefixThreeBound": {f"{k},{q}": b for (k, q), b
                                     in CONSTANT_PREFIX_THREE_BOUND.items()},
        "per_case": {f"{k},{q}": v for (k, q), v in per_case.items()},
        "total_survivors": total,
        "expected_total": EXPECTED_TOTAL,
        "inconsistent_window_pairs": inconsistent_window_pairs,
        "survivors": survivors,
        "elapsed_seconds": round(elapsed, 3),
    }
    jpath = os.path.join(ART, "constant_prefix3_survivors.json")
    with open(jpath, "w") as f:
        json.dump(payload, f, indent=1)
    cpath = os.path.join(ART, "constant_prefix3_survivors.csv")
    with open(cpath, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["k", "q", "d", "u", "A", "qtuple_consistent"])
        for s in survivors:
            w.writerow([s["k"], s["q"], s["d"], s["u"], s["A"],
                        int(s["qtuple_consistent"])])
    print(f"wrote {jpath}")
    print(f"wrote {cpath}")
    return survivors


if __name__ == "__main__":
    run()
