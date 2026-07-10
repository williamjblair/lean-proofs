"""T3 - exceptional finite checks (Erdos #686, N = 4 branch).

(a) k = 9, quotient tuple (5,6,6,6):
    d in 221..1413, u in 1..7, A = 6d - u (so n = A - 1 = 6d - u - 1).
    Conditions (exact spec from the reduction):
        h1: (6d-u)   | residualRowPoly(9, 5, d-u)
        h2: (6d-u+1) | residualRowPoly(9, 6, 7-u)
        h3: (6d-u+2) | residualRowPoly(9, 6, 14-u)
        h4: (6d-u+3) | residualRowPoly(9, 6, 21-u)
        window: upper ratio window ((6d-u-1)+d+9)^9 <= 4*((6d-u-1)+9)^9
    Expected: zero (d,u) pass all five.

(b) k = 13, quotient tuple (8,8,8,9):
    d in 221..269, u in 21..30, A = 9d - u.
    Conditions:
        h1: (9d-u)   | residualRowPoly(13, 8, d-u)
        h2: (9d-u+1) | residualRowPoly(13, 8, d-u+9)
        h3: (9d-u+2) | residualRowPoly(13, 8, d-u+18)
        h4: (9d-u+3) | residualRowPoly(13, 9, 30-u)
        window: lower ratio window 4*(9d-u)^13 <= ((9d-u-1)+d+1)^13
    Expected: zero pass all five.

For every (d,u) in each box we record the FIRST failing condition in the
order h1, h2, h3, h4, window (histogram), plus per-point first-fail witness
lists so the Lean certificate can use per-point witnesses.

All arithmetic exact.  Artifact: compute/artifacts/exceptional_cases.json
"""

import json
import os
import time
from collections import Counter

from erdos686_exact_core import residual_row_poly

HERE = os.path.dirname(os.path.abspath(__file__))
ART = os.path.join(HERE, "artifacts")


def scan_case_a():
    """k=9, tuple (5,6,6,6)."""
    first_fail = []
    passing = []
    for d in range(221, 1414):
        for u in range(1, 8):
            A = 6 * d - u
            n = A - 1
            conds = [
                ("h1", residual_row_poly(9, 5, d - u) % A == 0),
                ("h2", residual_row_poly(9, 6, 7 - u) % (A + 1) == 0),
                ("h3", residual_row_poly(9, 6, 14 - u) % (A + 2) == 0),
                ("h4", residual_row_poly(9, 6, 21 - u) % (A + 3) == 0),
                ("window", (n + d + 9) ** 9 <= 4 * (n + 9) ** 9),
            ]
            fail = next((name for name, ok in conds if not ok), None)
            if fail is None:
                passing.append({"d": d, "u": u, "A": A})
            else:
                first_fail.append({"d": d, "u": u, "A": A,
                                   "first_fail": fail})
    return first_fail, passing


def scan_case_b():
    """k=13, tuple (8,8,8,9)."""
    first_fail = []
    passing = []
    for d in range(221, 270):
        for u in range(21, 31):
            A = 9 * d - u
            n = A - 1
            conds = [
                ("h1", residual_row_poly(13, 8, d - u) % A == 0),
                ("h2", residual_row_poly(13, 8, d - u + 9) % (A + 1) == 0),
                ("h3", residual_row_poly(13, 8, d - u + 18) % (A + 2) == 0),
                ("h4", residual_row_poly(13, 9, 30 - u) % (A + 3) == 0),
                ("window", 4 * A ** 13 <= (n + d + 1) ** 13),
            ]
            fail = next((name for name, ok in conds if not ok), None)
            if fail is None:
                passing.append({"d": d, "u": u, "A": A})
            else:
                first_fail.append({"d": d, "u": u, "A": A,
                                   "first_fail": fail})
    return first_fail, passing


def run():
    t0 = time.time()
    results = {}
    order = ["h1", "h2", "h3", "h4", "window"]
    for name, scanner, box in [
            ("k9_tuple_5666", scan_case_a,
             {"k": 9, "qtuple": [5, 6, 6, 6], "A": "6d-u",
              "d_range": [221, 1413], "u_range": [1, 7]}),
            ("k13_tuple_8889", scan_case_b,
             {"k": 13, "qtuple": [8, 8, 8, 9], "A": "9d-u",
              "d_range": [221, 269], "u_range": [21, 30]}),
    ]:
        first_fail, passing = scanner()
        hist = Counter(r["first_fail"] for r in first_fail)
        total = len(first_fail) + len(passing)
        results[name] = {
            "box": box,
            "points_scanned": total,
            "passing_tuples": passing,
            "passing_count": len(passing),
            "first_fail_histogram": {c: hist.get(c, 0) for c in order},
            "first_fail_witnesses": first_fail,
        }
        print(f"{name}: scanned={total} passing={len(passing)} "
              f"histogram={{{', '.join(f'{c}: {hist.get(c, 0)}' for c in order)}}}")
        if passing:
            print("  PASSING TUPLES (expected none):")
            for p in passing:
                print("   ", p)

    elapsed = time.time() - t0
    print(f"elapsed={elapsed:.2f}s")

    os.makedirs(ART, exist_ok=True)
    payload = {
        "description": "Exceptional-quotient-tuple finite boxes for the "
                       "Erdos 686 constant-quotient reduction: k=9 tuple "
                       "(5,6,6,6) and k=13 tuple (8,8,8,9).  Each grid point "
                       "records its first failing condition among h1..h4 and "
                       "the ratio-window inequality (checked in that order).",
        "condition_order": order,
        "cases": results,
        "all_boxes_empty": all(r["passing_count"] == 0
                               for r in results.values()),
        "elapsed_seconds": round(elapsed, 3),
    }
    jpath = os.path.join(ART, "exceptional_cases.json")
    with open(jpath, "w") as f:
        json.dump(payload, f, indent=1)
    print(f"wrote {jpath}")
    return results


if __name__ == "__main__":
    run()
