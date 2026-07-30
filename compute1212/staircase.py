#!/usr/bin/env python3
"""
Erdos #1212 -- composite-anchor staircase search (the object of the proof).

A staircase is a sequence of hubs (a_i, b_i), a_i and b_i odd, given by
  * a horizontal run on row b_{i+1} from column a_i to column a_{i+1}
  * a vertical climb at column a_i from row b_i to row b_{i+1}
subject to
  (V)  gcd(a_i, s) = 1        for all s in [b_i, b_{i+1}]
  (H)  gcd(t, b_{i+1}) = 1    for all t in [a_i, a_{i+1}]
and with every anchor composite, so that the "at least one composite" condition
holds at every vertex of every leg.

This script runs the staircase greedily (with bounded backtracking) and records
the statistics that the proof obligation depends on:
  * how far one must climb before travel resumes,
  * how many candidate climb columns are consumed,
  * the least prime factor of the anchors actually used.
"""

from math import gcd
import argparse
import json
import sys

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from path_search import (  # noqa: E402
    is_prime,
    is_composite,
    prime_factors,
    pmin,
    verify_path_raw,
    legs_to_path,
)


def usable_row(b):
    """odd, composite, not divisible by 3 (=> p_min >= 5, horizontal runs exist)"""
    return b % 2 == 1 and b % 3 != 0 and b > 1 and not is_prime(b)


def reach(anchor, start, cap):
    """largest R with gcd(anchor, s) = 1 for every s in (start, start+R]"""
    R = cap
    for p in prime_factors(anchor):
        nxt = (start // p + 1) * p
        R = min(R, nxt - start - 1)
        if R <= 0:
            return 0
    return R


def hreach(a, b, cap):
    """largest W with gcd(t, b) = 1 for every t in [a, a+W]"""
    return reach(b, a - 1, cap + 1) - 1


def climb_legal(astar, b, b2):
    """every hub (astar, s), b < s < b2, satisfies the composite condition"""
    if is_composite(astar):
        return True
    for s in range(b + 2, b2, 2):
        if s % 3 == 0:
            continue  # odd multiple of 3 above 3 is composite
        if is_prime(s):
            return False
    return True


def step(a, b, climb_cap, col_budget, row_budget):
    """
    From hub (a,b) with b a usable (odd composite, 3-free) row, return
    (a*, b', ...) or None.
      a* : climb column inside the current run window on row b
      b' : next usable row, reached by an uninterrupted climb at a*, admitting
           an immediate rightward hub step.
    """
    W = hreach(a, b, climb_cap)
    cols = []
    c = a
    while c <= a + W and len(cols) < col_budget:
        if c % 2 == 1 and c % 3 != 0 and gcd(c, b) == 1:
            cols.append(c)
        c += 1
    # rough columns first (they permit long climbs), then right-most
    cols.sort(key=lambda z: (-min(pmin(z), 10 ** 12), -z))
    for astar in cols:
        H = reach(astar, b, cap=climb_cap)
        tried = 0
        for b2 in range(b + 2, b + H + 1, 2):
            if not usable_row(b2):
                continue
            tried += 1
            if tried > row_budget:
                break
            if gcd(astar + 1, b2) != 1 or gcd(astar + 2, b2) != 1:
                continue
            if not climb_legal(astar, b, b2):
                continue
            return astar, b2, len(cols), b2 - b, H, W
    return None


def run(a0, b0, cycles, climb_cap=100000, col_budget=200, row_budget=200):
    a, b = a0, b0
    legs = []
    stats = {"climb": [], "run": [], "cols_scanned": [], "pmin_row": [], "pmin_col": []}
    for i in range(cycles):
        r = step(a, b, climb_cap, col_budget, row_budget)
        if r is None:
            return {"status": "stuck", "cycle": i, "a": a, "b": b, "legs": legs, "stats": stats}
        astar, b2, ncols, dclimb, H, W = r
        if astar != a:
            legs.append(("H", a, astar, b))
        legs.append(("V", b, b2, astar))
        stats["run"].append(astar - a)
        stats["climb"].append(dclimb)
        stats["cols_scanned"].append(ncols)
        stats["pmin_row"].append(pmin(b2))
        stats["pmin_col"].append(pmin(astar))
        a, b = astar, b2
    return {"status": "ok", "cycles": cycles, "a": a, "b": b, "legs": legs, "stats": stats}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--start", default="27,25")
    ap.add_argument("--cycles", type=int, default=5000)
    ap.add_argument("--out", default="staircase.json")
    args = ap.parse_args()
    a0, b0 = (int(t) for t in args.start.split(","))
    res = run(a0, b0, args.cycles)
    print("status", res["status"], "final", (res["a"], res["b"]))
    s = res["stats"]
    if s["climb"]:
        n = len(s["climb"])
        print(f"cycles completed: {n}")
        print(f"  x advance per cycle: mean {sum(s['run'])/n:.2f} max {max(s['run'])}")
        print(f"  y climb per cycle:   mean {sum(s['climb'])/n:.2f} max {max(s['climb'])}")
        print(f"  climb columns scanned: mean {sum(s['cols_scanned'])/n:.2f} max {max(s['cols_scanned'])}")
        print(f"  p_min(row) used: mean {sum(s['pmin_row'])/n:.1f} max {max(s['pmin_row'])}")
        print(f"  p_min(col) used: mean {sum(s['pmin_col'])/n:.1f} max {max(s['pmin_col'])}")
    path = legs_to_path(res["legs"], (a0, b0))
    bad = verify_path_raw(path)
    print("path length", len(path), "final", path[-1], "raw violations", len(bad), bad[:3])
    json.dump(
        {
            "status": res["status"],
            "final": [res["a"], res["b"]],
            "path_len": len(path),
            "violations": len(bad),
            "first_legs": res["legs"][:30],
            "stats_summary": {
                k: {"mean": sum(v) / len(v), "max": max(v)} for k, v in s.items() if v
            },
        },
        open(args.out, "w"),
        indent=1,
    )


if __name__ == "__main__":
    main()
