#!/usr/bin/env python3
"""
Erdos Problem #1212 -- validation / search code.

Problem.  G has vertex set {(x,y) in N^2 : gcd(x,y)=1}; edges join vertices
differing by +-1 in exactly one coordinate.  Call (x,y) QUALIFYING if
    min(x,y) > 1,  gcd(x,y) = 1,  and at least one of x,y is composite.
Question: is there a path to infinity through qualifying vertices?

This script
  (A) verifies the structural reduction (parity grammar, hub graph H, dead rows,
      run-length formula) exhaustively on a box,
  (B) analyses connected components of the qualifying subgraph,
  (C) runs the composite-anchor staircase greedily to large coordinates,
  (D) re-verifies every produced path vertex-by-vertex against the RAW definition.

Usage:  python3 path_search.py [--box 600] [--steps 20000] [--seed-x ...]
"""

from math import gcd
import argparse
import json
import random
import sys

# ---------------------------------------------------------------------------
# small-number machinery
# ---------------------------------------------------------------------------


def sieve_spf(n):
    """smallest prime factor table for 0..n"""
    spf = list(range(n + 1))
    i = 2
    while i * i <= n:
        if spf[i] == i:
            for j in range(i * i, n + 1, i):
                if spf[j] == j:
                    spf[j] = i
        i += 1
    return spf


def is_prime_small(n, spf):
    return n >= 2 and spf[n] == n


# deterministic Miller-Rabin for 64-bit
_MR_BASES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)


def is_prime(n):
    if n < 2:
        return False
    for p in _MR_BASES:
        if n % p == 0:
            return n == p
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in _MR_BASES:
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


_SMALL_PRIMES = None


def small_primes(limit=100000):
    global _SMALL_PRIMES
    if _SMALL_PRIMES is None:
        sp = sieve_spf(limit)
        _SMALL_PRIMES = [i for i in range(2, limit + 1) if sp[i] == i]
    return _SMALL_PRIMES


def factor_small_part(n, bound=100000):
    """return (set of prime factors <= bound, remaining cofactor)"""
    fs = set()
    m = n
    for p in small_primes(bound):
        if p * p > m:
            break
        if m % p == 0:
            fs.add(p)
            while m % p == 0:
                m //= p
    return fs, m


def prime_factors(n):
    """full prime factor set; works whenever the cofactor after trial division
    up to 1e5 is 1, prime, or a perfect square/semiprime we can detect."""
    fs, m = factor_small_part(n)
    if m == 1:
        return fs
    if is_prime(m):
        fs.add(m)
        return fs
    # rho for the rest
    fs |= _rho_factor(m)
    return fs


def _rho_factor(n):
    if n == 1:
        return set()
    if is_prime(n):
        return {n}
    while True:
        c = random.randrange(1, n)
        f = lambda z: (z * z + c) % n
        x, y, d = random.randrange(0, n), 0, 1
        y = x
        d = 1
        while d == 1:
            x = f(x)
            y = f(f(y))
            d = gcd(abs(x - y), n)
        if d != n:
            return _rho_factor(d) | _rho_factor(n // d)


def pmin(n):
    """least prime factor (exact)"""
    if n <= 1:
        return None
    for p in small_primes(100000):
        if p * p > n:
            break
        if n % p == 0:
            return p
    if is_prime(n):
        return n
    return min(prime_factors(n))


def is_composite(n):
    return n > 1 and not is_prime(n)


# ---------------------------------------------------------------------------
# (A) raw definitions
# ---------------------------------------------------------------------------


def qualifying(x, y, spf=None):
    if x <= 1 or y <= 1:
        return False
    if gcd(x, y) != 1:
        return False
    px = is_prime_small(x, spf) if spf is not None and x < len(spf) else is_prime(x)
    py = is_prime_small(y, spf) if spf is not None and y < len(spf) else is_prime(y)
    return not (px and py)


def raw_neighbors(x, y):
    return [(x + 1, y), (x - 1, y), (x, y + 1), (x, y - 1)]


# ---------------------------------------------------------------------------
# (B) structural verification on a box
# ---------------------------------------------------------------------------


def verify_structure(B):
    spf = sieve_spf(B + 4)
    report = {"box": B}
    viol = {
        "horizontal_step_even_row": 0,
        "vertical_step_even_col": 0,
        "dead_row_horizontal": 0,
        "dead_col_vertical": 0,
        "intermediate_composite": 0,
        "run_length_formula": 0,
    }
    examples = {}

    Q = [[False] * (B + 1) for _ in range(B + 1)]
    for x in range(2, B + 1):
        for y in range(2, B + 1):
            Q[x][y] = qualifying(x, y, spf)

    # (1) parity move rules
    for x in range(2, B):
        for y in range(2, B):
            if not Q[x][y]:
                continue
            if Q[x + 1][y] and y % 2 == 0:
                viol["horizontal_step_even_row"] += 1
                examples.setdefault("horizontal_step_even_row", (x, y))
            if Q[x][y + 1] and x % 2 == 0:
                viol["vertical_step_even_col"] += 1
                examples.setdefault("vertical_step_even_col", (x, y))

    # (3) every vertex with an even coordinate >= 4 satisfies the composite
    #     condition automatically (given coprimality + min>1)
    for x in range(2, B + 1):
        for y in range(2, B + 1):
            if gcd(x, y) == 1 and min(x, y) > 1 and (x % 2 == 0 or y % 2 == 0):
                if max(x, y) >= 4 and not Q[x][y]:
                    # only failure mode allowed: (2,p) or (p,2)
                    if not (x == 2 or y == 2):
                        viol["intermediate_composite"] += 1
                        examples.setdefault("intermediate_composite", (x, y))

    # (4) dead rows / columns
    for y in range(3, B, 2):
        if y % 3 == 0:
            for x in range(2, B - 2):
                if gcd(x, y) == 1 and gcd(x + 1, y) == 1 and gcd(x + 2, y) == 1:
                    viol["dead_row_horizontal"] += 1
                    examples.setdefault("dead_row_horizontal", (x, y))
    for x in range(3, B, 2):
        if x % 3 == 0:
            for y in range(2, B - 2):
                if gcd(x, y) == 1 and gcd(x, y + 1) == 1 and gcd(x, y + 2) == 1:
                    viol["dead_col_vertical"] += 1
                    examples.setdefault("dead_col_vertical", (x, y))

    # (5) run-length formula: on odd row b with p = pmin(b), the maximal number
    # of consecutive hub steps (a -> a+2) is floor((p-3)/2) when b is composite
    runs = {}
    for b in range(5, min(B, 400), 2):
        if b % 3 == 0:
            continue
        if 4 * pmin(b) + 10 > B:  # box too small to realise the maximal run
            continue
        best = 0
        cur = 0
        for a in range(3, B - 3, 2):
            if gcd(a, b) == 1 and gcd(a + 1, b) == 1 and gcd(a + 2, b) == 1:
                cur += 1
                best = max(best, cur)
            else:
                cur = 0
        runs[b] = best
        p = pmin(b)
        pred = (p - 3) // 2
        if best != pred:
            viol["run_length_formula"] += 1
            examples.setdefault("run_length_formula", (b, best, pred))

    report["violations"] = viol
    report["examples"] = {k: str(v) for k, v in examples.items()}
    report["sample_runs"] = {b: runs[b] for b in sorted(runs) if b < 200}
    return report, Q, spf


# ---------------------------------------------------------------------------
# (C) component analysis
# ---------------------------------------------------------------------------


def components(B, Q):
    parent = {}

    def find(v):
        while parent[v] != v:
            parent[v] = parent[parent[v]]
            v = parent[v]
        return v

    def union(u, v):
        ru, rv = find(u), find(v)
        if ru != rv:
            parent[ru] = rv

    for x in range(2, B + 1):
        for y in range(2, B + 1):
            if Q[x][y]:
                parent[(x, y)] = (x, y)
    for x in range(2, B + 1):
        for y in range(2, B + 1):
            if not Q[x][y]:
                continue
            if x + 1 <= B and Q[x + 1][y]:
                union((x, y), (x + 1, y))
            if y + 1 <= B and Q[x][y + 1]:
                union((x, y), (x, y + 1))

    sizes = {}
    for v in parent:
        r = find(v)
        sizes[r] = sizes.get(r, 0) + 1
    order = sorted(sizes.items(), key=lambda kv: -kv[1])
    big = order[0][0] if order else None
    # how far does the biggest component reach?
    reach = max((max(v) for v in parent if find(v) == big), default=0)
    touches_border = any(
        find(v) == big and (v[0] >= B - 1 or v[1] >= B - 1) for v in parent
    )
    comp_of_9_10 = None
    if (9, 10) in parent:
        r = find((9, 10))
        comp_of_9_10 = sorted(v for v in parent if find(v) == r)
    return {
        "n_vertices": len(parent),
        "n_components": len(sizes),
        "largest_sizes": [s for _, s in order[:8]],
        "largest_reach": reach,
        "largest_touches_border": touches_border,
        "component_of_9_10": comp_of_9_10,
    }


# ---------------------------------------------------------------------------
# (D) the composite-anchor staircase, greedy, at large scale
# ---------------------------------------------------------------------------


def row_ok(b):
    """usable travel row: odd, composite, 3 does not divide b (=> pmin>=5)"""
    return b % 2 == 1 and b % 3 != 0 and b > 1 and not is_prime(b)


def climb_reach(a, b, cap):
    """largest H such that gcd(a,s)=1 for all s in (b, b+H]; capped."""
    fs = prime_factors(a)
    H = cap
    for p in fs:
        # next multiple of p strictly above b
        nxt = (b // p + 1) * p
        H = min(H, nxt - b - 1)
        if H <= 0:
            return 0
    return H


def horiz_reach(a, b, cap):
    """largest W such that gcd(t,b)=1 for all t in [a, a+W]; capped."""
    fs = prime_factors(b)
    W = cap
    for p in fs:
        nxt = (a // p + 1) * p
        W = min(W, nxt - a - 1)
        if W <= 0:
            return 0
    return W


def greedy_staircase(x0, y0, max_cycles, climb_cap=4000, verbose=False):
    """
    Greedy walk in the hub graph H.
    State: (a, b) both odd, coprime, b a usable row.
    Cycle: travel right on row b as far as useful, pick a climb column a*,
    climb to the next usable row b'.
    Selection rule: among climb columns in the run window prefer composite ones
    with large pmin (long climbs available); among target rows prefer composite
    rows with large pmin (long runs available).
    """
    a, b = x0, y0
    assert a % 2 == 1 and b % 2 == 1 and gcd(a, b) == 1
    legs = []  # (kind, from, to, fixed coord)
    for cyc in range(max_cycles):
        # --- horizontal run on row b starting at column a
        W = horiz_reach(a, b, cap=10 ** 6)
        # candidate climb columns: a, a+2, ..., a+W' with a+2 <= a+W-? we need
        # every column in [a, a*] to satisfy gcd(.,b)=1, which horiz_reach gives.
        cands = []
        astar_max = a + W
        c = a
        while c <= astar_max:
            if c % 2 == 1 and c % 3 != 0 and gcd(c, b) == 1:
                cands.append(c)
            c += 1
        if not cands:
            return {"status": "stuck-no-climb-column", "cycle": cyc, "a": a, "b": b, "legs": legs}
        # prefer farthest-right composite candidate with the largest pmin
        best = None
        for c in cands:
            comp = is_composite(c)
            pm = pmin(c)
            score = (1 if comp else 0, min(pm, 10 ** 9), c)
            if best is None or score > best[0]:
                best = (score, c)
        astar = best[1]
        if astar != a:
            legs.append(("H", a, astar, b))
        # --- climb at column astar to the next usable row
        H = climb_reach(astar, b, cap=climb_cap)
        target = None
        for bb in range(b + 2, b + H + 1, 2):
            if not row_ok(bb):
                continue
            if gcd(astar, bb) != 1:
                continue
            # need to be able to step right on row bb from astar
            if gcd(astar + 1, bb) != 1 or gcd(astar + 2, bb) != 1:
                continue
            target = bb
            break
        if target is None:
            return {
                "status": "stuck-no-target-row",
                "cycle": cyc,
                "a": astar,
                "b": b,
                "climb_reach": H,
                "legs": legs,
            }
        legs.append(("V", b, target, astar))
        a, b = astar, target
        if verbose and cyc % 200 == 0:
            print(f"  cycle {cyc}: (x,y)=({a},{b})", file=sys.stderr)
    return {"status": "ok", "cycles": max_cycles, "a": a, "b": b, "legs": legs}


def legs_to_path(legs, start):
    """expand the leg list into the full vertex sequence in G"""
    x, y = start
    path = [(x, y)]
    for kind, f, t, fixed in legs:
        if kind == "H":
            assert y == fixed and x == f, (kind, f, t, fixed, x, y)
            for xx in range(f + 1, t + 1):
                path.append((xx, y))
            x = t
        else:
            assert x == fixed and y == f, (kind, f, t, fixed, x, y)
            for yy in range(f + 1, t + 1):
                path.append((x, yy))
            y = t
    return path


def verify_path_raw(path):
    """check the path against the raw problem definition"""
    bad = []
    for i, (x, y) in enumerate(path):
        if not (min(x, y) > 1 and gcd(x, y) == 1):
            bad.append(("vertex-gcd/min", i, x, y))
        elif is_prime(x) and is_prime(y):
            bad.append(("both-prime", i, x, y))
    for i in range(len(path) - 1):
        (x1, y1), (x2, y2) = path[i], path[i + 1]
        if abs(x1 - x2) + abs(y1 - y2) != 1:
            bad.append(("adjacency", i, path[i], path[i + 1]))
    if len(set(path)) != len(path):
        bad.append(("injectivity", len(path) - len(set(path))))
    return bad


# ---------------------------------------------------------------------------
# (E) wall columns: columns where a whole finite band of rows blocks a->a+2
# ---------------------------------------------------------------------------


def wall_columns(band, limit):
    """columns a (odd) such that NO row b in band admits the hub step a->a+2,
    i.e. for every b either gcd(a,b)>1 or gcd(a+1,b)>1 or gcd(a+2,b)>1."""
    out = []
    for a in range(3, limit, 2):
        if all(
            gcd(a, b) > 1 or gcd(a + 1, b) > 1 or gcd(a + 2, b) > 1 for b in band
        ):
            out.append(a)
    return out


# ---------------------------------------------------------------------------
# (F) backtracking escape search in the raw graph G
# ---------------------------------------------------------------------------

_PRIME_CACHE = {}


def _isp(n):
    v = _PRIME_CACHE.get(n)
    if v is None:
        v = is_prime(n)
        if len(_PRIME_CACHE) < 4_000_000:
            _PRIME_CACHE[n] = v
    return v


def qual(x, y):
    if x <= 1 or y <= 1:
        return False
    if gcd(x, y) != 1:
        return False
    return not (_isp(x) and _isp(y))


def dfs_escape(start, target_x, max_nodes=3_000_000, ymax=None):
    """depth-first search for a simple path from `start` to a vertex with
    x >= target_x, moves ordered east, north, south, west."""
    if not qual(*start):
        raise ValueError("bad start")
    visited = {start}
    path = [start]

    def moves(v):
        x, y = v
        cand = [(x + 1, y), (x, y + 1), (x, y - 1), (x - 1, y)]
        if ymax is not None:
            cand = [c for c in cand if c[1] <= ymax]
        return cand

    stack = [(start, iter(moves(start)))]
    nodes = 1
    best_x = start[0]
    max_depth = 1
    while stack:
        v, it = stack[-1]
        pushed = False
        for w in it:
            if w in visited or not qual(*w):
                continue
            visited.add(w)
            path.append(w)
            nodes += 1
            max_depth = max(max_depth, len(path))
            best_x = max(best_x, w[0])
            if w[0] >= target_x:
                return {
                    "status": "reached",
                    "path": path,
                    "nodes": nodes,
                    "best_x": best_x,
                }
            stack.append((w, iter(moves(w))))
            pushed = True
            break
        if not pushed:
            stack.pop()
            path.pop()
        if nodes >= max_nodes:
            return {
                "status": "node-limit",
                "path": path,
                "nodes": nodes,
                "best_x": best_x,
                "max_depth": max_depth,
            }
    return {
        "status": "exhausted",
        "path": path,
        "nodes": nodes,
        "best_x": best_x,
        "max_depth": max_depth,
    }


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--box", type=int, default=600)
    ap.add_argument("--cycles", type=int, default=4000)
    ap.add_argument("--start", type=str, default="27,25")
    ap.add_argument("--out", type=str, default="results.json")
    args = ap.parse_args()

    out = {}
    print("== (A) structural verification on box", args.box)
    rep, Q, spf = verify_structure(args.box)
    out["structure"] = rep
    print(json.dumps(rep["violations"], indent=2))
    print("sample maximal hub-runs per row:", dict(list(rep["sample_runs"].items())[:20]))

    print("== (B) component analysis")
    comp = components(args.box, Q)
    out["components"] = {k: v for k, v in comp.items() if k != "component_of_9_10"}
    out["components"]["component_of_9_10"] = comp["component_of_9_10"]
    print(json.dumps(out["components"], indent=2, default=str))

    print("== (C) greedy staircase")
    x0, y0 = (int(t) for t in args.start.split(","))
    res = greedy_staircase(x0, y0, args.cycles, verbose=True)
    print("status:", res["status"], "final (x,y) =", (res.get("a"), res.get("b")))
    out["staircase"] = {
        "status": res["status"],
        "final": [res.get("a"), res.get("b")],
        "cycles": res.get("cycles", res.get("cycle")),
        "n_legs": len(res["legs"]),
        "first_legs": res["legs"][:24],
    }

    print("== (D) raw verification of the produced path")
    path = legs_to_path(res["legs"], (x0, y0))
    bad = verify_path_raw(path)
    out["verification"] = {
        "path_length": len(path),
        "max_x": max(p[0] for p in path),
        "max_y": max(p[1] for p in path),
        "violations": bad[:10],
        "n_violations": len(bad),
    }
    print(json.dumps(out["verification"], indent=2, default=str))

    with open(args.out, "w") as f:
        json.dump(out, f, indent=1, default=str)
    print("wrote", args.out)


if __name__ == "__main__":
    main()
