#!/usr/bin/env python3
"""Monotone (east/north only) escape search + leg statistics.

The monotone escape is exactly the composite-anchor staircase of the proof,
searched with full backtracking instead of greedily.  We record, for each
horizontal run and each vertical climb, its length and the least prime factor
of the anchor that carries it -- the quantities the proof obligation is about.
"""
import sys, random, time, json, argparse
from math import gcd

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from path_search import qual, verify_path_raw, pmin, is_prime  # noqa: E402


def mono_escape(start, dx, max_nodes=8_000_000):
    tx = start[0] + dx
    visited = {start}
    path = [start]
    nx = lambda w: ((w[0] + 1, w[1]), (w[0], w[1] + 1))
    stack = [(start, iter(nx(start)))]
    nodes = 1
    backtracks = 0
    while stack:
        v, it = stack[-1]
        pushed = False
        for w in it:
            if w in visited or not qual(*w):
                continue
            visited.add(w)
            path.append(w)
            nodes += 1
            if w[0] >= tx:
                return {"status": "reached", "path": path, "nodes": nodes, "backtracks": backtracks}
            stack.append((w, iter(nx(w))))
            pushed = True
            break
        if not pushed:
            stack.pop()
            path.pop()
            backtracks += 1
        if nodes >= max_nodes:
            return {"status": "node-limit", "path": path, "nodes": nodes, "backtracks": backtracks}
    return {"status": "exhausted", "path": path, "nodes": nodes, "backtracks": backtracks}


def legs(path):
    out = []
    i = 0
    while i < len(path) - 1:
        j = i
        if path[i + 1][0] == path[i][0] + 1:
            while j < len(path) - 1 and path[j + 1][0] == path[j][0] + 1:
                j += 1
            out.append(("H", path[j][0] - path[i][0], path[i][1]))  # (kind,len,row)
        else:
            while j < len(path) - 1 and path[j + 1][1] == path[j][1] + 1:
                j += 1
            out.append(("V", path[j][1] - path[i][1], path[i][0]))  # (kind,len,col)
        i = j
    return out


def summarize(lg, sample=4000):
    H = [(l, anc) for k, l, anc in lg if k == "H"]
    V = [(l, anc) for k, l, anc in lg if k == "V"]
    res = {}
    for name, arr in (("horizontal_runs", H), ("vertical_climbs", V)):
        if not arr:
            continue
        ls = [l for l, _ in arr]
        sub = arr[:: max(1, len(arr) // sample)]
        pm = [pmin(anc) for _, anc in sub if anc > 1]
        comp = sum(1 for _, anc in sub if not is_prime(anc)) / len(sub)
        res[name] = {
            "count": len(arr),
            "len_mean": sum(ls) / len(ls),
            "len_max": max(ls),
            "len_min": min(ls),
            "anchor_pmin_mean": sum(pm) / len(pm),
            "anchor_pmin_max": max(pm),
            "anchor_pmin_min": min(pm),
            "anchor_composite_frac": comp,
        }
    return res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--scale", type=float, default=1e9)
    ap.add_argument("--dx", type=int, default=2_000_000)
    ap.add_argument("--seed", type=int, default=11)
    ap.add_argument("--out", default="mono_stats.json")
    args = ap.parse_args()
    random.seed(args.seed)
    scale = int(args.scale)
    while True:
        x = random.randrange(scale, 2 * scale)
        y = random.randrange(scale, 2 * scale)
        if qual(x, y):
            break
    t = time.time()
    r = mono_escape((x, y), args.dx)
    p = r["path"]
    print(f"start {(x,y)} status {r['status']} nodes {r['nodes']} backtracks {r['backtracks']} "
          f"len {len(p)} {time.time()-t:.1f}s")
    bad = verify_path_raw(p)
    print("raw violations:", len(bad), bad[:3])
    lg = legs(p)
    s = summarize(lg)
    print(json.dumps(s, indent=1))
    dy = p[-1][1] - p[0][1]
    dxx = p[-1][0] - p[0][0]
    print(f"dx={dxx} dy={dy} ratio={dxx/max(dy,1):.1f}  drift |y-x| start {abs(y-x)} end {abs(p[-1][1]-p[-1][0])}")
    json.dump(
        {"start": [x, y], "status": r["status"], "nodes": r["nodes"],
         "backtracks": r["backtracks"], "path_len": len(p), "violations": len(bad),
         "dx": dxx, "dy": dy, "legs_summary": s},
        open(args.out, "w"), indent=1)


if __name__ == "__main__":
    main()
