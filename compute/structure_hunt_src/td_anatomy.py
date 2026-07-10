"""T-D: census + anatomy of ALL rows-1..15-passing points, k >= 16, N <= 3e7.

Sources:
  * old t4_prefix_survivors.csv (k in [16,3000], N <= 1e7): rows with
    first_fail_pure in {16, 17};
  * td_deep_survivors_new_regions.csv (k in (3000,6500] x N <= 1e7 and
    k in [16,6500] x N in (1e7, 3e7]): all rows (empty in practice);
  * exact resolution of the 10 ambiguous-floor (k, N) pairs the C scan
    skipped (bignum kth-root window, exact row checks).

For every census point (k, N, d), all in exact big-int arithmetic:
  * re-verify the ratio window (n-form) and d >= k;
  * first failing pure row a* over a = 1..k (and the a=0 row);
  * mechanism at a*: failing prime powers p^e || N+a* with
    v_p(block) < e, and whether the block [d+1-a*, d+k-a*] contains NO
    multiple of p (the 'prime with no multiple in interval' mechanism);
  * escape census over j in [1, k]:
      fail_j    = row j fails,
      nomult_j  = some prime p | N+j has no multiple in the row-j block;
  * P(N+j) for j = 1..18.

Output: td_deep_census.json + td_deep_census.txt.
"""
import csv
import json
import os
import sys
from math import isqrt

sys.path.insert(0, "/Users/williamblair/personal/lean-proofs/compute")
from erdos686_exact_core import integer_kth_root, window_n

OUT = "/Users/williamblair/personal/lean-proofs/compute/artifacts/structure_hunt"
AMBIG_PAIRS = [(4049, 14638015), (4049, 14642063), (3271, 21230338),
               (3271, 21233608), (4049, 21959047), (4049, 21963095),
               (262, 28337284), (262, 28337545), (4049, 29280079),
               (4049, 29284127)]

_fact_cache = {}


def factorize(m):
    if m in _fact_cache:
        return _fact_cache[m]
    out = []
    mm = m
    p = 2
    while p * p <= mm:
        if mm % p == 0:
            e = 0
            while mm % p == 0:
                mm //= p
                e += 1
            out.append((p, e))
        p += 1 if p == 2 else 2
    if mm > 1:
        out.append((mm, 1))
    _fact_cache[m] = out
    return out


def v_block(lo, hi, p, cap=64):
    v = 0
    pt = p
    while pt <= hi:
        v += hi // pt - (lo - 1) // pt
        if v >= cap:
            return v
        pt *= p
    return v


def row_fails(N, k, d, a):
    """(fails, failing_primes) for pure row a: (N+a) | prod [d+1-a, d+k-a]."""
    lo, hi = d + 1 - a, d + k - a
    bad = []
    for p, e in factorize(N + a):
        v = v_block(lo, hi, p, cap=e)
        if v < e:
            nomult = (hi // p - (lo - 1) // p) == 0
            bad.append({"p": p, "e": e, "v_block": v, "no_multiple": nomult})
    return (len(bad) > 0), bad


def exact_d_window(k, N):
    """[floor(g_k*(N+1))+1, floor(g_k*(N+k))] via exact integer kth roots:
    floor(g_k*x) = floor(4^(1/k)*x) - x = kthroot(4*x^k) - x (irrational)."""
    x1, x2 = N + 1, N + k
    lo = integer_kth_root(4 * x1 ** k, k) - x1 + 1
    hi = integer_kth_root(4 * x2 ** k, k) - x2
    return lo, hi


def resolve_ambiguous():
    found = []
    log = []
    for k, N in AMBIG_PAIRS:
        lo, hi = exact_d_window(k, N)
        dlo = max(lo, k)
        deg = dlo - lo
        pts = 0
        best_ff = 0
        for d in range(dlo, hi + 1):
            pts += 1
            ff = 0
            for a in range(1, 19):
                fails, _ = row_fails(N, k, d, a)
                if fails:
                    ff = a
                    break
            best_ff = max(best_ff, ff if ff else 99)
            if ff == 0 or ff >= 16:
                found.append((k, N, d))
        log.append({"k": k, "N": N, "d_window": [lo, hi],
                    "points_checked": pts, "degenerate_below_k": deg,
                    "max_first_fail": best_ff})
    return found, log


def largest_prime(m):
    return factorize(m)[-1][0]


def analyze_point(k, N, d):
    assert d >= k and window_n(k, N, d), (k, N, d)
    # first failing pure row over 1..k
    ff = None
    mech = None
    n_fail = 0
    n_nomult = 0
    for j in range(1, k + 1):
        fails, bad = row_fails(N, k, d, j)
        if fails:
            n_fail += 1
            if any(b["no_multiple"] for b in bad):
                n_nomult += 1
            if ff is None:
                ff = j
                mech = bad
    # a = 0 row: N | prod(d+i) - 4*k!
    pm = fm = 1
    for i in range(1, k + 1):
        pm = pm * ((d + i) % N) % N
        fm = fm * (i % N) % N
    a0 = (pm - 4 * fm) % N == 0
    Pj = {j: largest_prime(N + j) for j in range(1, 19)}
    mclass = None
    if mech is not None:
        if len(mech) == 1 and mech[0]["no_multiple"]:
            mclass = "single_prime_no_multiple"
        elif any(b["no_multiple"] for b in mech):
            mclass = "some_prime_no_multiple"
        else:
            mclass = "insufficient_valuation_only"
    return {"k": k, "N": N, "d": d, "a0_pass": bool(a0),
            "first_fail": ff, "first_fail_primes": mech,
            "mechanism": mclass,
            "n_failing_rows_1..k": n_fail,
            "n_rows_with_no_multiple_prime": n_nomult,
            "frac_rows_no_multiple": round(n_nomult / k, 4),
            "P_N_plus_j": Pj}


def main():
    census = []
    with open(os.path.join(OUT, "t4_prefix_survivors.csv")) as f:
        for r in csv.DictReader(f):
            if int(r["first_fail_pure"]) >= 16:
                census.append((int(r["k"]), int(r["N"]), int(r["d"])))
    with open(os.path.join(OUT, "td_deep_survivors_new_regions.csv")) as f:
        for r in csv.DictReader(f):
            census.append((int(r["k"]), int(r["N"]), int(r["d"])))
    amb_found, amb_log = resolve_ambiguous()
    census.extend(amb_found)
    census = sorted(set(census), key=lambda t: (t[1], t[0], t[2]))
    print(f"census: {len(census)} points "
          f"(ambiguous pairs contributed {len(amb_found)})")

    results = [analyze_point(*pt) for pt in census]

    # cluster-level aggregation by N
    clusters = {}
    for r in results:
        c = clusters.setdefault(r["N"], {
            "N": r["N"], "n_points": 0, "k_range": [10 ** 9, 0],
            "d_range": [10 ** 9, 0], "first_fail_hist": {},
            "mechanism_hist": {}, "a0_passes": 0,
            "frac_rows_no_multiple": []})
        c["n_points"] += 1
        c["k_range"] = [min(c["k_range"][0], r["k"]),
                        max(c["k_range"][1], r["k"])]
        c["d_range"] = [min(c["d_range"][0], r["d"]),
                        max(c["d_range"][1], r["d"])]
        ffk = str(r["first_fail"])
        c["first_fail_hist"][ffk] = c["first_fail_hist"].get(ffk, 0) + 1
        c["mechanism_hist"][r["mechanism"]] = \
            c["mechanism_hist"].get(r["mechanism"], 0) + 1
        c["a0_passes"] += r["a0_pass"]
        c["frac_rows_no_multiple"].append(r["frac_rows_no_multiple"])
    for c in clusters.values():
        fr = c.pop("frac_rows_no_multiple")
        c["frac_rows_no_multiple_min"] = min(fr)
        c["frac_rows_no_multiple_max"] = max(fr)
        N = c["N"]
        c["P_N_plus_j_1..18"] = {j: largest_prime(N + j)
                                 for j in range(1, 19)}

    n_single = sum(1 for r in results
                   if r["mechanism"] == "single_prime_no_multiple")
    n_nomult = sum(1 for r in results
                   if r["mechanism"] in ("single_prime_no_multiple",
                                         "some_prime_no_multiple"))
    payload = {
        "scan_coverage": "k in [16,6500], N in [2, 3e7] "
                         "(old t4: k<=3000,N<=1e7; new regions: rest); "
                         "10 ambiguous (k,N) pairs resolved exactly",
        "ambiguous_resolution_log": amb_log,
        "n_census_points": len(census),
        "n_first_fail_single_prime_no_multiple": n_single,
        "n_first_fail_any_prime_no_multiple": n_nomult,
        "clusters": {str(N): clusters[N] for N in sorted(clusters)},
        "points": results,
    }
    with open(os.path.join(OUT, "td_deep_census.json"), "w") as f:
        json.dump(payload, f, indent=1)

    lines = [f"deep census: {len(census)} points, "
             f"single-prime-no-multiple first-fail: {n_single}/{len(census)}, "
             f"any-prime-no-multiple: {n_nomult}/{len(census)}"]
    for N in sorted(clusters):
        c = clusters[N]
        lines.append(f"N={N}: {c['n_points']} pts k={c['k_range']} "
                     f"d={c['d_range']} ff={c['first_fail_hist']} "
                     f"mech={c['mechanism_hist']} a0_pass={c['a0_passes']} "
                     f"nomult_frac=[{c['frac_rows_no_multiple_min']},"
                     f"{c['frac_rows_no_multiple_max']}]")
        lines.append(f"   P(N+j) j=1..18: {c['P_N_plus_j_1..18']}")
    txt = "\n".join(lines)
    with open(os.path.join(OUT, "td_deep_census.txt"), "w") as f:
        f.write(txt + "\n")
    print(txt)


if __name__ == "__main__":
    main()
