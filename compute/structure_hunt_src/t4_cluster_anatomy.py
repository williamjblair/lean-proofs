"""T4b — anatomize the n=48502 cluster (script-N = 48503; also N=48502).

For representative points (k, N, d): for each row a, factor N+a and show
exactly which block elements [d+1-a, d+k-a] cover each prime power (or that
p > d+k-a proves failure).  Also: smoothness profile of 48503..48518, the
largest-prime-vs-cap table for every a, and the k-range boundary (d >= k).
Exact integer arithmetic only.
"""
import json
import os
import sys

sys.path.insert(0, "/Users/williamblair/personal/lean-proofs/compute")
from erdos686_exact_core import factorize

OUT = "/Users/williamblair/personal/lean-proofs/compute/artifacts/structure_hunt"


def vp_block(lo, hi, p, needed):
    """v_p(prod [lo..hi]) truncated once >= needed (exact)."""
    v = 0
    pt = p
    while True:
        v += hi // pt - (lo - 1) // pt
        if pt > hi // p:
            return v
        pt *= p


def row_anatomy(k, N, d, a):
    m = N + a
    lo, hi = d + 1 - a, d + k - a
    out = {"a": a, "modulus": m, "fact": factorize(m),
           "block": [lo, hi], "per_prime": [], "pass": True}
    for p, e in factorize(m):
        v = vp_block(lo, hi, p, e)
        mults = [x for x in range(lo + (-lo) % p, hi + 1, p)][:6]
        out["per_prime"].append(
            {"p": p, "e": e, "v_block": v, "ok": v >= e,
             "multiples_in_block": mults})
        if v < e:
            out["pass"] = False
    return out


def main():
    report = {}
    # smoothness profile of the modulus run
    prof = []
    for m in range(48496, 48522):
        fl = factorize(m)
        prof.append({"m": m, "fact": fl, "P": fl[-1][0]})
    report["modulus_run_48496_48521"] = prof

    # representative points
    reps = [(245, 48503, 276), (245, 48502, 277), (260, 48502, 260),
            (244, 48502, 277)]
    rep_out = []
    for k, N, d in reps:
        rows = [row_anatomy(k, N, d, a) for a in range(0, 17)]
        # a = 0 exact check (not pure product)
        import math
        P0 = 1
        for i in range(1, k + 1):
            P0 = P0 * (d + i)
        a0 = (P0 - 4 * math.factorial(k)) % N == 0
        first_fail_pure = next((r["a"] for r in rows[1:] if not r["pass"]),
                               None)
        rep_out.append({"k": k, "N": N, "d": d, "a0_pass": a0,
                        "first_fail_pure": first_fail_pure,
                        "rows": rows})
        print(f"(k={k}, N={N}, d={d}): a0={a0} "
              f"first_fail_pure={first_fail_pure}")
        for r in rows[1:]:
            bad = [pp for pp in r["per_prime"] if not pp["ok"]]
            tag = "PASS" if r["pass"] else \
                "FAIL " + ",".join(f"p={b['p']}^{b['e']}(v={b['v_block']})"
                                   for b in bad)
            fl = "*".join((f"{p}^{e}" if e > 1 else str(p))
                          for p, e in r["fact"])
            print(f"  a={r['a']:2d} m={r['modulus']}={fl:24s} "
                  f"block=[{r['block'][0]},{r['block'][1]}] {tag}")
    report["representatives"] = rep_out
    with open(os.path.join(OUT, "t4_cluster_anatomy.json"), "w") as f:
        json.dump(report, f, indent=1)
    print("wrote t4_cluster_anatomy.json")


if __name__ == "__main__":
    main()
