"""Cross-validate t4_scan (C, per-prime Legendre method) against an
independent exact Python implementation (direct big-int products, banked
ratio_d_range window code).  Two boxes:
  1. k in [16,40], N in [2,20000]        (dense small box)
  2. k in [230,270], N in [48400,48700]  (the known cluster)
Compares the full first-fail histogram restricted to d>=k points and the
survivor line sets.
"""
import os
import subprocess
import sys
from math import prod

sys.path.insert(0, "/Users/williamblair/personal/lean-proofs/compute")

SRC = "/Users/williamblair/personal/lean-proofs/compute/structure_hunt_src"
OUT = "/Users/williamblair/personal/lean-proofs/compute/artifacts/structure_hunt"
GAMMA = os.path.join(OUT, "gamma_scaled_large_k.txt")


def ratio_d_range(k, N):
    """Exact inclusive d-window (banked implementation, independent)."""
    hi = max(1, 2 * N + 10 * k + 10)
    while (N + hi + 1) ** k < 4 * (N + 1) ** k:
        hi *= 2
    left, right = 0, hi
    while left < right:
        mid = (left + right) // 2
        if (N + mid + 1) ** k >= 4 * (N + 1) ** k:
            right = mid
        else:
            left = mid + 1
    dmin = left
    hi = max(dmin, 1)
    while (N + hi + k) ** k <= 4 * (N + k) ** k:
        hi *= 2
    left, right = dmin, hi
    while left + 1 < right:
        mid = (left + right) // 2
        if (N + mid + k) ** k <= 4 * (N + k) ** k:
            left = mid
        else:
            right = mid
    return dmin, left


def py_box(kmin, kmax, Nlo, Nhi):
    hist = {}
    surv = set()
    for k in range(kmin, kmax + 1):
        for N in range(Nlo, Nhi + 1):
            dlo, dhi = ratio_d_range(k, N)
            dlo = max(dlo, k)
            for d in range(dlo, dhi + 1):
                ff = 0
                for a in range(1, 17):
                    P = prod(d + i - a for i in range(1, k + 1))
                    if P % (N + a) != 0:
                        ff = a
                        break
                key = (k, ff if ff else 17)
                hist[key] = hist.get(key, 0) + 1
                if ff == 0 or ff >= 8:
                    P0 = prod(d + i for i in range(1, k + 1))
                    import math
                    a0 = (P0 - 4 * math.factorial(k)) % N == 0
                    surv.add((k, N, d, int(a0), ff if ff else 17))
    return hist, surv


def c_box(kmin, kmax, Nlo, Nhi, tag):
    pref = os.path.join(SRC, "validate_tmp", f"t4_{tag}")
    os.makedirs(os.path.dirname(pref), exist_ok=True)
    subprocess.run([os.path.join(SRC, "t4_scan"), GAMMA, str(kmin),
                    str(kmax), str(Nlo), str(Nhi), str(Nhi + 31), pref],
                   check=True)
    assert os.path.getsize(pref + ".ambig") == 0, "ambig nonempty"
    hist = {}
    with open(pref + ".hist") as f:
        for line in f:
            if line.startswith("#") or line.startswith("k,"):
                continue
            v = [int(x) for x in line.split(",")]
            k = v[0]
            for a in range(1, 18):
                if v[a]:
                    hist[(k, a)] = v[a]
    surv = set()
    with open(pref + ".surv.csv") as f:
        next(f)
        for line in f:
            v = line.strip().split(",")
            surv.add((int(v[0]), int(v[1]), int(v[2]), int(v[3]),
                      int(v[4])))
    return hist, surv


def compare(tag, kmin, kmax, Nlo, Nhi):
    ch, cs = c_box(kmin, kmax, Nlo, Nhi, tag)
    ph, ps = py_box(kmin, kmax, Nlo, Nhi)
    ok = ch == ph and cs == ps
    print(f"[{tag}] hist match: {ch == ph}  surv match: {cs == ps}  "
          f"(C surv={len(cs)}, Py surv={len(ps)})")
    if not ok:
        for kk in sorted(set(ch) | set(ph)):
            if ch.get(kk) != ph.get(kk):
                print("  hist diff", kk, ch.get(kk), ph.get(kk))
        print("  C-only surv:", sorted(cs - ps)[:10])
        print("  Py-only surv:", sorted(ps - cs)[:10])
    return ok


def main():
    ok1 = compare("smallbox", 16, 40, 2, 20000)
    ok2 = compare("cluster", 230, 270, 48400, 48700)
    print("T4 VALIDATION", "PASS" if ok1 and ok2 else "FAIL")


if __name__ == "__main__":
    main()
