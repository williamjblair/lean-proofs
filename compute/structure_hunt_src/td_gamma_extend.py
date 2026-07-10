"""Extend gamma_scaled_large_k.txt from k<=3000 to k<=6500.

Same certification as groundwork.gamma_scaled_certified: g = floor((4^(1/k)-1)*2^60)
certified by exact integer inequalities (2^60+g)^k < 4*2^(60k) < (2^60+g+1)^k.
Needed because for N <= 3*10^7 the d>=k window is feasible up to
k ~ sqrt(ln4 * N) ~ 6448.
"""
import multiprocessing as mp
import os
from decimal import Decimal, getcontext

OUT = "/Users/williamblair/personal/lean-proofs/compute/artifacts/structure_hunt"
PATH = os.path.join(OUT, "gamma_scaled_large_k.txt")
S = 1 << 60


def gamma_scaled_certified(k: int) -> int:
    getcontext().prec = 50
    guess = int((Decimal(4) ** (Decimal(1) / k) - 1) * S)
    target = 4 * (1 << (60 * k))
    g = guess
    while (S + g) ** k >= target:
        g -= 1
    while (S + g + 1) ** k <= target:
        g += 1
    assert (S + g) ** k < target < (S + g + 1) ** k
    return g


def worker(k):
    return k, gamma_scaled_certified(k)


def main():
    have = {}
    with open(PATH) as f:
        for line in f:
            k, g = line.split()
            have[int(k)] = int(g)
    missing = [k for k in range(16, 6501) if k not in have]
    print(f"have {len(have)}, computing {len(missing)} new entries")
    with mp.Pool(8) as pool:
        for k, g in pool.imap_unordered(worker, missing, chunksize=20):
            have[k] = g
    # re-certify a random sample of OLD entries too (cross-check groundwork)
    import random
    random.seed(686)
    for k in random.sample(range(16, 3001), 25):
        assert have[k] == gamma_scaled_certified(k), f"old gamma wrong k={k}"
    lines = [f"{k} {have[k]}" for k in sorted(have)]
    with open(PATH, "w") as f:
        f.write("\n".join(lines) + "\n")
    print(f"wrote {len(lines)} entries to {PATH}")


if __name__ == "__main__":
    main()
