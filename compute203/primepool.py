#!/usr/bin/env python3
"""W2: algebraic prime pool for Erdos #203.
Primes usable in a 2D covering satisfy H_p = <2,3> small;
|H_p| divides h  <=>  p | g_h := gcd(2^h - 1, 3^h - 1).
Enumerate h <= H, factor g_h (typically small), dedupe primes,
compute |H_p| = lcm(ord_p 2, ord_p 3) and the density pool."""
import sys, math, json
from sympy import factorint, n_order
from functools import lru_cache

H = int(sys.argv[1]) if len(sys.argv) > 1 else 720
pool = {}   # p -> |H_p|
hard = []   # composite cofactors we couldn't factor fast
for h in range(1, H + 1):
    g = math.gcd(pow(2, h) - 1, pow(3, h) - 1)
    if g == 1: continue
    # factor g: pull small factors; anything left large goes to sympy with limit
    try:
        f = factorint(g, limit=10**6)
    except Exception:
        continue
    for q, e in f.items():
        if q in pool: continue
        # q may be composite (unfactored cofactor)
        from sympy import isprime
        if not isprime(q):
            if q < 10**30:
                try:
                    for qq in factorint(q):
                        if qq not in pool:
                            o = math.lcm(n_order(2, qq), n_order(3, qq))
                            pool[qq] = o
                except Exception:
                    hard.append((h, q))
            else:
                hard.append((h, q))
            continue
        o = math.lcm(n_order(2, q), n_order(3, q))
        pool[q] = o
dens = sorted(pool.items(), key=lambda kv: kv[1])
total = sum(1.0/o for _, o in dens)
print(f"H={H}: {len(pool)} primes in pool, {len(hard)} hard cofactors skipped")
print(f"TOTAL DENSITY Sigma 1/|H_p| = {total:.4f}  ({'>= 1: COVERING POSSIBLE in principle' if total >= 1 else '< 1: pool insufficient at this H'})")
print("smallest |H_p| primes:")
for p, o in dens[:25]:
    print(f"  p={p:<12} |H_p|={o}")
json.dump({str(p): o for p, o in pool.items()}, open(f"pool_H{H}.json", "w"))
# cumulative density by |H_p| cutoff
import itertools
cum = 0.0
cuts = [12, 24, 48, 120, 240, 720, 5040, 10080, 55440, 720720]
ci = 0
for p, o in dens:
    cum += 1.0/o
    while ci < len(cuts) and o > cuts[ci]:
        ci += 1
for c in cuts:
    s = sum(1.0/o for _, o in dens if o <= c)
    n = sum(1 for _, o in dens if o <= c)
    print(f"  |H_p| <= {c:<7}: {n:>4} primes, density {s:.4f}")
