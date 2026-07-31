#!/usr/bin/env python3
"""Divisor-targeted harvest: for smooth N, compute g_h = gcd(2^h-1, 3^h-1)
for every h | N, factor, keep primes with |H_p| | N. These are ALL primes
usable in a pure-N covering (any prime with n_p | N divides g_{n_p}, and
n_p | N means h = n_p is a divisor of N we scanned)."""
import sys, math, json
from sympy import factorint, isprime, n_order

N = int(sys.argv[1]) if len(sys.argv) > 1 else 720720
divs = [d for d in range(1, N + 1) if N % d == 0]
print(f"N={N}: {len(divs)} divisors")
pool = {}
skipped = []
for h in sorted(divs):
    g = math.gcd(pow(2, h) - 1, pow(3, h) - 1)
    if g == 1: continue
    # remove known primes fast
    for p in list(pool):
        while g % p == 0: g //= p
    if g == 1: continue
    if g < 10**40 or isprime(g):
        try:
            f = factorint(g, limit=10**7)
        except Exception:
            skipped.append((h, g)); continue
        for q in f:
            if not isprime(q): skipped.append((h, q)); continue
            n = math.lcm(n_order(2, q), n_order(3, q))
            if N % n == 0 and q not in pool:
                pool[q] = n
    else:
        # large cofactor: pull small primes only
        f = factorint(g, limit=10**6)
        big = 1
        for q, e in f.items():
            if isprime(q):
                n = math.lcm(n_order(2, q), n_order(3, q))
                if N % n == 0 and q not in pool: pool[q] = n
            else: big = q
        if big > 1: skipped.append((h, big))
dens = sum(1.0/n for n in pool.values())
print(f"harvest: {len(pool)} primes with n_p | N; density = {dens:.4f}")
print(f"skipped hard cofactors: {len(skipped)} (at h={[h for h,_ in skipped[:10]]})")
from collections import Counter
cnt = Counter(pool.values())
print("n-value multiplicities (n: #primes):", dict(sorted(cnt.items())[:30]))
json.dump({str(p): n for p, n in pool.items()}, open(f"harvest_N{N}.json", "w"))
