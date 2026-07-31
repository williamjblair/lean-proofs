#!/usr/bin/env python3
import math, json
from sympy import factorint, isprime, n_order
pool = {int(p): n for p, n in json.load(open('pool_merged.json')).items()}
new = {}
for j in range(1, 451):
    h = 11 * j
    g = math.gcd(pow(2, h) - 1, pow(3, h) - 1)
    for p in list(pool) + list(new):
        while g % p == 0: g //= p
    if g == 1: continue
    try: f = factorint(g, limit=10**6)
    except Exception: continue
    for q in f:
        if q in pool or q in new or not isprime(q): continue
        n = math.lcm(n_order(2, q), n_order(3, q))
        if n % 11 == 0 and n <= 10**5: new[q] = n
merged = {**pool, **new}
json.dump({str(p): n for p, n in merged.items()}, open('pool_merged.json','w'))
el = sorted(n for n in new.values())
print(f"harvest11: +{len(new)} primes with 11|n; new n values: {el[:30]}")
print(f"pool now {len(merged)} primes, density {sum(1.0/n for n in merged.values()):.4f}")
d11 = sum(1.0/n for n in merged.values() if n % 11 == 0)
print(f"11-part density: {d11:.4f} (need ~ >= (1/11)*(1+overlap) ~ 0.10+)")
