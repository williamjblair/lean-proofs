#!/usr/bin/env python3
"""Cover -> witness. Given shifts {p: c_p} covering the torus, produce m:
   m == -g_p^{-c_p} (mod p) for each p, m == 1 (mod 6).
Then verify: for all (k,l) in a large box, some p | 2^k 3^l m + 1, p < N_{k,l}."""
import json, sys, math
from sympy import primitive_root, discrete_log, isprime
from sympy.ntheory.modular import crt

data = json.load(open(sys.argv[1]))
N = data['N']; shifts = {int(p): c for p, c in data['shifts'].items()}
assert data['uncovered'] == 0, "not a full cover!"
fam = {int(p): n for p, n in json.load(open(f"harvest_N{N}.json")).items()}
mods, rems = [2, 3], [1, 1]
for p, c in shifts.items():
    n = fam[p]
    g0 = primitive_root(p); g = pow(g0, (p - 1) // n, p)
    t = pow(g, c, p)                    # tile: 2^k 3^l == t (mod p) => want -1/m == t
    m_p = (-pow(t, -1, p)) % p
    mods.append(p); rems.append(m_p)
m, M = crt(mods, rems)
m = int(m)
print(f"m = {m}  ({len(str(m))} digits)")
assert math.gcd(m, 6) == 1 and m > max(shifts)
# verification over a box (cover is periodic mod N in both k and l)
bad = []
for k in range(N):
    for l in range(N):
        ok = False
        for p, c in shifts.items():
            if (2 ** 0):  # cheap: check divisibility directly mod p
                if (pow(2, k, p) * pow(3, l, p) * m + 1) % p == 0: ok = True; break
        if not ok: bad.append((k, l)); 
        if len(bad) > 5: break
    if len(bad) > 5: break
print("verification box:", "CLEAN — m is a witness; #203 = YES" if not bad else f"FAILED at {bad[:3]}")
