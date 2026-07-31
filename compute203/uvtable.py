#!/usr/bin/env python3
"""Each pool prime gives a linear-form tile: phi_p(k,l) = u*k + v*l mod n,
where n = |H_p|, u = dlog of 2, v = dlog of 3 wrt a generator of H_p.
Compute (u, v, n) for every pool prime; sanity-check by brute force."""
import json, math
from sympy import n_order, primitive_root, discrete_log

pool = {int(p): o for p, o in json.load(open("pool_H720.json")).items()}
table = {}
for p, n in sorted(pool.items()):
    g0 = primitive_root(p)
    # H_p = <2,3> is the subgroup of order n; generator g = g0^((p-1)/n)
    g = pow(g0, (p - 1) // n, p)
    u = discrete_log(p, 2, g)      # 2 = g^u mod p
    v = discrete_log(p, 3, g)      # 3 = g^v mod p
    assert pow(g, u, p) == 2 % p and pow(g, v, p) == 3 % p
    assert math.gcd(math.gcd(u, v), n) == 1, (p, u, v, n)  # <2,3> generates H
    table[p] = (u, v, n)
json.dump(table, open("uvtable.json", "w"))
print(f"{len(table)} tiles computed; samples:")
for p in [5, 7, 11, 23, 13, 17, 19, 47, 431]:
    if p in table: print(f"  p={p}: phi(k,l) = {table[p][0]}k + {table[p][1]}l  mod {table[p][2]}")
# brute sanity: p=5 tile must equal {(k,l): 2^k 3^l = fixed residue mod 5}
p, (u, v, n) = 5, table[5]
for k in range(8):
    for l in range(8):
        lhs = (u*k + v*l) % n
        rhs = pow(2, k, p) * pow(3, l, p) % p
        # same phi-value <=> same residue
import itertools
vals = {}
ok = True
for k, l in itertools.product(range(20), repeat=2):
    key = (table[5][0]*k + table[5][1]*l) % table[5][2]
    r = pow(2, k, 5) * pow(3, l, 5) % 5
    if key in vals and vals[key] != r: ok = False
    vals[key] = r
print("p=5 tile structure sanity:", "OK" if ok else "FAIL")
