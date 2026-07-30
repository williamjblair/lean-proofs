#!/usr/bin/env python3
"""Erdos 1139 numerics: gaps in the sequence of n with Omega(n) <= 2 (multiplicity), including n=1.

Sieve to N=10^8, compute Omega(n) with multiplicity, extract u_k, print gap records
and gap/log k at each record.
"""
import numpy as np
import time

N = 100_000_000
t0 = time.time()

# 1. prime sieve
is_comp = np.zeros(N + 1, dtype=bool)
is_comp[:2] = True
for p in range(2, int(N**0.5) + 1):
    if not is_comp[p]:
        is_comp[p*p::p] = True
primes = np.flatnonzero(~is_comp)
print(f"pi({N}) = {len(primes)}  ({time.time()-t0:.0f}s)", flush=True)

# 2. Omega with multiplicity: += 1 for every prime power p^j
om = np.zeros(N + 1, dtype=np.uint8)
for i, p in enumerate(primes):
    p = int(p)
    pj = p
    while pj <= N:
        om[pj::pj] += 1
        pj *= p
    if (i + 1) % 500_000 == 0:
        print(f"  omega pass: {i+1} primes ({time.time()-t0:.0f}s)", flush=True)
print(f"Omega sieve done ({time.time()-t0:.0f}s)", flush=True)

mask = om <= 2
mask[0] = False  # n >= 1; n=1 has Omega=0, included
u = np.flatnonzero(mask)
K = len(u)
print(f"count of Omega<=2 up to {N}: {K}")

expected = [1,2,3,4,5,6,7,9,10,11,13,14,15,17,19,21,22,23,25,26,29,31,33,34,35,37,38,39,41,43]
got = u[:30].tolist()
print("first 30 terms:", got)
print("A037143 match:", got == expected)

gaps = np.diff(u)
print(f"max gap up to {N}: {gaps.max()}")

rec = 0
print(f"{'k':>12} {'u_k':>12} {'gap':>5} {'gap/log k':>10} {'gap/log u_k':>12}")
for i in np.flatnonzero(gaps > 1):
    g = int(gaps[i])
    if g > rec:
        rec = g
        k = i + 1  # u_k = u[i] under 1-based indexing
        print(f"{k:>12} {int(u[i]):>12} {g:>5} {g/np.log(k):>10.4f} {g/np.log(u[i]):>12.4f}")

i0 = np.searchsorted(u, N // 10)
print(f"mean gap in [{N//10},{N}]: {gaps[i0:].mean():.4f}; log(N)/loglog(N) = {np.log(N)/np.log(np.log(N)):.4f}")
print(f"total time {time.time()-t0:.0f}s")
