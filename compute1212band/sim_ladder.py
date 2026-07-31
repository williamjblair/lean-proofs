#!/usr/bin/env python3
"""O5: strategy simulation. Travel rightward in H using ONLY the ladder moves:
rows = z-rough odd composites in [z^2, z^2+B]; runs; sidesteps to nearby rows;
ladder switches (multi-row); count events and failures.

H rules (verified reduction): (a,b)~(a+2,b) iff gcd((a+1)(a+2), b)=1;
(a,b)~(a,b+2) iff gcd(a, (b+1)(b+2))=1. Hubs need gcd(a,b)=1, not both prime.
A climb from (a,R) to (a,R2) sweeps b in [R,R2]: needs gcd(a, m)=1 for all
m in (min..max+?) -- sufficient and clean: gcd(a, m)=1 for all m in
[min(R,R2), max(R,R2)] (covers every intermediate hub and parity vertex).
"""
import math, sys
from sympy import isprime, primerange

def rough_comp_rows(z, lo, hi):
    small = list(primerange(2, z + 1))
    rows = []
    for n in range(lo | 1, hi, 2):
        if any(n % p == 0 for p in small): continue
        if isprime(n): continue
        rows.append(n)
    return rows

def factors_gt(n, z):
    fs, m = [], n
    for p in primerange(2, int(math.isqrt(n)) + 1):
        if m % p == 0:
            fs.append(p)
            while m % p == 0: m //= p
    if m > 1: fs.append(m)
    return fs

def climb_ok(a, r1, r2):
    lo, hi = min(r1, r2), max(r1, r2)
    return all(math.gcd(a, m) == 1 for m in range(lo, hi + 1))

def run_block(a, pf):
    """next blocked hub-step column >= a on this row: step a->a+2 blocked iff
    (a+1) or (a+2) share a factor. Return smallest a' >= a with step blocked."""
    best = None
    for p in pf:
        # a'+1 ≡ 0 mod p  -> a' ≡ -1;  a'+2 ≡ 0 -> a' ≡ -2 (mod p)
        for r in (-1, -2):
            c = a + ((r - a) % p)
            if best is None or c < best: best = c
    return best

def simulate(z, x_target, B=None, max_ladder=40, seg_search=4000):
    lo = z * z
    B = B or 6000
    rows = rough_comp_rows(z, lo, lo + B)
    pf = {r: factors_gt(r, z) for r in rows}
    print(f"z={z}: {len(rows)} rows in [{lo},{lo+B}], gaps max="
          f"{max(b-a for a,b in zip(rows,rows[1:]))}")
    i = 0
    x = lo + 1  # start column; make it odd, gcd with row handled on the fly
    events = dict(sidestep=0, ladder=0, fail=0, run_len=0)
    while x < x_target:
        R = rows[i]
        b = run_block(x, pf[R])
        if b >= x_target: x = x_target; break
        events['run_len'] += b - x
        # need a climb column a in (b - seg_search, b], odd, on-run, to some row j != i
        moved = False
        order = sorted(range(max(0, i - max_ladder), min(len(rows), i + max_ladder + 1)),
                       key=lambda j: abs(rows[j] - R))
        # search the full open segment of row R ending at block b
        for a in range(b - (1 - b % 2), max(0, b - seg_search), -2):
            if run_block(a, pf[R]) < b:  # a lies behind an earlier block: segment over
                break
            if math.gcd(a, R) != 1: continue
            for j in order:
                if j == i: continue
                if math.gcd(a, rows[j]) != 1: continue
                if climb_ok(a, R, rows[j]):
                    if abs(j - i) == 1: events['sidestep'] += 1
                    else: events['ladder'] += 1
                    i, x, moved = j, a, True
                    break
            if moved: break
        if not moved:
            events['fail'] += 1
            x = b + 2  # teleport past (records the failure; = a move-4 repair)
    att = events['sidestep'] + events['ladder'] + events['fail']
    print(f"  reached x={x}: attempts={att} sidesteps={events['sidestep']} "
          f"ladder={events['ladder']} FAILURES={events['fail']} "
          f"(fail rate {events['fail']/max(1,att):.2%})")
    return events

if __name__ == '__main__':
    xt = int(sys.argv[-1]) if len(sys.argv) > 2 else 200_000
    for z in (int(a) for a in (sys.argv[1:-1] or ['20'])):
        simulate(z, max(xt, z * z + 50_000))
