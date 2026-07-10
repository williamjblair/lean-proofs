#!/usr/bin/env python3
"""Independent exact brute-force check of k5_tight_scan.c on a small range.

Window: A <= c*d <= A+4 tested EXACTLY via the quintic inequalities
    4 A^5 <= (A+d)^5        (<=> A <= c d)
    (A+d+4)^5 <= 4 (A+4)^5  (<=> c d <= A + 4)
Rows: A+j-1 | R_j(d) = prod_{i=1..5}(d+i-j), exact big-int arithmetic.
"""
import subprocess, sys

D_MAX = 300000

def window_As(d):
    # exact: A in [c d - 4, c d]; c*d ~ 3.13*d
    A0 = (3129812960126669571 * d) // 10**18
    out = []
    for A in range(A0 - 6, A0 + 3):
        if A < 1:
            continue
        if 4 * A**5 <= (A + d)**5 and (A + d + 4)**5 <= 4 * (A + 4)**5:
            out.append(A)
    return out

def R(j, d):
    p = 1
    for i in range(1, 6):
        p *= (d + i - j)
    return p

hits = []
maxwin = 0
for d in range(5, D_MAX):
    As = window_As(d)
    maxwin = max(maxwin, len(As))
    for A in As:
        if R(1, d) % A == 0 and R(2, d) % (A + 1) == 0:
            level = 2
            if R(3, d) % (A + 2) == 0:
                level = 3
                if R(4, d) % (A + 3) == 0:
                    level = 4
                    if R(5, d) % (A + 4) == 0:
                        level = 5
            hits.append((d, A, level))

print("max window size:", maxwin)
print("python hits (d, A, level):")
for h in hits:
    print("  ", h)

# compare with C scanner
res = subprocess.run(["./k5_tight_scan", "5", str(D_MAX), "2"],
                     capture_output=True, text=True,
                     cwd="/Users/williamblair/personal/lean-proofs/compute/theory")
c_hits = []
for line in res.stdout.strip().splitlines():
    parts = line.split()
    c_hits.append((int(parts[0]), int(parts[1]), int(parts[4])))

py = set(hits); cc = set(c_hits)
print("C hits match python:", py == cc)
if py != cc:
    print("  py-only:", sorted(py - cc))
    print("  c-only :", sorted(cc - py))
    sys.exit(1)
