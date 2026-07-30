"""Brute-force verification of the structural claims, directly from the
definition of G (no shortcuts).  Everything below is exhaustive over a box.
"""
from math import gcd
from sympy import isprime          # only used as an independent primality oracle

N = 400          # box: 2 <= x,y <= N


def vertex(x, y):
    return gcd(x, y) == 1


def adm(x, y):
    return (vertex(x, y) and min(x, y) > 1
            and (not isprime(x) or not isprime(y)) and x > 1 and y > 1)


def composite(n):
    return n >= 4 and not isprime(n)


print(f"box 2..{N}")

# ---- claim 1: gcd(x,y)=1 forbids both even
bad = [(x, y) for x in range(2, N + 1) for y in range(2, N + 1)
       if vertex(x, y) and x % 2 == 0 and y % 2 == 0]
print("1. no vertex has both coords even:", not bad)

# ---- claim 2: horizontal edge => y odd ; vertical edge => x odd
h_even_y = 0
v_even_x = 0
for x in range(2, N):
    for y in range(2, N):
        if vertex(x, y) and vertex(x + 1, y) and y % 2 == 0:
            h_even_y += 1
        if vertex(x, y) and vertex(x, y + 1) and x % 2 == 0:
            v_even_x += 1
print("2. horizontal edges on even rows:", h_even_y,
      "| vertical edges on even columns:", v_even_x)

# ---- claim 3: composite condition is free off the odd-odd sublattice
viol = 0
for x in range(2, N + 1):
    for y in range(2, N + 1):
        if not vertex(x, y):
            continue
        if (x % 2 == 0 or y % 2 == 0) and min(x, y) >= 3:
            if not (composite(x) or composite(y)):
                viol += 1
print("3. admissible-condition violations at vertices with an even coord >=4"
      " and min>=3:", viol)

# ---- claim 4: A (restricted to x,y>=3) is the subdivision of H
#      i.e. every admissible vertex with an even coordinate has exactly the two
#      hub neighbours, and the H edge rule matches.
mismatch = 0
for a in range(3, N, 2):
    for b in range(3, N, 2):
        hub = (gcd(a, b) == 1 and not (isprime(a) and isprime(b)))
        # H horizontal edge a -> a+2
        if a + 2 <= N:
            hub2 = (gcd(a + 2, b) == 1
                    and not (isprime(a + 2) and isprime(b)))
            h_edge = hub and hub2 and gcd(a + 1, b) == 1
            # G path a -> a+1 -> a+2 through the connector
            g_path = (adm(a, b) and adm(a + 1, b) and adm(a + 2, b)
                      and vertex(a, b) and vertex(a + 1, b)
                      and vertex(a + 2, b))
            if h_edge != g_path:
                mismatch += 1
        if b + 2 <= N:
            hub2 = (gcd(a, b + 2) == 1
                    and not (isprime(a) and isprime(b + 2)))
            v_edge = hub and hub2 and gcd(a, b + 1) == 1
            g_path = (adm(a, b) and adm(a, b + 1) and adm(a, b + 2))
            if v_edge != g_path:
                mismatch += 1
print("4. H-edge vs G-two-step mismatches (3<=a,b<=N):", mismatch)

# ---- claim 5: rows divisible by 3 admit no horizontal hop; columns divisible
#      by 3 admit no vertical hop
h3 = sum(1 for a in range(3, N - 2, 2) for b in range(3, N, 2)
         if b % 3 == 0 and gcd(a, b) == 1 and gcd(a + 1, b) == 1
         and gcd(a + 2, b) == 1)
v3 = sum(1 for a in range(3, N, 2) for b in range(3, N - 2, 2)
         if a % 3 == 0 and gcd(a, b) == 1 and gcd(a, b + 1) == 1
         and gcd(a, b + 2) == 1)
print("5. horizontal hops on rows divisible by 3:", h3,
      "| vertical hops on columns divisible by 3:", v3)

# ---- claim 6: the barrier.  at a = product of odd primes <= B there is no
#      vertex (a,b) with b <= B at all.
from sympy import primerange
for B in (13, 17, 19, 23):
    a = 1
    for p in primerange(3, B + 1):
        a *= p
    rows = [b for b in range(3, B + 1, 2) if gcd(a, b) == 1]
    print(f"6. B={B}: a={a}  odd rows b<=B coprime to a: {rows}")
