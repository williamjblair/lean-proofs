"""Erdős #848 exact small-N ground truth.

f(N) = max |A|, A ⊆ [1,N], ab+1 not squarefree for ALL a,b ∈ A (incl. a=b).
Claim (Erdős–Sárközy / Sawhney): f(N) = |A7(N)| where A7 = {n ≡ 7 mod 25}.
This script computes f(N) exactly for N ≤ NMAX and reports every N where
f(N) != |A7(N)|, plus witness sets.
"""
import sys
import networkx as nx

NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 1000

# primes up to NMAX (squares up to NMAX^2+1 relevant)
sieve_lim = NMAX + 1
is_p = [True] * (sieve_lim + 1)
is_p[0] = is_p[1] = False
for i in range(2, int(sieve_lim ** 0.5) + 1):
    if is_p[i]:
        for j in range(i * i, sieve_lim + 1, i):
            is_p[j] = False
primes = [i for i, b in enumerate(is_p) if b]

def not_squarefree(v):
    for p in primes:
        if p * p > v:
            return False
        if v % (p * p) == 0:
            return True
    return False

# universe: self-condition
U = [a for a in range(1, NMAX + 1) if not_squarefree(a * a + 1)]
G = nx.Graph()
G.add_nodes_from(U)
for i, a in enumerate(U):
    for b in U[i + 1:]:
        if not_squarefree(a * b + 1):
            G.add_edge(a, b)
print(f"NMAX={NMAX}: |U|={len(U)}, edges={G.number_of_edges()}", flush=True)

# f(N) at each breakpoint (N where U gains an element); f is constant between
a7 = lambda N: sum(1 for n in range(1, N + 1) if n % 25 == 7)
prev_f = 0
bad = []
for idx in range(len(U)):
    N_lo = U[idx]                      # from this N the prefix includes U[:idx+1]
    N_hi = U[idx + 1] - 1 if idx + 1 < len(U) else NMAX
    H = G.subgraph(U[:idx + 1])
    clique, f = nx.max_weight_clique(H, weight=None)
    # f constant on [N_lo, N_hi]; |A7| may increment inside — check both ends
    for N in (N_lo, N_hi):
        if f != a7(N):
            # a7 changes inside the interval; find exact mismatch points
            pass
    for N in range(N_lo, N_hi + 1):
        if f != a7(N):
            bad.append((N, f, a7(N), sorted(clique)))
    prev_f = f
if bad:
    print(f"{len(bad)} mismatch N values; first 20:")
    for N, f, a7N, cl in bad[:20]:
        print(f"  N={N}: f={f} vs |A7|={a7N}  witness={cl if f > a7N else '...'}")
else:
    print(f"CLAIM HOLDS for all N <= {NMAX}: f(N) == |A7(N)| everywhere")
