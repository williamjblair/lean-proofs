"""Reference implementation + validation for the Erdős #64 sieve.

has_cycle_len(G, L): does G contain a simple cycle of length exactly L?
Brute reference via networkx cycle enumeration for small graphs, plus an
independent DFS implementation mirroring checkc.c. Used to cross-validate
the C checker on random and named graphs.

For large structured graphs (census scans) use has_cycle_len_mitm, a
meet-in-the-middle variant that handles L up to 32 on graphs of arbitrary
order (bitset intersections over half-paths).
"""
from __future__ import annotations
import itertools
import random
import networkx as nx


def has_cycle_len_dfs(G: nx.Graph, L: int) -> bool:
    """Exact-length-L simple cycle detection, min-vertex-rooted DFS."""
    nodes = sorted(G.nodes())
    idx = {v: i for i, v in enumerate(nodes)}
    adj = {v: set(G[v]) for v in nodes}
    if L > len(nodes):
        return False

    for v in nodes:
        # BFS distances from v (full graph — sound pruning lower bound)
        dist = {v: 0}
        frontier = [v]
        while frontier:
            nxt = []
            for u in frontier:
                for w in adj[u]:
                    if w not in dist:
                        dist[w] = dist[u] + 1
                        nxt.append(w)
            frontier = nxt

        def dfs(u, depth, visited):
            remain = L - depth
            if remain == 1:
                return v in adj[u]
            for w in adj[u]:
                if w in visited or idx[w] <= idx[v]:
                    continue
                if dist.get(w, 99) > remain - 1:
                    continue
                if dfs(w, depth + 1, visited | {w}):
                    return True
            return False

        if dfs(v, 0, {v}):
            return True
    return False


def has_cycle_len_bruteforce(G: nx.Graph, L: int) -> bool:
    """Ground truth via exhaustive simple-cycle enumeration (small graphs)."""
    for cyc in nx.simple_cycles(G, length_bound=L):
        if len(cyc) == L:
            return True
    return False


def has_cycle_len_mitm(G: nx.Graph, L: int) -> bool:
    """Meet-in-the-middle: cycle of length L = two vertex-disjoint paths of
    length L//2 between an ordered anchor pair. Handles even L up to ~32 on
    larger sparse graphs. For odd halves use L = a + b with a = L//2, b = L - a.
    """
    assert L >= 3
    nodes = sorted(G.nodes())
    idx = {v: i for i, v in enumerate(nodes)}
    adj = {v: sorted(G[v]) for v in nodes}
    a, b = L // 2, L - L // 2

    def paths_from(v, length, min_idx):
        """All simple paths of `length` edges from v with interior+end > min_idx.
        Yields (endpoint, frozenset(interior))."""
        out = []
        def rec(u, depth, visited):
            if depth == length:
                out.append((u, visited))
                return
            for w in adj[u]:
                if idx[w] <= min_idx or w in visited:
                    continue
                rec(w, depth + 1, visited | {w})
        rec(v, 0, frozenset())
        return out

    for v in nodes:
        mi = idx[v]
        pa = {}
        for end, interior in paths_from(v, a, mi):
            pa.setdefault(end, []).append(interior - {end})
        for end, interior_b in paths_from(v, b, mi):
            if end not in pa:
                continue
            ib = interior_b - {end}
            for ia in pa[end]:
                if not (ia & ib):
                    # both paths v -> end, interiors disjoint, lengths a+b = L
                    if a >= 1 and b >= 1 and end != v:
                        return True
    return False


def power2_cycle_free(G: nx.Graph, method=has_cycle_len_dfs) -> bool:
    n = G.number_of_nodes()
    k = 4
    while k <= n:
        if method(G, k):
            return False
        k *= 2
    return True


def validate(trials: int = 400, seed: int = 64) -> None:
    rng = random.Random(seed)
    named = {
        "K4": nx.complete_graph(4),
        "K33": nx.complete_bipartite_graph(3, 3),
        "Petersen": nx.petersen_graph(),
        "Heawood": nx.heawood_graph(),
        "Pappus": nx.pappus_graph(),
        "Dodecahedral": nx.dodecahedral_graph(),
        "McGee": nx.LCF_graph(24, [12, 7, -7], 8),
        "TutteCoxeter": nx.LCF_graph(30, [-13, -9, 7, -7, 9, 13], 5),
    }
    for name, G in named.items():
        for L in (4, 8, 16):
            if L > G.number_of_nodes():
                continue
            ref = has_cycle_len_bruteforce(G, L)
            got = has_cycle_len_dfs(G, L)
            mitm = has_cycle_len_mitm(G, L)
            assert ref == got == mitm, (name, L, ref, got, mitm)
        print(f"  {name}: powers-of-2-free = {power2_cycle_free(G)}")
    for t in range(trials):
        n = rng.randint(5, 13)
        p = rng.uniform(0.15, 0.5)
        G = nx.gnp_random_graph(n, p, seed=rng.randint(0, 10**9))
        for L in (4, 5, 6, 7, 8, 9, 10):
            if L > n:
                continue
            ref = has_cycle_len_bruteforce(G, L)
            got = has_cycle_len_dfs(G, L)
            mitm = has_cycle_len_mitm(G, L)
            assert ref == got == mitm, (t, n, p, L, ref, got, mitm)
    print(f"  {trials} random graphs x lengths 4..10: DFS == MITM == brute. OK")


if __name__ == "__main__":
    validate()
