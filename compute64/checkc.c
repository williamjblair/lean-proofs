/* checkc.c — Erdős–Gyárfás (Erdős #64) counterexample sieve.
 *
 * Reads graph6 graphs on stdin (n <= 62). For each graph, decides whether it
 * contains a cycle of length exactly L for each L in {4, 8, 16, 32} with
 * L <= n. Graphs containing NO such cycle (counterexample candidates, given
 * min degree >= 3 which the generator guarantees) are echoed to stdout.
 *
 * Exact-length-L cycle test: for each vertex v taken as the minimum-labeled
 * vertex of a candidate cycle, DFS over simple paths from v through vertices
 * > v, pruned by BFS distance back to v (full-graph distance is a lower
 * bound for the restricted distance, so pruning is sound), closing the cycle
 * at depth L-1 via an edge back to v.
 *
 * Progress/stats go to stderr.
 */
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <stdlib.h>

typedef uint64_t bs;

static int n;
static bs adj[64];
static int deg[64], nbr[64][64];
static int dist_v[64];
static int target_len;

/* parse one graph6 line; returns n or -1 */
static int parse_g6(const char *s) {
    int c = s[0];
    if (c == ':' || c == '&') return -1;      /* sparse6/digraph6 unsupported */
    int nn = c - 63;
    const char *p = s + 1;
    if (nn == 63) { /* extended: n >= 63 unsupported here */ return -1; }
    memset(adj, 0, sizeof adj);
    int need = nn * (nn - 1) / 2;
    int bit = 0, i = 0, j = 1; /* column-major upper triangle: (i<j) pairs ordered by j then i */
    while (bit < need) {
        int ch = *p++ - 63;
        if (ch < 0) return -1;
        for (int k = 5; k >= 0 && bit < need; k--, bit++) {
            if ((ch >> k) & 1) {
                adj[i] |= (bs)1 << j;
                adj[j] |= (bs)1 << i;
            }
            i++;
            if (i == j) { i = 0; j++; }
        }
    }
    return nn;
}

/* C4 exists iff some pair shares >= 2 neighbors */
static int has_c4(void) {
    for (int i = 0; i < n; i++)
        for (int j = i + 1; j < n; j++)
            if (__builtin_popcountll(adj[i] & adj[j]) >= 2) return 1;
    return 0;
}

/* BFS distances from v over the whole graph */
static void bfs(int v) {
    for (int i = 0; i < n; i++) dist_v[i] = 99;
    int q[64], head = 0, tail = 0;
    dist_v[v] = 0; q[tail++] = v;
    while (head < tail) {
        int u = q[head++];
        bs m = adj[u];
        while (m) {
            int w = __builtin_ctzll(m); m &= m - 1;
            if (dist_v[w] == 99) { dist_v[w] = dist_v[u] + 1; q[tail++] = w; }
        }
    }
}

static int vroot;
/* DFS: at vertex u, |path| = depth edges used, visited set vis (vertices > vroot plus vroot).
 * Want simple cycle of length target_len through vroot with all other vertices > vroot. */
static int dfs(int u, int depth, bs vis) {
    int remain = target_len - depth;
    if (remain == 1) return (adj[u] >> vroot) & 1;
    bs m = adj[u] & ~vis;
    while (m) {
        int w = __builtin_ctzll(m); m &= m - 1;
        if (w <= vroot) continue;
        if (dist_v[w] > remain - 1) continue;      /* can't get back in time */
        if (dfs(w, depth + 1, vis | ((bs)1 << w))) return 1;
    }
    return 0;
}

static int has_cycle_len(int L) {
    if (L > n) return 0;
    if (L == 4) return has_c4();
    target_len = L;
    for (int v = 0; v + L <= n + 0 && v < n; v++) {
        /* need L-1 vertices > v: v <= n - L */
        if (v > n - L) break;
        bfs(v);
        vroot = v;
        if (dfs(v, 0, (bs)1 << v)) return 1;
    }
    return 0;
}

int main(int argc, char **argv) {
    char line[4096];
    long long total = 0, no4 = 0, no48 = 0, survivors = 0;
    FILE *c48out = NULL;
    const char *c48path = getenv("CHECKC_C48FREE_PATH");
    if (c48path) c48out = fopen(c48path, "w");
    while (fgets(line, sizeof line, stdin)) {
        size_t len = strlen(line);
        while (len && (line[len-1] == '\n' || line[len-1] == '\r')) line[--len] = 0;
        if (!len) continue;
        n = parse_g6(line);
        if (n < 0) { fprintf(stderr, "unparsed: %s\n", line); continue; }
        total++;
        if (has_cycle_len(4)) continue;
        no4++;
        if (has_cycle_len(8)) continue;
        no48++;
        if (c48out) { fprintf(c48out, "%s\n", line); fflush(c48out); }
        if (has_cycle_len(16)) continue;
        if (has_cycle_len(32)) continue;
        survivors++;
        printf("%s\n", line);
        fflush(stdout);
    }
    fprintf(stderr, "total=%lld no_c4=%lld no_c4c8=%lld survivors=%lld\n",
            total, no4, no48, survivors);
    return 0;
}
