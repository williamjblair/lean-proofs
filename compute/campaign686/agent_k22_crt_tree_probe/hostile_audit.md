# Hostile audit: k=22 simple CRT-tree probe

## Claim under audit

This probe does **not** prove the k=22 row and does **not** provide a Lean
certificate. It answers one bounded engineering question about the exact
`d >= 250` local sieve already banked in
`agent_k22_sieve_probe`.

Let

```text
B = 3,795,146,531,
t mod 46 in {17, 21, 25, 29},
1 <= t <= B.
```

Use the 132 nontrivial prime masks `A_p` with `p <= 953` reconstructed by the
banked verifier. A **simple CRT tree** starts with the four classes modulo 46.
At a live node it chooses one unused active prime `p`, makes one child for each
locally allowed residue in `A_p`, and discards a child exactly when its least
positive CRT representative exceeds `B`.

The exact conclusion is:

> Every such tree has at least 3,047,220 live nodes when every path has used
> three active prime masks. Therefore no proof in this explicit
> one-prime-at-a-time tree model can stay below the requested 1,000,000 simple
> nodes/checks.

This remains true when the second prime is chosen separately at every
first-level node and the third prime is chosen separately at every
second-level node.

## Exact result

The base classes contain exactly:

```text
a = 17: 82,503,186 integers
a = 21: 82,503,186 integers
a = 25: 82,503,185 integers
a = 29: 82,503,185 integers
total:   330,012,742 integers
```

The active-mask inventory has SHA-256

```text
48c2171142fd02c807946a070c6ddf1d56bf5c3693d48761a8b41688f130ed12
```

The scan covers all `C(132,2) = 8,646` unordered first-prime pairs and all
130 possible unused third primes for each pair. There are 1,123,980 logical
pair/third-prime tests. The branch-and-bound implementation performs 170,728
exact cyclic-window evaluations; every skipped evaluation has a cardinality
lower bound at least as large as the best exact value already found for its
pair.

The global minimum is attained by the prefix `(83,97,101)`:

| level | combined modulus | live residue nodes |
|---:|---:|---:|
| base | 46 | 4 |
| after 83 | 3,818 | 324 |
| after 97 | 370,346 | 30,780 |
| after 101 | 37,404,946 | 3,047,220 |

The corresponding allowed-mask sizes are `(81,95,99)`. The least number of
integers in a second-level node is

```text
floor(B / 370,346) = 10,247 > 101.
```

Consequently every allowed residue modulo 101 occurs in every second-level
node, so the last count is exactly

```text
4 * 81 * 95 * 99 = 3,047,220.
```

The full adaptive scan proves that no other pair followed by any third mask
has a smaller uniform lower bound. It also finds zero pairs for which an
adaptive third prime can kill a node outright.

Canonical payload SHA-256:

```text
7c6e19d2b5e44ae6f5f0fdf600e0e1c4a663189d17820d1bebdf486571088673
```

## Why the interval calculation is valid

After two distinct active primes `p1,p2`, put

```text
M = 46*p1*p2.
```

The largest possible two-prime modulus in the inventory is

```text
46*947*953 = 41,514,586 < B.
```

Thus every CRT combination through level two has a positive representative
at most `M`, hence is live.

Write a second-level class using its least positive representative as

```text
t = r + M*q,  1 <= r <= M.
```

It contains at least `L = floor(B/M)` consecutive nonnegative `q` values. For
an unused prime `p`, its local condition is exactly

```text
q in M^(-1) A_p - M^(-1) r  (mod p).
```

Multiplication by `M^(-1)` permutes residues, and the term involving `r` is a
translation. If `L >= p`, all `|A_p|` allowed residue classes make live CRT
children. If `L < p`, the verifier constructs the multiplied mask and takes
the minimum number of marked residues in any cyclic interval of length `L`.
Minimizing over all translations can only weaken the lower bound, so it is
valid uniformly for every actual node.

For pruning a third-prime calculation when `L < p`, the verifier uses

```text
hits >= max(0, |A_p| + L - p).
```

This is inclusion-exclusion for an allowed set of size `|A_p|` and an
interval of size `L` inside a universe of size `p`. A candidate is skipped
only if this lower bound cannot improve the pair's current best value.

For adaptivity, define `h(p1,p2)` as the minimum third-level child bound over
every unused third prime and every translation. The exhaustive result is

```text
|A_p1| * |A_p2| * h(p1,p2) >= 761,805
```

for every pair. If different first-level children choose different `p2`, the
same inequality applies term by term after division by the fixed
`|A_p1|`; summing over all `|A_p1|` children restores the 761,805 lower bound
for that base root. There are four base roots, giving 3,047,220. Choosing a
different `p1` for each base root does not change the bound.

## Dependency tree and verdicts

1. **Banked k=22 polynomial and local-mask reconstruction** — PASS as an
   exact-Python dependency. The new verifier imports the banked implementation
   and freezes the complete active-mask inventory by SHA-256.
2. **Inclusive bound and mod-46 compression** — PASS. All four arithmetic
   progression lengths and their sum are recomputed.
3. **No interval pruning through two primes** — PASS. The exact maximum
   modulus is 41,514,586, strictly below `B`.
4. **`t = r+Mq` transformation** — PASS. The inverse exists because all
   selected primes are distinct and neither divides 46.
5. **Short-interval third-child bound** — PASS in exact arithmetic. The cyclic
   scan uses byte values 0 and 1 and integer sums only.
6. **All 8,646 prime pairs and adaptive third choices** — PASS in the verifier.
   The exact global lower bound is 3,047,220.
7. **Sub-million explicit CRT certificate** — FAIL. The third level alone is
   already more than three times the requested cap.
8. **Kernel-backed k=22 closure** — NOT PRESENT. No theorem is added and no
   axiom-gate claim is made.

## Boundary and falsification checks

- **Residue nodes versus candidate integers:** one CRT residue class counts as
  one node even if it contains many integers. When `L >= p`, the verifier
  returns `|A_p|`, not the number of integer hits. A dedicated regression test
  freezes this correction.
- **Inclusive upper endpoint:** progression lengths use
  `floor((B-a)/46)+1`, and node lengths use the valid lower bound
  `floor(B/M)` for `1 <= r <= M`.
- **Least positive representative zero class:** residue zero is represented by
  `M`, so every class modulo `M < B` is live; there is no hidden zero endpoint.
- **Translation uniformity:** every occurrence of “uniform” above is the
  quantified minimum over all `p` cyclic translations, not a density
  heuristic.
- **Adaptive prime order:** `p2` and `p3` may vary node by node. The product
  inequality is applied after taking the minimum over all such choices.
- **Repeated or full masks:** reusing a prime adds no information. A full mask
  cannot reduce a live-node count. Omitting both cannot invalidate a lower
  bound for useful one-prime-at-a-time trees.
- **Floating point:** none is used.

## Exact remaining gap

The artifact rules out only the explicit one-unused-prime-per-node CRT model
over the 132 active masks with `p <= 953`. It does **not** rule out a compact
proof that uses any of the following:

- a batched composite-modulus checker whose kernel cost is proved separately;
- a DAG or symbolic interval argument that shares work across CRT nodes;
- new prime masks above 953 or a new algebraic restriction on `(v,w)`;
- a theorem proving the packed bit sieve without enumerating its represented
  candidates.

The single quantified positive lemma still needed for this route is:

> There exists a kernel-checkable certificate, using at most 1,000,000 simple
> proof steps (or another explicitly bounded feasible resource), that proves
> no integer `t` with `1 <= t <= 3,795,146,531` survives all 132 frozen local
> masks after the mod-46 compression.

The present explicit CRT-tree construction cannot witness that lemma.

## Reproduction

```bash
PYTHONDONTWRITEBYTECODE=1 python3 \
  compute/campaign686/agent_k22_crt_tree_probe/k22_crt_tree_probe_verify.py \
  --pretty

PYTHONDONTWRITEBYTECODE=1 python3 -m pytest -q -p no:cacheprovider \
  compute/campaign686/agent_k22_crt_tree_probe/test_k22_crt_tree_probe_verify.py
```
