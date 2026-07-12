# Hostile audit: even-`k` square-root closures

## Verdict

**PASS for the unconditional rows `k=16`, `k=18`, `k=20`, and `k=24`.
NOT a uniform proof for every even `k`.**

The public Lean theorems exclude the exact block-product equation for every
`d≥k` at the four named rows.  They therefore discharge the corresponding
Target 2 instances without assuming smoothness.  No theorem claims that the
finite list of rows is an induction.

## Dependency tree

| Node | Statement | Evidence | Verdict |
|---|---|---|---|
| A | Centered products represent the original blocks | `centeredBlockProduct_center`; row-specific expansion in Lean | PASS |
| B | `T²=c²S+D` for each displayed polynomial part | `ring` identities in Lean; independent exact generator | PASS |
| C | The equation implies `mX=D(w)-4D(v)` | A, B, and exact casts in each row theorem | PASS |
| D16 | `-16384<m<0` and `16384∣m` | Shifted positivity and the odd fixed divisor, all in Lean | PASS |
| D18a | `18≤d≤55` leaves exactly 1,311 ratio-window pairs, none a solution | Ordinary `decide` theorem `even18_finite_strip`; independent integer reproduction | PASS |
| D18b | `d≥56` implies `-242269137<m<0` and `81∣m` | 55-term shifted certificate, sign certificate, and `ZMod 81` divisor theorem in Lean | PASS |
| D18c | Every trapped `t` is excluded by 62 prime fields | Exact field masks; 190 bounded `w`-range shards plus the direct `p=19` table | PASS |
| D18d | The interval `1≤t≤2990976` is completely covered | Mod-19 classes `1,3,16,18`; 77 balanced `2^11` quotient scans; seven group glues | PASS |
| D20 | `-5853806<m<0`, `3200∣m`, and the 7-prime cover is empty | Lean shifted certificates and ordinary-decision tables | PASS |
| D24 | `-5993518490<m<0`, `10616832∣m`, and the 9-prime cover is empty | Lean shifted certificates and ordinary-decision tables | PASS |
| U | One symbolic theorem covers all even `k≥16` | No such symbolic coefficient/fixed-divisor bound is supplied | **NOT PROVED** |

Every PASS node used by a public theorem is reachable from its Lean source.
The only axioms printed by the public theorems are
`[propext, Classical.choice, Quot.sound]`.  No table uses `native_decide`.

## Quantified `k=18` audit

There is no hidden phrase such as “eventually positive”:

- the large-gap split is exactly `d≥56`;
- `4·12¹⁸<13¹⁸` then gives `n≥655`, `v≥1329`, and `w≥v+112`;
- the 55 shifted coefficients proving `m>-242269137` are all positive,
  with minimum `31010449536`;
- strict divisibility leaves exactly `242269136 / 81 = 2990976`
  positive values `m=-81t`;
- the kernel cover uses the exact prime order recorded by
  `KERNEL_COVER` in `k18_archimedean_closure_verify.py` and has survivor
  counts ending in `..., 3, 2, 1, 0`;
- the quotient decomposition has `t=19q+r`,
  `r∈{1,3,16,18}`, and `q<157420`;
- 77 balanced scans cover `0≤q<157696`, hence the required range;
- the small strip is exactly `18≤d≤55` with
  `12d-17≤n≤⌊(25d-3)/2⌋` and 1,311 pairs.

The smallest absolute centered-product error in the strip is

```
2307600880601197152466465133764408497930240000
```

at `(d,n)=(19,228)`.

## Falsification fixtures

| Fixture or caveat | Audit |
|---|---|
| `(984,3177026,4480)` row-prefix survivor | A divisor-skeleton survivor, not a solution of any proved exact row equation. |
| `n=48502` survivor cluster | The proofs use the full product equation, not a fixed row prefix. |
| MalekZ congruence family at `(N,k)=(4,5)` | Outside the four even rows; no uniform congruence claim is made. |
| Odd `d=1` telescopes at `k=9,15` | Outside both the even rows and the premises `d≥k`. |
| Smooth blocks may exist | Smoothness is neither assumed nor denied; the equation itself is excluded. |
| Two global `k=18` prime-field survivors | They are `t=2990977,3541067`; the strict large-gap bound ends at `2990976`, and the small gap is independently exhausted. |
| Local points through `p≤5000` for those survivors | Consistent with the proof: neither survivor lies in the final trapped interval. |

## Computational independence

All Python verifiers use exact integers and `fractions.Fraction`; NumPy is
used only for bounded integer indexing and Boolean masks.  The exact scripts
reconstruct `S,T,D`, fixed divisors, shifted coefficients, field masks,
survivor counts, and the finite strip.  The 62-prime kernel order is an
independently verified, lower-peak-memory alternative to the exact 35-prime
arithmetic cover; both end with no candidate in `1≤t≤2990976`.

The Lean field certificates use ordinary kernel reduction.  For primes above
19 the outer center is split into ranges of at most 128 values, so no single
field theorem enumerates a large `p²` table.  The final candidate cover uses a
balanced recursion tree rather than a three-million-deep `Fin` recursion.
The common mask-definition file also contains five inert search masks
(`73,89,113,157,167`) retained to keep the compiled table interface stable;
none is referenced by `even18CandidateAllowed` or the prime-condition theorem.
The active list has 62 distinct primes, asserted by the exact test suite.

## Reproduction

```bash
lake build ErdosProblems.Erdos686EvenK16
lake build ErdosProblems.Erdos686EvenK18
lake build ErdosProblems.Erdos686EvenK182024
python3 compute/campaign686/agent_t2_even_uniform_sqrt/k18_archimedean_closure_verify.py
python3 compute/campaign686/agent_t2_even_uniform_sqrt/k20_k24_cover_verify.py
python3 -m pytest -q compute/campaign686/agent_t2_even_uniform_sqrt
```

Expected public axiom output for each row:

```text
[propext, Classical.choice, Quot.sound]
```
