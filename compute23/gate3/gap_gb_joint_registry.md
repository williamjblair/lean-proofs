# Erdős 23 G-B joint-aggregation registry

Campaign branch: `codex/erdos23-rl-star`.

## Exact residual target

For a valid one-stub rooted instance `(B,M,w,x0)` on `n` vertices, put
`d=dist_B(w,x0)`, `s=n-1-d`, and
`Gamma=sum_{uv in M}(dist_B(u,v)+1)^2`.  The live RL* slice is

```text
n >= 14,
2 <= s,
2*s*p(d) < (d+1)^2,
|M| >= 2,
every interior w-x0 geodesic bridge has a side of size at most 3.
```

The target is `Gamma <= s*(2*d+2+s)+2*s*p(d)` under the strict Gamma
induction hypothesis.  A reformulation with equivalent strength is not a
new result.

## Route registry

| ID | Route | Proposed leverage | Initial status |
|---|---|---|---|
| GB-FLOW | RFC flow/cut duality | Sum a weighted laminar family of RFC cuts so every long demand receives quadratic credit while corridor capacity is counted once. | blocked as a proof route: cut domination does not imply multicommodity routing; retained only as BF-RL search context |
| GB-2E | Two-edge joint excess | Prove that two internal edges cannot simultaneously approach the single-edge bounds; test `sum(D_i-4)<=2*s-4` and capacity-corrected variants. | falsification-only: raw excess survives samples but is arithmetically insufficient for BF-RL without a separate multiplicity/cross-term bound |
| GB-DEL | Bridge-free deletion/induction | Delete or split at a corridor vertex whose removal preserves a smaller valid instance and quantify the exact distance/mass change. | partial success: every corridor bridge is eliminated; remaining graph is fully corridor-bridge-free with `d<=2s`, `s>=5` |
| GB-END | Endpoint-near series absorption | Extend the banked series theorem when one bridge component has at most three vertices by classifying the finite rooted block and paying its exact budget. | completed: exact gate dispatch, small-block retraction, and arbitrary endpoint-block absorption are proved |
| GB-CUTDUAL | Weighted RFC cut dual | Convert every integer vertex potential into an exact coarea inequality, then seek a laminar weighted-cut certificate majorizing `(D+1)^2` jointly. | interface completed in Lean; the certificate construction for BF-RL remains open and is not counted as closure |

## Mandatory falsification fixtures

Every candidate must be checked against:

1. balanced odd-cycle blow-ups at both long-thin and short-fat ends;
2. the `n=8` forced-hub double broom, which kills vertex-load bounds;
3. the `n=12` path-packing witness, which kills unit-congestion and volume aggregation;
4. both banked mixed/constant series fixtures;
5. all exhaustive rooted instances through the stored `n<=11, |M|<=2` corpus;
6. the exact thin-corridor families at `s=2,3`.

## Dead routes retained

- Do not use `sum D_i + d <= e(B)`; the `n=12` witness falsifies it.
- Do not sum the individual SE1/SE2 square bounds.
- Do not assign a uniform per-vertex load; the forced hub falsifies it.
- Do not invoke multicommodity routing from the RFC cut condition.
- Do not use order-11 flag algebras or a target-strength aggregation lemma.

## Banked frontier after this campaign

See `gap_gb_joint_findings.md` and `gap_gb_joint_audit.md`. The single open
node is BF-RL on a selected geodesic whose every edge is a nonbridge, with
the additional proved numerical restrictions `s>=5` and `d<=2s`.
