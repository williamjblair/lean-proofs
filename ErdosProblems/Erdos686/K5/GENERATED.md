# Erdős 686 — `k = 5` shards (generated)

The `P<pq>/` directories hold machine-generated Lean shards for the `k = 5`
case, one group per `(p, q)` window of the short-window lattice-sign argument.
A shard states a `decide`-checked kernel or cofactor fact for its window; there
are about 74 per window across 25 windows (`P11`…`P55`, plus the larger `P33`).

The files sitting directly in `K5/` (not under a `P<pq>/`) are the hand-written
mathematics the shards feed into: the puncture and no-go arguments, the
osculation dichotomy, the convergent and secant lemmas.

## Generators

| Files | Generator |
|-------|-----------|
| `P33/…` | `compute/campaign686/generate_k5_kernel_central.py` |
| puncture shards | `compute/campaign686/generate_k5_kernel_puncture.py` |
| non-common / puncture certificates | `compute/campaign686/generate_k5_noncommon_certificate.py`, `generate_k5_puncture_certificate.py` |

Each generator has a sibling verifier under `compute/campaign686/` that checks
the underlying exact arithmetic without Lean.

## Reproducing

The generators emit the flat `Erdos686K5*` module names into `ErdosProblems/`;
`compute/relayout_generated.py` moves them into this tree and rewrites imports:

```bash
python3 compute/campaign686/generate_k5_kernel_central.py
python3 compute/relayout_generated.py
python3 scripts/gen_aggregates.py
```

The committed `.lean` files are the artifact the axiom gate checks.
