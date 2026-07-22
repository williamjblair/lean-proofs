# Erdős 686 — even-`k` certificate tables (generated)

The Lean files under this directory are machine-generated. Each one states a
small `decide`-checked fact about an allowed residue mask over `ZMod p` for one
prime `p`, grouped by the block length `k`:

```
K16/ K18/ K22/ K28/ K32/   one directory per even k
  Table…                   per-prime allowed-mask tables and their covers
  Packed…                  packed periodic-cover shards (k=22)
```

The committed `.lean` files are the artifact the kernel checks; the generators
below are recorded so the tables can be rebuilt and diffed.

## Generators

| Directory | Generator |
|-----------|-----------|
| `K22/Packed/` | `compute/campaign686/agent_k22_packed_kernel/generate_clean_cover.py` |
| `K22/…` (Archimedean) | `compute/campaign686/agent_k22_archimedean_lean/generate_lean.py` |
| `K28/` | `compute/campaign686/agent_t2_even_k28/generate_lean.py` |
| `K32/` | `compute/campaign686/agent_t2_even_k32/generate_lean.py` |
| `K18/`, `Table20*`, `Table24*` | earlier campaign generators under `compute/campaign686/` |

Each generator has a sibling `*_verify.py` that reproduces the exact-arithmetic
facts the tables encode, independent of Lean.

## Reproducing

The generators write the flat `Erdos686EvenK*` module names into
`ErdosProblems/`; `compute/relayout_generated.py` moves each to its nested path
and rewrites the imports, so the pipeline reproduces this tree exactly:

```bash
python3 compute/campaign686/agent_t2_even_k32/generate_lean.py
python3 compute/relayout_generated.py
python3 scripts/gen_aggregates.py
```

1020 of these files were confirmed byte-identical through that pipeline when the
tree was created (K22 packed 737, K28 141, K32 111, K22 Archimedean 31). The
K18 tables predate that check and were not re-run in the same pass.
