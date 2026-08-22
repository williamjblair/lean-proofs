# Case B: Formal Conjectures to LeanEval inheritance

Relation: `deterministic_generated_challenge_lineage`.

Status: `verified_at_pins`. `OeisA303656.conjecture` was resolved against an
exact Formal Conjectures source commit and blob, rendered with its required
definition, handed to the pinned schema-version-1 generator, reproduced twice
with no byte diff, and elaborated at LeanEval's separate target pins.

The frozen directory retains the exact request, context module, provenance
sidecar, trust-relevant generated files, and the full generated-file digest
inventory. The packet does not claim that the conjecture is true, that source
and target environments are generally compatible, or that a similar-looking
future declaration has unchanged meaning.

Reproduce from the exact Formal Conjectures adapter checkout:

```bash
export LEAN_EVAL_GENERATOR_BIN=/path/to/lean-eval-generator
python3 comparator/adapter/make_comparator_workspace.py \
  OeisA303656.conjecture --verify --out /tmp/lc-run-1
python3 comparator/adapter/make_comparator_workspace.py \
  OeisA303656.conjecture --verify --out /tmp/lc-run-2
diff -ru /tmp/lc-run-1 /tmp/lc-run-2
```

At the generated workspace:

```bash
lake update
lake exe cache get
lake build Challenge ChallengeDeps
```

`Challenge.lean` is expected to warn about `sorry`: it is an open benchmark
statement. A solver result and Comparator result are outside this packet.
